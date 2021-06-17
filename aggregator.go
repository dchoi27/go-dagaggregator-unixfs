package dagaggregator

import (
	"context"
	"encoding/json"
	"io"
	"sort"
	"strings"

	"github.com/ipfs/go-cid"
	chunker "github.com/ipfs/go-ipfs-chunker"
	ipldformat "github.com/ipfs/go-ipld-format"
	"github.com/ipfs/go-merkledag"
	"github.com/ipfs/go-unixfs"
	"github.com/ipfs/go-unixfs/importer/balanced"
	importhelper "github.com/ipfs/go-unixfs/importer/helpers"
	"github.com/multiformats/go-multicodec"
	"golang.org/x/xerrors"
)

type RecordType string

const (
	DagAggregatePreamble RecordType = `DagAggregatePreamble`
	DagAggregateSummary  RecordType = `DagAggregateSummary`
	DagAggregateEntry    RecordType = `DagAggregateEntry`
)

// This must be something go-unixfs will sort first in the final structure
// ADL-free selectors-over-names are difficult in unixfs, so instead one can
// simply say "I want the cid of the first link of this structure" and be
// reasonably confident they will get to this file
const AggregateManifestFilename = `@BatchManifest.ndjson`

type ManifestPreamble struct {
	RecordType RecordType
	Version    uint
}

type ManifestSummary struct {
	RecordType      RecordType
	EntryCount      int
	EntriesSortedBy string
	Description     string
}

type ManifestDagEntry struct {
	rootCid       cid.Cid // private
	RecordType    RecordType
	DagCid        string
	NormalizedCid string `json:",omitempty"`
	DagSize       *uint64
	NodeCount     *uint64
	PathPrefixes  [2]string // not repeating the DagCid as segment#3 - too long
	PathIndexes   [3]int
}

type AggregateDagEntry struct {
	RootCid                   cid.Cid
	UniqueBlockCount          *uint64 // optional amount of blocks in dag, recorded in manifest
	UniqueBlockCumulativeSize *uint64 // optional dag size, used as the TSize in the unixfs link entry and recorded in manifest
}

type nodeMap map[string]*merkledag.ProtoNode

func Aggregate(ds ipldformat.DAGService, toAggregate []AggregateDagEntry) (aggregateRoot cid.Cid, err error) {

	if len(toAggregate) == 0 {
		return cid.Undef, xerrors.New("unable to aggregate empty set of entries")
	}

	dags := make(map[string]*ManifestDagEntry, 2*len(toAggregate))

	for _, d := range toAggregate {

		rootCidStr := d.RootCid.String()
		normCidStr := cidv1(d.RootCid).String()

		if d.UniqueBlockCount != nil && *d.UniqueBlockCount == 0 {
			return cid.Undef, xerrors.Errorf("unexpected unique blockcount of 0 for cid %s", rootCidStr)
		}

		if d.UniqueBlockCumulativeSize != nil && *d.UniqueBlockCumulativeSize == 0 && normCidStr != "bafkreihdwdcefgh4dqkjv67uzcmw7ojee6xedzdetojuzjevtenxquvyku" {
			return cid.Undef, xerrors.Errorf("unexpected cumulative size 0 for cid %s", rootCidStr)
		}

		if _, exists := dags[rootCidStr]; !exists {
			dags[rootCidStr] = &ManifestDagEntry{
				rootCid:       d.RootCid,
				RecordType:    DagAggregateEntry,
				NormalizedCid: normCidStr,
				DagCid:        rootCidStr,
				DagSize:       d.UniqueBlockCumulativeSize,
				NodeCount:     d.UniqueBlockCount,
			}
		}
	}

	// for every entry that ended up normalized, insert a norm-version as well
	for _, d := range dags {
		if _, normExists := dags[d.NormalizedCid]; !normExists {
			dags[d.NormalizedCid] = &ManifestDagEntry{
				rootCid:       cidv1(d.rootCid),
				RecordType:    DagAggregateEntry,
				NormalizedCid: d.NormalizedCid,
				DagCid:        d.NormalizedCid,
				DagSize:       d.DagSize,
				NodeCount:     d.NodeCount,
			}
		}
	}

	// unixfs sorts internally, so we need to pre-sort to match up insertion indices
	sortedDags := make([]*ManifestDagEntry, 0, len(dags))
	for _, d := range dags {
		sortedDags = append(sortedDags, d)
	}
	sort.Slice(sortedDags, func(i, j int) bool {
		return strings.Compare(sortedDags[i].DagCid, sortedDags[j].DagCid) < 0
	})

	// innermost layer, 4 bytes off end
	innerNodes := make(nodeMap)
	for _, d := range sortedDags {

		parentName := d.NormalizedCid[:3] + `...` + d.NormalizedCid[len(d.NormalizedCid)-4:]
		if _, exists := innerNodes[parentName]; !exists {
			innerNodes[parentName] = emptyDir()
		}

		var dagSize uint64
		if d.DagSize != nil {
			dagSize = *d.DagSize
		}

		if err := innerNodes[parentName].AddRawLink(d.DagCid, &ipldformat.Link{
			Size: dagSize,
			Cid:  d.rootCid,
		}); err != nil {
			return cid.Undef, err
		}
		d.PathIndexes[2] = len(innerNodes[parentName].Links()) - 1
	}

	newBlocks := make([]ipldformat.Node, 0, 1<<20)

	// secondary layer, 2 bytes off end ( drop the 2 second-to-last )
	outerNodes := make(nodeMap)
	for _, nodeName := range sortedNodeNames(innerNodes) {
		nd := innerNodes[nodeName]

		newBlocks = append(newBlocks, nd)
		parentName := nodeName[0:len(nodeName)-4] + nodeName[len(nodeName)-2:]
		if _, exists := outerNodes[parentName]; !exists {
			outerNodes[parentName] = emptyDir()
		}

		if err := outerNodes[parentName].AddNodeLink(nodeName, nd); err != nil {
			return cid.Undef, err
		}

		for _, innerDaglink := range nd.Links() {
			d := dags[innerDaglink.Name]
			d.PathPrefixes[1] = nodeName
			d.PathIndexes[1] = len(outerNodes[parentName].Links()) - 1
		}
	}

	// root
	root := emptyDir()
	for _, nodeName := range sortedNodeNames(outerNodes) {

		nd := outerNodes[nodeName]
		newBlocks = append(newBlocks, nd)
		if err := root.AddNodeLink(nodeName, nd); err != nil {
			return cid.Undef, err
		}

		for _, outerDagLink := range nd.Links() {
			for _, innerDaglink := range innerNodes[outerDagLink.Name].Links() {
				d := dags[innerDaglink.Name]
				d.PathPrefixes[0] = nodeName
				d.PathIndexes[0] = len(root.Links()) // no ...-1, idx#0 is left for the manifest
			}
		}
	}

	// now that we have all the paths correctly, assemble the manifest and add it to the root
	prdr, pwrr := io.Pipe()

	errCh := make(chan error, 1)
	go func() {

		defer func() {
			err := pwrr.Close()
			if err != nil {
				errCh <- err
			}
		}()

		j := json.NewEncoder(pwrr)

		err := j.Encode(ManifestPreamble{
			Version:    1,
			RecordType: DagAggregatePreamble,
		})
		if err != nil {
			errCh <- err
			return
		}

		err = j.Encode(ManifestSummary{
			RecordType:      DagAggregateSummary,
			EntriesSortedBy: "DagCid",
			Description:     "Aggregate of non-related DAGs, produced by github.com/filecoin-project/go-dagaggregator-unixfs",
			EntryCount:      len(sortedDags),
		})
		if err != nil {
			errCh <- err
			return
		}

		for _, d := range sortedDags {
			// do not duplicate the same cid twice in a row
			if d.NormalizedCid == d.DagCid {
				d.NormalizedCid = ""
			}
			err = j.Encode(d)
			if err != nil {
				errCh <- err
				return
			}
		}
	}()

	leaves, err := (&importhelper.DagBuilderParams{
		Dagserv:   ds,
		RawLeaves: true,
		Maxlinks:  8192 / 47, // importhelper.DefaultLinksPerBlock
		CidBuilder: cid.V1Builder{
			Codec:    uint64(multicodec.DagPb),
			MhType:   uint64(multicodec.Sha2_256),
			MhLength: 32,
		},
	}).New(chunker.NewSizeSplitter(prdr, 256<<10))
	if err != nil {
		return cid.Undef, err
	}

	manifest, err := balanced.Layout(leaves)
	if err != nil {
		return cid.Undef, err
	}
	if len(errCh) > 0 {
		return cid.Undef, <-errCh
	}

	if err = root.AddNodeLink(AggregateManifestFilename, manifest); err != nil {
		return cid.Undef, err
	}

	// we are done now, add everything
	newBlocks = append(newBlocks, root)
	ds.AddMany(context.Background(), newBlocks)

	return root.Cid(), nil
}

func sortedNodeNames(nodeMap nodeMap) []string {
	sortedNodeNames := make([]string, 0, len(nodeMap))
	for k := range nodeMap {
		sortedNodeNames = append(sortedNodeNames, k)
	}
	sort.Slice(sortedNodeNames, func(i, j int) bool {
		return sortedNodeNames[i] < sortedNodeNames[j]
	})
	return sortedNodeNames
}

func emptyDir() *merkledag.ProtoNode {
	nd := unixfs.EmptyDirNode()
	nd.SetCidBuilder(cid.V1Builder{
		Codec:    uint64(multicodec.DagPb),
		MhType:   uint64(multicodec.Sha2_256),
		MhLength: 32,
	})
	return nd
}

func cidv1(c cid.Cid) cid.Cid {
	if c.Version() == 1 {
		return c
	}
	return cid.NewCidV1(c.Type(), c.Hash())
}
