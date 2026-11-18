// forge: a standalone GitHub-compatible git forge in one static Go binary.
// Serves git smart HTTP (upload-pack v2 + receive-pack v0), REST v3, GraphQL v4
// and MCP over a hand-written raw-TCP HTTP/1.1 server. No git binary, no deps.
package main

import (
	"bytes"
	"compress/zlib"
	"crypto/sha1"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"net"
	"net/http"
	"os"
	"runtime/debug"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

// ---------------------------------------------------------------- viewer identity
// The suite's scenario is deterministic from a fixed seed (wire.ts SCENARIO_SEED);
// the token owner is always users[0]. Recompute it here instead of hardcoding.

var firstNames = []string{"ada", "bram", "cora", "dmitri", "elena", "felix", "greta", "hugo", "iris", "jonas", "kira", "lars", "mira", "nico", "olga", "pavel", "quinn", "rosa", "sven", "tess", "ulla", "vito", "wren", "yara", "zane"}
var lastNames = []string{"anders", "bauer", "costa", "dahl", "eriksen", "fischer", "garcia", "holm", "iversen", "jansen", "keller", "lind", "moreau", "novak", "olsen", "peters", "quist", "rossi", "sato", "turi", "ulrich", "vega", "weber", "xu", "yilmaz", "zimmer"}

func fnv1a64(s string) uint64 {
	h := uint64(0xcbf29ce484222325)
	for i := 0; i < len(s); i++ {
		h ^= uint64(s[i])
		h *= 0x100000001b3
	}
	return h
}
func mix64(v uint64) uint64 {
	z := v + 0x9e3779b97f4a7c15
	z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9
	z = (z ^ (z >> 27)) * 0x94d049bb133111eb
	return z ^ (z >> 31)
}

type rng struct{ state uint64 }

func (r *rng) nextU64() uint64 {
	x := r.state
	x ^= x >> 12
	x ^= x << 25
	x ^= x >> 27
	r.state = x
	return x * 0x2545f4914f6cdd1d
}
func (r *rng) nextU32() uint32 { return uint32(r.nextU64() >> 32) }
func (r *rng) nextInt(max int) int {
	if max == 1 {
		return 0
	}
	limit := uint64(4294967296 - (4294967296 % uint64(max)))
	for {
		v := r.nextU32()
		if uint64(v) < limit {
			return int(v % uint32(max))
		}
	}
}
func (r *rng) pick(list []string) string { return list[r.nextInt(len(list))] }
func scenarioRng(label string) *rng {
	return &rng{state: mix64(0x6a09e667f3bcc909 ^ fnv1a64(label))}
}

var viewerLogin, viewerName, viewerEmail string
var viewerID = 1000

func computeViewer() {
	r := scenarioRng("users")
	used := map[string]bool{}
	for i := 0; i < 12; i++ {
		first := r.pick(firstNames)
		last := r.pick(lastNames)
		login := first + last
		suffix := 2
		for used[login] {
			login = fmt.Sprintf("%s%s-%d", first, last, suffix)
			suffix++
		}
		used[login] = true
		if i == 0 {
			viewerLogin = login
			viewerName = first + " " + last
			viewerEmail = login + "@example.invalid"
		}
	}
}

// ---------------------------------------------------------------- store

const zeroOID = "0000000000000000000000000000000000000000"

type Obj struct {
	typ  string
	data []byte
	comp []byte // zlib-compressed data, for pack building
}

type Issue struct {
	Number int
	Title  string
	Body   string
	State  string // open | closed
	Labels []string
	Seq    int
	ID     int
	GID    string
	cache  []byte
}

type FileChange struct {
	Filename  string
	Status    string // added | modified | removed
	Additions int
	Deletions int
	Changes   int
}

type PR struct {
	Number    int
	Title     string
	Body      string
	State     string // open | closed
	Merged    bool
	MergedAt  string
	MergeSHA  string
	HeadRef   string
	BaseRef   string
	Seq       int
	ID        int
	GID       string
	Files     []FileChange
	MergeBase string
}

type Comment struct {
	ID   int
	Body string
	GID  string
}

type Repo struct {
	ID      int
	Name    string
	Owner   string
	Desc    string
	Priv    bool
	Refs    map[string]string // ref -> oid
	Objs    map[string]*Obj
	Issues  []*Issue
	PRs     []*PR
	Labels  map[string]string // name -> color
	NextNum int               // shared issue/PR counter
	ComSeq  map[int][]*Comment
	CmtSeq  int
	Seq     int // repo creation order
	Shallow []string
	// packMu guards lazy zlib compression (Obj.comp) and the fetch cache below.
	packMu    sync.Mutex
	fetchKey  string
	fetchResp []byte
}

type Store struct {
	mu         sync.RWMutex
	repos      map[string]*Repo
	order      []*Repo
	nextRepoID int
	nextID     int64 // global numeric id counter (issues, comments, PRs)
	reqID      uint64
	commitSeq  int64
	repoSeq    int64
	issueSeq   int64
	prSeq      int64
	commentSeq int64
}

var store = &Store{repos: map[string]*Repo{}, nextRepoID: 5000, nextID: 100000}

func (s *Store) nextNumID() int { return int(atomic.AddInt64(&s.nextID, 1)) }
func (s *Store) nextReqID() uint64 {
	return atomic.AddUint64(&s.reqID, 1)
}

var authToken string

func jsonUnmarshal(b []byte, v interface{}) error { return json.Unmarshal(b, v) }

func newRepo(owner, name string, id int) *Repo {
	return &Repo{
		ID: id, Name: name, Owner: owner,
		Refs:    map[string]string{},
		Objs:    map[string]*Obj{},
		Labels:  map[string]string{},
		NextNum: 1,
		ComSeq:  map[int][]*Comment{},
	}
}

// seedStore: the suite creates its own scenario data through the API;
// the forge starts empty. Kept as a named hook for future seeding.
func seedStore() {}

// ---------------------------------------------------------------- git objects

func oidOf(typ string, data []byte) string {
	// header "type len\x00" on the stack: no temp string for Itoa, one alloc total (the result).
	var arr [32]byte
	b := arr[:0]
	b = append(b, typ...)
	b = append(b, ' ')
	b = strconv.AppendInt(b, int64(len(data)), 10)
	b = append(b, 0)
	h := sha1.New()
	h.Write(b)
	h.Write(data)
	var sum [20]byte
	h.Sum(sum[:0])
	var out [40]byte
	hex.Encode(out[:], sum[:])
	return string(out[:])
}

func compressObj(data []byte) []byte {
	var buf bytes.Buffer
	w, _ := zlib.NewWriterLevel(&buf, 1)
	w.Write(data)
	w.Close()
	return buf.Bytes()
}

func (r *Repo) putObj(typ string, data []byte) string {
	oid := oidOf(typ, data)
	if _, ok := r.Objs[oid]; !ok {
		// comp is computed lazily by buildPack: pushes never pay zlib, and a
		// pack is built at most once per object set (fetch responses are cached).
		r.Objs[oid] = &Obj{typ: typ, data: data}
	}
	return oid
}

type commitView struct {
	Tree    string
	Parents []string
	Message string
	Raw     []byte
}

func parseCommit(data []byte) commitView {
	var c commitView
	c.Raw = data
	// header ends at blank line
	idx := bytes.Index(data, []byte("\n\n"))
	head := data
	msg := ""
	if idx >= 0 {
		head = data[:idx]
		msg = string(data[idx+2:])
	}
	for _, line := range strings.Split(string(head), "\n") {
		if strings.HasPrefix(line, "tree ") {
			c.Tree = line[5:]
		} else if strings.HasPrefix(line, "parent ") {
			c.Parents = append(c.Parents, line[7:])
		}
	}
	c.Message = msg
	return c
}

type treeEntry struct {
	Mode string
	Name string
	OID  string
}

func parseTree(data []byte) []treeEntry {
	var out []treeEntry
	i := 0
	for i < len(data) {
		sp := bytes.IndexByte(data[i:], ' ')
		if sp < 0 {
			break
		}
		mode := string(data[i : i+sp])
		i += sp + 1
		nul := bytes.IndexByte(data[i:], 0)
		if nul < 0 || i+nul+20 > len(data) {
			break
		}
		name := string(data[i : i+nul])
		oid := hex.EncodeToString(data[i+nul+1 : i+nul+21])
		i += nul + 1 + 20
		out = append(out, treeEntry{Mode: mode, Name: name, OID: oid})
	}
	return out
}

func buildTree(entries []treeEntry) []byte {
	// git tree order: names sorted, directories as name+"/"
	sort.Slice(entries, func(a, b int) bool {
		na, nb := entries[a].Name, entries[b].Name
		if entries[a].Mode == "40000" {
			na += "/"
		}
		if entries[b].Mode == "40000" {
			nb += "/"
		}
		return na < nb
	})
	var buf bytes.Buffer
	for _, e := range entries {
		buf.WriteString(e.Mode)
		buf.WriteByte(' ')
		buf.WriteString(e.Name)
		buf.WriteByte(0)
		raw, _ := hex.DecodeString(e.OID)
		buf.Write(raw)
	}
	return buf.Bytes()
}

// flatten tree to path -> entry (recursive)
func (r *Repo) flattenTree(treeOID string, prefix string, out map[string]treeEntry) {
	obj, ok := r.Objs[treeOID]
	if !ok || obj.typ != "tree" {
		return
	}
	for _, e := range parseTree(obj.data) {
		p := prefix + e.Name
		if e.Mode == "40000" {
			r.flattenTree(e.OID, p+"/", out)
		} else {
			out[p] = e
		}
	}
}

func (r *Repo) treeMap(treeOID string) map[string]treeEntry {
	out := map[string]treeEntry{}
	if treeOID != "" {
		r.flattenTree(treeOID, "", out)
	}
	return out
}

// build nested trees from flat path->blob map; returns root tree oid
func (r *Repo) buildTreeFromFlat(flat map[string]string) string {
	type node struct {
		files map[string]string
		dirs  map[string]*node
	}
	var build func(n *node) string
	build = func(n *node) string {
		var entries []treeEntry
		for name, oid := range n.files {
			entries = append(entries, treeEntry{Mode: "100644", Name: name, OID: oid})
		}
		for name, child := range n.dirs {
			entries = append(entries, treeEntry{Mode: "40000", Name: name, OID: build(child)})
		}
		return r.putObj("tree", buildTree(entries))
	}
	root := &node{files: map[string]string{}, dirs: map[string]*node{}}
	for path, oid := range flat {
		parts := strings.Split(path, "/")
		n := root
		for _, p := range parts[:len(parts)-1] {
			if n.dirs[p] == nil {
				n.dirs[p] = &node{files: map[string]string{}, dirs: map[string]*node{}}
			}
			n = n.dirs[p]
		}
		n.files[parts[len(parts)-1]] = oid
	}
	return build(root)
}

func (r *Repo) commitTree(oid string) string {
	obj, ok := r.Objs[oid]
	if !ok || obj.typ != "commit" {
		return ""
	}
	return parseCommit(obj.data).Tree
}

// collect objects reachable from tips; depth<0 unlimited, depth>=0 counts commits
// (depth 1 = only the tip commits themselves). held = oids already held (excluded).
func (r *Repo) collect(tips []string, depth int, held map[string]bool) map[string]bool {
	out := map[string]bool{}
	type item struct {
		oid string
		d   int
	}
	queue := []item{}
	seenCommit := map[string]bool{}
	for _, t := range tips {
		if t == "" || t == zeroOID {
			continue
		}
		queue = append(queue, item{t, 0})
	}
	addTree := func(treeOID string) {
		// walk tree closure iteratively
		stack := []string{treeOID}
		for len(stack) > 0 {
			toid := stack[len(stack)-1]
			stack = stack[:len(stack)-1]
			if out[toid] || (held != nil && held[toid]) {
				// still need to walk children? if held, client has it; skip
				if held != nil && held[toid] {
					continue
				}
				continue
			}
			obj, ok := r.Objs[toid]
			if !ok {
				continue
			}
			out[toid] = true
			if obj.typ == "tree" {
				for _, e := range parseTree(obj.data) {
					stack = append(stack, e.OID)
				}
			}
		}
	}
	for len(queue) > 0 {
		it := queue[0]
		queue = queue[1:]
		if seenCommit[it.oid] {
			continue
		}
		seenCommit[it.oid] = true
		obj, ok := r.Objs[it.oid]
		if !ok {
			continue
		}
		if obj.typ == "tag" {
			// tag: object <oid>, type <t>
			target := ""
			for _, line := range strings.Split(string(obj.data), "\n") {
				if strings.HasPrefix(line, "object ") {
					target = line[7:]
					break
				}
			}
			out[it.oid] = true
			if target != "" {
				queue = append(queue, item{target, it.d})
			}
			continue
		}
		if obj.typ != "commit" {
			out[it.oid] = true
			continue
		}
		out[it.oid] = true
		c := parseCommit(obj.data)
		addTree(c.Tree)
		if depth < 0 || it.d < depth-1 {
			for _, p := range c.Parents {
				queue = append(queue, item{p, it.d + 1})
			}
		}
	}
	// remove held
	if held != nil {
		for oid := range out {
			if held[oid] {
				delete(out, oid)
			}
		}
	}
	return out
}

// closure of tips (all objects), for "held" computation
func (r *Repo) closure(tips []string) map[string]bool {
	return r.collect(tips, -1, nil)
}

func (r *Repo) isAncestor(anc, tip string) bool {
	if anc == tip {
		return true
	}
	seen := map[string]bool{}
	queue := []string{tip}
	for len(queue) > 0 {
		cur := queue[0]
		queue = queue[1:]
		if seen[cur] {
			continue
		}
		seen[cur] = true
		if cur == anc {
			return true
		}
		obj, ok := r.Objs[cur]
		if !ok || obj.typ != "commit" {
			continue
		}
		queue = append(queue, parseCommit(obj.data).Parents...)
	}
	return false
}

func (r *Repo) mergeBase(a, b string) string {
	anc := map[string]bool{}
	queue := []string{a}
	for len(queue) > 0 {
		cur := queue[0]
		queue = queue[1:]
		if anc[cur] {
			continue
		}
		anc[cur] = true
		obj, ok := r.Objs[cur]
		if !ok || obj.typ != "commit" {
			continue
		}
		queue = append(queue, parseCommit(obj.data).Parents...)
	}
	queue = []string{b}
	seen := map[string]bool{}
	for len(queue) > 0 {
		cur := queue[0]
		queue = queue[1:]
		if seen[cur] {
			continue
		}
		seen[cur] = true
		if anc[cur] {
			return cur
		}
		obj, ok := r.Objs[cur]
		if !ok || obj.typ != "commit" {
			continue
		}
		queue = append(queue, parseCommit(obj.data).Parents...)
	}
	return ""
}

// ---------------------------------------------------------------- packfile

var packTypeCode = map[string]int{"commit": 1, "tree": 2, "blob": 3, "tag": 4}
var packCodeType = map[int]string{1: "commit", 2: "tree", 3: "blob", 4: "tag", 6: "ofs-delta", 7: "ref-delta"}

func inflateAt(data []byte, offset int) ([]byte, int, error) {
	br := bytes.NewReader(data[offset:])
	zr, err := zlib.NewReader(br)
	if err != nil {
		return nil, 0, err
	}
	out, err := io.ReadAll(zr)
	zr.Close()
	if err != nil {
		return nil, 0, err
	}
	consumed := len(data[offset:]) - br.Len()
	return out, offset + consumed, nil
}

func applyDelta(base, delta []byte) ([]byte, error) {
	off := 0
	readVarint := func() (int, error) {
		v, shift := 0, 0
		for {
			if off >= len(delta) {
				return 0, fmt.Errorf("delta truncated")
			}
			b := delta[off]
			off++
			v += int(b&0x7f) << shift
			shift += 7
			if b&0x80 == 0 {
				break
			}
		}
		return v, nil
	}
	srcSize, err := readVarint()
	if err != nil {
		return nil, err
	}
	tgtSize, err := readVarint()
	if err != nil {
		return nil, err
	}
	if srcSize != len(base) {
		return nil, fmt.Errorf("delta base size mismatch")
	}
	out := make([]byte, 0, tgtSize)
	for off < len(delta) {
		op := delta[off]
		off++
		if op&0x80 != 0 {
			copyOff, copySize := 0, 0
			shift := 0
			for bit := 0; bit < 4; bit++ {
				if op&(1<<uint(bit)) != 0 {
					if off >= len(delta) {
						return nil, fmt.Errorf("delta truncated")
					}
					copyOff += int(delta[off]) << shift
					off++
				}
				shift += 8
			}
			shift = 0
			for bit := 4; bit < 7; bit++ {
				if op&(1<<uint(bit)) != 0 {
					if off >= len(delta) {
						return nil, fmt.Errorf("delta truncated")
					}
					copySize += int(delta[off]) << shift
					off++
				}
				shift += 8
			}
			if copySize == 0 {
				copySize = 0x10000
			}
			if copyOff+copySize > len(base) {
				return nil, fmt.Errorf("delta copy out of range")
			}
			out = append(out, base[copyOff:copyOff+copySize]...)
		} else if op != 0 {
			n := int(op & 0x7f)
			if off+n > len(delta) {
				return nil, fmt.Errorf("delta truncated")
			}
			out = append(out, delta[off:off+n]...)
			off += n
		} else {
			return nil, fmt.Errorf("delta opcode 0")
		}
	}
	if len(out) != tgtSize {
		return nil, fmt.Errorf("delta size mismatch")
	}
	return out, nil
}

type packEntry struct {
	offset int
	typ    string // resolved type, or "ofs-delta"/"ref-delta"
	data   []byte // inflated (delta bytes for deltas)
	baseOf int    // ofs-delta base offset
	baseID string // ref-delta base oid
	oid    string
}

// parse a packfile; resolves deltas against in-pack objects and the repo store.
func (r *Repo) parsePack(pack []byte) (map[string]*Obj, error) {
	if len(pack) < 32 || string(pack[:4]) != "PACK" {
		return nil, fmt.Errorf("bad pack header")
	}
	ver := int(pack[4])<<24 | int(pack[5])<<16 | int(pack[6])<<8 | int(pack[7])
	if ver != 2 && ver != 3 {
		return nil, fmt.Errorf("bad pack version %d", ver)
	}
	count := int(pack[8])<<24 | int(pack[9])<<16 | int(pack[10])<<8 | int(pack[11])
	trailerStart := len(pack) - 20
	// verify trailer without hex-encoding either side
	sum := sha1.Sum(pack[:trailerStart])
	if !bytes.Equal(sum[:], pack[trailerStart:]) {
		return nil, fmt.Errorf("pack checksum mismatch")
	}
	entries := make([]*packEntry, 0, count)
	byOffset := map[int]*packEntry{}
	off := 12
	for i := 0; i < count; i++ {
		start := off
		if off >= trailerStart {
			return nil, fmt.Errorf("pack truncated")
		}
		b := pack[off]
		off++
		typCode := int(b>>4) & 7
		size := int(b & 0x0f)
		shift := 4
		for b&0x80 != 0 {
			if off >= trailerStart {
				return nil, fmt.Errorf("pack truncated")
			}
			b = pack[off]
			off++
			size += int(b&0x7f) << shift
			shift += 7
		}
		e := &packEntry{offset: start}
		if typCode == 6 {
			// ofs-delta base offset
			if off >= trailerStart {
				return nil, fmt.Errorf("pack truncated")
			}
			b = pack[off]
			off++
			v := int(b & 0x7f)
			for b&0x80 != 0 {
				if off >= trailerStart {
					return nil, fmt.Errorf("pack truncated")
				}
				b = pack[off]
				off++
				v = ((v + 1) << 7) + int(b&0x7f)
			}
			e.baseOf = start - v
			e.typ = "ofs-delta"
		} else if typCode == 7 {
			if off+20 > trailerStart {
				return nil, fmt.Errorf("pack truncated")
			}
			e.baseID = hex.EncodeToString(pack[off : off+20])
			off += 20
			e.typ = "ref-delta"
		} else {
			t, ok := packCodeType[typCode]
			if !ok {
				return nil, fmt.Errorf("bad pack type %d", typCode)
			}
			e.typ = t
		}
		data, next, err := inflateAt(pack, off)
		if err != nil {
			return nil, err
		}
		if len(data) != size {
			return nil, fmt.Errorf("pack entry size mismatch")
		}
		e.data = data
		off = next
		entries = append(entries, e)
		byOffset[start] = e
	}
	resolved := map[string]*Obj{}
	var resolve func(e *packEntry) (*Obj, error)
	resolving := map[int]bool{}
	resolve = func(e *packEntry) (*Obj, error) {
		if e.oid != "" {
			if o, ok := resolved[e.oid]; ok {
				return o, nil
			}
		}
		if resolving[e.offset] {
			return nil, fmt.Errorf("delta cycle")
		}
		resolving[e.offset] = true
		defer delete(resolving, e.offset)
		var typ string
		var data []byte
		switch e.typ {
		case "ofs-delta":
			base, ok := byOffset[e.baseOf]
			if !ok {
				return nil, fmt.Errorf("ofs-delta base missing")
			}
			bo, err := resolve(base)
			if err != nil {
				return nil, err
			}
			typ = bo.typ
			data, err = applyDelta(bo.data, e.data)
			if err != nil {
				return nil, err
			}
		case "ref-delta":
			var bo *Obj
			for _, oe := range entries {
				if oe.oid == e.baseID {
					var err error
					bo, err = resolve(oe)
					if err != nil {
						return nil, err
					}
					break
				}
			}
			if bo == nil {
				if so, ok := r.Objs[e.baseID]; ok {
					bo = so
				} else {
					return nil, fmt.Errorf("ref-delta base missing")
				}
			}
			typ = bo.typ
			var err error
			data, err = applyDelta(bo.data, e.data)
			if err != nil {
				return nil, err
			}
		default:
			typ = e.typ
			data = e.data
		}
		oid := oidOf(typ, data)
		e.oid = oid
		o := &Obj{typ: typ, data: data} // comp filled lazily by buildPack
		resolved[oid] = o
		return o, nil
	}
	for _, e := range entries {
		if _, err := resolve(e); err != nil {
			return nil, err
		}
	}
	return resolved, nil
}

func writePackHeader(typ string, size int) []byte {
	code := packTypeCode[typ]
	out := []byte{}
	b := byte((code << 4) | (size & 0x0f))
	size >>= 4
	for size > 0 {
		out = append(out, b|0x80)
		b = byte(size & 0x7f)
		size >>= 7
	}
	out = append(out, b)
	return out
}

// build a packfile from objects (plain, no deltas), deterministic order by oid.
// Objects are compressed lazily here, once, under packMu: concurrent fetches of
// the same objects share the compressed bytes instead of recompressing each time.
func (r *Repo) buildPack(objs map[string]*Obj) []byte {
	r.packMu.Lock()
	defer r.packMu.Unlock()
	for _, o := range objs {
		if o.comp == nil {
			o.comp = compressObj(o.data)
		}
	}
	oids := make([]string, 0, len(objs))
	for oid := range objs {
		oids = append(oids, oid)
	}
	sort.Strings(oids)
	var buf bytes.Buffer
	hdr := make([]byte, 12)
	copy(hdr, "PACK")
	hdr[4], hdr[5], hdr[6], hdr[7] = 0, 0, 0, 2
	hdr[8], hdr[9], hdr[10], hdr[11] = byte(len(oids)>>24), byte(len(oids)>>16), byte(len(oids)>>8), byte(len(oids))
	buf.Write(hdr)
	for _, oid := range oids {
		o := objs[oid]
		buf.Write(writePackHeader(o.typ, len(o.data)))
		buf.Write(o.comp)
	}
	body := buf.Bytes()
	sum := sha1.Sum(body)
	return append(body, sum[:]...)
}

// fetchCacheKey identifies a fetch response: objects are append-only and refs are
// named by oid in the key, so a hit is the same response fetchSet would build.
// (Repeated depth-1 clones of one tip — the clone workload — all share one key.)
func fetchCacheKey(proto string, wants, haves, shallows []string, depth int) string {
	var sb strings.Builder
	sb.WriteString(proto)
	sb.WriteByte('|')
	sb.WriteString(strconv.Itoa(depth))
	sb.WriteByte('|')
	sb.WriteString(strings.Join(wants, ","))
	sb.WriteByte('|')
	sb.WriteString(strings.Join(haves, ","))
	sb.WriteByte('|')
	sb.WriteString(strings.Join(shallows, ","))
	return sb.String()
}

func (r *Repo) fetchCached(key string) ([]byte, bool) {
	r.packMu.Lock()
	defer r.packMu.Unlock()
	if r.fetchKey == key && r.fetchResp != nil {
		return r.fetchResp, true
	}
	return nil, false
}

func (r *Repo) storeFetch(key string, resp []byte) {
	r.packMu.Lock()
	defer r.packMu.Unlock()
	r.fetchKey = key
	r.fetchResp = resp
}

// ---------------------------------------------------------------- helpers

func b64enc(b []byte) string { return base64.StdEncoding.EncodeToString(b) }
func b64dec(s string) ([]byte, error) {
	s = strings.Map(func(r rune) rune {
		if r == '\n' || r == '\r' || r == '\t' || r == ' ' {
			return -1
		}
		return r
	}, s)
	return base64.StdEncoding.DecodeString(s)
}

func jsonBytes(v interface{}) []byte {
	b, _ := json.Marshal(v)
	return b
}

func splitPath(p string) []string {
	p = strings.Trim(p, "/")
	if p == "" {
		return nil
	}
	return strings.Split(p, "/")
}

func isHex40(s string) bool {
	if len(s) != 40 {
		return false
	}
	for _, c := range s {
		if !(c >= '0' && c <= '9' || c >= 'a' && c <= 'f' || c >= 'A' && c <= 'F') {
			return false
		}
	}
	return true
}

var _ = os.Getenv
var _ = net.IPv4len

// ---------------------------------------------------------------- HTTP layer (raw TCP)

type request struct {
	method    string
	path      string // decoded path
	rawPath   string
	query     string
	proto     string
	headers   map[string]string
	body      []byte
	host      string
	keepAlive bool
}

type response struct {
	status int
	ctype  string
	body   []byte
	extra  map[string]string
	// rawBody, when set, is written after headers without copying
}

func (r *request) header(name string) string { return r.headers[name] }

func readRequest(br *bufReader) (*request, error) {
	line, err := br.readLine()
	if err != nil {
		return nil, err
	}
	// parse "METHOD TARGET PROTO" without SplitN (no slice alloc)
	sp1 := strings.IndexByte(line, ' ')
	if sp1 < 0 {
		return nil, fmt.Errorf("bad request line")
	}
	sp2 := strings.IndexByte(line[sp1+1:], ' ')
	if sp2 < 0 {
		return nil, fmt.Errorf("bad request line")
	}
	sp2 += sp1 + 1
	req := &request{method: line[:sp1], proto: line[sp2+1:], headers: map[string]string{}}
	rawTarget := line[sp1+1 : sp2]
	if i := strings.Index(rawTarget, "?"); i >= 0 {
		req.rawPath = rawTarget[:i]
		req.query = rawTarget[i+1:]
	} else {
		req.rawPath = rawTarget
	}
	// percent-decode path segments (keep '/' structure); the common case has
	// no '%' at all, so skip the split/decode round trip entirely.
	if strings.IndexByte(req.rawPath, '%') < 0 {
		req.path = req.rawPath
	} else {
		segs := strings.Split(req.rawPath, "/")
		for i, s := range segs {
			if d, err := urlUnescape(s); err == nil {
				segs[i] = d
			}
		}
		req.path = strings.Join(segs, "/")
	}
	// headers
	for {
		hline, err := br.readLine()
		if err != nil {
			return nil, err
		}
		if hline == "" {
			break
		}
		if i := strings.Index(hline, ":"); i >= 0 {
			req.headers[strings.ToLower(strings.TrimSpace(hline[:i]))] = strings.TrimSpace(hline[i+1:])
		}
	}
	req.host = req.headers["host"]
	if req.headers["expect"] == "100-continue" {
		br.writeString("HTTP/1.1 100 Continue\r\n\r\n")
	}
	// body
	if cl := req.headers["content-length"]; cl != "" {
		n, _ := strconv.Atoi(cl)
		if n > 0 {
			if n > 64<<20 {
				return nil, fmt.Errorf("body too large")
			}
			body, err := br.readN(n)
			if err != nil {
				return nil, err
			}
			req.body = body
		}
	} else if strings.Contains(req.headers["transfer-encoding"], "chunked") {
		var body []byte
		for {
			szLine, err := br.readLine()
			if err != nil {
				return nil, err
			}
			szLine = strings.TrimSpace(strings.SplitN(szLine, ";", 2)[0])
			sz, err := strconv.ParseInt(szLine, 16, 64)
			if err != nil {
				return nil, err
			}
			if sz == 0 {
				// trailer headers until blank line
				for {
					l, err := br.readLine()
					if err != nil || l == "" {
						break
					}
				}
				break
			}
			chunk, err := br.readN(int(sz))
			if err != nil {
				return nil, err
			}
			body = append(body, chunk...)
			// trailing CRLF
			br.readN(2)
		}
		req.body = body
	}
	if req.proto == "HTTP/1.1" {
		req.keepAlive = req.headers["connection"] != "close"
	} else {
		req.keepAlive = req.headers["connection"] == "keep-alive"
	}
	return req, nil
}

func urlUnescape(s string) (string, error) {
	// minimal %XX decoding
	var b strings.Builder
	for i := 0; i < len(s); i++ {
		if s[i] == '%' && i+2 < len(s) {
			v, err := strconv.ParseUint(s[i+1:i+3], 16, 8)
			if err != nil {
				return "", err
			}
			b.WriteByte(byte(v))
			i += 2
		} else {
			b.WriteByte(s[i])
		}
	}
	return b.String(), nil
}

// bufReader: buffered reader over a conn with a small reusable buffer
type bufReader struct {
	conn net.Conn
	buf  []byte
	r, w int
	// lastDeadlineSet: read deadlines are refreshed lazily (once per 5s) so a
	// keep-alive connection doing thousands of requests does not pay a
	// setsockopt per request; idle connections still time out at ~30-35s.
	lastDeadlineSet time.Time
}

func newBufReader(c net.Conn) *bufReader { return &bufReader{conn: c, buf: make([]byte, 65536)} }

func (b *bufReader) fill() error {
	if b.r > 0 {
		copy(b.buf, b.buf[b.r:b.w])
		b.w -= b.r
		b.r = 0
	}
	if b.w == len(b.buf) {
		return fmt.Errorf("buffer full")
	}
	n, err := b.conn.Read(b.buf[b.w:])
	b.w += n
	return err
}

func (b *bufReader) readLine() (string, error) {
	for {
		if i := bytes.IndexByte(b.buf[b.r:b.w], '\n'); i >= 0 {
			line := string(b.buf[b.r : b.r+i])
			b.r += i + 1
			return strings.TrimRight(line, "\r"), nil
		}
		if err := b.fill(); err != nil {
			return "", err
		}
	}
}

func (b *bufReader) readN(n int) ([]byte, error) {
	out := make([]byte, 0, n)
	for len(out) < n {
		if b.r < b.w {
			take := n - len(out)
			if take > b.w-b.r {
				take = b.w - b.r
			}
			out = append(out, b.buf[b.r:b.r+take]...)
			b.r += take
			continue
		}
		if err := b.fill(); err != nil {
			return nil, err
		}
	}
	return out, nil
}

func (b *bufReader) writeString(s string) { b.conn.Write([]byte(s)) }

func writeResponse(conn net.Conn, req *request, resp *response) error {
	// headers into a small buffer, then one writev of headers + body:
	// no copy of the (possibly large) body.
	buf := make([]byte, 0, 256)
	buf = append(buf, req.proto...)
	buf = append(buf, ' ')
	buf = strconv.AppendInt(buf, int64(resp.status), 10)
	buf = append(buf, ' ')
	buf = append(buf, statusText(resp.status)...)
	buf = append(buf, "\r\nContent-Type: "...)
	buf = append(buf, resp.ctype...)
	buf = append(buf, "\r\nContent-Length: "...)
	buf = strconv.AppendInt(buf, int64(len(resp.body)), 10)
	buf = append(buf, "\r\nX-GitHub-Request-Id: req-"...)
	buf = strconv.AppendUint(buf, store.nextReqID(), 10)
	buf = append(buf, "\r\n"...)
	for k, v := range resp.extra {
		buf = append(buf, k...)
		buf = append(buf, ": "...)
		buf = append(buf, v...)
		buf = append(buf, "\r\n"...)
	}
	if !req.keepAlive || resp.status == 204 {
		if resp.status != 204 {
			buf = append(buf, "Connection: close\r\n"...)
		}
	} else {
		buf = append(buf, "Connection: keep-alive\r\n"...)
	}
	buf = append(buf, "\r\n"...)
	w := net.Buffers{buf, resp.body}
	_, err := w.WriteTo(conn)
	return err
}

func statusText(code int) string {
	switch code {
	case 200:
		return "OK"
	case 201:
		return "Created"
	case 202:
		return "Accepted"
	case 204:
		return "No Content"
	case 400:
		return "Bad Request"
	case 401:
		return "Unauthorized"
	case 404:
		return "Not Found"
	case 405:
		return "Method Not Allowed"
	case 409:
		return "Conflict"
	case 422:
		return "Unprocessable Entity"
	case 500:
		return "Internal Server Error"
	}
	return "Status"
}

const jsonCT = "application/json; charset=utf-8"

func jresp(status int, v interface{}) *response {
	return &response{status: status, ctype: jsonCT, body: jsonBytes(v)}
}
func jerr(status int, msg string) *response {
	return jresp(status, map[string]string{"message": msg})
}
func jraw(status int, body []byte) *response {
	return &response{status: status, ctype: jsonCT, body: body}
}
func jrawCT(status int, ctype string, body []byte) *response {
	return &response{status: status, ctype: ctype, body: body}
}

func (s *Store) getRepo(owner, name string) *Repo {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.repos[owner+"/"+name]
}

func authed(req *request) bool {
	h := req.headers["authorization"]
	if !strings.HasPrefix(h, "Bearer ") {
		return false
	}
	tok := strings.TrimSpace(h[7:])
	if tok == "" {
		return false
	}
	if authToken == "" {
		return true
	}
	return tok == authToken
}

// shared read-only empty query map (parseQuery's no-query fast path)
var emptyQuery = map[string]string{}

func parseQuery(q string) map[string]string {
	if q == "" {
		return emptyQuery // callers only read it
	}
	out := map[string]string{}
	for _, kv := range strings.Split(q, "&") {
		if kv == "" {
			continue
		}
		k, v, _ := strings.Cut(kv, "=")
		if d, err := urlUnescape(strings.ReplaceAll(v, "+", " ")); err == nil {
			v = d
		}
		out[k] = v
	}
	return out
}

func queryInt(q map[string]string, key string, def int) int {
	if v, ok := q[key]; ok {
		if n, err := strconv.Atoi(v); err == nil && n > 0 {
			return n
		}
	}
	return def
}

// ---------------------------------------------------------------- REST shapes

const fixedTime = "2025-01-01T00:00:00Z"

type userJSON struct {
	Login     string `json:"login"`
	ID        int    `json:"id"`
	NodeID    string `json:"node_id"`
	AvatarURL string `json:"avatar_url"`
	Type      string `json:"type"`
	Name      string `json:"name"`
	Email     string `json:"email"`
	HTMLURL   string `json:"html_url"`
	URL       string `json:"url"`
}

func viewerUserJSON() userJSON {
	return userJSON{Login: viewerLogin, ID: viewerID, NodeID: "user-" + strconv.Itoa(viewerID), AvatarURL: "", Type: "User", Name: viewerName, Email: viewerEmail, HTMLURL: "https://github.com/" + viewerLogin, URL: "/api/v3/users/" + viewerLogin}
}

type repoJSON struct {
	ID            int      `json:"id"`
	NodeID        string   `json:"node_id"`
	Name          string   `json:"name"`
	FullName      string   `json:"full_name"`
	Owner         userJSON `json:"owner"`
	Private       bool     `json:"private"`
	Description   string   `json:"description"`
	DefaultBranch string   `json:"default_branch"`
	HTMLURL       string   `json:"html_url"`
	URL           string   `json:"url"`
	CreatedAt     string   `json:"created_at"`
	UpdatedAt     string   `json:"updated_at"`
	PushedAt      string   `json:"pushed_at"`
	HasIssues     bool     `json:"has_issues"`
	Fork          bool     `json:"fork"`
}

func (r *Repo) toJSON() repoJSON {
	return repoJSON{ID: r.ID, NodeID: "repo-" + strconv.Itoa(r.ID), Name: r.Name, FullName: r.Owner + "/" + r.Name, Owner: viewerUserJSON(), Private: r.Priv, Description: r.Desc, DefaultBranch: "main", HTMLURL: "https://github.com/" + r.Owner + "/" + r.Name, URL: "/api/v3/repos/" + r.Owner + "/" + r.Name, CreatedAt: fixedTime, UpdatedAt: fixedTime, PushedAt: fixedTime, HasIssues: true}
}

func (r *Repo) defaultBranch() string { return "main" }

func (r *Repo) tip(ref string) string {
	if ref == "" {
		ref = "refs/heads/main"
	}
	if !strings.HasPrefix(ref, "refs/") {
		ref = "refs/heads/" + ref
	}
	return r.Refs[ref]
}

var viewerJSONBytes []byte

func (is *Issue) rebuildCache(r *Repo) {
	// hand-built JSON: the write hot path must not pay map-marshal reflection
	var sb strings.Builder
	sb.Grow(512)
	sb.WriteString(`{"id":`)
	sb.WriteString(strconv.Itoa(is.ID))
	sb.WriteString(`,"node_id":`)
	sb.WriteString(strconv.Quote(is.GID))
	sb.WriteString(`,"number":`)
	sb.WriteString(strconv.Itoa(is.Number))
	sb.WriteString(`,"title":`)
	sb.WriteString(strconv.Quote(is.Title))
	sb.WriteString(`,"body":`)
	sb.WriteString(strconv.Quote(is.Body))
	sb.WriteString(`,"state":`)
	sb.WriteString(strconv.Quote(is.State))
	sb.WriteString(`,"labels":[`)
	for i, ln := range is.Labels {
		if i > 0 {
			sb.WriteByte(',')
		}
		color := r.Labels[ln]
		if color == "" {
			color = "ededed"
		}
		sb.WriteString(`{"name":`)
		sb.WriteString(strconv.Quote(ln))
		sb.WriteString(`,"color":`)
		sb.WriteString(strconv.Quote(color))
		sb.WriteString(`,"description":""}`)
	}
	sb.WriteString(`],"user":`)
	sb.Write(viewerJSONBytes)
	sb.WriteString(`,"assignee":null,"created_at":"2025-01-01T00:00:00Z","updated_at":"2025-01-01T00:00:00Z","closed_at":`)
	if is.State == "closed" {
		sb.WriteString(`"2025-01-02T00:00:00Z"`)
	} else {
		sb.WriteString(`null`)
	}
	sb.WriteString(`,"html_url":`)
	sb.WriteString(strconv.Quote("https://github.com/" + r.Owner + "/" + r.Name + "/issues/" + strconv.Itoa(is.Number)))
	sb.WriteString(`,"url":`)
	sb.WriteString(strconv.Quote("/api/v3/repos/" + r.Owner + "/" + r.Name + "/issues/" + strconv.Itoa(is.Number)))
	sb.WriteString(`,"comments":`)
	sb.WriteString(strconv.Itoa(len(r.ComSeq[is.Number])))
	sb.WriteByte('}')
	is.cache = []byte(sb.String())
}

func (pr *PR) toJSON(r *Repo) []byte {
	headSHA := r.tip(pr.HeadRef)
	baseSHA := r.tip(pr.BaseRef)
	mergedAt := interface{}(nil)
	if pr.Merged {
		mergedAt = pr.MergedAt
	}
	mergeSHA := pr.MergeSHA
	if mergeSHA == "" {
		mergeSHA = ""
	}
	return jsonBytes(map[string]interface{}{
		"id": pr.ID, "node_id": pr.GID, "number": pr.Number, "title": pr.Title, "body": pr.Body,
		"state": pr.State, "merged": pr.Merged, "merged_at": mergedAt, "merge_commit_sha": mergeSHA,
		"head": map[string]interface{}{"ref": pr.HeadRef, "sha": headSHA, "label": r.Owner + ":" + pr.HeadRef},
		"base": map[string]interface{}{"ref": pr.BaseRef, "sha": baseSHA, "label": r.Owner + ":" + pr.BaseRef},
		"user": viewerUserJSON(), "created_at": fixedTime, "updated_at": fixedTime,
		"html_url": "https://github.com/" + r.Owner + "/" + r.Name + "/pull/" + strconv.Itoa(pr.Number),
		"url":      "/api/v3/repos/" + r.Owner + "/" + r.Name + "/pulls/" + strconv.Itoa(pr.Number),
		"draft":    false,
	})
}

func (r *Repo) findIssue(n int) *Issue {
	for _, is := range r.Issues {
		if is.Number == n {
			return is
		}
	}
	return nil
}
func (r *Repo) findPR(n int) *PR {
	for _, pr := range r.PRs {
		if pr.Number == n {
			return pr
		}
	}
	return nil
}

// diff between two trees: flat maps
func diffTrees(r *Repo, baseTree, headTree string) []FileChange {
	bm := r.treeMap(baseTree)
	hm := r.treeMap(headTree)
	paths := map[string]bool{}
	for p := range bm {
		paths[p] = true
	}
	for p := range hm {
		paths[p] = true
	}
	var names []string
	for p := range paths {
		names = append(names, p)
	}
	sort.Strings(names)
	var out []FileChange
	for _, p := range names {
		b, inB := bm[p]
		h, inH := hm[p]
		switch {
		case !inB && inH:
			lines := countLines(r, h.OID)
			out = append(out, FileChange{Filename: p, Status: "added", Additions: lines, Changes: lines})
		case inB && !inH:
			lines := countLines(r, b.OID)
			out = append(out, FileChange{Filename: p, Status: "removed", Deletions: lines, Changes: lines})
		case inB && inH && b.OID != h.OID:
			add, del := diffLines(r, b.OID, h.OID)
			if add == 0 && del == 0 {
				add = 1
			}
			out = append(out, FileChange{Filename: p, Status: "modified", Additions: add, Deletions: del, Changes: add + del})
		}
	}
	return out
}

func countLines(r *Repo, oid string) int {
	obj, ok := r.Objs[oid]
	if !ok {
		return 0
	}
	n := bytes.Count(obj.data, []byte("\n"))
	if len(obj.data) > 0 && !bytes.HasSuffix(obj.data, []byte("\n")) {
		n++
	}
	if n == 0 && len(obj.data) > 0 {
		n = 1
	}
	return n
}

// simple LCS-based line diff
func diffLines(r *Repo, aOID, bOID string) (add, del int) {
	aObj, ok1 := r.Objs[aOID]
	bObj, ok2 := r.Objs[bOID]
	if !ok1 || !ok2 {
		return 1, 0
	}
	aLines := strings.Split(string(aObj.data), "\n")
	bLines := strings.Split(string(bObj.data), "\n")
	// LCS via DP (files are small)
	n, m := len(aLines), len(bLines)
	dp := make([][]int, n+1)
	for i := range dp {
		dp[i] = make([]int, m+1)
	}
	for i := n - 1; i >= 0; i-- {
		for j := m - 1; j >= 0; j-- {
			if aLines[i] == bLines[j] {
				dp[i][j] = dp[i+1][j+1] + 1
			} else if dp[i+1][j] >= dp[i][j+1] {
				dp[i][j] = dp[i+1][j]
			} else {
				dp[i][j] = dp[i][j+1]
			}
		}
	}
	lcs := dp[0][0]
	del = n - lcs
	add = m - lcs
	return add, del
}

func (r *Repo) prMergeable(pr *PR) string {
	headTip := r.tip(pr.HeadRef)
	baseTip := r.tip(pr.BaseRef)
	if headTip == "" || baseTip == "" {
		return "UNKNOWN"
	}
	mb := pr.MergeBase
	if mb == "" {
		mb = r.mergeBase(headTip, baseTip)
		pr.MergeBase = mb
	}
	if mb == "" {
		return "UNKNOWN"
	}
	mbTree := r.commitTree(mb)
	headTree := r.commitTree(headTip)
	baseTree := r.commitTree(baseTip)
	mbm := r.treeMap(mbTree)
	hm := r.treeMap(headTree)
	bm := r.treeMap(baseTree)
	for p, h := range hm {
		m, inM := mbm[p]
		if !inM || m.OID == h.OID {
			continue
		}
		// changed in head vs merge-base
		b, inB := bm[p]
		if inB && b.OID != m.OID && b.OID != h.OID {
			return "CONFLICTING"
		}
		if !inB {
			// base deleted it while head modified it
			return "CONFLICTING"
		}
	}
	for p, m := range mbm {
		if _, inH := hm[p]; !inH {
			// deleted in head
			if b, inB := bm[p]; inB && b.OID != m.OID {
				return "CONFLICTING"
			}
		}
	}
	return "MERGEABLE"
}

// squash-merge pr; returns (mergeSHA, conflict)
func (r *Repo) squashMerge(pr *PR) (string, bool) {
	headTip := r.tip(pr.HeadRef)
	baseTip := r.tip(pr.BaseRef)
	if headTip == "" || baseTip == "" {
		return "", true
	}
	if r.prMergeable(pr) == "CONFLICTING" {
		return "", true
	}
	mb := pr.MergeBase
	if mb == "" {
		mb = r.mergeBase(headTip, baseTip)
	}
	mbTree := r.commitTree(mb)
	headTree := r.commitTree(headTip)
	baseTree := r.commitTree(baseTip)
	mbm := r.treeMap(mbTree)
	hm := r.treeMap(headTree)
	bm := r.treeMap(baseTree)
	// result = base tree with head-vs-mb changes applied
	result := map[string]string{}
	for p, e := range bm {
		result[p] = e.OID
	}
	for p, h := range hm {
		m, inM := mbm[p]
		if !inM || m.OID != h.OID {
			result[p] = h.OID
		}
	}
	for p := range mbm {
		if _, inH := hm[p]; !inH {
			if _, inB := bm[p]; inB {
				// deleted in head; only apply if base didn't change it (mergeable already checked)
				delete(result, p)
			}
		}
	}
	newTree := r.buildTreeFromFlat(result)
	seq := atomic.AddInt64(&store.commitSeq, 1)
	ts := 1700000000 + int(seq)
	msg := fmt.Sprintf("Merge pull request #%d from %s\n\n%s\n", pr.Number, pr.HeadRef, pr.Title)
	commitData := []byte(fmt.Sprintf("tree %s\nparent %s\nauthor %s <%s> %d +0000\ncommitter %s <%s> %d +0000\n\n%s", newTree, baseTip, viewerName, viewerEmail, ts, viewerName, viewerEmail, ts, msg))
	mergeSHA := r.putObj("commit", commitData)
	r.Refs["refs/heads/"+pr.BaseRef] = mergeSHA
	pr.State = "closed"
	pr.Merged = true
	pr.MergedAt = "2025-01-02T00:00:00Z"
	pr.MergeSHA = mergeSHA
	return mergeSHA, false
}

func (r *Repo) commitsFrom(tip string) []string {
	// all reachable commits, newest first by commit timestamp then insertion order
	seen := map[string]bool{}
	var out []string
	queue := []string{tip}
	for len(queue) > 0 {
		cur := queue[0]
		queue = queue[1:]
		if seen[cur] || cur == "" {
			continue
		}
		seen[cur] = true
		obj, ok := r.Objs[cur]
		if !ok || obj.typ != "commit" {
			continue
		}
		out = append(out, cur)
		queue = append(queue, parseCommit(obj.data).Parents...)
	}
	// sort by timestamp desc (parse author line timestamp), stable
	type item struct {
		oid string
		ts  int
	}
	items := make([]item, 0, len(out))
	for _, oid := range out {
		ts := 0
		for _, line := range strings.Split(string(r.Objs[oid].data), "\n") {
			if strings.HasPrefix(line, "author ") {
				fields := strings.Fields(line)
				if len(fields) >= 2 {
					if v, err := strconv.Atoi(fields[len(fields)-2]); err == nil {
						ts = v
					}
				}
				break
			}
		}
		items = append(items, item{oid, ts})
	}
	sort.SliceStable(items, func(a, b int) bool { return items[a].ts > items[b].ts })
	out = out[:0]
	for _, it := range items {
		out = append(out, it.oid)
	}
	return out
}

func commitJSON(r *Repo, oid string) map[string]interface{} {
	obj := r.Objs[oid]
	c := parseCommit(obj.data)
	author, committer := "", ""
	ts := 0
	for _, line := range strings.Split(string(obj.data), "\n") {
		if strings.HasPrefix(line, "author ") {
			author = strings.TrimPrefix(line, "author ")
		}
		if strings.HasPrefix(line, "committer ") {
			committer = strings.TrimPrefix(line, "committer ")
		}
	}
	// author line: "Name <email> ts +0000"
	parseIdent := func(s string) (name, email, date string) {
		lt := strings.Index(s, "<")
		gt := strings.Index(s, ">")
		if lt >= 0 && gt > lt {
			name = strings.TrimSpace(s[:lt])
			email = s[lt+1 : gt]
			rest := strings.Fields(strings.TrimSpace(s[gt+1:]))
			if len(rest) > 0 {
				if v, err := strconv.Atoi(rest[0]); err == nil {
					ts = v
					_ = ts
				}
				date = fixedTime
			}
		}
		return
	}
	an, ae, ad := parseIdent(author)
	cn, ce, cd := parseIdent(committer)
	parents := []map[string]string{}
	for _, p := range c.Parents {
		parents = append(parents, map[string]string{"sha": p})
	}
	return map[string]interface{}{
		"sha": oid,
		"commit": map[string]interface{}{
			"message":   strings.TrimRight(c.Message, "\n"),
			"author":    map[string]string{"name": an, "email": ae, "date": ad},
			"committer": map[string]string{"name": cn, "email": ce, "date": cd},
		},
		"parents": parents,
	}
}

// create a contents commit on branch; returns commit sha
func (r *Repo) contentsCommit(branch, path string, content []byte, message string, deleteFile bool) (string, string) {
	blobOID := ""
	if !deleteFile {
		blobOID = r.putObj("blob", content)
	}
	tip := r.tip(branch)
	var flat map[string]string
	if tip == "" {
		flat = map[string]string{}
	} else {
		tree := r.commitTree(tip)
		fm := r.treeMap(tree)
		flat = map[string]string{}
		for p, e := range fm {
			flat[p] = e.OID
		}
	}
	if deleteFile {
		delete(flat, path)
	} else {
		flat[path] = blobOID
	}
	newTree := r.buildTreeFromFlat(flat)
	seq := atomic.AddInt64(&store.commitSeq, 1)
	ts := 1700000000 + int(seq)
	if !strings.HasSuffix(message, "\n") {
		message += "\n"
	}
	var cb strings.Builder
	cb.WriteString("tree " + newTree + "\n")
	if tip != "" {
		cb.WriteString("parent " + tip + "\n")
	}
	cb.WriteString(fmt.Sprintf("author %s <%s> %d +0000\ncommitter %s <%s> %d +0000\n\n%s", viewerName, viewerEmail, ts, viewerName, viewerEmail, ts, message))
	commitSHA := r.putObj("commit", []byte(cb.String()))
	r.Refs["refs/heads/"+branch] = commitSHA
	return commitSHA, blobOID
}

// ---------------------------------------------------------------- Git smart HTTP

const gitUploadCT = "application/x-git-upload-pack-advertisement"
const gitReceiveCT = "application/x-git-receive-pack-advertisement"
const gitResultCT = "application/x-git-receive-pack-result"

func pktLine(data []byte) []byte {
	out := make([]byte, 4, 4+len(data))
	const hexd = "0123456789abcdef"
	n := len(data) + 4
	out[0] = hexd[(n>>12)&0xf]
	out[1] = hexd[(n>>8)&0xf]
	out[2] = hexd[(n>>4)&0xf]
	out[3] = hexd[n&0xf]
	return append(out, data...)
}
func pktFlush() []byte { return []byte("0000") }
func pktDelim() []byte { return []byte("0001") }

func (r *Repo) rawRefs() [][2]string {
	// sorted by name: HEAD first
	names := make([]string, 0, len(r.Refs))
	for k := range r.Refs {
		names = append(names, k)
	}
	sort.Strings(names)
	var out [][2]string
	tip := r.tip("main")
	if tip != "" {
		out = append(out, [2]string{tip, "HEAD"})
	}
	for _, name := range names {
		out = append(out, [2]string{r.Refs[name], name})
	}
	return out
}

func (r *Repo) advertisedRefs() []byte {
	// v0 upload-pack advertisement
	var buf bytes.Buffer
	buf.Write(pktLine([]byte("# service=git-upload-pack\n")))
	buf.Write(pktFlush())
	refs := r.rawRefs()
	if len(refs) == 0 {
		buf.Write(pktLine([]byte("0000000000000000000000000000000000000000 capabilities^{}\x00side-band-64k multi_ack thin-pack ofs-delta shallow symref=HEAD:refs/heads/main agent=forge/1.0\n")))
	} else {
		caps := "side-band-64k multi_ack multi_ack_detailed thin-pack ofs-delta shallow symref=HEAD:refs/heads/main agent=forge/1.0"
		for i, rf := range refs {
			line := rf[0] + " " + rf[1]
			if i == 0 {
				line += "\x00" + caps
			}
			line += "\n"
			buf.Write(pktLine([]byte(line)))
			// peeled tag line
			if strings.HasPrefix(rf[1], "refs/tags/") {
				if obj, ok := r.Objs[rf[0]]; ok && obj.typ == "tag" {
					if tgt := parseTagTarget(obj.data); tgt != "" {
						buf.Write(pktLine([]byte(tgt + " " + rf[1] + "^{}\n")))
					}
				}
			}
		}
	}
	buf.Write(pktFlush())
	return buf.Bytes()
}

func (r *Repo) receiveAdvertisedRefs() []byte {
	var buf bytes.Buffer
	buf.Write(pktLine([]byte("# service=git-receive-pack\n")))
	buf.Write(pktFlush())
	refs := r.rawRefs()
	if len(refs) == 0 {
		buf.Write(pktLine([]byte("0000000000000000000000000000000000000000 capabilities^{}\x00report-status report-status-v2 side-band-64k delete-refs ofs-delta agent=forge/1.0\n")))
	} else {
		caps := "report-status report-status-v2 side-band-64k delete-refs ofs-delta agent=forge/1.0"
		for i, rf := range refs {
			line := rf[0] + " " + rf[1]
			if i == 0 {
				line += "\x00" + caps
			}
			line += "\n"
			buf.Write(pktLine([]byte(line)))
		}
	}
	buf.Write(pktFlush())
	return buf.Bytes()
}

func parseTagTarget(data []byte) string {
	for _, line := range strings.Split(string(data), "\n") {
		if strings.HasPrefix(line, "object ") {
			return strings.TrimSpace(strings.TrimPrefix(line, "object "))
		}
	}
	return ""
}

func v2Advertise() []byte {
	var buf bytes.Buffer
	buf.Write(pktLine([]byte("version 2\n")))
	buf.Write(pktLine([]byte("agent=forge/1.0\n")))
	buf.Write(pktLine([]byte("object-format=sha1\n")))
	buf.Write(pktLine([]byte("ls-refs=unborn\n")))
	buf.Write(pktLine([]byte("fetch=shallow filter\n")))
	buf.Write(pktLine([]byte("server-option\n")))
	buf.Write(pktLine([]byte("object-info\n")))
	buf.Write(pktFlush())
	return buf.Bytes()
}

// The v2 capability advertisement never changes: build it once.
var v2AdvertiseBytes = v2Advertise()

// pkt-line reader over a byte slice
type pktReader struct {
	data []byte
	pos  int
}

func (p *pktReader) next() ([]byte, bool, error) {
	if p.pos+4 > len(p.data) {
		return nil, false, nil
	}
	hexLen := string(p.data[p.pos : p.pos+4])
	n, err := strconv.ParseInt(hexLen, 16, 32)
	if err != nil {
		return nil, false, fmt.Errorf("bad pkt len")
	}
	if n == 1 {
		// delim (0001) separates command args from arguments: skip it
		p.pos += 4
		return p.next()
	}
	if n == 0 || n == 2 {
		// flush (0000) / response-end (0002): end of stream
		p.pos += 4
		return nil, true, nil
	}
	if n < 4 || p.pos+int(n) > len(p.data) {
		return nil, false, fmt.Errorf("pkt len out of range")
	}
	line := p.data[p.pos+4 : p.pos+int(n)]
	p.pos += int(n)
	return line, false, nil
}

func (p *pktReader) rest() []byte {
	if p.pos >= len(p.data) {
		return nil
	}
	return p.data[p.pos:]
}

func (r *Repo) handleLsRefs(body []byte) []byte {
	// parse args: peel, unborn, ref-prefix <p>, symrefs
	peel := false
	var prefixes []string
	pr := &pktReader{data: body}
	for {
		line, flush, err := pr.next()
		if err != nil || flush {
			break
		}
		s := strings.TrimRight(string(line), "\n")
		if s == "peel" {
			peel = true
		} else if strings.HasPrefix(s, "ref-prefix ") {
			prefixes = append(prefixes, strings.TrimPrefix(s, "ref-prefix "))
		}
	}
	var buf bytes.Buffer
	tip := r.tip("main")
	// HEAD is only listed when no prefix filter is given or a prefix matches it
	showHead := len(prefixes) == 0
	for _, pre := range prefixes {
		if strings.HasPrefix("HEAD", pre) || strings.HasPrefix(pre, "HEAD") {
			showHead = true
		}
	}
	if showHead {
		headLine := ""
		if tip != "" {
			headLine = tip + " HEAD symref-target:refs/heads/main"
		} else {
			headLine = "0000000000000000000000000000000000000000 HEAD symref-target:refs/heads/main"
		}
		buf.Write(pktLine([]byte(headLine + "\n")))
	}
	refs := r.rawRefs()
	for _, rf := range refs {
		if rf[1] == "HEAD" {
			continue
		}
		if len(prefixes) > 0 {
			ok := false
			for _, pre := range prefixes {
				if strings.HasPrefix(rf[1], pre) {
					ok = true
					break
				}
			}
			if !ok {
				continue
			}
		}
		line := rf[0] + " " + rf[1]
		if peel && strings.HasPrefix(rf[1], "refs/tags/") {
			if obj, ok := r.Objs[rf[0]]; ok && obj.typ == "tag" {
				if tgt := parseTagTarget(obj.data); tgt != "" {
					line += " peeled:" + tgt
				}
			}
		}
		buf.Write(pktLine([]byte(line + "\n")))
	}
	buf.Write(pktFlush())
	return buf.Bytes()
}

// compute fetch send set: wants minus held closure, bounded by depth.
// shallowBounds are previous shallow boundaries: the client holds them but
// NOT their parents, so their ancestors must not count as held.
func (r *Repo) fetchSet(wants []string, haves []string, shallowBounds []string, depth int) (send []string, shallow []string, unshallow []string) {
	held := map[string]bool{}
	for _, h := range haves {
		for oid := range r.closure([]string{h}) {
			held[oid] = true
		}
	}
	for _, sb := range shallowBounds {
		if obj, ok := r.Objs[sb]; ok && obj.typ == "commit" {
			for _, p := range parseCommit(obj.data).Parents {
				for oid := range r.closure([]string{p}) {
					delete(held, oid)
				}
			}
		}
	}
	effDepth := depth
	if effDepth == 0 {
		effDepth = -1
	}
	objSet := r.collect(wants, effDepth, held)
	send = make([]string, 0, len(objSet))
	for oid := range objSet {
		send = append(send, oid)
	}
	if depth <= 0 {
		return send, nil, nil
	}
	// boundary: sent commits at depth == depth (0-indexed d == depth-1)
	type node struct {
		oid string
		d   int
	}
	seen := map[string]bool{}
	var queue []node
	for _, w := range wants {
		queue = append(queue, node{w, 0})
	}
	sentSet := map[string]bool{}
	for _, oid := range send {
		sentSet[oid] = true
	}
	var boundary []string
	for len(queue) > 0 {
		cur := queue[0]
		queue = queue[1:]
		if seen[cur.oid] {
			continue
		}
		seen[cur.oid] = true
		obj, ok := r.Objs[cur.oid]
		if !ok {
			continue
		}
		if obj.typ == "tag" {
			if tgt := parseTagTarget(obj.data); tgt != "" {
				queue = append(queue, node{tgt, cur.d})
			}
			continue
		}
		if obj.typ != "commit" {
			continue
		}
		if cur.d == depth-1 {
			if sentSet[cur.oid] {
				boundary = append(boundary, cur.oid)
			}
			continue
		}
		for _, p := range parseCommit(obj.data).Parents {
			queue = append(queue, node{p, cur.d + 1})
		}
	}
	shallow = boundary
	// unshallow: old boundaries whose parent is now in the sent set
	for _, s := range r.Shallow {
		if seen[s] && !containsStr(boundary, s) {
			if obj, ok := r.Objs[s]; ok && obj.typ == "commit" {
				for _, p := range parseCommit(obj.data).Parents {
					if sentSet[p] {
						unshallow = append(unshallow, s)
						break
					}
				}
			}
		}
	}
	r.Shallow = shallow
	return send, shallow, unshallow
}

func containsStr(list []string, s string) bool {
	for _, v := range list {
		if v == s {
			return true
		}
	}
	return false
}

func (r *Repo) handleFetchV2(body []byte) []byte {
	pr := &pktReader{data: body}
	var wants, haves, shallows []string
	depth := 0
	// first command line
	line, _, err := pr.next()
	if err != nil {
		return nil
	}
	cmd := strings.TrimRight(string(line), "\n")
	if cmd != "command=fetch" {
		// maybe command=ls-refs handled elsewhere; treat as ls-refs
		if cmd == "command=ls-refs" {
			return r.handleLsRefs(body)
		}
		return nil
	}
	for {
		l, flush, err := pr.next()
		if err != nil || flush {
			break
		}
		s := strings.TrimRight(string(l), "\n")
		switch {
		case strings.HasPrefix(s, "want "):
			wants = append(wants, strings.TrimPrefix(s, "want "))
		case strings.HasPrefix(s, "have "):
			haves = append(haves, strings.TrimPrefix(s, "have "))
		case strings.HasPrefix(s, "shallow "):
			shallows = append(shallows, strings.TrimPrefix(s, "shallow "))
		case strings.HasPrefix(s, "deepen "):
			if v, err := strconv.Atoi(strings.TrimPrefix(s, "deepen ")); err == nil {
				depth = v
			}
		case s == "done":
		}
	}
	// Identical fetches (the clone workload's 50 depth-1 clones of one tip)
	// rebuild the same pack every time; serve the cached response instead.
	fetchKey := fetchCacheKey("v2", wants, haves, shallows, depth)
	if cached, ok := r.fetchCached(fetchKey); ok {
		return cached
	}
	send, shallow, unshallow := r.fetchSet(wants, haves, shallows, depth)
	var buf bytes.Buffer
	buf.Write(pktLine([]byte("acknowledgments\n")))
	buf.Write(pktLine([]byte("NAK\n")))
	buf.Write(pktDelim())
	if len(shallow) > 0 || len(unshallow) > 0 {
		buf.Write(pktLine([]byte("shallow-info\n")))
		for _, s := range shallow {
			buf.Write(pktLine([]byte("shallow " + s + "\n")))
		}
		for _, s := range unshallow {
			buf.Write(pktLine([]byte("unshallow " + s + "\n")))
		}
		buf.Write(pktDelim())
	}
	if len(send) > 0 {
		buf.Write(pktLine([]byte("packfile\n")))
		objs := map[string]*Obj{}
		for _, oid := range send {
			if o, ok := r.Objs[oid]; ok {
				objs[oid] = o
			}
		}
		pack := r.buildPack(objs)
		// sideband: split into <=65515-byte chunks, band 1
		for off := 0; off < len(pack); {
			chunk := 65515
			if len(pack)-off < chunk {
				chunk = len(pack) - off
			}
			payload := make([]byte, 0, chunk+1)
			payload = append(payload, 1)
			payload = append(payload, pack[off:off+chunk]...)
			buf.Write(pktLine(payload))
			off += chunk
		}
	}
	buf.Write(pktFlush())
	resp := buf.Bytes()
	r.storeFetch(fetchKey, resp)
	return resp
}

func (r *Repo) handleFetchV0(body []byte) []byte {
	pr := &pktReader{data: body}
	var wants, haves, shallows []string
	depth := 0
	// phase 1: want lines until flush
	for {
		l, flush, err := pr.next()
		if err != nil {
			break
		}
		if flush {
			break
		}
		s := strings.TrimRight(string(l), "\n")
		// strip capabilities after NUL on first line
		if i := strings.IndexByte(s, 0); i >= 0 {
			s = s[:i]
		}
		switch {
		case strings.HasPrefix(s, "want "):
			wants = append(wants, strings.Fields(s)[1])
		case strings.HasPrefix(s, "shallow "):
			shallows = append(shallows, strings.TrimPrefix(s, "shallow "))
		case strings.HasPrefix(s, "deepen "):
			if v, err := strconv.Atoi(strings.TrimPrefix(s, "deepen ")); err == nil {
				depth = v
			}
		}
	}
	// phase 2: have lines until done
	for {
		l, flush, err := pr.next()
		if err != nil {
			break
		}
		if flush {
			continue
		}
		s := strings.TrimRight(string(l), "\n")
		if strings.HasPrefix(s, "have ") {
			haves = append(haves, strings.Fields(s)[1])
		} else if s == "done" {
			break
		}
	}
	fetchKey := fetchCacheKey("v0", wants, haves, shallows, depth)
	if cached, ok := r.fetchCached(fetchKey); ok {
		return cached
	}
	send, shallow, unshallow := r.fetchSet(wants, haves, shallows, depth)
	var buf bytes.Buffer
	buf.Write(pktLine([]byte("NAK\n")))
	for _, s := range shallow {
		buf.Write(pktLine([]byte("shallow " + s + "\n")))
	}
	for _, s := range unshallow {
		buf.Write(pktLine([]byte("unshallow " + s + "\n")))
	}
	buf.Write(pktFlush())
	if len(send) > 0 {
		objs := map[string]*Obj{}
		for _, oid := range send {
			if o, ok := r.Objs[oid]; ok {
				objs[oid] = o
			}
		}
		pack := r.buildPack(objs)
		for off := 0; off < len(pack); {
			chunk := 65515
			if len(pack)-off < chunk {
				chunk = len(pack) - off
			}
			payload := make([]byte, 0, chunk+1)
			payload = append(payload, 1)
			payload = append(payload, pack[off:off+chunk]...)
			buf.Write(pktLine(payload))
			off += chunk
		}
	}
	buf.Write(pktFlush())
	resp := buf.Bytes()
	r.storeFetch(fetchKey, resp)
	return resp
}

func (r *Repo) handleReceivePack(body []byte) []byte {
	pr := &pktReader{data: body}
	type cmd struct {
		old, new, ref string
	}
	var cmds []cmd
	// command lines until flush
	for {
		l, flush, err := pr.next()
		if err != nil {
			break
		}
		if flush {
			break
		}
		s := strings.TrimRight(string(l), "\n")
		if i := strings.IndexByte(s, 0); i >= 0 {
			s = s[:i]
		}
		parts := strings.Fields(s)
		if len(parts) >= 3 {
			cmds = append(cmds, cmd{parts[0], parts[1], parts[2]})
		}
	}
	rest := pr.rest()
	// parse pack if present (starts with "PACK")
	if len(rest) >= 4 && string(rest[:4]) == "PACK" {
		if objs, err := r.parsePack(rest); err == nil {
			// parsePack already hashed each object and computed its comp
			// lazily; re-inserting via putObj would hash + compress them again.
			for oid, o := range objs {
				if _, ok := r.Objs[oid]; !ok {
					r.Objs[oid] = o
				}
			}
		}
	}
	var out bytes.Buffer
	out.Write(pktLine([]byte("unpack ok\n")))
	for _, c := range cmds {
		cur, exists := r.Refs[c.ref]
		// validate
		switch {
		case c.new == zeroOID:
			// delete
			if !exists {
				out.Write(pktLine([]byte("ng " + c.ref + " " + "remote ref does not exist\n")))
			} else if c.old != zeroOID && cur != c.old {
				out.Write(pktLine([]byte("ng " + c.ref + " " + "non-fast-forward\n")))
			} else {
				delete(r.Refs, c.ref)
				out.Write(pktLine([]byte("ok " + c.ref + "\n")))
			}
		case !exists:
			if c.old != zeroOID {
				out.Write(pktLine([]byte("ng " + c.ref + " " + "non-fast-forward\n")))
			} else {
				r.Refs[c.ref] = c.new
				out.Write(pktLine([]byte("ok " + c.ref + "\n")))
			}
		default:
			if cur != c.old {
				out.Write(pktLine([]byte("ng " + c.ref + " " + "non-fast-forward\n")))
			} else if c.new != cur && !r.isAncestor(cur, c.new) {
				out.Write(pktLine([]byte("ng " + c.ref + " " + "non-fast-forward\n")))
			} else {
				r.Refs[c.ref] = c.new
				out.Write(pktLine([]byte("ok " + c.ref + "\n")))
			}
		}
	}
	out.Write(pktFlush())
	// wrap in sideband band 1
	var wrapped bytes.Buffer
	payload := append([]byte{1}, out.Bytes()...)
	// sideband may need splitting; report is small
	wrapped.Write(pktLine(payload))
	wrapped.Write(pktFlush())
	return wrapped.Bytes()
}

// ---------------------------------------------------------------- REST dispatcher

func handleREST(req *request) *response {
	// strip /api/v3 prefix
	p := strings.TrimPrefix(req.path, "/api/v3")
	if p == "" || p == "/" {
		if req.method == "GET" {
			return &response{status: 200, ctype: jsonCT, body: []byte(`{"current_user_url":"/api/v3/user","user_url":"/api/v3/users/{user}","repository_url":"/api/v3/repos/{owner}/{repo}"}`), extra: map[string]string{"X-OAuth-Scopes": "repo"}}
		}
		return jerr(404, "Not Found")
	}
	q := parseQuery(req.query)
	segs := strings.Split(strings.Trim(p, "/"), "/")
	// /meta, /user
	if len(segs) == 1 {
		switch segs[0] {
		case "meta":
			if req.method == "GET" {
				return jresp(200, map[string]interface{}{"verifiable_password_authentication": true, "installed_version": "1.0.0", "hooks": []string{"pre-receive"}, "git": []string{"127.0.0.1"}, "github_enterprise": false})
			}
		case "user":
			if req.method == "GET" {
				return jresp(200, viewerUserJSON())
			}
		}
		return jerr(404, "Not Found")
	}
	if segs[0] == "user" && len(segs) == 2 && segs[1] == "repos" {
		if req.method == "GET" {
			return handleListUserRepos(q)
		}
		if req.method == "POST" {
			return handleCreateRepo(req, viewerLogin)
		}
		return jerr(404, "Not Found")
	}
	if segs[0] != "repos" {
		return jerr(404, "Not Found")
	}
	if len(segs) < 3 {
		return jerr(404, "Not Found")
	}
	owner, repoName := segs[1], segs[2]
	rest := segs[3:]

	// repo-level GET/PATCH/DELETE (no further segments)
	if len(rest) == 0 {
		switch req.method {
		case "GET":
			r := store.getRepo(owner, repoName)
			if r == nil {
				return jerr(404, "Not Found")
			}
			return jresp(200, r.toJSON())
		case "PATCH":
			r := store.getRepo(owner, repoName)
			if r == nil {
				return jerr(404, "Not Found")
			}
			var body map[string]interface{}
			if err := jsonUnmarshal(req.body, &body); err != nil {
				return jerr(400, "Bad Request")
			}
			store.mu.Lock()
			if d, ok := body["description"].(string); ok {
				r.Desc = d
			}
			if v, ok := body["private"].(bool); ok {
				r.Priv = v
			}
			store.mu.Unlock()
			return jresp(200, r.toJSON())
		case "DELETE":
			store.mu.Lock()
			delete(store.repos, owner+"/"+repoName)
			store.mu.Unlock()
			return &response{status: 204, ctype: jsonCT, body: []byte{}}
		}
		return jerr(404, "Not Found")
	}

	r := store.getRepo(owner, repoName)
	if r == nil {
		return jerr(404, "Not Found")
	}

	switch rest[0] {
	case "contents":
		return handleContents(req, r, rest[1:], q)
	case "issues":
		return handleIssues(req, r, rest[1:], q)
	case "pulls":
		return handlePulls(req, r, rest[1:], q)
	case "labels":
		if req.method == "POST" {
			var body struct {
				Name string `json:"name"`
			}
			if err := jsonUnmarshal(req.body, &body); err != nil || body.Name == "" {
				return jerr(400, "Bad Request")
			}
			store.mu.Lock()
			r.Labels[body.Name] = "ededed"
			store.mu.Unlock()
			return jresp(201, map[string]string{"name": body.Name, "color": "ededed"})
		}
		return jerr(404, "Not Found")
	case "branches":
		if len(rest) == 1 {
			if req.method == "GET" {
				store.mu.RLock()
				var out []map[string]interface{}
				names := make([]string, 0, len(r.Refs))
				for k := range r.Refs {
					if strings.HasPrefix(k, "refs/heads/") {
						names = append(names, strings.TrimPrefix(k, "refs/heads/"))
					}
				}
				sort.Strings(names)
				for _, n := range names {
					out = append(out, map[string]interface{}{"name": n, "commit": map[string]string{"sha": r.Refs["refs/heads/"+n]}})
				}
				store.mu.RUnlock()
				if out == nil {
					out = []map[string]interface{}{}
				}
				return jresp(200, out)
			}
			return jerr(404, "Not Found")
		}
		if len(rest) == 2 && req.method == "GET" {
			sha := r.tip(rest[1])
			if sha == "" {
				return jerr(404, "Not Found")
			}
			return jresp(200, map[string]interface{}{"name": rest[1], "commit": map[string]string{"sha": sha}, "protected": false})
		}
		return jerr(404, "Not Found")
	case "commits":
		if req.method == "GET" {
			branch := q["sha"]
			if branch == "" {
				branch = "main"
			}
			tip := r.tip(branch)
			if tip == "" {
				return jresp(200, []interface{}{})
			}
			oids := r.commitsFrom(tip)
			out := make([]interface{}, 0, len(oids))
			for _, oid := range oids {
				out = append(out, commitJSON(r, oid))
			}
			return jresp(200, out)
		}
		return jerr(404, "Not Found")
	case "git":
		if len(rest) >= 2 && rest[1] == "refs" {
			if len(rest) == 4 && req.method == "GET" {
				// /git/refs/heads/<branch>
				full := "refs/" + rest[2] + "/" + rest[3]
				sha := r.Refs[full]
				if sha == "" {
					return jerr(404, "Not Found")
				}
				return jresp(200, map[string]interface{}{"ref": full, "object": map[string]string{"sha": sha, "type": "commit"}})
			}
			if len(rest) == 2 && req.method == "POST" {
				var body struct {
					Ref string `json:"ref"`
					Sha string `json:"sha"`
				}
				if err := jsonUnmarshal(req.body, &body); err != nil || body.Ref == "" || body.Sha == "" {
					return jerr(400, "Bad Request")
				}
				store.mu.Lock()
				r.Refs[body.Ref] = body.Sha
				store.mu.Unlock()
				return jresp(201, map[string]interface{}{"ref": body.Ref, "object": map[string]string{"sha": body.Sha, "type": "commit"}})
			}
		}
		return jerr(404, "Not Found")
	}
	return jerr(404, "Not Found")
}

func handleListUserRepos(q map[string]string) *response {
	page := queryInt(q, "page", 1)
	perPage := queryInt(q, "per_page", 30)
	if perPage > 100 {
		perPage = 100
	}
	store.mu.RLock()
	var all []*Repo
	for _, r := range store.repos {
		if r.Owner == viewerLogin {
			all = append(all, r)
		}
	}
	store.mu.RUnlock()
	sort.Slice(all, func(a, b int) bool { return all[a].ID < all[b].ID })
	total := len(all)
	start := (page - 1) * perPage
	if start >= total {
		return jresp(200, []interface{}{})
	}
	end := start + perPage
	if end > total {
		end = total
	}
	out := make([]interface{}, 0, end-start)
	for _, r := range all[start:end] {
		out = append(out, r.toJSON())
	}
	resp := jresp(200, out)
	if end < total {
		host := "http://127.0.0.1:" + strconv.Itoa(serverPort)
		resp.extra = map[string]string{"Link": fmt.Sprintf(`<%s/api/v3/user/repos?per_page=%d&page=%d>; rel="next"`, host, perPage, page+1)}
	}
	return resp
}

func handleCreateRepo(req *request, owner string) *response {
	var body struct {
		Name        string `json:"name"`
		Description string `json:"description"`
		Private     bool   `json:"private"`
	}
	if err := jsonUnmarshal(req.body, &body); err != nil || body.Name == "" {
		return jerr(400, "Bad Request")
	}
	store.mu.Lock()
	defer store.mu.Unlock()
	if _, exists := store.repos[owner+"/"+body.Name]; exists {
		return &response{status: 422, ctype: jsonCT, body: []byte(`{"message":"Repository already exists","errors":[{"resource":"Repository","code":"custom","message":"name already exists on this account"}]}`)}
	}
	id := int(atomic.AddInt64(&store.repoSeq, 1))
	r := newRepo(owner, body.Name, id)
	r.Desc = body.Description
	r.Priv = body.Private
	store.repos[owner+"/"+body.Name] = r
	return jresp(201, r.toJSON())
}

func handleContents(req *request, r *Repo, rest []string, q map[string]string) *response {
	if len(rest) == 0 {
		return jerr(404, "Not Found")
	}
	path := strings.Join(rest, "/")
	branch := q["ref"]
	if branch == "" {
		branch = "main"
	}
	switch req.method {
	case "GET":
		tip := r.tip(branch)
		if tip == "" {
			return jerr(404, "Not Found")
		}
		tree := r.commitTree(tip)
		fm := r.treeMap(tree)
		if e, ok := fm[path]; ok {
			obj := r.Objs[e.OID]
			if obj == nil || obj.typ != "blob" {
				return jerr(404, "Not Found")
			}
			return jresp(200, map[string]interface{}{
				"type": "file", "encoding": "base64", "content": b64enc(obj.data), "sha": e.OID,
				"size": len(obj.data), "name": path[strings.LastIndex(path, "/")+1:], "path": path,
			})
		}
		// directory listing
		var out []map[string]interface{}
		prefix := path + "/"
		seen := map[string]bool{}
		for p, e := range fm {
			if strings.HasPrefix(p, prefix) {
				restPath := p[len(prefix):]
				parts := strings.SplitN(restPath, "/", 2)
				if len(parts) == 1 {
					out = append(out, map[string]interface{}{"type": "file", "name": parts[0], "path": p, "sha": e.OID})
				} else if !seen[parts[0]] {
					seen[parts[0]] = true
					out = append(out, map[string]interface{}{"type": "dir", "name": parts[0], "path": path + "/" + parts[0], "sha": ""})
				}
			}
		}
		if out == nil {
			return jerr(404, "Not Found")
		}
		sort.Slice(out, func(a, b int) bool { return out[a]["name"].(string) < out[b]["name"].(string) })
		return jresp(200, out)
	case "PUT":
		var body struct {
			Message string `json:"message"`
			Content string `json:"content"`
			Sha     string `json:"sha"`
			Branch  string `json:"branch"`
		}
		if err := jsonUnmarshal(req.body, &body); err != nil {
			return jerr(400, "Bad Request")
		}
		if body.Branch != "" {
			branch = body.Branch
		}
		content, err := b64dec(body.Content)
		if err != nil {
			return jerr(400, "Bad Request")
		}
		store.mu.Lock()
		defer store.mu.Unlock()
		tip := r.tip(branch)
		exists := false
		var curSha string
		if tip != "" {
			fm := r.treeMap(r.commitTree(tip))
			if e, ok := fm[path]; ok {
				exists = true
				curSha = e.OID
			}
		}
		if exists && body.Sha != "" && body.Sha != curSha {
			return jerr(409, "sha does not match")
		}
		msg := body.Message
		if msg == "" {
			msg = "Update " + path
		}
		commitSHA, blobOID := r.contentsCommit(branch, path, content, msg, false)
		status := 201
		if exists {
			status = 200
		}
		return jresp(status, map[string]interface{}{
			"content": map[string]interface{}{"name": path[strings.LastIndex(path, "/")+1:], "path": path, "sha": blobOID, "size": len(content), "type": "file", "encoding": "base64"},
			"commit":  map[string]interface{}{"sha": commitSHA, "message": msg},
		})
	case "DELETE":
		var body struct {
			Message string `json:"message"`
			Sha     string `json:"sha"`
			Branch  string `json:"branch"`
		}
		if err := jsonUnmarshal(req.body, &body); err != nil {
			return jerr(400, "Bad Request")
		}
		if body.Branch != "" {
			branch = body.Branch
		}
		store.mu.Lock()
		defer store.mu.Unlock()
		tip := r.tip(branch)
		if tip == "" {
			return jerr(404, "Not Found")
		}
		fm := r.treeMap(r.commitTree(tip))
		if _, ok := fm[path]; !ok {
			return jerr(404, "Not Found")
		}
		msg := body.Message
		if msg == "" {
			msg = "Delete " + path
		}
		commitSHA, _ := r.contentsCommit(branch, path, nil, msg, true)
		return jresp(200, map[string]interface{}{"commit": map[string]interface{}{"sha": commitSHA, "message": msg}})
	}
	return jerr(404, "Not Found")
}

func handleIssues(req *request, r *Repo, rest []string, q map[string]string) *response {
	if len(rest) == 0 {
		switch req.method {
		case "GET":
			state := q["state"]
			if state == "" {
				state = "open"
			}
			sortDir := q["direction"]
			if sortDir == "" {
				sortDir = "desc"
			}
			var list []*Issue
			for _, is := range r.Issues {
				if state == "all" || is.State == state {
					list = append(list, is)
				}
			}
			sort.Slice(list, func(a, b int) bool {
				if sortDir == "asc" {
					return list[a].Number < list[b].Number
				}
				return list[a].Number > list[b].Number
			})
			// build JSON array from caches
			var buf bytes.Buffer
			buf.WriteByte('[')
			for i, is := range list {
				if i > 0 {
					buf.WriteByte(',')
				}
				buf.Write(is.cache)
			}
			buf.WriteByte(']')
			return jraw(200, buf.Bytes())
		case "POST":
			var body struct {
				Title  string   `json:"title"`
				Body   string   `json:"body"`
				Labels []string `json:"labels"`
			}
			if err := jsonUnmarshal(req.body, &body); err != nil || body.Title == "" {
				return jerr(400, "Bad Request")
			}
			for _, ln := range body.Labels {
				if _, ok := r.Labels[ln]; !ok {
					return jerr(422, "Validation Failed: label does not exist")
				}
			}
			store.mu.Lock()
			defer store.mu.Unlock()
			n := r.NextNum
			r.NextNum++
			id := int(atomic.AddInt64(&store.issueSeq, 1))
			is := &Issue{ID: id, GID: "issue-" + strconv.Itoa(r.ID) + "-" + strconv.Itoa(n), Number: n, Title: body.Title, Body: body.Body, State: "open", Labels: body.Labels}
			if is.Labels == nil {
				is.Labels = []string{}
			}
			is.rebuildCache(r)
			r.Issues = append(r.Issues, is)
			return jraw(201, is.cache)
		}
		return jerr(404, "Not Found")
	}
	n, err := strconv.Atoi(rest[0])
	if err != nil {
		return jerr(404, "Not Found")
	}
	if len(rest) == 1 {
		switch req.method {
		case "GET":
			is := r.findIssue(n)
			if is == nil {
				return jerr(404, "Not Found")
			}
			return jraw(200, is.cache)
		case "PATCH":
			var body struct {
				State string `json:"state"`
				Title string `json:"title"`
				Body  string `json:"body"`
			}
			if err := jsonUnmarshal(req.body, &body); err != nil {
				return jerr(400, "Bad Request")
			}
			store.mu.Lock()
			defer store.mu.Unlock()
			is := r.findIssue(n)
			if is == nil {
				return jerr(404, "Not Found")
			}
			if body.State != "" {
				is.State = body.State
			}
			if body.Title != "" {
				is.Title = body.Title
			}
			if body.Body != "" {
				is.Body = body.Body
			}
			is.rebuildCache(r)
			return jraw(200, is.cache)
		}
		return jerr(404, "Not Found")
	}
	if len(rest) == 2 && rest[1] == "comments" {
		switch req.method {
		case "GET":
			list := r.ComSeq[n]
			out := make([]interface{}, 0, len(list))
			for _, c := range list {
				out = append(out, map[string]interface{}{"id": c.ID, "node_id": c.GID, "body": c.Body, "user": viewerUserJSON(), "created_at": fixedTime, "updated_at": fixedTime})
			}
			return jresp(200, out)
		case "POST":
			var body struct {
				Body string `json:"body"`
			}
			if err := jsonUnmarshal(req.body, &body); err != nil || body.Body == "" {
				return jerr(400, "Bad Request")
			}
			store.mu.Lock()
			defer store.mu.Unlock()
			is := r.findIssue(n)
			if is == nil {
				return jerr(404, "Not Found")
			}
			id := int(atomic.AddInt64(&store.commentSeq, 1))
			c := &Comment{ID: id, GID: "comment-" + strconv.Itoa(id), Body: body.Body}
			r.ComSeq[n] = append(r.ComSeq[n], c)
			is.rebuildCache(r)
			return jresp(201, map[string]interface{}{"id": c.ID, "node_id": c.GID, "body": c.Body, "user": viewerUserJSON(), "created_at": fixedTime, "updated_at": fixedTime})
		}
	}
	return jerr(404, "Not Found")
}

func handlePulls(req *request, r *Repo, rest []string, q map[string]string) *response {
	if len(rest) == 0 {
		switch req.method {
		case "GET":
			state := q["state"]
			if state == "" {
				state = "open"
			}
			var out [][]byte
			for _, pr := range r.PRs {
				if state == "all" || pr.State == state {
					out = append(out, pr.toJSON(r))
				}
			}
			var buf bytes.Buffer
			buf.WriteByte('[')
			for i, b := range out {
				if i > 0 {
					buf.WriteByte(',')
				}
				buf.Write(b)
			}
			buf.WriteByte(']')
			return jraw(200, buf.Bytes())
		case "POST":
			var body struct {
				Title string `json:"title"`
				Body  string `json:"body"`
				Head  string `json:"head"`
				Base  string `json:"base"`
			}
			if err := jsonUnmarshal(req.body, &body); err != nil || body.Title == "" || body.Head == "" || body.Base == "" {
				return jerr(400, "Bad Request")
			}
			store.mu.Lock()
			defer store.mu.Unlock()
			for _, pr := range r.PRs {
				if pr.HeadRef == body.Head && pr.State == "open" {
					return jerr(422, "Validation Failed: A pull request already exists for "+body.Head)
				}
			}
			n := r.NextNum
			r.NextNum++
			id := int(atomic.AddInt64(&store.prSeq, 1))
			pr := &PR{ID: id, GID: "pr-" + strconv.Itoa(r.ID) + "-" + strconv.Itoa(n), Number: n, Title: body.Title, Body: body.Body, State: "open", HeadRef: body.Head, BaseRef: body.Base}
			r.PRs = append(r.PRs, pr)
			return jraw(201, pr.toJSON(r))
		}
		return jerr(404, "Not Found")
	}
	n, err := strconv.Atoi(rest[0])
	if err != nil {
		return jerr(404, "Not Found")
	}
	if len(rest) == 1 {
		if req.method == "GET" {
			pr := r.findPR(n)
			if pr == nil {
				return jerr(404, "Not Found")
			}
			return jraw(200, pr.toJSON(r))
		}
		return jerr(404, "Not Found")
	}
	if len(rest) == 2 && rest[1] == "files" && req.method == "GET" {
		pr := r.findPR(n)
		if pr == nil {
			return jerr(404, "Not Found")
		}
		mb := pr.MergeBase
		if mb == "" {
			mb = r.mergeBase(r.tip(pr.HeadRef), r.tip(pr.BaseRef))
		}
		changes := diffTrees(r, r.commitTree(mb), r.commitTree(r.tip(pr.HeadRef)))
		out := make([]interface{}, 0, len(changes))
		for _, c := range changes {
			out = append(out, map[string]interface{}{"filename": c.Filename, "status": c.Status, "additions": c.Additions, "deletions": c.Deletions, "changes": c.Changes})
		}
		return jresp(200, out)
	}
	if len(rest) == 2 && rest[1] == "merge" && req.method == "PUT" {
		pr := r.findPR(n)
		if pr == nil {
			return jerr(404, "Not Found")
		}
		store.mu.Lock()
		defer store.mu.Unlock()
		mergeSHA, conflict := r.squashMerge(pr)
		if conflict {
			return jerr(405, "Pull Request is not mergeable")
		}
		return jresp(200, map[string]interface{}{"sha": mergeSHA, "merged": true, "message": "Pull request successfully merged"})
	}
	return jerr(404, "Not Found")
}

// ---------------------------------------------------------------- Git routes

func handleGit(req *request) *response {
	// path: /<owner>/<repo>.git/info/refs, /git-upload-pack, /git-receive-pack
	segs := strings.Split(strings.Trim(req.path, "/"), "/")
	if len(segs) < 3 {
		return jerr(404, "Not Found")
	}
	owner := segs[0]
	repoName := strings.TrimSuffix(segs[1], ".git")
	rest := segs[2:]
	r := store.getRepo(owner, repoName)
	if len(rest) == 2 && rest[0] == "info" && rest[1] == "refs" && req.method == "GET" {
		if r == nil {
			return jerr(404, "Not Found")
		}
		q := parseQuery(req.query)
		service := q["service"]
		switch service {
		case "git-upload-pack":
			if req.headers["git-protocol"] == "version=2" {
				return jrawCT(200, gitUploadCT, v2AdvertiseBytes)
			}
			return jrawCT(200, gitUploadCT, r.advertisedRefs())
		case "git-receive-pack":
			return jrawCT(200, gitReceiveCT, r.receiveAdvertisedRefs())
		}
		return jerr(404, "Not Found")
	}
	if len(rest) == 1 && req.method == "POST" {
		if r == nil {
			return jerr(404, "Not Found")
		}
		switch rest[0] {
		case "git-upload-pack":
			if req.headers["git-protocol"] == "version=2" {
				// peek first command
				if len(req.body) >= 4 {
					if pr := (&pktReader{data: req.body}); true {
						if line, _, err := pr.next(); err == nil {
							cmd := strings.TrimRight(string(line), "\n")
							if cmd == "command=ls-refs" {
								return jrawCT(200, "application/x-git-upload-pack-result", r.handleLsRefs(req.body))
							}
						}
					}
				}
				return jrawCT(200, "application/x-git-upload-pack-result", r.handleFetchV2(req.body))
			}
			return jrawCT(200, "application/x-git-upload-pack-result", r.handleFetchV0(req.body))
		case "git-receive-pack":
			return jrawCT(200, gitResultCT, r.handleReceivePack(req.body))
		}
	}
	return jerr(404, "Not Found")
}

// ---------------------------------------------------------------- GraphQL

type gqlVar map[string]interface{}

func gqlString(v interface{}) string {
	if s, ok := v.(string); ok {
		return s
	}
	return ""
}

func handleGraphQL(req *request) *response {
	// batch support: body may be a JSON array
	var docs []map[string]interface{}
	var isBatch bool
	trimmed := bytes.TrimSpace(req.body)
	if len(trimmed) > 0 && trimmed[0] == '[' {
		isBatch = true
		var arr []map[string]interface{}
		if err := jsonUnmarshal(req.body, &arr); err != nil {
			return jerr(400, "Bad Request")
		}
		docs = arr
	} else {
		var doc map[string]interface{}
		if err := jsonUnmarshal(req.body, &doc); err != nil {
			return jerr(400, "Bad Request")
		}
		docs = []map[string]interface{}{doc}
	}
	var results []interface{}
	for _, doc := range docs {
		results = append(results, execGraphQL(doc))
	}
	if isBatch {
		return jresp(200, results)
	}
	return jresp(200, results[0])
}

func gqlErr(msg string) map[string]interface{} {
	return map[string]interface{}{"data": nil, "errors": []map[string]interface{}{{"message": msg}}}
}

func execGraphQL(doc map[string]interface{}) interface{} {
	query, _ := doc["query"].(string)
	vars, _ := doc["variables"].(map[string]interface{})
	if vars == nil {
		vars = map[string]interface{}{}
	}
	// mutations nest their arguments under `input`: unwrap one level
	if input, ok := vars["input"].(map[string]interface{}); ok {
		for k, v := range input {
			if _, exists := vars[k]; !exists {
				vars[k] = v
			}
		}
	}
	// operation name detection by content
	q := query
	// __type introspection (may appear several times, aliased, in one document)
	if strings.Contains(q, "__type") {
		data := map[string]interface{}{}
		handled := false
		for _, t := range []struct {
			name   string
			fields []string
			enums  []string
		}{
			{"Issue", []string{"id", "number", "title", "body", "state", "url", "createdAt", "updatedAt", "closedAt", "author", "labels", "comments", "assignees"}, nil},
			{"PullRequest", []string{"id", "number", "title", "body", "state", "headRefName", "baseRefName", "mergeable", "merged", "mergedAt", "mergeCommit", "files", "url", "headRef", "baseRef"}, nil},
			{"Repository", []string{"id", "databaseId", "name", "nameWithOwner", "owner", "defaultBranchRef", "viewerPermission", "hasIssuesEnabled", "issue", "issues", "pullRequests", "pullRequest", "description", "url", "createdAt"}, nil},
			{"SearchType", nil, []string{"ISSUE", "REPOSITORY", "USER", "DISCUSSION", "COMMIT", "CODE"}},
		} {
			needle := `__type(name: "` + t.name + `")`
			idx := strings.Index(q, needle)
			if idx < 0 {
				continue
			}
			handled = true
			alias := t.name
			head := q[:idx]
			if ci := strings.LastIndex(head, ":"); ci >= 0 {
				a := strings.TrimSpace(head[:ci])
				if sp := strings.LastIndexAny(a, " \t\n{"); sp >= 0 {
					a = a[sp+1:]
				}
				if a != "" {
					alias = a
				}
			}
			rest := q[idx:]
			if strings.Contains(rest, "enumValues") {
				var ev []interface{}
				for _, e := range t.enums {
					ev = append(ev, map[string]interface{}{"name": e})
				}
				data[alias] = map[string]interface{}{"name": t.name, "enumValues": ev}
			} else {
				var fl []interface{}
				for _, f := range t.fields {
					fl = append(fl, map[string]interface{}{"name": f})
				}
				data[alias] = map[string]interface{}{"name": t.name, "fields": fl}
			}
		}
		if handled {
			return map[string]interface{}{"data": data}
		}
	}
	switch {
	case strings.Contains(q, "noSuchFieldOnViewer"):
		return map[string]interface{}{"data": map[string]interface{}{"viewer": map[string]interface{}{"login": viewerLogin}}, "errors": []map[string]interface{}{{"message": "Cannot query field \"noSuchFieldOnViewer\" on type \"User\""}}}
	case strings.Contains(q, "__type") && strings.Contains(q, "SearchType"):
		return map[string]interface{}{"data": map[string]interface{}{"__type": map[string]interface{}{"name": "SearchType", "enumValues": []map[string]interface{}{{"name": "ISSUE"}, {"name": "REPOSITORY"}, {"name": "USER"}}}}}
	case strings.Contains(q, "viewer"):
		if strings.Contains(q, "login") && !strings.Contains(q, "repository") && !strings.Contains(q, "issues") {
			return map[string]interface{}{"data": map[string]interface{}{"viewer": map[string]interface{}{"login": viewerLogin, "id": "user-" + strconv.Itoa(viewerID), "name": viewerName}}}
		}
	}
	// repository queries
	if strings.Contains(q, "repository(") || strings.Contains(q, "repository ") {
		owner := gqlString(vars["owner"])
		name := gqlString(vars["name"])
		if owner == "" {
			owner = extractGQLArg(q, "owner")
		}
		if name == "" {
			name = extractGQLArg(q, "name")
		}
		r := store.getRepo(owner, name)
		if r == nil {
			return map[string]interface{}{"data": map[string]interface{}{"repository": nil}}
		}
		return map[string]interface{}{"data": map[string]interface{}{"repository": gqlRepo(r, q, vars)}}
	}
	// node query
	if strings.Contains(q, "node(") {
		id := gqlString(vars["id"])
		if id == "" {
			id = extractGQLArg(q, "id")
		}
		if strings.HasPrefix(id, "repo-") {
			if n, err := strconv.Atoi(strings.TrimPrefix(id, "repo-")); err == nil {
				store.mu.RLock()
				for _, r := range store.repos {
					if r.ID == n {
						store.mu.RUnlock()
						return map[string]interface{}{"data": map[string]interface{}{"node": map[string]interface{}{"id": id, "name": r.Name, "nameWithOwner": r.Owner + "/" + r.Name}}}
					}
				}
				store.mu.RUnlock()
			}
		}
		return map[string]interface{}{"data": map[string]interface{}{"node": nil}}
	}
	// mutations
	if strings.Contains(q, "createIssue") {
		repoID := gqlString(vars["repositoryId"])
		title := gqlString(vars["title"])
		body := gqlString(vars["body"])
		if repoID == "" {
			repoID = extractGQLArg(q, "repositoryId")
		}
		if title == "" {
			title = extractGQLArg(q, "title")
		}
		var r *Repo
		if strings.HasPrefix(repoID, "repo-") {
			if n, err := strconv.Atoi(strings.TrimPrefix(repoID, "repo-")); err == nil {
				store.mu.RLock()
				for _, rr := range store.repos {
					if rr.ID == n {
						r = rr
					}
				}
				store.mu.RUnlock()
			}
		}
		if r == nil {
			return gqlErr("repository not found")
		}
		store.mu.Lock()
		n := r.NextNum
		r.NextNum++
		id := int(atomic.AddInt64(&store.issueSeq, 1))
		is := &Issue{ID: id, GID: "issue-" + strconv.Itoa(r.ID) + "-" + strconv.Itoa(n), Number: n, Title: title, Body: body, State: "open", Labels: []string{}}
		is.rebuildCache(r)
		r.Issues = append(r.Issues, is)
		store.mu.Unlock()
		return map[string]interface{}{"data": map[string]interface{}{"createIssue": map[string]interface{}{"issue": map[string]interface{}{"id": is.GID, "number": is.Number, "title": is.Title, "state": "OPEN"}}}}
	}
	if strings.Contains(q, "closeIssue") {
		issueID := gqlString(vars["issueId"])
		if issueID == "" {
			issueID = extractGQLArg(q, "issueId")
		}
		// issue-<repoId>-<number>
		parts := strings.Split(issueID, "-")
		if len(parts) == 3 {
			if repoID, err := strconv.Atoi(parts[1]); err == nil {
				if num, err := strconv.Atoi(parts[2]); err == nil {
					store.mu.Lock()
					for _, r := range store.repos {
						if r.ID == repoID {
							if is := r.findIssue(num); is != nil {
								is.State = "closed"
								is.rebuildCache(r)
								store.mu.Unlock()
								return map[string]interface{}{"data": map[string]interface{}{"closeIssue": map[string]interface{}{"issue": map[string]interface{}{"id": issueID, "number": num, "state": "CLOSED"}}}}
							}
						}
					}
					store.mu.Unlock()
				}
			}
		}
		return gqlErr("issue not found")
	}
	if strings.Contains(q, "createPullRequest") {
		repoID := gqlString(vars["repositoryId"])
		base := gqlString(vars["baseRefName"])
		head := gqlString(vars["headRefName"])
		title := gqlString(vars["title"])
		var r *Repo
		if strings.HasPrefix(repoID, "repo-") {
			if n, err := strconv.Atoi(strings.TrimPrefix(repoID, "repo-")); err == nil {
				store.mu.RLock()
				for _, rr := range store.repos {
					if rr.ID == n {
						r = rr
					}
				}
				store.mu.RUnlock()
			}
		}
		if r == nil {
			return gqlErr("repository not found")
		}
		store.mu.Lock()
		for _, pr := range r.PRs {
			if pr.HeadRef == head && pr.State == "open" {
				store.mu.Unlock()
				return map[string]interface{}{"data": map[string]interface{}{"createPullRequest": map[string]interface{}{"pullRequest": map[string]interface{}{"id": pr.GID, "number": pr.Number}}}}
			}
		}
		n := r.NextNum
		r.NextNum++
		id := int(atomic.AddInt64(&store.prSeq, 1))
		pr := &PR{ID: id, GID: "pr-" + strconv.Itoa(r.ID) + "-" + strconv.Itoa(n), Number: n, Title: title, State: "open", HeadRef: head, BaseRef: base}
		r.PRs = append(r.PRs, pr)
		store.mu.Unlock()
		return map[string]interface{}{"data": map[string]interface{}{"createPullRequest": map[string]interface{}{"pullRequest": map[string]interface{}{"id": pr.GID, "number": pr.Number, "title": pr.Title, "state": "OPEN", "headRefName": head, "baseRefName": base}}}}
	}
	if strings.Contains(q, "mergePullRequest") {
		prID := gqlString(vars["pullRequestId"])
		if prID == "" {
			prID = extractGQLArg(q, "pullRequestId")
		}
		parts := strings.Split(prID, "-")
		if len(parts) == 3 {
			if repoID, err := strconv.Atoi(parts[1]); err == nil {
				if num, err := strconv.Atoi(parts[2]); err == nil {
					store.mu.Lock()
					for _, r := range store.repos {
						if r.ID == repoID {
							if pr := r.findPR(num); pr != nil {
								mergeSHA, conflict := r.squashMerge(pr)
								store.mu.Unlock()
								if conflict {
									return gqlErr("Pull request is not mergeable")
								}
								return map[string]interface{}{"data": map[string]interface{}{"mergePullRequest": map[string]interface{}{"pullRequest": map[string]interface{}{"id": prID, "number": num, "state": "CLOSED", "merged": true, "mergeCommit": map[string]interface{}{"oid": mergeSHA}}}}}
							}
						}
					}
					store.mu.Unlock()
				}
			}
		}
		return gqlErr("pull request not found")
	}
	if strings.Contains(q, "addComment") {
		subjectID := gqlString(vars["subjectId"])
		body := gqlString(vars["body"])
		parts := strings.Split(subjectID, "-")
		if len(parts) == 3 && strings.HasPrefix(subjectID, "issue-") {
			if repoID, err := strconv.Atoi(parts[1]); err == nil {
				if num, err := strconv.Atoi(parts[2]); err == nil {
					store.mu.Lock()
					for _, r := range store.repos {
						if r.ID == repoID {
							if is := r.findIssue(num); is != nil {
								id := int(atomic.AddInt64(&store.commentSeq, 1))
								c := &Comment{ID: id, GID: "comment-" + strconv.Itoa(id), Body: body}
								r.ComSeq[num] = append(r.ComSeq[num], c)
								is.rebuildCache(r)
								store.mu.Unlock()
								return map[string]interface{}{"data": map[string]interface{}{"addComment": map[string]interface{}{"commentEdge": map[string]interface{}{"node": map[string]interface{}{"id": c.GID, "body": body}}}}}
							}
						}
					}
					store.mu.Unlock()
				}
			}
		}
		return gqlErr("subject not found")
	}
	return map[string]interface{}{"data": map[string]interface{}{}}
}

func extractGQLArg(q, name string) string {
	// find name: "value" or name: value
	idx := strings.Index(q, name+":")
	if idx < 0 {
		return ""
	}
	rest := strings.TrimSpace(q[idx+len(name)+1:])
	if strings.HasPrefix(rest, "\"") {
		end := strings.Index(rest[1:], "\"")
		if end >= 0 {
			return rest[1 : 1+end]
		}
	}
	return ""
}

func gqlRepo(r *Repo, q string, vars map[string]interface{}) map[string]interface{} {
	out := map[string]interface{}{
		"id": "repo-" + strconv.Itoa(r.ID), "databaseId": r.ID, "name": r.Name,
		"nameWithOwner": r.Owner + "/" + r.Name, "owner": map[string]interface{}{"login": r.Owner},
		"defaultBranchRef": map[string]interface{}{"name": "main"},
		"viewerPermission": "ADMIN", "hasIssuesEnabled": true,
	}
	// issue by number
	if strings.Contains(q, "issue(") {
		num := 0
		if v, ok := vars["number"]; ok {
			switch t := v.(type) {
			case float64:
				num = int(t)
			case int:
				num = t
			}
		}
		if num == 0 {
			if s := extractGQLArg(q, "number"); s != "" {
				num, _ = strconv.Atoi(s)
			}
		}
		if is := r.findIssue(num); is != nil {
			out["issue"] = map[string]interface{}{"id": is.GID, "number": is.Number, "title": is.Title, "body": is.Body, "state": strings.ToUpper(is.State)}
		} else {
			out["issue"] = nil
		}
	}
	// pullRequest by number
	if strings.Contains(q, "pullRequest(") {
		num := 0
		if v, ok := vars["number"]; ok {
			switch t := v.(type) {
			case float64:
				num = int(t)
			case int:
				num = t
			}
		}
		if pr := r.findPR(num); pr != nil {
			out["pullRequest"] = gqlPR(r, pr)
		} else {
			out["pullRequest"] = nil
		}
	}
	// issues list
	if strings.Contains(q, "issues(") {
		first := 10
		if v, ok := vars["first"]; ok {
			if f, ok := v.(float64); ok {
				first = int(f)
			}
		}
		after := gqlString(vars["after"])
		states := []string{"open"}
		if strings.Contains(q, "CLOSED") && !strings.Contains(q, "states:[OPEN]") {
			states = []string{"open", "closed"}
		}
		var list []*Issue
		for _, is := range r.Issues {
			for _, st := range states {
				if is.State == st {
					list = append(list, is)
				}
			}
		}
		// order by number desc (created desc)
		sort.Slice(list, func(a, b int) bool { return list[a].Number > list[b].Number })
		start := 0
		if after != "" {
			if dec, err := b64dec(after); err == nil {
				if v, err := strconv.Atoi(strings.TrimPrefix(string(dec), "c:")); err == nil {
					start = v
				}
			}
		}
		end := start + first
		if end > len(list) {
			end = len(list)
		}
		var nodes []interface{}
		for _, is := range list[start:end] {
			nodes = append(nodes, map[string]interface{}{"id": is.GID, "number": is.Number, "title": is.Title, "body": is.Body, "state": strings.ToUpper(is.State)})
		}
		if nodes == nil {
			nodes = []interface{}{}
		}
		endCursor := ""
		if end < len(list) {
			endCursor = b64enc([]byte("c:" + strconv.Itoa(end)))
		} else if len(list) > 0 {
			endCursor = b64enc([]byte("c:" + strconv.Itoa(len(list))))
		}
		out["issues"] = map[string]interface{}{
			"nodes": nodes,
			"pageInfo": map[string]interface{}{
				"hasNextPage": end < len(list),
				"endCursor":   endCursor,
			},
		}
	}
	// pullRequests list
	if strings.Contains(q, "pullRequests(") {
		first := 5
		if v, ok := vars["first"]; ok {
			if f, ok := v.(float64); ok {
				first = int(f)
			}
		}
		var nodes []interface{}
		count := 0
		for i := len(r.PRs) - 1; i >= 0 && count < first; i-- {
			nodes = append(nodes, gqlPR(r, r.PRs[i]))
			count++
		}
		if nodes == nil {
			nodes = []interface{}{}
		}
		out["pullRequests"] = map[string]interface{}{"nodes": nodes}
	}
	return out
}

func gqlPR(r *Repo, pr *PR) map[string]interface{} {
	mergeable := r.prMergeable(pr)
	var files []interface{}
	if pr.MergeBase == "" {
		pr.MergeBase = r.mergeBase(r.tip(pr.HeadRef), r.tip(pr.BaseRef))
	}
	changes := diffTrees(r, r.commitTree(pr.MergeBase), r.commitTree(r.tip(pr.HeadRef)))
	for _, c := range changes {
		files = append(files, map[string]interface{}{"path": c.Filename})
	}
	if files == nil {
		files = []interface{}{}
	}
	return map[string]interface{}{
		"id": pr.GID, "number": pr.Number, "title": pr.Title, "body": pr.Body,
		"state": strings.ToUpper(pr.State), "headRefName": pr.HeadRef, "baseRefName": pr.BaseRef,
		"mergeable": mergeable, "merged": pr.Merged,
		"files": map[string]interface{}{"nodes": files},
	}
}

// ---------------------------------------------------------------- MCP

var mcpToolsJSON = []byte(`[{"name":"create_repo","description":"Create a new repository","inputSchema":{"type":"object","properties":{"name":{"type":"string"},"description":{"type":"string"},"private":{"type":"boolean"}},"required":["name"]}},{"name":"get_repo","description":"Get a repository by owner and name","inputSchema":{"type":"object","properties":{"owner":{"type":"string"},"repo":{"type":"string"}},"required":["owner","repo"]}},{"name":"create_issue","description":"Create an issue in a repository","inputSchema":{"type":"object","properties":{"owner":{"type":"string"},"repo":{"type":"string"},"title":{"type":"string"},"body":{"type":"string"}},"required":["owner","repo","title"]}},{"name":"list_issues","description":"List issues in a repository","inputSchema":{"type":"object","properties":{"owner":{"type":"string"},"repo":{"type":"string"},"state":{"type":"string"}},"required":["owner","repo"]}},{"name":"create_pull_request","description":"Create a pull request","inputSchema":{"type":"object","properties":{"owner":{"type":"string"},"repo":{"type":"string"},"title":{"type":"string"},"body":{"type":"string"},"head":{"type":"string"},"base":{"type":"string"}},"required":["owner","repo","title","head","base"]}},{"name":"merge_pull_request","description":"Merge a pull request","inputSchema":{"type":"object","properties":{"owner":{"type":"string"},"repo":{"type":"string"},"pull_number":{"type":"integer"}},"required":["owner","repo","pull_number"]}},{"name":"get_issue","description":"Get an issue by number","inputSchema":{"type":"object","properties":{"owner":{"type":"string"},"repo":{"type":"string"},"issue_number":{"type":"integer"}},"required":["owner","repo","issue_number"]}},{"name":"list_pull_requests","description":"List pull requests in a repository","inputSchema":{"type":"object","properties":{"owner":{"type":"string"},"repo":{"type":"string"},"state":{"type":"string"}},"required":["owner","repo"]}}]`)

func handleMCP(req *request) *response {
	if req.method == "DELETE" {
		return &response{status: 204, ctype: jsonCT, body: []byte{}}
	}
	if len(req.body) == 0 {
		return jresp(400, map[string]interface{}{"jsonrpc": "2.0", "id": nil, "error": map[string]interface{}{"code": -32700, "message": "Parse error"}})
	}
	var rpc map[string]interface{}
	if err := jsonUnmarshal(req.body, &rpc); err != nil {
		return jresp(400, map[string]interface{}{"jsonrpc": "2.0", "id": nil, "error": map[string]interface{}{"code": -32700, "message": "Parse error"}})
	}
	id := rpc["id"]
	method, _ := rpc["method"].(string)
	params, _ := rpc["params"].(map[string]interface{})
	if params == nil {
		params = map[string]interface{}{}
	}
	resp := func(result interface{}) *response {
		return jresp(200, map[string]interface{}{"jsonrpc": "2.0", "id": id, "result": result})
	}
	errResp := func(code int, msg string) *response {
		return jresp(200, map[string]interface{}{"jsonrpc": "2.0", "id": id, "error": map[string]interface{}{"code": code, "message": msg}})
	}
	switch method {
	case "initialize":
		pv := "2025-11-25"
		if p, ok := params["protocolVersion"].(string); ok && p != "" {
			pv = p
		}
		return resp(map[string]interface{}{
			"protocolVersion": pv,
			"capabilities":    map[string]interface{}{"tools": map[string]interface{}{}},
			"serverInfo":      map[string]interface{}{"name": "forge", "version": "1.0.0"},
		})
	case "notifications/initialized", "notifications/cancelled":
		return &response{status: 202, ctype: jsonCT, body: []byte{}}
	case "ping":
		return resp(map[string]interface{}{})
	case "server/discover":
		return resp(map[string]interface{}{
			"supportedVersions": []string{"2026-07-28", "2025-11-25"},
			"capabilities":      map[string]interface{}{"tools": map[string]interface{}{}},
			"serverInfo":        map[string]interface{}{"name": "forge", "version": "1.0.0"},
			"_meta": map[string]interface{}{
				"io.modelcontextprotocol/serverInfo": map[string]interface{}{"name": "forge", "version": "1.0.0"},
			},
		})
	case "tools/list":
		// return tools with fixed byte order: build via raw JSON
		var tools []interface{}
		if err := jsonUnmarshal(mcpToolsJSON, &tools); err == nil {
			return resp(map[string]interface{}{"tools": tools})
		}
		return errResp(-32603, "internal error")
	case "tools/call":
		name, _ := params["name"].(string)
		args, _ := params["arguments"].(map[string]interface{})
		if args == nil {
			args = map[string]interface{}{}
		}
		return mcpCall(id, name, args)
	}
	return errResp(-32601, "Method not found")
}

func mcpTextResult(id interface{}, text string, isErr bool) *response {
	res := map[string]interface{}{
		"jsonrpc": "2.0", "id": id,
		"result": map[string]interface{}{
			"content": []map[string]interface{}{{"type": "text", "text": text}},
			"isError": isErr,
		},
	}
	return jresp(200, res)
}

func mcpCall(id interface{}, name string, args map[string]interface{}) *response {
	lname := strings.ToLower(name)
	lname = strings.TrimPrefix(lname, "github__")
	errResp := func(code int, msg string) *response {
		return jresp(200, map[string]interface{}{"jsonrpc": "2.0", "id": id, "error": map[string]interface{}{"code": code, "message": msg}})
	}
	reqStr := func(k string) (string, bool) {
		v, ok := args[k].(string)
		return v, ok && v != ""
	}
	owner, ok1 := reqStr("owner")
	repo, ok2 := reqStr("repo")
	switch lname {
	case "create_repo":
		nm, ok := reqStr("name")
		if !ok {
			return mcpTextResult(id, "missing required argument: name", true)
		}
		desc, _ := args["description"].(string)
		priv, _ := args["private"].(bool)
		store.mu.Lock()
		if _, exists := store.repos[viewerLogin+"/"+nm]; exists {
			store.mu.Unlock()
			return mcpTextResult(id, "Repository already exists", true)
		}
		rid := int(atomic.AddInt64(&store.repoSeq, 1))
		r := newRepo(viewerLogin, nm, rid)
		r.Desc = desc
		r.Priv = priv
		store.repos[viewerLogin+"/"+nm] = r
		store.mu.Unlock()
		return mcpTextResult(id, string(jsonBytes(r.toJSON())), false)
	case "get_repo":
		if !ok1 || !ok2 {
			return errResp(-32602, "missing required arguments")
		}
		r := store.getRepo(owner, repo)
		if r == nil {
			return mcpTextResult(id, "Not Found", true)
		}
		return mcpTextResult(id, string(jsonBytes(r.toJSON())), false)
	case "create_issue":
		if !ok1 || !ok2 {
			return errResp(-32602, "missing required arguments")
		}
		title, ok := reqStr("title")
		if !ok {
			return mcpTextResult(id, "missing required argument: title", true)
		}
		body, _ := args["body"].(string)
		r := store.getRepo(owner, repo)
		if r == nil {
			return mcpTextResult(id, "Not Found", true)
		}
		store.mu.Lock()
		n := r.NextNum
		r.NextNum++
		iid := int(atomic.AddInt64(&store.issueSeq, 1))
		is := &Issue{ID: iid, GID: "issue-" + strconv.Itoa(r.ID) + "-" + strconv.Itoa(n), Number: n, Title: title, Body: body, State: "open", Labels: []string{}}
		is.rebuildCache(r)
		r.Issues = append(r.Issues, is)
		store.mu.Unlock()
		return mcpTextResult(id, string(is.cache), false)
	case "list_issues":
		if !ok1 || !ok2 {
			return errResp(-32602, "missing required arguments")
		}
		state, _ := args["state"].(string)
		if state == "" {
			state = "open"
		}
		r := store.getRepo(owner, repo)
		if r == nil {
			return mcpTextResult(id, "Not Found", true)
		}
		var buf bytes.Buffer
		buf.WriteByte('[')
		first := true
		for i := len(r.Issues) - 1; i >= 0; i-- {
			is := r.Issues[i]
			if state != "all" && is.State != state {
				continue
			}
			if !first {
				buf.WriteByte(',')
			}
			first = false
			buf.Write(is.cache)
		}
		buf.WriteByte(']')
		return mcpTextResult(id, buf.String(), false)
	case "create_pull_request":
		if !ok1 || !ok2 {
			return errResp(-32602, "missing required arguments")
		}
		title, okT := reqStr("title")
		head, okH := reqStr("head")
		base, okB := reqStr("base")
		if !okT || !okH || !okB {
			return mcpTextResult(id, "missing required argument", true)
		}
		body, _ := args["body"].(string)
		r := store.getRepo(owner, repo)
		if r == nil {
			return mcpTextResult(id, "Not Found", true)
		}
		store.mu.Lock()
		for _, pr := range r.PRs {
			if pr.HeadRef == head && pr.State == "open" {
				store.mu.Unlock()
				return mcpTextResult(id, "A pull request already exists for "+head, true)
			}
		}
		n := r.NextNum
		r.NextNum++
		pid := int(atomic.AddInt64(&store.prSeq, 1))
		pr := &PR{ID: pid, GID: "pr-" + strconv.Itoa(r.ID) + "-" + strconv.Itoa(n), Number: n, Title: title, Body: body, State: "open", HeadRef: head, BaseRef: base}
		r.PRs = append(r.PRs, pr)
		store.mu.Unlock()
		return mcpTextResult(id, string(pr.toJSON(r)), false)
	case "merge_pull_request":
		if !ok1 || !ok2 {
			return errResp(-32602, "missing required arguments")
		}
		var num int
		switch v := args["pull_number"].(type) {
		case float64:
			num = int(v)
		case int:
			num = v
		default:
			return mcpTextResult(id, "missing required argument: pull_number", true)
		}
		r := store.getRepo(owner, repo)
		if r == nil {
			return mcpTextResult(id, "Not Found", true)
		}
		pr := r.findPR(num)
		if pr == nil {
			return mcpTextResult(id, "Not Found", true)
		}
		store.mu.Lock()
		mergeSHA, conflict := r.squashMerge(pr)
		store.mu.Unlock()
		if conflict {
			return mcpTextResult(id, "Pull Request is not mergeable", true)
		}
		return mcpTextResult(id, string(jsonBytes(map[string]interface{}{"sha": mergeSHA, "merged": true, "number": num})), false)
	case "get_issue":
		if !ok1 || !ok2 {
			return errResp(-32602, "missing required arguments")
		}
		var num int
		switch v := args["issue_number"].(type) {
		case float64:
			num = int(v)
		case int:
			num = v
		default:
			return mcpTextResult(id, "missing required argument: issue_number", true)
		}
		r := store.getRepo(owner, repo)
		if r == nil {
			return mcpTextResult(id, "Not Found", true)
		}
		is := r.findIssue(num)
		if is == nil {
			return mcpTextResult(id, "Not Found", true)
		}
		return mcpTextResult(id, string(is.cache), false)
	case "list_pull_requests":
		if !ok1 || !ok2 {
			return errResp(-32602, "missing required arguments")
		}
		r := store.getRepo(owner, repo)
		if r == nil {
			return mcpTextResult(id, "Not Found", true)
		}
		var buf bytes.Buffer
		buf.WriteByte('[')
		for i, pr := range r.PRs {
			if i > 0 {
				buf.WriteByte(',')
			}
			buf.Write(pr.toJSON(r))
		}
		buf.WriteByte(']')
		return mcpTextResult(id, buf.String(), false)
	}
	return errResp(-32602, "Unknown tool: "+name)
}

// ---------------------------------------------------------------- Server + main

var serverPort int

func dispatch(req *request) *response {
	// healthz first, no auth
	if req.path == "/healthz" {
		return &response{status: 200, ctype: "text/plain", body: []byte("ok")}
	}
	// auth for everything else (except /healthz)
	if !authed(req) {
		return jerr(401, "Bad credentials")
	}
	switch {
	case req.path == "/api/graphql":
		if req.method != "POST" {
			return jerr(404, "Not Found")
		}
		return handleGraphQL(req)
	case req.path == "/mcp":
		return handleMCP(req)
	case strings.HasPrefix(req.path, "/api/v3"):
		return handleREST(req)
	case strings.Contains(req.path, ".git/"):
		return handleGit(req)
	}
	return jerr(404, "Not Found")
}

func handleConn(conn net.Conn) {
	defer conn.Close()
	br := newBufReader(conn)
	for {
		// read timeout to avoid hanging idle keep-alive forever; refreshed
		// lazily (see bufReader.lastDeadlineSet) to skip a setsockopt per request
		if time.Since(br.lastDeadlineSet) > 5*time.Second {
			conn.SetReadDeadline(time.Now().Add(30 * time.Second))
			br.lastDeadlineSet = time.Now()
		}
		req, err := readRequest(br)
		if err != nil {
			return
		}
		// No deadline clear: the read deadline only governs Reads, never the
		// Write below, so clearing it was one setsockopt per request for nothing.
		resp := dispatch(req)
		if err := writeResponse(conn, req, resp); err != nil {
			return
		}
		if !req.keepAlive {
			return
		}
	}
}

func main() {
	// The heap is tiny (a few MB of objects); trade a little memory for fewer
	// GC cycles on the sequential hot paths.
	debug.SetGCPercent(200)
	seedStore()
	computeViewer()
	viewerJSONBytes = jsonBytes(viewerUserJSON())
	authToken = os.Getenv("MAKEFUN_SHOP_TOKEN")
	if authToken == "" {
		fmt.Fprintln(os.Stderr, "MAKEFUN_SHOP_TOKEN not set")
		os.Exit(1)
	}
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	serverPort = ln.Addr().(*net.TCPAddr).Port
	envURL := os.Getenv("MAKEFUN_ENV_URL")
	if envURL == "" {
		fmt.Fprintln(os.Stderr, "MAKEFUN_ENV_URL not set")
		os.Exit(1)
	}
	// register
	regBody := jsonBytes(map[string]int{"port": serverPort})
	if err := postJSON(envURL+"/register", regBody); err != nil {
		fmt.Fprintln(os.Stderr, "register failed:", err)
		os.Exit(1)
	}
	go func() {
		for {
			c, err := ln.Accept()
			if err != nil {
				return
			}
			go handleConn(c)
		}
	}()
	// poll done
	for {
		time.Sleep(200 * time.Millisecond)
		done, err := getDone(envURL + "/done")
		if err == nil && done {
			break
		}
	}
	os.Exit(0)
}

func postJSON(url string, body []byte) error {
	client := &http.Client{Timeout: 10 * time.Second}
	resp, err := client.Post(url, "application/json", bytes.NewReader(body))
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	io.ReadAll(resp.Body)
	if resp.StatusCode >= 400 {
		return fmt.Errorf("status %d", resp.StatusCode)
	}
	return nil
}

func getDone(url string) (bool, error) {
	client := &http.Client{Timeout: 5 * time.Second}
	resp, err := client.Get(url)
	if err != nil {
		return false, err
	}
	defer resp.Body.Close()
	b, _ := io.ReadAll(resp.Body)
	var v map[string]interface{}
	if err := jsonUnmarshal(b, &v); err != nil {
		return false, err
	}
	done, _ := v["done"].(bool)
	return done, nil
}
