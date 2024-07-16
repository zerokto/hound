// Copyright 2011 The Go Authors.  All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package index

// Index format.
//
// An index stored on disk has the format:
//
//	"csearch index 1\n"
//	list of paths
//	list of names
//	list of posting lists
//	name index
//	posting list index
//	trailer
//
// The list of paths is a sorted sequence of NUL-terminated file or directory names.
// The index covers the file trees rooted at those paths.
// The list ends with an empty name ("\x00").
//
// The list of names is a sorted sequence of NUL-terminated file names.
// The initial entry in the list corresponds to file #0,
// the next to file #1, and so on.  The list ends with an
// empty name ("\x00").
//
// The list of posting lists are a sequence of posting lists.
// Each posting list has the form:
//
//	trigram [3]
//	deltas [v]...
//
// The trigram gives the 3 byte trigram that this list describes.  The
// delta list is a sequence of varint-encoded deltas between file
// IDs, ending with a zero delta.  For example, the delta list [2,5,1,1,0]
// encodes the file ID list 1, 6, 7, 8.  The delta list [0] would
// encode the empty file ID list, but empty posting lists are usually
// not recorded at all.  The list of posting lists ends with an entry
// with trigram "\xff\xff\xff" and a delta list consisting a single zero.
//
// The indexes enable efficient random access to the lists.  The name
// index is a sequence of 4-byte big-endian values listing the byte
// offset in the name list where each name begins.  The posting list
// index is a sequence of index entries describing each successive
// posting list.  Each index entry has the form:
//
//	trigram [3]
//	file count [4]
//	offset [4]
//
// Index entries are only written for the non-empty posting lists,
// so finding the posting list for a specific trigram requires a
// binary search over the posting list index.  In practice, the majority
// of the possible trigrams are never seen, so omitting the missing
// ones represents a significant storage savings.
//
// The trailer has the form:
//
//	offset of path list [4]
//	offset of name list [4]
//	offset of posting lists [4]
//	offset of name index [4]
//	offset of posting list index [4]
//	"\ncsearch trailr\n"

import (
	"bytes"
	"encoding/binary"
	"log"
	"os"
	"runtime"
	"sort"
)

const (
	magic        = "csearch index 1\n"
	trailerMagic = "\ncsearch trailr\n"
)

// An Index implements read-only access to a trigram index.
type Index struct {
	Verbose   bool
	data      mmapData
	pathData  uint32
	nameData  uint32
	postData  uint32
	nameIndex uint32
	postIndex uint32
	numName   int
	numPost   int
}

const postEntrySize = 3 + 4 + 4

func Open(file string) *Index {
	mm := mmap(file) // 将文件映射到内存

	// 长度不满足条件，文件结尾不符合要求
	if len(mm.d) < 4*4+len(trailerMagic) || string(mm.d[len(mm.d)-len(trailerMagic):]) != trailerMagic {
		corrupt(mm.f)
	}

	// 计算从数据开始到 trailerMagic 之前的字节数
	n := uint32(len(mm.d) - len(trailerMagic) - 5*4)
	ix := &Index{data: mm}
	ix.pathData = ix.uint32(n) // 通过文件尾部的偏移量获取pathData
	ix.nameData = ix.uint32(n + 4)
	ix.postData = ix.uint32(n + 8)
	ix.nameIndex = ix.uint32(n + 12)
	ix.postIndex = ix.uint32(n + 16)
	ix.numName = int((ix.postIndex-ix.nameIndex)/4) - 1  // 计算名称索引中条目的数量  再减去1（因为最后一个条目是结束标记)
	ix.numPost = int((n - ix.postIndex) / postEntrySize) // 计算倒排列表索引中条目的数量
	return ix
}

// slice returns the slice of index data starting at the given byte offset.
// If n >= 0, the slice must have length at least n and is truncated to length n.
func (ix *Index) slice(off uint32, n int) []byte {
	o := int(off)
	if uint32(o) != off || n >= 0 && o+n > len(ix.data.d) { // 判断是否越界
		corrupt(ix.data.f)
	}
	if n < 0 {
		return ix.data.d[o:]
	}

	return ix.data.d[o : o+n]
}

// uint32 returns the uint32 value at the given offset in the index data.
func (ix *Index) uint32(off uint32) uint32 {
	return binary.BigEndian.Uint32(ix.slice(off, 4))
}

func (ix *Index) Close() error {
	return ix.data.close()
}

// uvarint returns the varint value at the given offset in the index data.
func (ix *Index) uvarint(off uint32) uint32 { //nolint
	v, n := binary.Uvarint(ix.slice(off, -1)) // 读取到末尾
	if n <= 0 {
		corrupt(ix.data.f)
	}
	return uint32(v)
}

// Paths returns the list of indexed paths.
func (ix *Index) Paths() []string {
	off := ix.pathData
	var x []string
	for {
		s := ix.str(off) // 读取字符串
		if len(s) == 0 {
			break
		}
		x = append(x, string(s))
		off += uint32(len(s) + 1) // 添加偏移量
	}
	return x
}

// NameBytes returns the name corresponding to the given fileid.
func (ix *Index) NameBytes(fileid uint32) []byte {
	off := ix.uint32(ix.nameIndex + 4*fileid) // 计算文件id对应的偏移量
	return ix.str(ix.nameData + off)
}

func (ix *Index) str(off uint32) []byte {
	str := ix.slice(off, -1)
	i := bytes.IndexByte(str, '\x00') // 查找字符串结束标记
	if i < 0 {
		corrupt(ix.data.f)
	}
	return str[:i] // 返回字符串
}

// Name returns the name corresponding to the given fileid.
func (ix *Index) Name(fileid uint32) string {
	return string(ix.NameBytes(fileid))
}

// listAt returns the index list entry at the given offset.
func (ix *Index) listAt(off uint32) (trigram, count, offset uint32) {
	d := ix.slice(ix.postIndex+off, postEntrySize)              // 从倒排列表索引的起始位置 ix.postIndex 加上偏移量 off 开始，读取一个长度为 postEntrySize 的字节切片
	trigram = uint32(d[0])<<16 | uint32(d[1])<<8 | uint32(d[2]) // 三个字节合并成一个32位的整数
	count = binary.BigEndian.Uint32(d[3:])                      // 解析文件数量
	offset = binary.BigEndian.Uint32(d[3+4:])                   // 从切片 d 的第七个字节开始读取一个32位的大端序整数，得到倒排列表的偏移量
	return
}

func (ix *Index) dumpPosting() { //nolint
	d := ix.slice(ix.postIndex, postEntrySize*ix.numPost) // 读取倒排列表索引的起始位置到末尾，每个条目 postEntrySize 个字节
	for i := 0; i < ix.numPost; i++ {
		j := i * postEntrySize
		t := uint32(d[j])<<16 | uint32(d[j+1])<<8 | uint32(d[j+2])
		count := int(binary.BigEndian.Uint32(d[j+3:]))
		offset := binary.BigEndian.Uint32(d[j+3+4:])
		log.Printf("%#x: %d at %d", t, count, offset) // 用于打印索引中所有倒排列表条目的详细信息
	}
}

// 通过二分搜索在倒排列表索引中查找与给定trigram相匹配的倒排列表条目，返回条目的数量和偏移量。
func (ix *Index) findList(trigram uint32) (count int, offset uint32) {
	// binary search
	d := ix.slice(ix.postIndex, postEntrySize*ix.numPost)
	i := sort.Search(ix.numPost, func(i int) bool {
		i *= postEntrySize
		t := uint32(d[i])<<16 | uint32(d[i+1])<<8 | uint32(d[i+2])
		return t >= trigram
	})
	if i >= ix.numPost {
		return 0, 0
	}
	i *= postEntrySize
	t := uint32(d[i])<<16 | uint32(d[i+1])<<8 | uint32(d[i+2])
	if t != trigram {
		return 0, 0
	}
	count = int(binary.BigEndian.Uint32(d[i+3:]))
	offset = binary.BigEndian.Uint32(d[i+3+4:])
	return
}

type postReader struct {
	ix       *Index   // 索引对象的引用
	count    int      // 倒排列表中的文件数量
	offset   uint32   // 倒排列表的偏移量
	fileid   uint32   // 当前文件ID
	d        []byte   // 倒排列表的剩余数据
	restrict []uint32 // 限制搜索的文件ID列表
}

func (r *postReader) init(ix *Index, trigram uint32, restrict []uint32) {
	count, offset := ix.findList(trigram)
	if count == 0 {
		return
	}
	r.ix = ix
	r.count = count
	r.offset = offset
	r.fileid = ^uint32(0)
	r.d = ix.slice(ix.postData+offset+3, -1)
	r.restrict = restrict
}

func (r *postReader) max() int {
	return int(r.count)
}

func (r *postReader) next() bool {
	for r.count > 0 {
		r.count--
		delta64, n := binary.Uvarint(r.d) // 读取倒排列表中的文件ID，返回文件ID和读取的字节数
		delta := uint32(delta64)
		if n <= 0 || delta == 0 {
			corrupt(r.ix.data.f)
		}

		r.d = r.d[n:]     // 更新倒排列表的剩余数据
		r.fileid += delta // 累加文件ID
		if r.restrict != nil {
			i := 0
			for i < len(r.restrict) && r.restrict[i] < r.fileid {
				i++
			}
			r.restrict = r.restrict[i:]                            // 更新限制搜索的文件ID列表
			if len(r.restrict) == 0 || r.restrict[0] != r.fileid { // 当前文件ID不在限制列表中，跳过
				continue
			}
		}
		return true
	}
	// list should end with terminating 0 delta
	if r.d != nil && (len(r.d) == 0 || r.d[0] != 0) { // 倒排列表的剩余数据不以0结尾，则说明索引文件格式错误
		corrupt(r.ix.data.f)
	}
	r.fileid = ^uint32(0) // 标记当前文件ID无效
	return false
}

func (ix *Index) PostingList(trigram uint32) []uint32 {
	return ix.postingList(trigram, nil)
}

func (ix *Index) postingList(trigram uint32, restrict []uint32) []uint32 {
	var r postReader
	r.init(ix, trigram, restrict)
	x := make([]uint32, 0, r.max())
	for r.next() {
		x = append(x, r.fileid)
	}
	return x
}

func (ix *Index) PostingAnd(list []uint32, trigram uint32) []uint32 {
	return ix.postingAnd(list, trigram, nil)
}

// 返回list中与trigram匹配的文件ID列表, 求交集
func (ix *Index) postingAnd(list []uint32, trigram uint32, restrict []uint32) []uint32 {
	var r postReader
	r.init(ix, trigram, restrict)
	x := list[:0]
	i := 0
	for r.next() {
		fileid := r.fileid
		for i < len(list) && list[i] < fileid { // 跳过list中比fileid小的文件ID
			i++
		}

		if i < len(list) && list[i] == fileid { // 找到list中等于fileid的文件ID
			x = append(x, fileid)
			i++
		}
	}
	return x
}

func (ix *Index) PostingOr(list []uint32, trigram uint32) []uint32 {
	return ix.postingOr(list, trigram, nil)
}

// 返回list中与trigram匹配的文件ID列表, 求并集
func (ix *Index) postingOr(list []uint32, trigram uint32, restrict []uint32) []uint32 {
	var r postReader
	r.init(ix, trigram, restrict)
	x := make([]uint32, 0, len(list)+r.max())
	i := 0
	for r.next() {
		fileid := r.fileid
		for i < len(list) && list[i] < fileid {
			x = append(x, list[i])
			i++
		}
		x = append(x, fileid)
		if i < len(list) && list[i] == fileid {
			i++
		}
	}
	x = append(x, list[i:]...)
	return x
}

func (ix *Index) PostingQuery(q *Query) []uint32 {
	return ix.postingQuery(q, nil)
}

// 用于处理查询 q 并返回与查询匹配的文件ID列表
func (ix *Index) postingQuery(q *Query, restrict []uint32) (ret []uint32) {
	var list []uint32
	switch q.Op {
	case QNone:
		// nothing
	case QAll:
		if restrict != nil {
			return restrict
		}
		list = make([]uint32, ix.numName)
		for i := range list {
			list[i] = uint32(i)
		}
		return list
	case QAnd:
		for _, t := range q.Trigram {
			tri := uint32(t[0])<<16 | uint32(t[1])<<8 | uint32(t[2])
			if list == nil {
				list = ix.postingList(tri, restrict)
			} else {
				list = ix.postingAnd(list, tri, restrict)
			}
			if len(list) == 0 {
				return nil
			}
		}
		for _, sub := range q.Sub {
			if list == nil {
				list = restrict
			}
			list = ix.postingQuery(sub, list)
			if len(list) == 0 {
				return nil
			}
		}
	case QOr:
		for _, t := range q.Trigram {
			tri := uint32(t[0])<<16 | uint32(t[1])<<8 | uint32(t[2])
			if list == nil {
				list = ix.postingList(tri, restrict)
			} else {
				list = ix.postingOr(list, tri, restrict)
			}
		}
		for _, sub := range q.Sub {
			list1 := ix.postingQuery(sub, restrict)
			list = mergeOr(list, list1)
		}
	}
	return list
}

// 合并两个有序的列表
func mergeOr(l1, l2 []uint32) []uint32 {
	var l []uint32
	i := 0
	j := 0
	for i < len(l1) || j < len(l2) {
		switch {
		case j == len(l2) || (i < len(l1) && l1[i] < l2[j]):
			l = append(l, l1[i])
			i++
		case i == len(l1) || (j < len(l2) && l1[i] > l2[j]):
			l = append(l, l2[j])
			j++
		case l1[i] == l2[j]:
			l = append(l, l1[i])
			i++
			j++
		}
	}
	return l
}

func corrupt(file *os.File) {
	log.Fatalf("corrupt index: %s", file.Name())
}

// An mmapData is mmap'ed read-only data from a file.
type mmapData struct {
	f *os.File
	d []byte
	o []byte
}

func (m *mmapData) close() error {
	return unmmapFile(m)
}

// mmap maps the given file into memory.
func mmap(file string) mmapData {
	f, err := os.Open(file)
	if err != nil {
		log.Fatal(err)
	}
	return mmapFile(f)
}

// File returns the name of the index file to use.
// It is either $CSEARCHINDEX or $HOME/.csearchindex.
func File() string {
	f := os.Getenv("CSEARCHINDEX")
	if f != "" {
		return f
	}
	var home string
	if runtime.GOOS == "windows" {
		home = os.Getenv("HOMEPATH")
	} else {
		home = os.Getenv("HOME")
	}
	return home + "/.csearchindex"
}
