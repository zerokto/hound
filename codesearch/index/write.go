// Copyright 2011 The Go Authors.  All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package index

import (
	"fmt"
	"io"
	"io/ioutil"
	"log"
	"os"
	"strings"
	"unsafe"

	"github.com/hound-search/hound/codesearch/sparse"
)

// Index writing.  See read.go for details of on-disk format.
//
// It would suffice to make a single large list of (trigram, file#) pairs
// while processing the files one at a time, sort that list by trigram,
// and then create the posting lists from subsequences of the list.
// However, we do not assume that the entire index fits in memory.
// Instead, we sort and flush the list to a new temporary file each time
// it reaches its maximum in-memory size, and then at the end we
// create the final posting lists by merging the temporary files as we
// read them back in.
//
// It would also be useful to be able to create an index for a subset
// of the files and then merge that index into an existing one.  This would
// allow incremental updating of an existing index when a directory changes.
// But we have not implemented that.

// An IndexWriter creates an on-disk index corresponding to a set of files.
type IndexWriter struct {
	LogSkip bool // log information about skipped files 是否记录跳过文件的信息
	Verbose bool // log status using package log 是否记录详细的运行状态

	trigram *sparse.Set // trigrams for the current file 稀疏集合，用于存储当前文件的三元组
	buf     [8]byte     // scratch buffer 字节缓存区， 用于临时存储操作中的字节数据。
	paths   []string    // 一个字符串切片，存储文件路径。

	nameData   *bufWriter // temp file holding list of names // 存储文件名数据的临时文件
	nameLen    uint32     //nolint number of bytes written to nameData 存储文件名数据的长度
	nameIndex  *bufWriter // temp file holding name index 文件名索引的临时文件
	numName    int        // number of names written 已经写入的文件名数量
	totalBytes int64      // 已处理的总字节数。

	post      []postEntry // list of (trigram, file#) pairs 存储（三元组，文件编号）对
	postFile  []*os.File  // flushed post entries 已冲洗的倒排索引文件
	postData  [][]byte    // mmap buffers to be unmapped 内存映射的缓冲区
	postIndex *bufWriter  // temp file holding posting list index 存储倒排索引的临时文件

	inbuf []byte     // input buffer 输入缓冲区，用于读取文件数据
	main  *bufWriter // main index file 主索引文件，用于最终的索引输出
}

const npost = 64 << 20 / 8 // 64 MB worth of post entries

// Create returns a new IndexWriter that will write the index to file.
func Create(file string) *IndexWriter {
	return &IndexWriter{
		trigram:   sparse.NewSet(1 << 24), // 稀疏集合，可以存储2^24个元素
		nameData:  bufCreate(""),
		nameIndex: bufCreate(""),
		postIndex: bufCreate(""),
		main:      bufCreate(file),
		post:      make([]postEntry, 0, npost),
		inbuf:     make([]byte, 16384),
	}
}

// A postEntry is an in-memory (trigram, file#) pair.
type postEntry uint64

func (p postEntry) trigram() uint32 {
	return uint32(p >> 32) // 高32位为三元组，低32位为文件编号
}

func (p postEntry) fileid() uint32 {
	return uint32(p) // 高32位为三元组，低32位为文件编号
}

func makePostEntry(trigram, fileid uint32) postEntry {
	return postEntry(trigram)<<32 | postEntry(fileid)
}

// Tuning constants for detecting text files.
// A file is assumed not to be text files (and thus not indexed)
// if it contains an invalid UTF-8 sequences, if it is longer than maxFileLength
// bytes, if it contains more than maxLongLineRatio lines longer than maxLineLen bytes,
// or if it contains more than maxTextTrigrams distinct trigrams AND
// it has a ratio of trigrams to filesize > maxTrigramRatio.
const (
	maxFileLen       = 1 << 25
	maxLineLen       = 2000
	maxLongLineRatio = 0.1
	maxTextTrigrams  = 20000
	maxTrigramRatio  = 0.1
)

// AddPaths adds the given paths to the index's list of paths.
func (ix *IndexWriter) AddPaths(paths []string) {
	ix.paths = append(ix.paths, paths...)
}

// AddFile adds the file with the given name (opened using os.Open)
// to the index.  It logs errors using package log.
func (ix *IndexWriter) AddFile(name string) {
	f, err := os.Open(name)
	if err != nil {
		log.Print(err)
		return
	}
	defer f.Close()
	ix.Add(name, f)
}

// Add adds the file f to the index under the given name.
// It logs errors using package log.
func (ix *IndexWriter) Add(name string, f io.Reader) string {
	ix.trigram.Reset()

	var (
		c          = byte(0) //nolint
		i          = 0
		buf        = ix.inbuf[:0]
		tv         = uint32(0)
		n          = int64(0)
		linelen    = 0
		numLines   = 0
		longLines  = 0
		skipReason = "" //nolint
	)

	for {

		tv = (tv << 8) & (1<<24 - 1) // 移位并掩码操作以保持 tv 为 24 位
		if i >= len(buf) {           // 缓冲区已经用完，需要读取
			n, err := f.Read(buf[:cap(buf)]) // 读取到 buf 的容量大小
			if n == 0 {
				if err != nil {
					if err == io.EOF {
						break
					}
					log.Printf("%s: %v\n", name, err)
					return ""
				}
				log.Printf("%s: 0-length read\n", name)
				return ""
			}
			buf = buf[:n] // 更新 buf 的长度
			i = 0         // 重置 i
		}

		c = buf[i] // 获取下一个字符
		i++
		tv |= uint32(c)  // 更新tv的后8位
		if n++; n >= 3 { // 更新文件总字节数，当达到 3 字节时开始添加三元组
			ix.trigram.Add(tv)
		}

		if !validUTF8((tv>>8)&0xFF, tv&0xFF) { // 检查当前三元组是否为有效的 UTF-8 序列
			skipReason = "Invalid UTF-8"
			if ix.LogSkip {
				log.Printf("%s: %s\n", name, skipReason)
			}
			return skipReason
		}

		if n > maxFileLen { // 查文件是否超过最大允许长度
			skipReason = "Too long"
			if ix.LogSkip {
				log.Printf("%s: %s\n", name, skipReason)
			}
			return skipReason
		}

		linelen++ //  增加当前行长度
		if c == '\n' {
			numLines++
			if linelen > maxLineLen {
				longLines++ // 增加长行数
			}
			linelen = 0
		}
	}

	if n > 0 { // 如果文件中有数据
		trigramRatio := float32(ix.trigram.Len()) / float32(n)                    // 计算三元组比率
		if trigramRatio > maxTrigramRatio && ix.trigram.Len() > maxTextTrigrams { // 检查比率是否过高
			skipReason = fmt.Sprintf("Trigram ratio too high (%0.2f), probably not text", trigramRatio)
			if ix.LogSkip {
				log.Printf("%s: %s\n", name, skipReason)
			}
			return skipReason
		}

		longLineRatio := float32(longLines) / float32(numLines) // 计算长行比率
		if longLineRatio > maxLongLineRatio {
			skipReason = fmt.Sprintf("Too many long lines, ratio: %0.2f", longLineRatio)
			if ix.LogSkip {
				log.Printf("%s: %s\n", name, skipReason)
			}
			return skipReason
		}
	}

	ix.totalBytes += n // 更新文件总字节数

	if ix.Verbose {
		log.Printf("%d %d %s\n", n, ix.trigram.Len(), name)
	}

	fileid := ix.addName(name)                   // 添加文件名到索引，并获取文件 ID
	for _, trigram := range ix.trigram.Dense() { // 遍历所有三元组
		if len(ix.post) >= cap(ix.post) { // 检查倒排索引是否已满
			ix.flushPost() // 如果已满，刷新倒排索引
		}
		ix.post = append(ix.post, makePostEntry(trigram, fileid)) // 将三元组和文件 ID 添加到倒排索引
	}

	return ""
}

// Flush flushes the index entry to the target file.
func (ix *IndexWriter) Flush() {
	ix.addName("")

	// 保存关键部分的文件偏移量
	var off [5]uint32
	ix.main.writeString(magic)
	off[0] = ix.main.offset()

	for _, p := range ix.paths {
		ix.main.writeString(p)
		ix.main.writeString("\x00")
	}
	ix.main.writeString("\x00")
	off[1] = ix.main.offset()

	copyFile(ix.main, ix.nameData)
	off[2] = ix.main.offset()

	ix.mergePost(ix.main)
	off[3] = ix.main.offset()

	copyFile(ix.main, ix.nameIndex)
	off[4] = ix.main.offset()

	copyFile(ix.main, ix.postIndex)
	for _, v := range off {
		ix.main.writeUint32(v)
	}
	ix.main.writeString(trailerMagic)

	// 清理工作
	os.Remove(ix.nameData.name)
	for _, d := range ix.postData {
		unmmap(d) //nolint
	}
	for _, f := range ix.postFile {
		f.Close()
		os.Remove(f.Name())
	}
	os.Remove(ix.nameIndex.name)
	os.Remove(ix.postIndex.name)

	log.Printf("%d data bytes, %d index bytes", ix.totalBytes, ix.main.offset())

	ix.main.flush()
}

func (ix *IndexWriter) Close() {
	ix.main.file.Close()
}

func copyFile(dst, src *bufWriter) {
	dst.flush()
	_, err := io.Copy(dst.file, src.finish())
	if err != nil {
		log.Fatalf("copying %s to %s: %v", src.name, dst.name, err)
	}
}

// addName adds the file with the given name to the index.
// It returns the assigned file ID number.
func (ix *IndexWriter) addName(name string) uint32 {
	if strings.Contains(name, "\x00") { // 文件名不能包含 NUL 字节
		log.Fatalf("%q: file has NUL byte in name", name)
	}

	ix.nameIndex.writeUint32(ix.nameData.offset()) // 写入文件名偏移量到索引
	ix.nameData.writeString(name)                  // 写入文件名到数据
	ix.nameData.writeByte(0)                       // 写入 NUL 字节
	id := ix.numName                               // 获取文件 ID, 已经添加过的文件 个数
	ix.numName++
	return uint32(id)
}

// flushPost writes ix.post to a new temporary file and
// clears the slice.
func (ix *IndexWriter) flushPost() {
	w, err := ioutil.TempFile("", "csearch-index")
	if err != nil {
		log.Fatal(err)
	}
	if ix.Verbose {
		log.Printf("flush %d entries to %s", len(ix.post), w.Name())
	}
	sortPost(ix.post)

	// Write the raw ix.post array to disk as is.
	// This process is the one reading it back in, so byte order is not a concern.
	data := (*[npost * 8]byte)(unsafe.Pointer(&ix.post[0]))[:len(ix.post)*8]
	if n, err := w.Write(data); err != nil || n < len(data) {
		if err != nil {
			log.Fatal(err)
		}
		log.Fatalf("short write writing %s", w.Name())
	}

	ix.post = ix.post[:0]
	w.Seek(0, 0) //nolint
	ix.postFile = append(ix.postFile, w)
}

// mergePost reads the flushed index entries and merges them
// into posting lists, writing the resulting lists to out.
func (ix *IndexWriter) mergePost(out *bufWriter) {
	var h postHeap

	log.Printf("merge %d files + mem", len(ix.postFile))
	for _, f := range ix.postFile {
		ix.postData = append(
			ix.postData,
			h.addFile(f))
	}
	sortPost(ix.post)
	h.addMem(ix.post)

	npost := 0
	e := h.next()
	offset0 := out.offset()
	for {
		npost++
		offset := out.offset() - offset0
		trigram := e.trigram()
		ix.buf[0] = byte(trigram >> 16)
		ix.buf[1] = byte(trigram >> 8)
		ix.buf[2] = byte(trigram)

		// posting list
		fileid := ^uint32(0)
		nfile := uint32(0)
		out.write(ix.buf[:3])
		for ; e.trigram() == trigram && trigram != 1<<24-1; e = h.next() {
			out.writeUvarint(e.fileid() - fileid)
			fileid = e.fileid()
			nfile++
		}
		out.writeUvarint(0)

		// index entry
		ix.postIndex.write(ix.buf[:3])
		ix.postIndex.writeUint32(nfile)
		ix.postIndex.writeUint32(offset)

		if trigram == 1<<24-1 {
			break
		}
	}
}

// A postChunk represents a chunk of post entries flushed to disk or
// still in memory.
type postChunk struct {
	e postEntry   // next entry 下一个
	m []postEntry // remaining entries after e 之后所有的
}

const postBuf = 4096 //nolint

// A postHeap is a heap (priority queue) of postChunks. 用来管理倒排索引的堆数据结构， tirgram 排序， 每个 triram 对应一个 postChunk，小根堆
type postHeap struct {
	ch []*postChunk // 管理Chunk的集合
}

func (h *postHeap) addFile(f *os.File) []byte {
	data := mmapFile(f).d // 使用mmapFile函数将文件映射到内存中
	m := (*[npost]postEntry)(unsafe.Pointer(&data[0]))[:len(data)/8]
	h.addMem(m)
	return data
}

func (h *postHeap) addMem(x []postEntry) {
	h.add(&postChunk{m: x})
}

// step reads the next entry from ch and saves it in ch.e.
// It returns false if ch is over.
func (h *postHeap) step(ch *postChunk) bool { //nolint
	old := ch.e
	m := ch.m
	if len(m) == 0 {
		return false
	}
	// 读取下一个
	ch.e = postEntry(m[0])
	// 更新m
	m = m[1:]
	ch.m = m
	if old >= ch.e { // 违反排序规则
		panic("bad sort")
	}
	return true
}

// add adds the chunk to the postHeap.
// All adds must be called before the first call to next.
func (h *postHeap) add(ch *postChunk) {
	// 将第一个条目放到堆中
	if len(ch.m) > 0 {
		ch.e = ch.m[0]
		ch.m = ch.m[1:]
		h.push(ch)
	}
}

// empty reports whether the postHeap is empty.
func (h *postHeap) empty() bool { //nolint
	return len(h.ch) == 0
}

// next returns the next entry from the postHeap.
// It returns a postEntry with trigram == 1<<24 - 1 if h is empty.
func (h *postHeap) next() postEntry {
	if len(h.ch) == 0 {
		return makePostEntry(1<<24-1, 0)
	}
	ch := h.ch[0]
	e := ch.e
	m := ch.m
	if len(m) == 0 {
		h.pop()
	} else {
		ch.e = m[0]
		ch.m = m[1:]
		h.siftDown(0)
	}
	return e
}

func (h *postHeap) pop() *postChunk {
	ch := h.ch[0]
	n := len(h.ch) - 1
	h.ch[0] = h.ch[n]
	h.ch = h.ch[:n]
	if n > 1 {
		h.siftDown(0)
	}
	return ch
}

func (h *postHeap) push(ch *postChunk) {
	n := len(h.ch)
	h.ch = append(h.ch, ch)
	if len(h.ch) >= 2 {
		h.siftUp(n)
	}
}

func (h *postHeap) siftDown(i int) {
	ch := h.ch
	for {
		j1 := 2*i + 1
		if j1 >= len(ch) {
			break
		}
		j := j1
		if j2 := j1 + 1; j2 < len(ch) && ch[j1].e >= ch[j2].e {
			j = j2
		}
		if ch[i].e < ch[j].e {
			break
		}
		ch[i], ch[j] = ch[j], ch[i]
		i = j
	}
}

func (h *postHeap) siftUp(j int) {
	ch := h.ch
	for {
		i := (j - 1) / 2
		if i == j || ch[i].e < ch[j].e {
			break
		}
		ch[i], ch[j] = ch[j], ch[i]
		j = i
	}
}

// A bufWriter is a convenience wrapper: a closeable bufio.Writer.
type bufWriter struct {
	name string   // 文件名称
	file *os.File // 指向底层的os.File的指针，用于实际的文件IO操作
	buf  []byte   // 一个字节切片
	tmp  [8]byte  //nolint 一个临时字节数组，可能用于内部操作，例如格式化数字等
}

// bufCreate creates a new file with the given name and returns a
// corresponding bufWriter.  If name is empty, bufCreate uses a
// temporary file.
func bufCreate(name string) *bufWriter {
	var (
		f   *os.File
		err error
	)

	if name != "" {
		f, err = os.OpenFile(name, os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0600)
	} else {
		f, err = ioutil.TempFile("", "csearch")
	}

	if err != nil {
		log.Fatal(err)
	}

	return &bufWriter{
		name: f.Name(),
		buf:  make([]byte, 0, 256<<10),
		file: f,
	}
}

func (b *bufWriter) write(x []byte) {
	n := cap(b.buf) - len(b.buf) // 计算当前bufWriter的可用空间
	if len(x) > n {
		b.flush()                 // 刷新当前bufWriter
		if len(x) >= cap(b.buf) { // 判断x是否大于bufWriter的容量
			if _, err := b.file.Write(x); err != nil { // 直接写入文件
				log.Fatalf("writing %s: %v", b.name, err)
			}
			return
		}
	}

	b.buf = append(b.buf, x...)
}

func (b *bufWriter) writeByte(x byte) {
	if len(b.buf) >= cap(b.buf) {
		b.flush()
	}
	b.buf = append(b.buf, x)
}

func (b *bufWriter) writeString(s string) {
	n := cap(b.buf) - len(b.buf)
	if len(s) > n {
		b.flush()
		if len(s) >= cap(b.buf) {
			if _, err := b.file.WriteString(s); err != nil {
				log.Fatalf("writing %s: %v", b.name, err)
			}
			return
		}
	}
	b.buf = append(b.buf, s...)
}

// offset returns the current write offset.
func (b *bufWriter) offset() uint32 {
	off, _ := b.file.Seek(0, 1)    // 获取当前文件指针的位置
	off += int64(len(b.buf))       // 计算当前bufWriter的偏移
	if int64(uint32(off)) != off { // 判断是否发生溢出，如果发生溢出，贼超过4GB
		log.Fatalf("index is larger than 4GB")
	}

	return uint32(off)
}

func (b *bufWriter) flush() {
	if len(b.buf) == 0 {
		return
	}
	_, err := b.file.Write(b.buf)
	if err != nil {
		log.Fatalf("writing %s: %v", b.name, err)
	}
	b.buf = b.buf[:0]
}

// finish flushes the file to disk and returns an open file ready for reading.
func (b *bufWriter) finish() *os.File {
	b.flush()
	f := b.file
	f.Seek(0, 0) //nolint 将读写指针移动到开始位置
	return f
}

func (b *bufWriter) writeTrigram(t uint32) {
	if cap(b.buf)-len(b.buf) < 3 {
		b.flush()
	}
	b.buf = append(b.buf, byte(t>>16), byte(t>>8), byte(t))
}

func (b *bufWriter) writeUint32(x uint32) {
	if cap(b.buf)-len(b.buf) < 4 {
		b.flush()
	}
	b.buf = append(b.buf, byte(x>>24), byte(x>>16), byte(x>>8), byte(x))
}

// 功能是将一个 32 位无符号整数 (uint32) 编码为可变长度整数 (Varint) 并写入缓冲区。Varints 是一种用于编码整数的序列化技术，特别适用于那些小整数占多数的场景，因为它可以节省存储空间。
func (b *bufWriter) writeUvarint(x uint32) {
	if cap(b.buf)-len(b.buf) < 5 {
		b.flush()
	}
	switch {
	case x < 1<<7:
		b.buf = append(b.buf, byte(x))
	case x < 1<<14:
		b.buf = append(b.buf, byte(x|0x80), byte(x>>7))
	case x < 1<<21:
		b.buf = append(b.buf, byte(x|0x80), byte(x>>7|0x80), byte(x>>14))
	case x < 1<<28:
		b.buf = append(b.buf, byte(x|0x80), byte(x>>7|0x80), byte(x>>14|0x80), byte(x>>21))
	default:
		b.buf = append(b.buf, byte(x|0x80), byte(x>>7|0x80), byte(x>>14|0x80), byte(x>>21|0x80), byte(x>>28))
	}
}

// validUTF8 reports whether the byte pair can appear in a
// valid sequence of UTF-8-encoded code points.
func validUTF8(c1, c2 uint32) bool {
	switch {
	case c1 < 0x80:
		// 1-byte, must be followed by 1-byte or first of multi-byte
		return c2 < 0x80 || 0xc0 <= c2 && c2 < 0xf8
	case c1 < 0xc0:
		// continuation byte, can be followed by nearly anything
		return c2 < 0xf8
	case c1 < 0xf8:
		// first of multi-byte, must be followed by continuation byte
		return 0x80 <= c2 && c2 < 0xc0
	}
	return false
}

// sortPost sorts the postentry list.
// The list is already sorted by fileid (bottom 32 bits)
// and the top 8 bits are always zero, so there are only
// 24 bits to sort.  Run two rounds of 12-bit radix sort.
const sortK = 12

// TODO(knorton): sortTmp and sortN were previously static state
// presumably to avoid allocations of the large buffers. Sadly,
// this makes it impossible for us to run concurrent indexers.
// I have moved them into local allocations but if we really do
// need to share a buffer, they can easily go into a reusable
// object, similar to the way buffers are reused in grepper.
func sortPost(post []postEntry) {
	var sortN [1 << sortK]int

	sortTmp := make([]postEntry, len(post))
	tmp := sortTmp[:len(post)]

	const k = sortK
	for i := range sortN {
		sortN[i] = 0
	}
	for _, p := range post {
		r := uintptr(p>>32) & (1<<k - 1)
		sortN[r]++
	}
	tot := 0
	for i, count := range sortN {
		sortN[i] = tot
		tot += count
	}
	for _, p := range post {
		r := uintptr(p>>32) & (1<<k - 1)
		o := sortN[r]
		sortN[r]++
		tmp[o] = p
	}
	tmp, post = post, tmp

	for i := range sortN {
		sortN[i] = 0
	}
	for _, p := range post {
		r := uintptr(p>>(32+k)) & (1<<k - 1)
		sortN[r]++
	}
	tot = 0
	for i, count := range sortN {
		sortN[i] = tot
		tot += count
	}
	for _, p := range post {
		r := uintptr(p>>(32+k)) & (1<<k - 1)
		o := sortN[r]
		sortN[r]++
		tmp[o] = p
	}
}
