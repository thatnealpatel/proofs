package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"slices"
	"syscall"
)

func digest(value []byte) string {
	sum := sha256.Sum256(value)
	return hex.EncodeToString(sum[:])
}

func readAuthenticated(path string, spec inputSpec) ([]byte, error) {
	fd, err := syscall.Open(path, syscall.O_RDONLY|syscall.O_CLOEXEC|syscall.O_NOFOLLOW|syscall.O_NONBLOCK, 0)
	if err != nil {
		return nil, fmt.Errorf("%s: open authenticated descriptor: %w", spec.Role, err)
	}
	file := os.NewFile(uintptr(fd), path)
	if file == nil {
		syscall.Close(fd)
		return nil, fmt.Errorf("%s: create authenticated descriptor", spec.Role)
	}
	defer file.Close()
	before, err := file.Stat()
	if err != nil {
		return nil, fmt.Errorf("%s: fstat: %w", spec.Role, err)
	}
	if !before.Mode().IsRegular() {
		return nil, fmt.Errorf("%s must be a regular non-symlink file", spec.Role)
	}
	if before.Size() != int64(spec.Size) {
		return nil, fmt.Errorf("%s size is %d, want %d", spec.Role, before.Size(), spec.Size)
	}
	value, err := io.ReadAll(io.LimitReader(file, int64(spec.Size)+1))
	if err != nil {
		return nil, fmt.Errorf("%s: read: %w", spec.Role, err)
	}
	if len(value) != spec.Size {
		return nil, fmt.Errorf("%s read %d bytes, want %d", spec.Role, len(value), spec.Size)
	}
	if got := digest(value); got != spec.SHA256 {
		return nil, fmt.Errorf("%s SHA-256 is %s, want %s", spec.Role, got, spec.SHA256)
	}
	after, err := file.Stat()
	if err != nil {
		return nil, fmt.Errorf("%s: post-read fstat: %w", spec.Role, err)
	}
	if !after.Mode().IsRegular() || after.Size() != int64(spec.Size) || !os.SameFile(before, after) {
		return nil, fmt.Errorf("%s descriptor identity, type, or size changed during read", spec.Role)
	}
	return value, nil
}

func canonicalJSON(value any) ([]byte, error) {
	var output bytes.Buffer
	encoder := json.NewEncoder(&output)
	encoder.SetEscapeHTML(false)
	if err := encoder.Encode(value); err != nil {
		return nil, err
	}
	encoded := output.Bytes()
	return append([]byte(nil), encoded[:len(encoded)-1]...), nil
}

func decodeStrictJSONValue(decoder *json.Decoder) (any, error) {
	token, err := decoder.Token()
	if err != nil {
		return nil, err
	}
	delimiter, isDelimiter := token.(json.Delim)
	if !isDelimiter {
		return token, nil
	}
	switch delimiter {
	case '{':
		object := make(map[string]any)
		for decoder.More() {
			keyToken, err := decoder.Token()
			if err != nil {
				return nil, err
			}
			key, ok := keyToken.(string)
			if !ok {
				return nil, fmt.Errorf("object key is not a string")
			}
			if _, exists := object[key]; exists {
				return nil, fmt.Errorf("duplicate JSON key %q", key)
			}
			child, err := decodeStrictJSONValue(decoder)
			if err != nil {
				return nil, err
			}
			object[key] = child
		}
		closing, err := decoder.Token()
		if err != nil || closing != json.Delim('}') {
			return nil, fmt.Errorf("malformed JSON object")
		}
		return object, nil
	case '[':
		array := make([]any, 0)
		for decoder.More() {
			child, err := decodeStrictJSONValue(decoder)
			if err != nil {
				return nil, err
			}
			array = append(array, child)
		}
		closing, err := decoder.Token()
		if err != nil || closing != json.Delim(']') {
			return nil, fmt.Errorf("malformed JSON array")
		}
		return array, nil
	default:
		return nil, fmt.Errorf("unexpected JSON delimiter %q", delimiter)
	}
}

func parseSummary(raw []byte) (map[string]any, error) {
	if len(raw) == 0 || raw[len(raw)-1] != '\n' || bytes.Contains(raw, []byte{'\r'}) {
		return nil, fmt.Errorf("summary newline encoding mismatch")
	}
	decoder := json.NewDecoder(bytes.NewReader(raw[:len(raw)-1]))
	decoder.UseNumber()
	value, err := decodeStrictJSONValue(decoder)
	if err != nil {
		return nil, fmt.Errorf("parse summary: %w", err)
	}
	var trailing any
	if err := decoder.Decode(&trailing); err != io.EOF {
		if err == nil {
			return nil, fmt.Errorf("summary has trailing JSON value")
		}
		return nil, fmt.Errorf("summary trailing data: %w", err)
	}
	document, ok := value.(map[string]any)
	if !ok {
		return nil, fmt.Errorf("summary top level is not an object")
	}
	canonical, err := canonicalJSON(document)
	if err != nil {
		return nil, err
	}
	if !bytes.Equal(append(canonical, '\n'), raw) {
		return nil, fmt.Errorf("summary is not canonical compact JSON plus LF")
	}
	if document["schema"] != schema {
		return nil, fmt.Errorf("summary schema mismatch")
	}
	semantic, ok := document["semantic"].(map[string]any)
	if !ok {
		return nil, fmt.Errorf("summary semantic object missing")
	}
	encodedSemantic, err := canonicalJSON(semantic)
	if err != nil {
		return nil, err
	}
	want := digest(append([]byte(schema+"\x00semantic\x00"), encodedSemantic...))
	integrity, ok := document["integrity"].(map[string]any)
	if !ok || integrity["semantic_sha256"] != want || integrity["classification"] != "integrity/checksums, not authentication" {
		return nil, fmt.Errorf("summary semantic integrity mismatch")
	}
	return document, nil
}

func appendU16(dst []byte, values ...uint16) []byte {
	for _, value := range values {
		dst = binary.LittleEndian.AppendUint16(dst, value)
	}
	return dst
}
func appendU32(dst []byte, values ...uint32) []byte {
	for _, value := range values {
		dst = binary.LittleEndian.AppendUint32(dst, value)
	}
	return dst
}

func canonicalPayload(terms []triple) []byte {
	ordered := append([]triple(nil), terms...)
	slices.SortFunc(ordered, compareTriple)
	data := appendU16(nil, 4, 4, 4, uint16(len(ordered)))
	for _, term := range ordered {
		data = appendU16(data, term[0], term[1], term[2])
	}
	return data
}

func orderedPayload(terms []triple) []byte {
	data := appendU16(nil, 4, 4, 4, uint16(len(terms)))
	for mode := range 3 {
		for _, term := range terms {
			data = appendU16(data, term[mode])
		}
	}
	return data
}

func compareTriple(a, b triple) int {
	for mode := range 3 {
		if a[mode] < b[mode] {
			return -1
		}
		if a[mode] > b[mode] {
			return 1
		}
	}
	return 0
}

type exactClassHash func([]byte) string

func exactClasses(values [][]byte, role string) ([]exactClass, map[string]int, error) {
	return exactClassesWithHash(values, role, func(value []byte) string { return digest(value) })
}

func exactClassesWithHash(values [][]byte, role string, hash exactClassHash) ([]exactClass, map[string]int, error) {
	byHash := make(map[string]int)
	classes := make([]exactClass, 0)
	for index, value := range values {
		bucket := hash(value)
		if slot, ok := byHash[bucket]; ok {
			if !bytes.Equal(classes[slot].value, value) {
				return nil, nil, fmt.Errorf("%s SHA-256 collision on differing exact bytes", role)
			}
			classes[slot].members = append(classes[slot].members, index)
		} else {
			byHash[bucket] = len(classes)
			classes = append(classes, exactClass{append([]byte(nil), value...), []int{index}})
		}
	}
	slices.SortFunc(classes, func(a, b exactClass) int { return bytes.Compare(a.value, b.value) })
	lookup := make(map[string]int, len(classes))
	for index := range classes {
		lookup[string(classes[index].value)] = index
	}
	return classes, lookup, nil
}

func sectionDigest(name string, value []byte) string {
	prefix := []byte(schema + "\x00section\x00" + name + "\x00")
	return digest(append(prefix, value...))
}
