package main

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"syscall"
)

func digest(value []byte) string {
	sum := sha256.Sum256(value)
	return hex.EncodeToString(sum[:])
}

func domainDigest(label string, value []byte) string {
	prefix := []byte(outputSchema + "\x00stream\x00" + label + "\x00")
	return digest(append(prefix, value...))
}

func readAuthenticated(path string, spec inputSpec) (value []byte, returnErr error) {
	fd, err := syscall.Open(path, syscall.O_RDONLY|syscall.O_CLOEXEC|syscall.O_NOFOLLOW|syscall.O_NONBLOCK, 0)
	if err != nil {
		return nil, fmt.Errorf("%s: open authenticated descriptor: %w", spec.Role, err)
	}
	file := os.NewFile(uintptr(fd), path)
	if file == nil {
		if closeErr := syscall.Close(fd); closeErr != nil {
			return nil, fmt.Errorf("%s: create authenticated descriptor and close failed: %w", spec.Role, closeErr)
		}
		return nil, fmt.Errorf("%s: create authenticated descriptor", spec.Role)
	}
	defer func() {
		if err := file.Close(); err != nil && returnErr == nil {
			value = nil
			returnErr = fmt.Errorf("%s: close authenticated descriptor: %w", spec.Role, err)
		}
	}()
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
	value, err = io.ReadAll(io.LimitReader(file, int64(spec.Size)+1))
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

func writeAll(writer io.Writer, value []byte) error {
	written, err := writer.Write(value)
	if err != nil {
		return err
	}
	if written != len(value) {
		return io.ErrShortWrite
	}
	return nil
}
