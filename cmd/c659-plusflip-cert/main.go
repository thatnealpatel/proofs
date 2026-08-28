package main

import (
	"encoding/json"
	"fmt"
	"io"
	"os"
)

const usage = "Usage: c659-plusflip-cert C659_ROOT_PATH C680_ROOT_PATH\n"

func main() {
	if err := run(os.Args[1:], os.Stdout); err != nil {
		fmt.Fprintf(os.Stderr, "%s: %v\n", commandName, err)
		os.Exit(1)
	}
}

func run(args []string, output io.Writer) error {
	if len(args) == 1 && (args[0] == "-h" || args[0] == "--help") {
		return writeUsage(output)
	}
	if len(args) != 2 {
		if err := writeUsage(output); err != nil {
			return err
		}
		return fmt.Errorf("require exactly two root paths in order c659 then c680, got %d", len(args))
	}
	semantic, err := executeExperiment(args[0], args[1])
	if err != nil {
		return err
	}
	value, err := makeReport(semantic)
	if err != nil {
		return err
	}
	encoded, err := json.MarshalIndent(value, "", "  ")
	if err != nil {
		return fmt.Errorf("encode report: %w", err)
	}
	encoded = append(encoded, '\n')
	written, err := output.Write(encoded)
	if err != nil {
		return fmt.Errorf("write report: %w", err)
	}
	if written != len(encoded) {
		return fmt.Errorf("write report: %w", io.ErrShortWrite)
	}
	return nil
}

func writeUsage(output io.Writer) error {
	written, err := io.WriteString(output, usage)
	if err != nil {
		return fmt.Errorf("write usage: %w", err)
	}
	if written != len(usage) {
		return fmt.Errorf("write usage: %w", io.ErrShortWrite)
	}
	return nil
}

func makeReport(semantic semanticCertificate) (report, error) {
	encoded, err := json.Marshal(semantic)
	if err != nil {
		return report{}, fmt.Errorf("encode semantic digest input: %w", err)
	}
	digest := sha256Hex(encoded)
	if expectedSemanticSHA256 != "" && digest != expectedSemanticSHA256 {
		return report{}, fmt.Errorf("semantic SHA-256 is %s, want %s", digest, expectedSemanticSHA256)
	}
	return report{
		Envelope: envelope{
			Schema:           certificateSchema,
			DigestAlgorithm:  "SHA-256",
			SemanticEncoding: "compact encoding/json serialization of the semantic object",
			SemanticSHA256:   digest,
			ExcludedFields:   []string{"envelope", "runtime"},
		},
		Runtime: runtimeBinding{
			Measurement: "omitted",
			Reason:      "the certificate stdout is deterministic; runtime and the digest envelope are outside the semantic digest",
		},
		Semantic: semantic,
	}, nil
}
