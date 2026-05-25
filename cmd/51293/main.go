package main

import (
	"fmt"
	"os"
)

func main() {
	if len(os.Args) < 2 {
		fmt.Fprintf(os.Stderr, "usage: 51293 <terms|convergence> [args]\n")
		os.Exit(1)
	}
	switch os.Args[1] {
	case "terms":
		runTerms(os.Args[2:])
	case "convergence":
		runConvergence(os.Args[2:])
	case "tailbound":
		runTailbound(os.Args[2:])
	case "counting":
		runCounting(os.Args[2:])
	case "perk":
		runPerk(os.Args[2:])
	case "orbits":
		runOrbits(os.Args[2:])
	default:
		fmt.Fprintf(os.Stderr, "unknown subcommand: %s\n", os.Args[1])
		os.Exit(1)
	}
}
