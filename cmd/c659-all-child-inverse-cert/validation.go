package main

import (
	"bytes"
	"fmt"
)

type regenerationDependencies struct {
	rootExact          func([]triple, tensorBits) error
	plusConstructor    func(triple, triple, [3]int) ([3]triple, error)
	forwardExact       func([3]triple, [2]triple, []triple) error
	bucketOccurrence   func(int, int, int, triple) error
	inverseEquations   func([3]triple, [2]triple, [3]triple, uint16) bool
	inverseConstructor func([3]triple, [3]int, int) ([2]triple, error)
	localReplay        func([2]triple, [3]triple, [3]triple) error
	scatterReplay      func([]triple, [3]triple, []byte) error
	parentExact        func([]triple, tensorBits) error
	parentClassBrent   func([]triple) error
}

func productionRegenerationDependencies() regenerationDependencies {
	return regenerationDependencies{
		rootExact: func(root []triple, target tensorBits) error {
			if err := validateExactScheme(root, true); err != nil {
				return err
			}
			if tensorSum(root) != target {
				return fmt.Errorf("tensor mismatch")
			}
			return nil
		},
		plusConstructor: exactPlusConstructor,
		forwardExact: func(outputs [3]triple, sources [2]triple, terms []triple) error {
			if tensorSum(outputs[:]) != tensorSum(sources[:]) {
				return fmt.Errorf("local tensor identity failed")
			}
			if !validTerms(terms) {
				return fmt.Errorf("child nonzero/distinct failed")
			}
			return nil
		},
		bucketOccurrence: func(int, int, int, triple) error { return nil },
		inverseEquations: func(outputs [3]triple, _ [2]triple, replay [3]triple, mask uint16) bool {
			return mask == 511 && replay == outputs
		},
		inverseConstructor: exactInverseConstructor,
		localReplay: func(sources [2]triple, replay, outputs [3]triple) error {
			if replay != outputs || tensorSum(sources[:]) != tensorSum(outputs[:]) {
				return fmt.Errorf("local tensor replay failed")
			}
			return nil
		},
		scatterReplay: func(survivors []triple, replay [3]triple, child []byte) error {
			if !bytes.Equal(canonicalPayload(append(append([]triple(nil), survivors...), replay[:]...)), child) {
				return fmt.Errorf("scatter bytes differ")
			}
			return nil
		},
		parentExact: func(parent []triple, target tensorBits) error {
			if len(parent) != 47 || !validTerms(parent) || tensorSum(parent) != target {
				return fmt.Errorf("parent tensor/nonzero/distinct failed")
			}
			return nil
		},
		parentClassBrent: func(parent []triple) error { return validateExactScheme(parent, true) },
	}
}

type regenerationGates struct {
	dependencies regenerationDependencies
	counts       validationCounts
}

func (g *regenerationGates) validateRoot(root []triple, target tensorBits) error {
	g.counts.rootBrent++
	return g.dependencies.rootExact(root, target)
}

func (g *regenerationGates) constructPlus(first, second triple, positions [3]int) ([3]triple, error) {
	g.counts.plusConstructor++
	return g.dependencies.plusConstructor(first, second, positions)
}

func (g *regenerationGates) validateForward(outputs [3]triple, sources [2]triple, terms []triple) error {
	g.counts.forwardExact++
	return g.dependencies.forwardExact(outputs, sources, terms)
}

func (g *regenerationGates) observeBucket(child, mode, color int, term triple) error {
	g.counts.bucketOccurrences++
	return g.dependencies.bucketOccurrence(child, mode, color, term)
}

func (g *regenerationGates) validateEquations(outputs [3]triple, sources [2]triple, replay [3]triple, mask uint16) bool {
	if !g.dependencies.inverseEquations(outputs, sources, replay, mask) {
		return false
	}
	g.counts.equationHits++
	return true
}

func (g *regenerationGates) constructInverse(outputs [3]triple, positions [3]int, variant int, residualPass bool) ([2]triple, error) {
	g.counts.inverseConstructor++
	if !residualPass {
		g.counts.inverseConstructorResidualFailure++
	}
	return g.dependencies.inverseConstructor(outputs, positions, variant)
}

func (g *regenerationGates) validateLocal(sources [2]triple, replay, outputs [3]triple) error {
	if err := g.dependencies.localReplay(sources, replay, outputs); err != nil {
		return err
	}
	g.counts.localReplay++
	return nil
}

func (g *regenerationGates) validateScatter(survivors []triple, replay [3]triple, child []byte) error {
	if err := g.dependencies.scatterReplay(survivors, replay, child); err != nil {
		return err
	}
	g.counts.scatterReplay++
	return nil
}

func (g *regenerationGates) validateParent(parent []triple, target tensorBits) error {
	if err := g.dependencies.parentExact(parent, target); err != nil {
		return err
	}
	g.counts.parentExact++
	return nil
}

func (g *regenerationGates) validateParentClass(parent []triple) error {
	g.counts.parentClassBrent++
	return g.dependencies.parentClassBrent(parent)
}
