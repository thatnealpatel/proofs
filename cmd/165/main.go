package main

import (
	"fmt"
	"math"
	rand "math/rand/v2" // why need 'rand' (gotip on 2026may23)
)

func main() {
	const trials = 1000

	fmt.Printf("%6s %6s %10s\n", "n", "α_min", "c_est")
	for n := 20; n <= 200; n += 20 {
		minAlpha := n
		for range trials {
			adj := triangleFree(n)
			if a := independence(adj); a < minAlpha {
				minAlpha = a
			}
		}
		k := float64(minAlpha)
		c := float64(n) * math.Log(k) / (k * k)
		fmt.Printf("%6d %6d %10.4f\n", n, minAlpha, c)
	}
}

func triangleFree(n int) [][]bool {
	adj := make([][]bool, n)
	for i := range adj {
		adj[i] = make([]bool, n)
	}
	edges := make([][2]int, 0, n*(n-1)/2)
	for i := range n {
		for j := i + 1; j < n; j++ {
			edges = append(edges, [2]int{i, j})
		}
	}
	rand.Shuffle(len(edges), func(i, j int) {
		edges[i], edges[j] = edges[j], edges[i]
	})
	for _, e := range edges {
		u, v := e[0], e[1]
		hasTriangle := false
		for w := range n {
			if adj[u][w] && adj[v][w] {
				hasTriangle = true
				break
			}
		}
		if !hasTriangle {
			adj[u][v] = true
			adj[v][u] = true
		}
	}
	return adj
}

func independence(adj [][]bool) int {
	n := len(adj)
	removed := make([]bool, n)
	count := 0
	for {
		best, bestDeg := -1, n+1
		for v := range n {
			if removed[v] {
				continue
			}
			deg := 0
			for w := range n {
				if !removed[w] && adj[v][w] {
					deg++
				}
			}
			if deg < bestDeg {
				best, bestDeg = v, deg
			}
		}
		if best == -1 {
			break
		}
		count++
		for w := range n {
			if adj[best][w] {
				removed[w] = true
			}
		}
		removed[best] = true
	}
	return count
}
