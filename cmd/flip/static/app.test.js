"use strict";

const test = require("node:test");
const assert = require("node:assert/strict");
const {
  activeNeighborhood,
  anchoredScale,
  clearActivation,
  hasActivation,
  nodeTransform,
  prepareActivation,
  state
} = require("./app.js");

test("semantic zoom preserves node and self-loop display sizes", () => {
  assert.equal(nodeTransform({ position: [120, 340] }, 4), "translate(120 340) scale(0.25)");
  assert.equal(anchoredScale([120, 340], 4), "translate(120 340) scale(0.25) translate(-120 -340)");
});

test("node activations accumulate and toggle until cleared", () => {
  clearActivation();

  prepareActivation({ kind: "node", id: "n1" });
  prepareActivation({ kind: "node", id: "n2" });

  assert.deepEqual([...state.activeNodes], ["n1", "n2"]);
  assert.equal(hasActivation(), true);

  const neighborhood = activeNeighborhood([
    { id: "e12", from: "n1", to: "n2" },
    { id: "e13", from: "n1", to: "n3" },
    { id: "e24", from: "n2", to: "n4" },
    { id: "e45", from: "n4", to: "n5" }
  ]);
  assert.deepEqual([...neighborhood.nodes], ["n2", "n1", "n3", "n4"]);
  assert.deepEqual([...neighborhood.edges], ["e12", "e13", "e24"]);

  prepareActivation({ kind: "node", id: "n1" });
  assert.deepEqual([...state.activeNodes], ["n2"]);
  const remaining = activeNeighborhood([
    { id: "e12", from: "n1", to: "n2" },
    { id: "e13", from: "n1", to: "n3" },
    { id: "e24", from: "n2", to: "n4" }
  ]);
  assert.deepEqual([...remaining.nodes], ["n1", "n4"]);
  assert.deepEqual([...remaining.edges], ["e12", "e24"]);

  clearActivation();
  assert.equal(state.activeNodes.size, 0);
  assert.equal(hasActivation(), false);
});

test("edge activation retains graph highlighting without card pinning", () => {
  clearActivation();
  prepareActivation({ kind: "edge", id: "e1" });

  assert.deepEqual([...state.activeEdges], ["e1"]);
  assert.equal("pinned" in state, false);

  prepareActivation({ kind: "edge", id: "e1" });
  assert.equal(state.activeEdges.size, 0);
});
