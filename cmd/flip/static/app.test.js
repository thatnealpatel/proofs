"use strict";

const test = require("node:test");
const assert = require("node:assert/strict");
const { anchoredScale, nodeTransform, prepareActivation, state } = require("./app.js");

test("semantic zoom preserves node and self-loop display sizes", () => {
  assert.equal(nodeTransform({ position: [120, 340] }, 4), "translate(120 340) scale(0.25)");
  assert.equal(anchoredScale([120, 340], 4), "translate(120 340) scale(0.25) translate(-120 -340)");
});

test("node activation retains graph highlighting without card pinning", () => {
  const node = { kind: "node", id: "n1" };

  prepareActivation(node);

  assert.equal(state.activeItem, node);
  assert.equal("pinned" in state, false);
});

test("edge activation retains graph highlighting without card pinning", () => {
  const edge = { kind: "edge", id: "e1" };

  prepareActivation(edge);

  assert.equal(state.activeItem, edge);
  assert.equal("pinned" in state, false);
});
