"use strict";

const test = require("node:test");
const assert = require("node:assert/strict");
const { activationMode, prepareActivation, state } = require("./app.js");

test("node activation highlights without retaining card pinning", () => {
  const node = { kind: "node", id: "n1" };
  state.pinned = { kind: "edge", id: "e1" };
  state.pinSource = {};

  assert.equal(prepareActivation(node), "highlight");
  assert.equal(state.activeNode, node);
  assert.equal(state.pinned, null);
  assert.equal(state.pinSource, null);
});

test("edge activation retains pinning policy and supersedes node highlighting", () => {
  state.activeNode = { kind: "node", id: "n1" };

  assert.equal(activationMode({ kind: "edge" }), "pin");
  assert.equal(prepareActivation({ kind: "edge", id: "e1" }), "pin");
  assert.equal(state.activeNode, null);
});
