"use strict";

const svgNS = "http://www.w3.org/2000/svg";
const branchRows = [70, 135, 200, 265, 500, 565, 630, 695];
const state = {
  graph: null,
  nodes: new Map(),
  edges: new Map(),
  current: null,
  pinned: null,
  pinSource: null,
  pathIndex: 0,
  hideTimer: null
};

function element(name, className, text) {
  const node = document.createElement(name);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

function svgElement(name, attributes = {}) {
  const node = document.createElementNS(svgNS, name);
  for (const [key, value] of Object.entries(attributes)) node.setAttribute(key, value);
  return node;
}

function nodePosition(node, branchIndex) {
  const x = 92 + node.anchor * 150;
  if (node.pathIndex !== null) return [x, node.rank === 23 ? 730 : 382];
  return [x + (branchIndex % 2 ? 30 : -30), branchRows[branchIndex]];
}

function edgePath(from, to) {
  const [x1, y1] = from.position;
  const [x2, y2] = to.position;
  if (Math.abs(x2 - x1) < 4) {
    const bend = x1 + (y2 > y1 ? 38 : -38);
    return `M ${x1} ${y1} Q ${bend} ${(y1 + y2) / 2} ${x2} ${y2}`;
  }
  const middle = (x1 + x2) / 2;
  return `M ${x1} ${y1} C ${middle} ${y1}, ${middle} ${y2}, ${x2} ${y2}`;
}

function descriptor(kind, value) {
  return { kind, value, id: value.id };
}

function sameItem(left, right) {
  return Boolean(left && right && left.kind === right.kind && left.id === right.id);
}

function cancelHide() {
  if (state.hideTimer !== null) window.clearTimeout(state.hideTimer);
  state.hideTimer = null;
}

function scheduleRestore() {
  cancelHide();
  if (state.pinned) return;
  state.hideTimer = window.setTimeout(() => {
    state.hideTimer = null;
    closeInspector(false);
  }, 80);
}

function pointerPosition(event) {
  return { x: event.clientX, y: event.clientY };
}

function targetPosition(target) {
  if (!target) return { x: window.innerWidth / 2, y: window.innerHeight / 2 };
  const bounds = target.getBoundingClientRect();
  return { x: bounds.left + bounds.width / 2, y: bounds.top + bounds.height / 2 };
}

function itemTarget(item) {
  const className = item.kind === "node" ? "graph-node" : "graph-edge";
  return document.querySelector(`.${className}[data-id="${item.id}"]`);
}

function positionInspector(position) {
  const inspector = document.querySelector("#inspector");
  const gap = 16;
  const margin = 10;
  const bounds = inspector.getBoundingClientRect();
  let left = position.x + gap;
  let top = position.y + gap;
  if (left + bounds.width > window.innerWidth - margin) left = position.x - gap - bounds.width;
  if (top + bounds.height > window.innerHeight - margin) top = position.y - gap - bounds.height;
  left = Math.max(margin, Math.min(left, window.innerWidth - bounds.width - margin));
  top = Math.max(margin, Math.min(top, window.innerHeight - bounds.height - margin));
  inspector.style.left = `${Math.round(left)}px`;
  inspector.style.top = `${Math.round(top)}px`;
}

function inspect(item, options = {}) {
  cancelHide();
  if (options.pin) {
    state.pinned = item;
    state.pinSource = options.source || null;
    if (item.kind === "node" && item.value.pathIndex !== null) state.pathIndex = item.value.pathIndex;
    if (item.kind === "edge") {
      const destination = state.nodes.get(item.value.to);
      if (item.value.onPath && destination.pathIndex !== null) state.pathIndex = destination.pathIndex;
    }
  } else if (state.pinned && !sameItem(state.pinned, item)) {
    return;
  }
  state.current = item;
  if (item.kind === "node") renderNode(item.value);
  else renderEdge(item.value);
  const inspector = document.querySelector("#inspector");
  inspector.hidden = false;
  inspector.classList.toggle("pinned", Boolean(state.pinned));
  positionInspector(options.point || targetPosition(options.source || itemTarget(item)));
  updateSelection();
  if (options.center) centerNode(item.kind === "node" ? item.value : state.nodes.get(item.value.to));
}

function closeInspector(restoreFocus = false) {
  cancelHide();
  const source = state.pinSource;
  state.pinned = null;
  state.pinSource = null;
  state.current = null;
  document.querySelector("#inspector").hidden = true;
  updateSelection();
  if (restoreFocus && source?.isConnected) source.focus();
}

function bindInspectorTarget(target, item) {
  target.addEventListener("pointerenter", event => inspect(item, { point: pointerPosition(event) }));
  target.addEventListener("pointermove", event => {
    if (!state.pinned && sameItem(state.current, item)) positionInspector(pointerPosition(event));
  });
  target.addEventListener("pointerleave", scheduleRestore);
  target.addEventListener("focus", () => inspect(item, { point: targetPosition(target) }));
  target.addEventListener("blur", scheduleRestore);
  target.addEventListener("click", event => {
    event.stopPropagation();
    inspect(item, { pin: true, source: target, point: pointerPosition(event) });
  });
  target.addEventListener("keydown", event => {
    if (event.key === "Enter" || event.key === " ") {
      event.preventDefault();
      inspect(item, { pin: true, source: target, point: targetPosition(target) });
    }
  });
}

function formatModes(counts) {
  return ["A", "B", "C"].map(mode => `${mode}: ${counts[mode] || 0}`).join(" · ");
}

function factorName(kind, index) {
  return `${kind}${Math.floor(index / 3)}${index % 3}`;
}

function formatFactor(kind, values) {
  const terms = [];
  values.forEach((coefficient, index) => {
    if (coefficient === "0") return;
    const variable = factorName(kind, index);
    if (coefficient === "1") terms.push(`+ ${variable}`);
    else if (coefficient === "-1") terms.push(`− ${variable}`);
    else if (coefficient.startsWith("-")) terms.push(`− ${coefficient.slice(1)}${variable}`);
    else terms.push(`+ ${coefficient}${variable}`);
  });
  return terms.length ? terms.join(" ").replace(/^\+ /, "") : "0";
}

function termCard(term, sharedMode) {
  const card = element("div", "term-card");
  card.append(element("div", "coefficient", `scalar ${term.coefficient}`));
  for (const mode of ["A", "B", "C"]) {
    const row = element("div", `factor${mode === sharedMode ? " shared-factor" : ""}`);
    row.append(element("strong", null, mode), element("code", null, formatFactor(mode, term[mode])));
    if (mode === sharedMode) row.append(element("span", "held", "held fixed"));
    card.append(row);
  }
  return card;
}

function metric(label, value) {
  const box = element("div", "metric");
  box.append(element("span", null, label), element("strong", null, String(value)));
  return box;
}

function inspectorHeading(kind, title) {
  const content = document.querySelector("#inspector-content");
  content.replaceChildren();
  content.append(element("p", `type ${kind.replaceAll(" ", "-")}`, kind), element("h2", null, title));
  return content;
}

function renderNode(node) {
  const content = inspectorHeading(node.pathIndex === null ? "sampled neighbor" : "recorded state", node.name);
  content.append(element("p", "decomposition-callout", `Complete ${node.rank}-term decomposition of the 3×3 matrix multiplication tensor`));
  content.append(element("span", "badge", "exact on all 729 coordinates"));
  content.append(element("p", "hash", `state ${node.id}`));
  const metrics = element("div", "metrics");
  metrics.append(
    metric("rank-one terms", node.rank),
    metric("movable pairs", node.movablePairs),
    metric("reductions", node.reductions),
    metric("largest component", Math.max(...node.components))
  );
  content.append(metrics, element("h3", null, "Flip opportunities by shared factor"));
  content.append(element("p", "identity", formatModes(node.movableByMode)));
  const incident = state.graph.edges.filter(edge => edge.from === node.id || edge.to === node.id);
  const sampleStatus = node.pathIndex === null
    ? `Sampled off-path state · ${incident.length} displayed connection${incident.length === 1 ? "" : "s"}.`
    : `Recorded path state ${node.pathIndex + 1} of ${state.graph.path.length} · ${incident.length} displayed connection${incident.length === 1 ? "" : "s"}.`;
  content.append(element("p", "sample-status", sampleStatus));
}

function basisDiagram(columns) {
  const wrap = element("div", "basis-block");
  wrap.append(element("span", "basis-label", "2×2 basis · columns u, v"));
  const matrix = element("div", "basis-matrix");
  matrix.append(
    element("code", null, columns[0][0]), element("code", null, columns[1][0]),
    element("code", null, columns[0][1]), element("code", null, columns[1][1])
  );
  wrap.append(matrix);
  return wrap;
}

function termGroup(label, terms, sharedMode, className) {
  const group = element("section", `term-group ${className}`);
  group.append(element("h3", null, label));
  for (const term of terms) group.append(termCard(term, sharedMode));
  return group;
}

function renderDelta(content, edge) {
  const comparison = element("div", "delta-comparison");
  comparison.append(
    termGroup(`Before · remove ${edge.removed.length}`, edge.removed, edge.type === "flip" ? edge.mode : null, "before"),
    element("div", "delta-arrow", "→"),
    termGroup(`After · add ${edge.added.length}`, edge.added, edge.type === "flip" ? edge.mode : null, "after")
  );
  content.append(comparison);
}

function renderEdge(edge) {
  const from = state.nodes.get(edge.from);
  const to = state.nodes.get(edge.to);
  const title = edge.type === "flip" ? `${from.name} ↔ ${to.name}` : `${from.name} → ${to.name}`;
  const content = inspectorHeading(edge.onPath ? `recorded ${edge.type}` : `sampled ${edge.type}`, title);

  if (edge.type === "flip") {
    content.append(element("p", "mechanic-summary", `Reversible, length-preserving move · ${from.rank} terms ↔ ${to.rank} terms`));
    const explanation = element("p", "identity");
    explanation.append("The two terms share their ", element("strong", "mode-chip", `${edge.mode} factor`), ". Hold that factor fixed; change the other two modes with a basis / inverse-basis pair.");
    content.append(explanation);
    if (edge.basisColumns) content.append(basisDiagram(edge.basisColumns));
  } else {
    const isSplit = edge.type === "split";
    content.append(element("p", `mechanic-summary ${edge.type}`,
      isSplit
        ? `Split: one rank-one term becomes two; length ${from.rank} → ${to.rank}.`
        : `Reduction: two compatible terms contract to one; length ${from.rank} → ${to.rank}.`));
    content.append(element("p", "sample-status", isSplit
      ? "The local tensor contribution is unchanged while the decomposition gains one term. Reversing this move is the displayed reduction."
      : "The local tensor contribution is unchanged while the decomposition loses one term. Reversing this move is a split."));
  }

  if (Array.isArray(edge.removed) && Array.isArray(edge.added)) {
    renderDelta(content, edge);
  } else {
    content.append(element("p", "unavailable", "Local factor delta unavailable for this sampled cross-link. Only its endpoints, shared mode, and 2×2 basis were retained."));
  }
  content.append(element("p", "edge-status", edge.onPath ? "Recorded construction edge · exact local replacement data." : "Sampled neighborhood cross-link."));
}

function updateSelection() {
  if (!state.graph) return;
  const branches = document.querySelector("#branches").checked;
  const selected = state.pinned;
  document.querySelectorAll(".graph-node").forEach(group => {
    const node = state.nodes.get(group.dataset.id);
    group.classList.toggle("hidden", !branches && node.pathIndex === null);
    group.classList.toggle("selected", selected?.kind === "node" && selected.id === node.id);
    group.classList.remove("adjacent");
  });
  document.querySelectorAll(".graph-edge").forEach(path => {
    const edge = state.edges.get(path.dataset.id);
    path.classList.toggle("hidden", !branches && !edge.onPath && edge.type !== "reduction");
    path.classList.toggle("selected", selected?.kind === "edge" && selected.id === edge.id);
    path.classList.remove("adjacent");
  });
  if (selected?.kind === "node") {
    const id = selected.id;
    for (const edge of state.graph.edges) {
      if (edge.from !== id && edge.to !== id) continue;
      document.querySelector(`.graph-edge[data-id="${edge.id}"]`)?.classList.add("adjacent");
      const other = edge.from === id ? edge.to : edge.from;
      document.querySelector(`.graph-node[data-id="${other}"]`)?.classList.add("adjacent");
    }
  }
  document.querySelector("#progress").textContent = `path ${state.pathIndex + 1}/${state.graph.path.length}`;
  document.querySelector("#previous").disabled = state.pathIndex === 0;
  document.querySelector("#next").disabled = state.pathIndex === state.graph.path.length - 1;
}

function centerNode(node) {
  const viewport = document.querySelector(".viewport");
  viewport.scrollTo({ left: Math.max(0, node.position[0] - viewport.clientWidth / 2), behavior: "smooth" });
}

function showPathStep(index) {
  state.pathIndex = Math.max(0, Math.min(state.graph.path.length - 1, index));
  const node = state.nodes.get(state.graph.path[state.pathIndex]);
  if (state.pathIndex === 0) {
    inspect(descriptor("node", node), { pin: true, center: true });
    return;
  }
  const previous = state.graph.path[state.pathIndex - 1];
  const edge = state.graph.edges.find(value => value.onPath && value.from === previous && value.to === node.id);
  inspect(edge ? descriptor("edge", edge) : descriptor("node", node), { pin: true, center: true });
}

function draw(graph) {
  state.graph = graph;
  state.nodes = new Map(graph.nodes.map(node => [node.id, node]));
  state.edges = new Map(graph.edges.map(edge => [edge.id, edge]));
  const perAnchor = new Map();
  for (const node of graph.nodes) {
    if (node.pathIndex !== null) continue;
    const siblings = perAnchor.get(node.anchor) || [];
    siblings.push(node);
    perAnchor.set(node.anchor, siblings);
  }
  for (const siblings of perAnchor.values()) siblings.sort((a, b) => a.id.localeCompare(b.id));
  for (const node of graph.nodes) {
    const index = node.pathIndex === null ? perAnchor.get(node.anchor).indexOf(node) : 0;
    node.position = nodePosition(node, index);
  }

  const svg = document.querySelector("#graph");
  const bands = svgElement("g", { class: "bands" });
  bands.append(
    svgElement("line", { x1: 28, y1: 382, x2: 1532, y2: 382 }),
    svgElement("line", { x1: 28, y1: 730, x2: 1532, y2: 730 })
  );
  const length24 = svgElement("text", { x: 30, y: 364 }); length24.textContent = "length 24";
  const length23 = svgElement("text", { x: 30, y: 712 }); length23.textContent = "length 23";
  bands.append(length24, length23);
  svg.append(bands);

  const edgeLayer = svgElement("g", { class: "edges" });
  for (const edge of graph.edges) {
    const from = state.nodes.get(edge.from);
    const to = state.nodes.get(edge.to);
    const path = svgElement("path", {
      d: edgePath(from, to),
      class: `graph-edge ${edge.type}${edge.onPath ? " on-path" : ""}`,
      "data-id": edge.id,
      tabindex: "0",
      role: "button",
      "aria-label": `${edge.type} from ${from.name} to ${to.name}; focus to inspect, press Enter to pin`
    });
    bindInspectorTarget(path, descriptor("edge", edge));
    edgeLayer.append(path);
  }
  svg.append(edgeLayer);

  const nodeLayer = svgElement("g", { class: "nodes" });
  for (const node of graph.nodes) {
    const [x, y] = node.position;
    const group = svgElement("g", {
      class: `graph-node ${node.pathIndex === null ? "branch" : "path-node"} length-${node.rank}`,
      transform: `translate(${x} ${y})`,
      "data-id": node.id,
      tabindex: "0",
      role: "button",
      "aria-label": `${node.name}, complete length ${node.rank} decomposition; focus to inspect, press Enter to pin`
    });
    group.append(svgElement("circle", { r: node.pathIndex === null ? 9 : 17 }));
    if (node.pathIndex !== null) {
      const number = svgElement("text", { y: 5 }); number.textContent = node.pathIndex;
      const label = svgElement("text", { y: node.rank === 23 ? 34 : -28, class: "node-label" }); label.textContent = node.name;
      group.append(number, label);
    }
    const title = svgElement("title");
    title.textContent = `${node.name}: complete length ${node.rank} decomposition, ${node.movablePairs} movable pairs, ${node.reductions} reductions`;
    group.append(title);
    bindInspectorTarget(group, descriptor("node", node));
    nodeLayer.append(group);
  }
  svg.append(nodeLayer);

  document.querySelector("#scope").textContent = graph.scope;
  document.querySelector("#provenance").textContent = graph.provenance;
  document.querySelector("#previous").addEventListener("click", () => showPathStep(state.pathIndex - 1));
  document.querySelector("#next").addEventListener("click", () => showPathStep(state.pathIndex + 1));
  document.querySelector("#reset").addEventListener("click", () => {
    document.querySelector("#branches").checked = true;
    showPathStep(0);
    document.querySelector(".viewport").scrollTo({ left: 0, behavior: "smooth" });
  });
  document.querySelector("#branches").addEventListener("change", updateSelection);
  centerNode(state.nodes.get(graph.path[0]));
  updateSelection();
}

const inspector = document.querySelector("#inspector");
inspector.addEventListener("pointerenter", cancelHide);
inspector.addEventListener("pointerleave", scheduleRestore);
inspector.addEventListener("focusin", cancelHide);
inspector.addEventListener("focusout", scheduleRestore);
document.querySelector("#inspector-close").addEventListener("click", () => closeInspector(true));
document.addEventListener("keydown", event => {
  if (event.key === "Escape" && !inspector.hidden) {
    event.preventDefault();
    closeInspector(true);
  }
});

fetch("/api/graph")
  .then(response => {
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    return response.json();
  })
  .then(draw)
  .catch(error => {
    document.querySelector("#scope").textContent = `Could not load graph: ${error.message}`;
  });
