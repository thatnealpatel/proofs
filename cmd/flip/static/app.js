"use strict";

const svgNS = "http://www.w3.org/2000/svg";
const graphFrame = Object.freeze({ x: 0, y: 0, width: 1560, height: 780 });
const minZoom = 1;
const maxZoom = 8;
const branchRows = [70, 135, 200, 265, 500, 565, 630, 695];
const views = {
  m2: {
    key: "m2",
    kind: "orbit",
    url: "/graph-222.json",
    documentTitle: "M₂ orbit flip graph",
    eyebrow: "EXACT 2×2 MATRIX MULTIPLICATION · F₂ · SYMMETRY ORBITS",
    pageTitle: "The complete small case",
    graphTitle: "The schoolbook component, generated from 272 representatives",
    graphDescription: "Each point is a symmetry orbit of complete presentations. Hover or focus a node or transition to inspect it. Activate nodes to toggle their incident edges and neighboring nodes in the combined highlighting; Escape clears the set. Cards remain hover or focus only. Scroll to zoom and drag empty space to pan.",
    readingTitle: "What this complete component says",
    readingBody: "The generated data contains all 272 orbits and 1,183 transition edges in the rank-at-most-8 component containing schoolbook multiplication over F₂. The gold route is a deterministically chosen shortest path of eight moves to the unique length-7 representative, Strassen’s orbit.",
    footer: "Complete schoolbook component over F₂. One further length-8 orbit is isolated in the published data; no claim is made that these are every component.",
    ariaLabel: "Complete orbit flip graph component for two by two matrix multiplication over F2",
    alternativesLabel: "all orbits",
    legend: [["path", "shortest schoolbook–Strassen path"], ["flip", "same-length flip"], ["reduction", "length-reducing edge"], ["loop", "flip within one orbit"]]
  },
  m3: {
    key: "m3",
    kind: "sample",
    url: "/api/graph",
    size: 3,
    coordinateCount: 729,
    lowerBound: 19,
    xStep: 150,
    rankY: { 24: 382, 23: 730 },
    bands: [{ rank: 24, y: 382 }, { rank: 23, y: 730 }],
    documentTitle: "M₃ exact decomposition landscape",
    eyebrow: "EXACT 3×3 MATRIX MULTIPLICATION · RATIONAL COEFFICIENTS",
    pageTitle: "A real split-and-flip path, with its local neighborhood",
    graphTitle: "Laderman length 23 → split → eight flips",
    graphDescription: "Path nodes are gold. Hover or focus a node or edge to inspect it. Activate nodes to toggle their incident edges and neighboring nodes in the combined highlighting; Escape clears the set. Cards remain hover or focus only. Scroll to zoom and drag empty space to pan.",
    readingTitle: "What this finite sample is",
    readingBody: "Every vertex is a complete presentation of the same tensor. Same-length flip edges are invertible. Reversing the gold path applies eight inverse flips and then the green reduction back to Laderman’s length-23 presentation.",
    footer: "Finite curated M₃ sample only: not an exhaustive search, an optimality proof, or a nonexistence result.",
    ariaLabel: "Exact sampled neighborhood around a Laderman split-and-flip path",
    alternativesLabel: "alternatives",
    legend: [["path", "recorded path"], ["flip", "sampled flip"], ["split", "split / +1"], ["reduction", "reduction / −1"]]
  }
};
const state = {
  view: views.m2,
  graph: null,
  nodes: new Map(),
  edges: new Map(),
  current: null,
  activeNodes: new Set(),
  activeEdges: new Set(),
  pathIndex: 0,
  hideTimer: null,
  loadToken: 0,
  camera: { ...graphFrame },
  drag: null
};

function element(name, className, text) {
  const node = document.createElement(name);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

function svgElement(name, attributes = {}) {
  const node = document.createElementNS(svgNS, name);
  for (const [key, value] of Object.entries(attributes)) {
    if (value != null) node.setAttribute(key, value);
  }
  return node;
}

function cameraZoom() {
  return graphFrame.width / state.camera.width;
}

function clampCamera(camera) {
  const width = Math.min(graphFrame.width, camera.width);
  const height = Math.min(graphFrame.height, camera.height);
  return {
    x: Math.max(graphFrame.x, Math.min(camera.x, graphFrame.width - width)),
    y: Math.max(graphFrame.y, Math.min(camera.y, graphFrame.height - height)),
    width,
    height
  };
}

function applyCamera() {
  const { x, y, width, height } = state.camera;
  document.querySelector("#graph").setAttribute("viewBox", `${x} ${y} ${width} ${height}`);
  const zoom = cameraZoom();
  document.querySelector("#zoom-level").textContent = `${Math.round(zoom * 100)}%`;
  document.querySelector("#zoom-out").disabled = zoom <= minZoom;
  document.querySelector("#zoom-in").disabled = zoom >= maxZoom;
}

function setCamera(camera) {
  state.camera = clampCamera(camera);
  applyCamera();
}

function nodeTransform(node, zoom = cameraZoom()) {
  return `translate(${node.position[0]} ${node.position[1]}) scale(${1 / zoom})`;
}

function anchoredScale(position, zoom = cameraZoom()) {
  const [x, y] = position;
  return `translate(${x} ${y}) scale(${1 / zoom}) translate(${-x} ${-y})`;
}

function applySemanticZoom() {
  const zoom = cameraZoom();
  document.querySelectorAll(".graph-node").forEach(group => {
    const node = state.nodes.get(group.dataset.id);
    if (node) group.setAttribute("transform", nodeTransform(node, zoom));
  });
  document.querySelectorAll(".graph-edge.self-loop").forEach(path => {
    const edge = state.edges.get(path.dataset.id);
    const node = edge && state.nodes.get(edge.from);
    if (node) path.setAttribute("transform", anchoredScale(node.position, zoom));
  });
}

function setZoom(zoom, focus = null) {
  zoom = Math.max(minZoom, Math.min(maxZoom, zoom));
  const current = state.camera;
  const point = focus || { x: current.x + current.width / 2, y: current.y + current.height / 2 };
  const xRatio = (point.x - current.x) / current.width;
  const yRatio = (point.y - current.y) / current.height;
  const width = graphFrame.width / zoom;
  const height = graphFrame.height / zoom;
  setCamera({
    x: point.x - xRatio * width,
    y: point.y - yRatio * height,
    width,
    height
  });
  applySemanticZoom();
}

function resetCamera() {
  setCamera({ ...graphFrame });
  applySemanticZoom();
}

function clientGraphPoint(event) {
  const svg = document.querySelector("#graph");
  const point = svg.createSVGPoint();
  point.x = event.clientX;
  point.y = event.clientY;
  return point.matrixTransform(svg.getScreenCTM().inverse());
}

function startPan(event) {
  const svg = document.querySelector("#graph");
  if (event.button !== 0 || event.target !== svg) return;
  const matrix = svg.getScreenCTM();
  state.drag = {
    pointerId: event.pointerId,
    clientX: event.clientX,
    clientY: event.clientY,
    camera: { ...state.camera },
    scale: Math.hypot(matrix.a, matrix.b)
  };
  svg.setPointerCapture(event.pointerId);
  svg.classList.add("panning");
  event.preventDefault();
}

function movePan(event) {
  if (!state.drag || event.pointerId !== state.drag.pointerId) return;
  const dx = (event.clientX - state.drag.clientX) / state.drag.scale;
  const dy = (event.clientY - state.drag.clientY) / state.drag.scale;
  setCamera({ ...state.drag.camera, x: state.drag.camera.x - dx, y: state.drag.camera.y - dy });
}

function stopPan(event) {
  if (!state.drag || event.pointerId !== state.drag.pointerId) return;
  const svg = document.querySelector("#graph");
  if (svg.hasPointerCapture(event.pointerId)) svg.releasePointerCapture(event.pointerId);
  state.drag = null;
  svg.classList.remove("panning");
}

function wheelZoom(event) {
  if (!state.graph) return;
  event.preventDefault();
  setZoom(cameraZoom() * Math.exp(-event.deltaY * 0.0015), clientGraphPoint(event));
}

function nodePosition(node, branchIndex) {
  if (state.view.kind === "orbit") return [node.x * 1560, node.y * 780];
  const x = 92 + node.anchor * state.view.xStep;
  if (node.pathIndex != null) return [x, state.view.rankY[node.rank]];
  return [x + (branchIndex % 2 ? 30 : -30), branchRows[branchIndex]];
}

function edgePath(from, to) {
  const [x1, y1] = from.position;
  const [x2, y2] = to.position;
  if (from.id === to.id) {
    return `M ${x1 - 4} ${y1 - 4} C ${x1 - 24} ${y1 - 34}, ${x1 + 24} ${y1 - 34}, ${x1 + 4} ${y1 - 4}`;
  }
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
  state.hideTimer = window.setTimeout(() => {
    state.hideTimer = null;
    closeInspector();
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

function retainActivation(item) {
  const active = item.kind === "node" ? state.activeNodes : state.activeEdges;
  active.add(item.id);
}

function prepareActivation(item) {
  const active = item.kind === "node" ? state.activeNodes : state.activeEdges;
  if (active.has(item.id)) active.delete(item.id);
  else active.add(item.id);
}

function clearActivation() {
  state.activeNodes.clear();
  state.activeEdges.clear();
}

function hasActivation() {
  return state.activeNodes.size > 0 || state.activeEdges.size > 0;
}

function activeNeighborhood(edges, activeNodes = state.activeNodes) {
  const nodes = new Set();
  const edgeIDs = new Set();
  for (const edge of edges) {
    const fromActive = activeNodes.has(edge.from);
    const toActive = activeNodes.has(edge.to);
    if (!fromActive && !toActive) continue;
    edgeIDs.add(edge.id);
    if (fromActive) nodes.add(edge.to);
    if (toActive) nodes.add(edge.from);
  }
  return { nodes, edges: edgeIDs };
}

function activateInspectorTarget(target, item, point) {
  prepareActivation(item);
  inspect(item, { source: target, point });
}

function inspect(item, options = {}) {
  cancelHide();
  state.current = item;
  if (item.kind === "node") renderNode(item.value);
  else renderEdge(item.value);
  const inspector = document.querySelector("#inspector");
  inspector.hidden = false;
  positionInspector(options.point || targetPosition(options.source || itemTarget(item)));
  updateSelection();
}

function closeInspector() {
  cancelHide();
  state.current = null;
  document.querySelector("#inspector").hidden = true;
  updateSelection();
}

function bindInspectorTarget(target, item) {
  target.addEventListener("pointerenter", event => inspect(item, { point: pointerPosition(event) }));
  target.addEventListener("pointermove", event => {
    if (sameItem(state.current, item)) positionInspector(pointerPosition(event));
  });
  target.addEventListener("pointerleave", scheduleRestore);
  target.addEventListener("focus", () => inspect(item, { point: targetPosition(target) }));
  target.addEventListener("blur", scheduleRestore);
  target.addEventListener("click", event => {
    event.stopPropagation();
    activateInspectorTarget(target, item, pointerPosition(event));
  });
  target.addEventListener("keydown", event => {
    if (event.key === "Enter" || event.key === " ") {
      event.preventDefault();
      activateInspectorTarget(target, item, targetPosition(target));
    }
  });
}

function modeOpportunities(counts) {
  const list = element("div", "mode-opportunities");
  for (const mode of ["A", "B", "C"]) {
    const count = counts[mode] || 0;
    const item = element("div", `mode-opportunity${count === 0 ? " empty" : ""}`);
    item.append(
      element("strong", null, mode),
      element("b", null, String(count)),
      element("span", null, count === 1 ? "eligible pair" : "eligible pairs")
    );
    list.append(item);
  }
  return list;
}

function factorName(kind, index) {
  return `${kind}${Math.floor(index / state.view.size)}${index % state.view.size}`;
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
    if (mode === sharedMode) row.append(element("span", "held", "same projective factor"));
    card.append(row);
  }
  return card;
}

function sectionTitle(text) {
  return element("h3", "inspector-section-title", text);
}

function inspectorHeading(kind, title) {
  const content = document.querySelector("#inspector-content");
  content.replaceChildren();
  content.append(element("p", `type ${kind.replaceAll(" ", "-")}`, kind), element("h2", null, title));
  return content;
}

function metric(label, value) {
  const card = element("div", "metric");
  card.append(element("span", null, label), element("strong", null, String(value)));
  return card;
}

function supportSummary(histogram) {
  return histogram.map((count, index) => count ? `${count} × weight ${index + 1}` : null).filter(Boolean).join(" · ");
}

function renderOrbitNode(node) {
  const isSource = node.id === state.graph.source;
  const isTarget = node.id === state.graph.target;
  const onPath = node.pathIndex != null;
  const title = isSource ? "Schoolbook orbit" : isTarget ? "Strassen orbit" : `Orbit ${node.name}`;
  const content = inspectorHeading(onPath ? "shortest-path orbit" : "orbit representative", title);

  const identity = element("div", "validity-card");
  identity.append(
    element("strong", null, `LENGTH ${node.length} · OVER F₂`),
    element("span", null, "This point represents a complete symmetry orbit of presentations, not one raw scheme. Its ID names the published representative used to generate the graph.")
  );
  content.append(identity);

  const metrics = element("div", "metrics");
  metrics.append(
    metric("distinct neighbors", node.degree),
    metric("flip edges", node.flipEdges),
    metric("reduction edges", node.reductions),
    metric("self-loops", node.selfLoops)
  );
  content.append(metrics, sectionTitle("Representative support profile"));

  const profile = element("div", "mode-opportunities");
  ["A", "B", "C"].forEach((mode, index) => {
    const row = element("div", "mode-opportunity");
    row.append(element("strong", null, mode), element("span", null, supportSummary(node.supportHistogram[index])));
    profile.append(row);
  });
  content.append(profile);

  const reference = element("div", "reference");
  reference.append(
    element("strong", null, onPath ? `Shortest-path checkpoint ${node.pathIndex + 1}/${state.graph.path.length}` : "Complete component vertex"),
    element("span", null, isSource
      ? "All factors in the representative are coordinate vectors, which identifies schoolbook multiplication."
      : isTarget
        ? "This is the component’s unique length-7 representative."
        : "Incidence counts include every deduplicated orbit edge in the published component."),
    element("code", null, `representative ${node.id}`)
  );
  content.append(reference);
}

function renderOrbitEdge(edge) {
  const from = state.nodes.get(edge.from);
  const to = state.nodes.get(edge.to);
  const loop = edge.selfLoop;
  const title = loop ? `${from.name} ↺ its orbit` : `${from.name} ${edge.type === "reduction" ? "→" : "↔"} ${to.name}`;
  const content = inspectorHeading(edge.onPath ? `shortest-path ${edge.type}` : `orbit ${edge.type}`, title);

  const summary = edge.type === "reduction"
    ? `CONTRACTION · LENGTH ${from.length} → ${to.length}`
    : loop
      ? `INVERTIBLE FLIP · LENGTH ${from.length} · SAME SYMMETRY ORBIT`
      : `INVERTIBLE FLIP · LENGTH ${from.length} UNCHANGED`;
  content.append(element("p", `mechanic-summary ${edge.type}`, summary));
  content.append(element("p", "mechanic-explanation", edge.type === "reduction"
    ? "A length-reducing transition connects these two presentation orbits. Direction is shown from the longer presentation to the shorter one."
    : loop
      ? "The flip changes the representative scheme but symmetry canonicalization returns it to the same orbit. The self-loop is retained because it is one of the published 1,183 orbit edges."
      : "An invertible same-length flip connects representatives in these two symmetry orbits."));

  const reference = element("div", "reference");
  reference.append(
    element("strong", null, edge.onPath ? "Chosen shortest route" : "Complete component transition"),
    element("span", null, "The importer canonicalizes endpoint order and removes duplicate rows from edges.txt; no geometry comes from the paper figure."),
    element("code", null, `edge ${edge.id}`)
  );
  content.append(reference);
}

function renderNode(node) {
  if (state.view.kind === "orbit") return renderOrbitNode(node);
  const onPath = node.pathIndex !== null;
  const content = inspectorHeading(onPath ? "gold path checkpoint" : "retained sample state", node.name);

  const tensorName = `M${state.view.size}`;
  const validity = element("div", "validity-card");
  validity.append(
    element("strong", null, `VALID · ${node.rank}-TERM PRESENTATION`),
    element("span", null, `Its ${state.view.size * state.view.size} × ${state.view.size * state.view.size} × ${state.view.size * state.view.size} = ${state.view.coordinateCount} rational coordinates exactly equal the ${tensorName} tensor. This certifies the construction, not optimality.`)
  );
  content.append(validity);

  content.append(sectionTitle("Useful next moves"));
  const atLowerBound = node.rank === state.view.lowerBound;
  const reduction = element("div", `move-signal${node.reductions > 0 || atLowerBound ? " available" : ""}`);
  reduction.append(
    element("strong", null, atLowerBound
      ? `Proven optimum · tensor rank ${state.view.lowerBound}`
      : node.reductions > 0
        ? `${node.reductions} immediate ${node.reductions === 1 ? "contraction" : "contractions"}`
        : "No immediate contraction"),
    element("span", null, atLowerBound
      ? `No exact presentation with fewer than ${state.view.lowerBound} rank-one terms exists.`
      : node.reductions > 0
        ? `A displayed 2 → 1 move can lower this presentation from ${node.rank} to ${node.rank - 1} terms.`
        : "No currently recognized pair combines directly from two terms to one.")
  );
  content.append(reduction);

  const pairs = element("p", "pair-summary");
  pairs.append(element("strong", null, `${node.movablePairs} eligible term ${node.movablePairs === 1 ? "pair" : "pairs"}`),
    " share exactly one projective factor. Each pair can support many rational rebases; this is not a count of neighboring states.");
  content.append(pairs, modeOpportunities(node.movableByMode));

  const largestComponent = Math.max(...node.components);
  content.append(sectionTitle("Mobility heuristic"));
  const mobility = element("p", "mobility-note");
  mobility.append(element("strong", null, `${largestComponent} terms connected`),
    " in the largest chain of shared-factor opportunities. A larger chain suggests that local flips can propagate farther; it does not prove reachability or reducibility.");
  content.append(mobility);

  const incident = state.graph.edges.filter(edge => edge.from === node.id || edge.to === node.id);
  const reference = element("div", "reference");
  reference.append(
    element("strong", null, onPath
      ? `Gold path checkpoint ${node.pathIndex + 1}/${state.graph.path.length}`
      : "Off-path state retained for this finite sample"),
    element("span", null, `Only ${incident.length} incident ${incident.length === 1 ? "edge is" : "edges are"} retained in this picture; this is not the state’s full degree.`),
    element("code", null, `state ${node.id}`)
  );
  content.append(reference);
}

function basisDiagram(columns) {
  const wrap = element("div", "basis-block");
  wrap.append(element("span", "basis-label", "Invertible G · columns u, v"));
  const matrix = element("div", "basis-matrix");
  matrix.append(
    element("code", null, columns[0][0]), element("code", null, columns[1][0]),
    element("code", null, columns[0][1]), element("code", null, columns[1][1])
  );
  wrap.append(matrix, element("strong", "invertible", "det G ≠ 0"));
  return wrap;
}

function flipMechanic(sharedMode) {
  const changedModes = ["A", "B", "C"].filter(mode => mode !== sharedMode);
  const map = element("div", "transform-map");
  for (const [mode, operation, description] of [
    [sharedMode, "fixed", "same projective factor"],
    [changedModes[0], "× G", "choose a new basis"],
    [changedModes[1], "× G⁻¹", "apply the dual change"]
  ]) {
    const step = element("div", `transform-step${mode === sharedMode ? " shared" : ""}`);
    step.append(element("strong", null, mode), element("b", null, operation), element("span", null, description));
    map.append(step);
  }
  return map;
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
    termGroup(`Local tensor before · remove ${edge.removed.length}`, edge.removed, edge.type === "flip" ? edge.mode : null, "before"),
    element("div", "delta-arrow", "="),
    termGroup(`Same local tensor after · add ${edge.added.length}`, edge.added, edge.type === "flip" ? edge.mode : null, "after")
  );
  content.append(comparison);
}

function renderEdge(edge) {
  if (state.view.kind === "orbit") return renderOrbitEdge(edge);
  const from = state.nodes.get(edge.from);
  const to = state.nodes.get(edge.to);
  const title = edge.type === "flip" ? `${from.name} ↔ ${to.name}` : `${from.name} → ${to.name}`;
  const content = inspectorHeading(edge.onPath ? `gold path ${edge.type}` : `sampled ${edge.type}`, title);

  if (edge.type === "flip") {
    content.append(element("p", "mechanic-summary", `LOCAL REBASING · 2 → 2 TERMS · LENGTH ${from.rank} UNCHANGED`));
    content.append(flipMechanic(edge.mode));
    const explanation = element("p", "mechanic-explanation");
    explanation.append("The terms share one ", element("strong", "mode-chip", `${edge.mode} projective factor`),
      ". Choosing an invertible 2 × 2 basis G in one remaining mode and the inverse basis in the other preserves their sum. The move is exactly reversible.");
    content.append(explanation);
    if (edge.basisColumns) content.append(basisDiagram(edge.basisColumns));
  } else {
    const isSplit = edge.type === "split";
    content.append(element("p", `mechanic-summary ${edge.type}`, isSplit
      ? `LIFT · 1 → 2 TERMS · LENGTH ${from.rank} → ${to.rank}`
      : `CONTRACTION · 2 → 1 TERM · LENGTH ${from.rank} → ${to.rank}`));
    content.append(element("p", "mechanic-explanation", isSplit
      ? "One rank-one contribution is represented by two terms. The tensor is unchanged, but the extra term introduces redundancy that later flips can redistribute."
      : "Two compatible rank-one contributions combine into one. The tensor is unchanged while the presentation loses a term."));
  }

  if (Array.isArray(edge.removed) && Array.isArray(edge.added)) {
    const untouched = from.rank - edge.removed.length;
    content.append(element("p", "untouched", `Only the terms shown below change; the other ${untouched} terms remain untouched.`));
    renderDelta(content, edge);
  } else {
    content.append(element("p", "unavailable", "NOT VISUALLY INSPECTABLE: this sampled cross-link stores only endpoints, shared mode, and G. Its removed and added terms were not retained."));
  }

  const status = element("div", "reference");
  status.append(
    element("strong", null, edge.onPath ? "Gold path certificate" : "Finite-sample cross-link"),
    element("span", null, edge.onPath
      ? "The complete local replacement is stored and can be replayed exactly."
      : "Its presence proves this sampled adjacency, not that it is preferred or exhaustive."),
    element("code", null, `edge ${edge.id}`)
  );
  content.append(status);
}

function updateSelection() {
  if (!state.graph) return;
  const branches = document.querySelector("#branches").checked;
  const neighborhood = activeNeighborhood(state.graph.edges);
  document.querySelectorAll(".graph-node").forEach(group => {
    const node = state.nodes.get(group.dataset.id);
    const selected = state.activeNodes.has(node.id);
    group.classList.toggle("hidden", !branches && node.pathIndex == null);
    group.classList.toggle("selected", selected);
    group.classList.toggle("adjacent", neighborhood.nodes.has(node.id));
    group.setAttribute("aria-pressed", String(selected));
  });
  document.querySelectorAll(".graph-edge").forEach(path => {
    const edge = state.edges.get(path.dataset.id);
    const selected = state.activeEdges.has(edge.id);
    const keepSampleReduction = state.view.kind === "sample" && edge.type === "reduction";
    path.classList.toggle("hidden", !branches && !edge.onPath && !keepSampleReduction);
    path.classList.toggle("selected", selected);
    path.classList.toggle("adjacent", neighborhood.edges.has(edge.id));
    path.setAttribute("aria-pressed", String(selected));
  });
  document.querySelector("#progress").textContent = `path ${state.pathIndex + 1}/${state.graph.path.length}`;
  document.querySelector("#previous").disabled = state.pathIndex === 0;
  document.querySelector("#next").disabled = state.pathIndex === state.graph.path.length - 1;
}

function centerNode(node) {
  if (cameraZoom() <= minZoom) return;
  setCamera({
    ...state.camera,
    x: node.position[0] - state.camera.width / 2,
    y: node.position[1] - state.camera.height / 2
  });
}

function showPathStep(index) {
  state.pathIndex = Math.max(0, Math.min(state.graph.path.length - 1, index));
  const node = state.nodes.get(state.graph.path[state.pathIndex]);
  let item = descriptor("node", node);
  if (state.pathIndex > 0) {
    const previous = state.graph.path[state.pathIndex - 1];
    const edge = state.graph.edges.find(value => value.onPath &&
      ((value.from === previous && value.to === node.id) || (value.to === previous && value.from === node.id)));
    if (edge) item = descriptor("edge", edge);
  }
  retainActivation(item);
  closeInspector();
  centerNode(node);
}

function draw(graph) {
  closeInspector();
  clearActivation();
  state.graph = graph;
  state.pathIndex = 0;
  for (const node of graph.nodes) node.pathIndex ??= null;
  state.nodes = new Map(graph.nodes.map(node => [node.id, node]));
  state.edges = new Map(graph.edges.map(edge => [edge.id, edge]));

  const perAnchor = new Map();
  if (state.view.kind === "sample") {
    for (const node of graph.nodes) {
      if (node.pathIndex != null) continue;
      const siblings = perAnchor.get(node.anchor) || [];
      siblings.push(node);
      perAnchor.set(node.anchor, siblings);
    }
    for (const siblings of perAnchor.values()) siblings.sort((a, b) => a.id.localeCompare(b.id));
  }
  for (const node of graph.nodes) {
    const siblings = perAnchor.get(node.anchor) || [];
    const index = node.pathIndex == null ? siblings.indexOf(node) : 0;
    node.position = nodePosition(node, index);
  }

  const svg = document.querySelector("#graph");
  resetCamera();
  svg.replaceChildren();
  if (state.view.bands) {
    const bands = svgElement("g", { class: "bands" });
    for (const band of state.view.bands) {
      bands.append(svgElement("line", { x1: 28, y1: band.y, x2: 1532, y2: band.y }));
      const label = svgElement("text", { x: 30, y: band.y - 18 });
      label.textContent = `length ${band.rank}`;
      bands.append(label);
    }
    svg.append(bands);
  }

  const edgeLayer = svgElement("g", { class: "edges" });
  for (const edge of graph.edges) {
    const from = state.nodes.get(edge.from);
    const to = state.nodes.get(edge.to);
    const path = svgElement("path", {
      d: edgePath(from, to),
      class: `graph-edge ${edge.type}${edge.selfLoop ? " self-loop" : ""}${edge.onPath ? " on-path" : ""}`,
      transform: edge.selfLoop ? anchoredScale(from.position) : null,
      "data-id": edge.id,
      tabindex: "0",
      role: "button",
      "aria-pressed": "false",
      "aria-label": `${edge.type} from ${from.name} to ${to.name}; focus to inspect, activate to retain its graph highlight`
    });
    bindInspectorTarget(path, descriptor("edge", edge));
    edgeLayer.append(path);
  }
  svg.append(edgeLayer);

  const nodeLayer = svgElement("g", { class: "nodes" });
  for (const node of graph.nodes) {
    const length = node.length ?? node.rank;
    const group = svgElement("g", {
      class: `graph-node ${state.view.kind === "orbit" ? "orbit-node " : ""}${node.pathIndex == null ? "branch" : "path-node"} length-${length}${node.id === graph.source ? " source-node" : ""}${node.id === graph.target ? " target-node" : ""}`,
      transform: nodeTransform(node),
      "data-id": node.id,
      tabindex: "0",
      role: "button",
      "aria-pressed": "false",
      "aria-label": `${node.name}, complete length ${length} presentation; focus to inspect, activate to highlight its incident edges and neighboring nodes`
    });
    const ordinaryRadius = state.view.kind === "orbit" ? 5 : 9;
    const pathRadius = state.view.kind === "orbit" ? 10 : 17;
    group.append(svgElement("circle", { r: node.pathIndex == null ? ordinaryRadius : pathRadius }));
    if (node.pathIndex != null) {
      const number = svgElement("text", { y: 4 });
      number.textContent = node.pathIndex;
      group.append(number);
      if (state.view.kind === "sample" || node.id === graph.source || node.id === graph.target) {
        const label = svgElement("text", { y: node.position[1] > 500 ? 29 : -19, class: "node-label" });
        label.textContent = node.id === graph.source ? "schoolbook" : node.id === graph.target ? "Strassen" : node.name;
        group.append(label);
      }
    }
    const title = svgElement("title");
    title.textContent = state.view.kind === "orbit"
      ? `${node.name}: length ${length} orbit, ${node.degree} distinct neighbors, ${node.reductions} reduction edges`
      : `${node.name}: complete length ${length} presentation, ${node.movablePairs} movable pairs, ${node.reductions} reductions`;
    group.append(title);
    bindInspectorTarget(group, descriptor("node", node));
    nodeLayer.append(group);
  }
  svg.append(nodeLayer);

  document.querySelector("#scope").textContent = graph.scope;
  const provenance = typeof graph.provenance === "string"
    ? graph.provenance
    : `Generated from ${graph.provenance.dataset} at ${graph.provenance.revision.slice(0, 12)} · ${graph.provenance.repository}`;
  document.querySelector("#provenance").textContent = provenance;
  const hasAlternatives = graph.nodes.some(node => node.pathIndex == null);
  document.querySelector("#alternatives-control").hidden = !hasAlternatives;
  document.querySelector("#branches").checked = true;
  centerNode(state.nodes.get(graph.path[0]));
  updateSelection();
}

function renderLegend(view) {
  const legend = document.querySelector("#legend");
  legend.replaceChildren();
  for (const [className, label] of view.legend) {
    const item = element("span");
    item.append(element("i", className), document.createTextNode(label));
    legend.append(item);
  }
}

function configureView(view) {
  document.title = view.documentTitle;
  document.querySelector("#eyebrow").textContent = view.eyebrow;
  document.querySelector("#page-title").textContent = view.pageTitle;
  document.querySelector("#graph-title").textContent = view.graphTitle;
  document.querySelector("#graph-description").textContent = view.graphDescription;
  document.querySelector("#reading-title").textContent = view.readingTitle;
  document.querySelector("#reading-body").textContent = view.readingBody;
  document.querySelector("#footer-note").textContent = view.footer;
  document.querySelector("#alternatives-label").textContent = view.alternativesLabel;
  document.querySelector("#graph").setAttribute("aria-label", view.ariaLabel);
  for (const [key, candidate] of Object.entries(views)) {
    const tab = document.querySelector(`#tab-${key}`);
    const active = candidate === view;
    tab.classList.toggle("active", active);
    tab.setAttribute("aria-selected", String(active));
  }
  renderLegend(view);
}

function loadGraph(view) {
  state.view = view;
  state.graph = null;
  clearActivation();
  const token = ++state.loadToken;
  configureView(view);
  resetCamera();
  closeInspector();
  document.querySelector("#graph").replaceChildren();
  document.querySelector("#scope").textContent = "Loading exact graph…";
  fetch(view.url)
    .then(response => {
      if (!response.ok) throw new Error(`HTTP ${response.status}`);
      return response.json();
    })
    .then(graph => {
      if (token === state.loadToken) draw(graph);
    })
    .catch(error => {
      if (token === state.loadToken) document.querySelector("#scope").textContent = `Could not load graph: ${error.message}`;
    });
}

function start() {
  const inspector = document.querySelector("#inspector");
  document.addEventListener("keydown", event => {
    if (event.key === "Escape" && (!inspector.hidden || hasActivation())) {
      event.preventDefault();
      clearActivation();
      closeInspector();
    }
  });

  document.querySelector("#previous").addEventListener("click", () => showPathStep(state.pathIndex - 1));
  document.querySelector("#next").addEventListener("click", () => showPathStep(state.pathIndex + 1));
  document.querySelector("#zoom-out").addEventListener("click", () => setZoom(cameraZoom() / 1.35));
  document.querySelector("#zoom-in").addEventListener("click", () => setZoom(cameraZoom() * 1.35));
  document.querySelector("#zoom-fit").addEventListener("click", resetCamera);
  const svg = document.querySelector("#graph");
  svg.addEventListener("wheel", wheelZoom, { passive: false });
  svg.addEventListener("pointerdown", startPan);
  svg.addEventListener("pointermove", movePan);
  svg.addEventListener("pointerup", stopPan);
  svg.addEventListener("pointercancel", stopPan);
  document.querySelector("#reset").addEventListener("click", () => {
    resetCamera();
    clearActivation();
    document.querySelector("#branches").checked = true;
    showPathStep(0);
  });
  document.querySelector("#branches").addEventListener("change", updateSelection);
  document.querySelector("#tab-m2").addEventListener("click", () => loadGraph(views.m2));
  document.querySelector("#tab-m3").addEventListener("click", () => loadGraph(views.m3));

  loadGraph(views.m2);
}

if (typeof module === "undefined") {
  start();
} else {
  module.exports = { activeNeighborhood, anchoredScale, clearActivation, hasActivation, nodeTransform, prepareActivation, state };
}
