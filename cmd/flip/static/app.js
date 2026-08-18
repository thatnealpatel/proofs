"use strict";

const svgNS = "http://www.w3.org/2000/svg";
const branchRows = [70, 135, 200, 265, 500, 565, 630, 695];
const state = { graph: null, nodes: new Map(), selected: null, pathIndex: 0 };

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

function activate(node, callback) {
  node.addEventListener("click", event => {
    event.stopPropagation();
    callback();
  });
  node.addEventListener("keydown", event => {
    if (event.key === "Enter" || event.key === " ") {
      event.preventDefault();
      callback();
    }
  });
}

function nodePosition(node, branchIndex) {
  const x = 92 + node.anchor * 150;
  if (node.pathIndex !== null) return [x, node.rank === 23 ? 730 : 382];
  const jitter = branchIndex % 2 ? 30 : -30;
  return [x + jitter, branchRows[branchIndex]];
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
    else if (coefficient === "-1") terms.push(`- ${variable}`);
    else if (coefficient.startsWith("-")) terms.push(`- ${coefficient.slice(1)}${variable}`);
    else terms.push(`+ ${coefficient}${variable}`);
  });
  return terms.length ? terms.join(" ").replace(/^\+ /, "") : "0";
}

function termCard(term) {
  const card = element("div", "term-card");
  card.append(element("div", "coefficient", `coefficient ${term.coefficient}`));
  for (const mode of ["A", "B", "C"]) {
    const row = element("div", "factor");
    row.append(element("strong", null, mode), element("code", null, formatFactor(mode, term[mode])));
    card.append(row);
  }
  return card;
}

function metric(label, value) {
  const box = element("div", "metric");
  box.append(element("span", null, label), element("strong", null, String(value)));
  return box;
}

function setDetailHeading(kind, title) {
  const detail = document.querySelector("#detail");
  detail.replaceChildren();
  detail.append(element("p", `type ${kind.replaceAll(" ", "-")}`, kind), element("h2", null, title));
  return detail;
}

function showNode(node, center = false) {
  state.selected = { kind: "node", id: node.id };
  if (node.pathIndex !== null) state.pathIndex = node.pathIndex;
  updateSelection();
  const detail = setDetailHeading(node.pathIndex === null ? "sampled neighbor" : "recorded state", node.name);
  detail.append(element("span", "badge", "exactly verified on all 729 coordinates"));
  detail.append(element("p", "hash", `state ${node.id}`));
  const metrics = element("div", "metrics");
  metrics.append(
    metric("presentation length", node.rank),
    metric("movable pairs", node.movablePairs),
    metric("reductions", node.reductions),
    metric("largest component", Math.max(...node.components))
  );
  detail.append(metrics);
  detail.append(element("h3", null, "Available flips by shared factor"));
  detail.append(element("p", "identity", formatModes(node.movableByMode)));
  const incident = state.graph.edges.filter(edge => edge.from === node.id || edge.to === node.id);
  detail.append(element("p", null, `${incident.length} transition${incident.length === 1 ? "" : "s"} connect this vertex inside the displayed finite sample.`));
  if (node.pathIndex !== null) {
    detail.append(element("p", null, `Recorded path position ${node.pathIndex + 1} of ${state.graph.path.length}. Use Previous/Next to inspect the exact change leading between path states.`));
  }
  if (center) centerNode(node);
}

function showTerms(detail, heading, terms) {
  detail.append(element("h3", null, heading));
  const list = element("div", "term-list");
  for (const term of terms) list.append(termCard(term));
  detail.append(list);
}

function showEdge(edge, center = false) {
  state.selected = { kind: "edge", id: edge.id };
  const from = state.nodes.get(edge.from);
  const to = state.nodes.get(edge.to);
  if (edge.onPath && to.pathIndex !== null) state.pathIndex = to.pathIndex;
  updateSelection();
  const title = edge.type === "flip"
    ? `${from.name} ↔ ${to.name}`
    : `${from.name} → ${to.name}`;
  const detail = setDetailHeading(edge.onPath ? `recorded ${edge.type}` : edge.type, title);
  detail.append(element("span", "badge", "replayable exact transition"));
  detail.append(element("p", null, edge.type === "flip"
    ? `An invertible same-length flip sharing mode ${edge.mode}.`
    : `${edge.type === "split" ? "One term is replaced by two" : "Two terms contract to one"}; the presentation length changes from ${from.rank} to ${to.rank}.`));
  if (edge.basisColumns) {
    const matrix = edge.basisColumns.map(column => `[${column.join(", ")}]`).join("  ");
    detail.append(element("p", "identity", `Basis columns: ${matrix}`));
  }
  if (edge.removed && edge.added) {
    showTerms(detail, `Remove ${edge.removed.length} term${edge.removed.length === 1 ? "" : "s"}`, edge.removed);
    showTerms(detail, `Add ${edge.added.length} term${edge.added.length === 1 ? "" : "s"}`, edge.added);
  } else {
    detail.append(element("p", "identity", "This sampled cross-link stores its endpoints, shared mode, and basis matrix. Full changed-factor cards are retained for the recorded path to keep the embedded sample compact."));
  }
  if (center) centerNode(to);
}

function updateSelection() {
  const branches = document.querySelector("#branches").checked;
  document.querySelectorAll(".graph-node").forEach(group => {
    const node = state.nodes.get(group.dataset.id);
    group.classList.toggle("hidden", !branches && node.pathIndex === null);
    group.classList.toggle("selected", state.selected?.kind === "node" && state.selected.id === node.id);
    group.classList.remove("adjacent");
  });
  document.querySelectorAll(".graph-edge").forEach(path => {
    const edge = state.graph.edges.find(value => value.id === path.dataset.id);
    const hidden = !branches && !edge.onPath && edge.type !== "reduction";
    path.classList.toggle("hidden", hidden);
    path.classList.toggle("selected", state.selected?.kind === "edge" && state.selected.id === edge.id);
  });
  if (state.selected?.kind === "node") {
    const id = state.selected.id;
    for (const edge of state.graph.edges) {
      if (edge.from !== id && edge.to !== id) continue;
      document.querySelector(`[data-id="${edge.id}"]`)?.classList.add("adjacent");
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
  const target = Math.max(0, node.position[0] - viewport.clientWidth / 2);
  viewport.scrollTo({ left: target, behavior: "smooth" });
}

function showPathStep(index) {
  state.pathIndex = Math.max(0, Math.min(state.graph.path.length - 1, index));
  const node = state.nodes.get(state.graph.path[state.pathIndex]);
  if (state.pathIndex === 0) {
    showNode(node, true);
    return;
  }
  const previous = state.graph.path[state.pathIndex - 1];
  const edge = state.graph.edges.find(value => value.onPath && value.from === previous && value.to === node.id);
  if (edge) showEdge(edge, true);
  else showNode(node, true);
}

function draw(graph) {
  state.graph = graph;
  state.nodes = new Map(graph.nodes.map(node => [node.id, node]));
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
  const rank24 = svgElement("text", { x: 30, y: 364 }); rank24.textContent = "length 24";
  const rank23 = svgElement("text", { x: 30, y: 712 }); rank23.textContent = "length 23";
  bands.append(rank24, rank23);
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
      "aria-label": `${edge.type} from ${from.name} to ${to.name}`
    });
    activate(path, () => showEdge(edge));
    edgeLayer.append(path);
  }
  svg.append(edgeLayer);

  const nodeLayer = svgElement("g", { class: "nodes" });
  for (const node of graph.nodes) {
    const [x, y] = node.position;
    const group = svgElement("g", {
      class: `graph-node ${node.pathIndex === null ? "branch" : "path-node"} rank-${node.rank}`,
      transform: `translate(${x} ${y})`,
      "data-id": node.id,
      tabindex: "0",
      role: "button",
      "aria-label": `${node.name}, length ${node.rank}`
    });
    group.append(svgElement("circle", { r: node.pathIndex === null ? 9 : 17 }));
    if (node.pathIndex !== null) {
      const number = svgElement("text", { y: 5 });
      number.textContent = node.pathIndex;
      const label = svgElement("text", { y: node.rank === 23 ? 34 : -28, class: "node-label" });
      label.textContent = node.name;
      group.append(number, label);
    }
    const title = svgElement("title");
    title.textContent = `${node.name}: length ${node.rank}, ${node.movablePairs} movable pairs, ${node.reductions} reductions`;
    group.append(title);
    activate(group, () => showNode(node));
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
  showPathStep(0);
}

fetch("/api/graph")
  .then(response => {
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    return response.json();
  })
  .then(draw)
  .catch(error => {
    document.querySelector("#scope").textContent = `Could not load graph: ${error.message}`;
  });
