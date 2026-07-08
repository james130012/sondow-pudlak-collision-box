#!/usr/bin/env python3
from __future__ import annotations

import html
import json
import shutil
import subprocess
import textwrap
from collections import defaultdict, deque
from pathlib import Path

OUT = Path(__file__).resolve().parent
ROOT = (
    "SondowMainCheckedCodeBridge."
    "SondowProjectBigNCleanSubmissionRoute.cleanUpperProvider_submissionRoute"
)


def short_name(name: str) -> str:
    replacements = [
        ("SondowMainCheckedCodeBridge.", ""),
        ("SondowProjectBigNCleanSubmissionRoute.", "BigNClean."),
        ("SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint.", "Checker."),
        ("SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.", "Month12."),
        ("SondowProjectMonth9Month10InternalPudlakWitnessSurface.", "Pudlak."),
        ("SondowProjectMonth9Month10Month11ExactProofGapHandoff.", "Gap."),
    ]
    for old, new in replacements:
        name = name.replace(old, new)
    return name


def wrap_label(label: str, width: int = 28) -> list[str]:
    chunks: list[str] = []
    for part in label.split("\n"):
        chunks.extend(textwrap.wrap(part, width=width, break_long_words=True) or [""])
    return chunks


def svg_box(x: float, y: float, w: float, h: float, label: str,
            fill: str = "#e9f7f7", stroke: str = "#6aa6a6",
            text_size: int = 15) -> str:
    lines = wrap_label(label)
    out = [
        f'<rect x="{x:.1f}" y="{y:.1f}" width="{w:.1f}" height="{h:.1f}" '
        f'rx="6" fill="{fill}" stroke="{stroke}" stroke-width="1.4"/>'
    ]
    start_y = y + h / 2 - (len(lines) - 1) * text_size * 0.58
    for i, line in enumerate(lines):
        out.append(
            f'<text x="{x + w/2:.1f}" y="{start_y + i * text_size * 1.18:.1f}" '
            f'text-anchor="middle" dominant-baseline="middle" '
            f'font-family="Noto Sans, Arial, sans-serif" font-size="{text_size}">'
            f'{html.escape(line)}</text>'
        )
    return "\n".join(out)


def svg_edge(x1: float, y1: float, x2: float, y2: float,
             dashed: bool = False, label: str | None = None) -> str:
    dash = ' stroke-dasharray="7 6"' if dashed else ""
    mx, my = (x1 + x2) / 2, (y1 + y2) / 2
    path = (
        f'<path d="M {x1:.1f} {y1:.1f} C {x1:.1f} {my:.1f}, '
        f'{x2:.1f} {my:.1f}, {x2:.1f} {y2:.1f}" '
        f'fill="none" stroke="#9a9a9a" stroke-width="1.3"{dash} '
        f'marker-end="url(#arrow)"/>'
    )
    if not label:
        return path
    return (
        path
        + f'\n<text x="{mx:.1f}" y="{my - 6:.1f}" text-anchor="middle" '
        + 'font-family="Noto Sans, Arial, sans-serif" font-size="13" '
        + f'fill="#555">{html.escape(label)}</text>'
    )


def write_svg(path: Path, width: int, height: int, body: str) -> None:
    svg = f'''<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">
<defs>
  <marker id="arrow" markerWidth="10" markerHeight="10" refX="9" refY="3" orient="auto" markerUnits="strokeWidth">
    <path d="M0,0 L0,6 L9,3 z" fill="#9a9a9a"/>
  </marker>
</defs>
<rect width="100%" height="100%" fill="#ffffff"/>
{body}
</svg>
'''
    path.write_text(svg, encoding="utf-8")


def dot_quote(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'


def write_dot(
    path: Path,
    nodes: dict[str, dict[str, object]],
    edge_direction: str = "dependency_to_dependent",
) -> None:
    lines = [
        "digraph G {",
        "  graph [rankdir=TB, bgcolor=white, splines=ortho, nodesep=0.45, ranksep=0.7];",
        "  node [shape=box, style=\"rounded,filled\", color=\"#6aa6a6\", fillcolor=\"#e9f7f7\", fontname=\"Noto Sans\"];",
        "  edge [color=\"#999999\", arrowsize=0.7];",
    ]
    for key, node in nodes.items():
        label = str(node["name"])
        fill = "#fff4df" if node.get("constCategory") == "Theorem" else "#e9f7f7"
        lines.append(f"  {dot_quote(key)} [label={dot_quote(short_name(label))}, fillcolor={dot_quote(fill)}];")
    for key, node in nodes.items():
        for ref in node.get("references", []):
            if ref not in nodes:
                continue
            if edge_direction == "dependency_to_dependent":
                lines.append(f"  {dot_quote(ref)} -> {dot_quote(key)};")
            else:
                lines.append(f"  {dot_quote(key)} -> {dot_quote(ref)};")
    lines.append("}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def maybe_render_dot(dot_path: Path, svg_path: Path) -> None:
    if not shutil.which("dot"):
        return
    subprocess.run(["dot", "-Tsvg", str(dot_path), "-o", str(svg_path)], check=True)


def write_spine() -> None:
    nodes = {
        "h": {"name": "h : is_rational euler_mascheroni", "constCategory": "Other", "constType": "", "references": []},
        "upper": {"name": "checkedSearchUpperTail", "constCategory": "Definition", "constType": "", "references": ["h"]},
        "upper_tail": {"name": "U, polynomial, upperN\nn >= upperN -> M(n) <= U(n)", "constCategory": "Other", "constType": "", "references": ["upper"]},
        "gap": {"name": "gap_for_polynomial_upper", "constCategory": "Definition", "constType": "", "references": ["upper_tail"]},
        "gap_tail": {"name": "threshold\nn >= threshold -> U(n) < M(n)", "constCategory": "Other", "constType": "", "references": ["gap"]},
        "max": {"name": "N = max upperN threshold", "constCategory": "Definition", "constType": "", "references": ["upper_tail", "gap_tail"]},
        "ineq": {"name": "M(N) <= U(N)\nand U(N) < M(N)", "constCategory": "Other", "constType": "", "references": ["max"]},
        "false": {"name": "False", "constCategory": "Other", "constType": "", "references": ["ineq"]},
        "notrat": {"name": "not is_rational\neuler_mascheroni", "constCategory": "Theorem", "constType": "", "references": ["false"]},
        "eqmax": {"name": "cleanComputedBigN\n_eq_tailGapMax", "constCategory": "Theorem", "constType": "", "references": ["upper_tail", "gap_tail", "max"]},
        "provider": {"name": "cleanProvider\n_not_rational", "constCategory": "Theorem", "constType": "", "references": ["ineq", "false", "notrat"]},
        "main": {"name": "cleanUpperProvider\n_submissionRoute", "constCategory": "Theorem", "constType": "", "references": ["eqmax", "provider"]},
    }
    (OUT / "clean_collision_proof_spine.lean_graph.json").write_text(
        json.dumps(list(nodes.values()), ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    write_dot(OUT / "clean_collision_proof_spine.dot", nodes)
    maybe_render_dot(
        OUT / "clean_collision_proof_spine.dot",
        OUT / "clean_collision_proof_spine.graphviz.svg",
    )

    pos = {
        "h": (610, 50),
        "upper": (250, 150),
        "upper_tail": (250, 260),
        "gap": (970, 150),
        "gap_tail": (970, 260),
        "max": (610, 380),
        "ineq": (610, 500),
        "false": (610, 610),
        "notrat": (610, 720),
        "eqmax": (250, 620),
        "provider": (970, 620),
        "main": (610, 850),
    }
    size = {k: (310, 70) for k in pos}
    size["upper_tail"] = (390, 88)
    size["gap_tail"] = (390, 88)
    size["ineq"] = (340, 78)
    size["main"] = (390, 70)
    theorem_fill = "#fff4df"
    body: list[str] = [
        '<text x="610" y="28" text-anchor="middle" font-family="Noto Sans, Arial, sans-serif" font-size="22" font-weight="700">Clean Sondow-Pudlak Collision Proof Spine</text>',
        '<text x="250" y="118" text-anchor="middle" font-family="Noto Sans, Arial, sans-serif" font-size="17" fill="#555">Sondow side</text>',
        '<text x="970" y="118" text-anchor="middle" font-family="Noto Sans, Arial, sans-serif" font-size="17" fill="#555">Pudlak / checker side</text>',
    ]
    edges = [
        ("h", "upper"), ("upper", "upper_tail"), ("upper_tail", "gap"),
        ("gap", "gap_tail"), ("upper_tail", "max"), ("gap_tail", "max"),
        ("max", "ineq"), ("ineq", "false"), ("false", "notrat"),
        ("upper_tail", "eqmax"), ("gap_tail", "eqmax"), ("max", "eqmax"),
        ("ineq", "provider"), ("false", "provider"), ("notrat", "provider"),
        ("eqmax", "main"), ("provider", "main"),
    ]
    for a, b in edges:
        ax, ay = pos[a]
        bx, by = pos[b]
        aw, ah = size[a]
        bw, bh = size[b]
        body.append(svg_edge(ax, ay + ah, bx, by, dashed=(a in {"upper_tail", "gap_tail", "ineq", "false"} and b in {"eqmax", "provider"})))
    for k, (x, y) in pos.items():
        w, h = size[k]
        fill = theorem_fill if nodes[k]["constCategory"] == "Theorem" else "#e9f7f7"
        body.append(svg_box(x - w / 2, y, w, h, nodes[k]["name"], fill=fill))
    write_svg(OUT / "clean_collision_proof_spine.svg", 1220, 950, "\n".join(body))


def write_project_type_svg() -> None:
    path = OUT / "cleanUpperProvider_submissionRoute.project_type.depth3.json"
    data = json.loads(path.read_text(encoding="utf-8"))
    by_name = {n["name"]: n for n in data}
    refs = {n["name"]: [r for r in n.get("references", []) if r in by_name] for n in data}
    write_dot(
        OUT / "cleanUpperProvider_submissionRoute.project_type.depth3.dot",
        by_name,
        edge_direction="declaration_to_dependency",
    )
    maybe_render_dot(
        OUT / "cleanUpperProvider_submissionRoute.project_type.depth3.dot",
        OUT / "cleanUpperProvider_submissionRoute.project_type.depth3.graphviz.svg",
    )
    dist = {ROOT: 0}
    q = deque([ROOT])
    while q:
        n = q.popleft()
        for r in refs.get(n, []):
            if r not in dist:
                dist[r] = dist[n] + 1
                q.append(r)
    layers: dict[int, list[str]] = defaultdict(list)
    for n in by_name:
        layers[dist.get(n, 4)].append(n)
    for layer in layers.values():
        layer.sort(key=short_name)
    width = 2200
    max_layer = max(layers)
    height = 260 + max(len(v) for v in layers.values()) * 115
    node_w, node_h = 420, 74
    x_gap = width / (max_layer + 2)
    positions: dict[str, tuple[float, float]] = {}
    for d in sorted(layers):
        names = layers[d]
        x = 120 + d * x_gap
        y0 = 100
        for i, name in enumerate(names):
            positions[name] = (x, y0 + i * 105)
    body: list[str] = [
        '<text x="1100" y="40" text-anchor="middle" font-family="Noto Sans, Arial, sans-serif" font-size="24" font-weight="700">Project Type Dependency Graph: cleanUpperProvider_submissionRoute</text>',
        '<text x="1100" y="70" text-anchor="middle" font-family="Noto Sans, Arial, sans-serif" font-size="15" fill="#666">Generated from Lean declarations; Mathlib/Core dependencies filtered out</text>',
    ]
    for name, outs in refs.items():
        if name not in positions:
            continue
        x1, y1 = positions[name]
        for r in outs:
            if r not in positions:
                continue
            x2, y2 = positions[r]
            body.append(svg_edge(x1 + node_w, y1 + node_h / 2, x2, y2 + node_h / 2, dashed=True))
    for name, (x, y) in positions.items():
        cat = by_name[name].get("constCategory")
        fill = "#fff4df" if cat == "Theorem" else ("#eef1ff" if cat == "Other" else "#e9f7f7")
        body.append(svg_box(x, y, node_w, node_h, short_name(name), fill=fill, text_size=12))
    write_svg(OUT / "cleanUpperProvider_submissionRoute.project_type.depth3.svg", width, max(height, 1300), "\n".join(body))


def write_index() -> None:
    html_text = """<!doctype html>
<meta charset="utf-8">
<title>Lean graph artifacts</title>
<style>
body { font-family: system-ui, sans-serif; margin: 2rem; line-height: 1.45; }
code { background: #f4f4f4; padding: .12rem .25rem; }
li { margin: .35rem 0; }
</style>
<h1>Clean BigN Lean Graph Artifacts</h1>
<p>These files visualize dependencies for <code>cleanUpperProvider_submissionRoute</code>.</p>
<ul>
  <li><a href="clean_collision_proof_spine.svg">clean_collision_proof_spine.svg</a></li>
  <li><a href="clean_collision_proof_spine.dot">clean_collision_proof_spine.dot</a></li>
  <li><a href="clean_collision_proof_spine.lean_graph.json">clean_collision_proof_spine.lean_graph.json</a></li>
  <li><a href="cleanUpperProvider_submissionRoute.project_type.depth3.svg">cleanUpperProvider_submissionRoute.project_type.depth3.svg</a></li>
  <li><a href="cleanUpperProvider_submissionRoute.project_type.depth3.dot">cleanUpperProvider_submissionRoute.project_type.depth3.dot</a></li>
  <li><a href="cleanUpperProvider_submissionRoute.project_type.depth3.json">cleanUpperProvider_submissionRoute.project_type.depth3.json</a></li>
  <li><a href="DependencyExtractorType.lean">DependencyExtractorType.lean</a></li>
</ul>
<h2>Proof Spine</h2>
<img src="clean_collision_proof_spine.svg" style="max-width: 100%; border: 1px solid #ddd;">
"""
    (OUT / "index.html").write_text(html_text, encoding="utf-8")


def main() -> None:
    write_spine()
    write_project_type_svg()
    write_index()


if __name__ == "__main__":
    main()
