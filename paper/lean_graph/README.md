# Lean Graph Audit Artifacts

This directory contains dependency-visualization artifacts for the clean
submission route theorem
`SondowMainCheckedCodeBridge.SondowProjectBigNCleanSubmissionRoute.cleanUpperProvider_submissionRoute`.

## What Is Included

- `clean_collision_proof_spine.svg` is a compact proof-spine diagram for the
  clean Sondow--Pudlak collision route.
- `clean_collision_proof_spine.lean_graph.json` is the same proof spine in the
  JSON schema used by `lean-graph`.
- `clean_collision_proof_spine.dot` is a Graphviz/DOT source file for the same
  proof spine.
- `cleanUpperProvider_submissionRoute.project_type.depth3.json` is a
  machine-generated Lean declaration/type dependency graph for the main clean
  submission route.
- `cleanUpperProvider_submissionRoute.project_type.depth3.svg` is a static SVG
  rendering of that machine-generated graph.
- `cleanUpperProvider_submissionRoute.project_type.depth3.dot` is a
  Graphviz/DOT source file for the same machine-generated graph.
- `cleanComputedBigN_eq_tailGapMax.project_type.depth3.json` and
  `cleanProvider_not_rational.project_type.depth3.json` are companion
  machine-generated graphs for the two main components of the route.
- `DependencyExtractorType.lean` is the Lean extractor used to regenerate the
  project dependency JSON files.
- `render_clean_graphs.py` regenerates the SVG/HTML artifacts from the JSON
  files.
- `index.html` is a local entry page for viewing the generated SVG files.

## Reproduction

From the repository root:

```bash
lake env lean paper/lean_graph/DependencyExtractorType.lean
python3 paper/lean_graph/render_clean_graphs.py
```

If Graphviz is installed, the DOT files can also be rendered directly:

```bash
dot -Tsvg paper/lean_graph/clean_collision_proof_spine.dot \
  -o paper/lean_graph/clean_collision_proof_spine.graphviz.svg

dot -Tsvg paper/lean_graph/cleanUpperProvider_submissionRoute.project_type.depth3.dot \
  -o paper/lean_graph/cleanUpperProvider_submissionRoute.project_type.depth3.graphviz.svg
```

The generated JSON files can also be loaded into the upstream `lean-graph`
viewer:

https://patrik-cihal.github.io/lean-graph/

The upstream `lean-graph` desktop application is optional.  It is a GUI program
and therefore requires an X11/Wayland display.  In a headless shell it can be
smoke-tested with a virtual display, for example:

```bash
timeout 5s xvfb-run -a lean-graph
```

An exit code of `124` from this command means `timeout` stopped the GUI after
five seconds; it is not a Lean graph failure.

## Lean 4.31 Proof-Body Caveat

The upstream `lean-graph` extractor collects references from a declaration's
stored value.  In this project, Lean 4.31 does not expose imported theorem proof
bodies through `value?`, so a direct upstream proof-body extraction of imported
theorems collapses to a one-node graph.

This does not mean that the project theorem is isolated or small.  The
machine-generated graph in this directory instead records constants occurring
in declaration types and visible definition bodies, filtered to the project
namespace and a few logical boundary symbols.  For the main clean route this
produces a 60-node, 294-edge project dependency graph.

The proof-spine diagram is intentionally separate: it is a readable audit
diagram of the current source theorem's mathematical route, not a claim that
Lean exposed the full imported theorem proof body as a graph.

## Source Links

- Main theorem source:
  https://github.com/james130012/sondow-pudlak-collision-box/blob/main/integration/SondowProjectBigNCleanSubmissionRoute.lean
- GitHub repository:
  https://github.com/james130012/sondow-pudlak-collision-box
