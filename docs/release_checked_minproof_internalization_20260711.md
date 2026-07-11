# Checked-Minproof Arithmetic Internalization Release

Release tag: `checked-minproof-internalization-20260711`

This release is a reproducible source snapshot of the lower-bound
internalization work. It does not claim that the final Pudlak lower-bound
theorem is closed.

## Kernel-Checked Milestones

- Primitive-recursive packed-input extraction and exact payload recovery.
- Primitive-recursive `binaryNatCode` token-stream decoding.
- Exact finite ordered-ring function and relation symbol checks.
- A pure-natural arithmetic term/formula task machine.
- Exact execution-step and fixed-fuel sufficiency theorems for every genuine
  arithmetic term and formula.
- Canonical parser round trips with the same unconsumed token suffix.
- The initial pure-natural listed-proof task machine and exact sequent-list
  scheduling theorem.
- Public verifier cost closure and the guarded 23-tag PA-axiom comparison route
  developed in the same snapshot.

The audited public endpoints expose only `propext`, `Classical.choice`, and
`Quot.sound`, or a subset of them. They contain no `sorry`/`admit`, and no
unresolved project `axiom`, `tail_gap`, `upper_provider`, project
`proof_length`, or `haxm` input. Historical audit text may name rejected
interfaces in order to document why they are not on the live route.

## Current Frontier

The active obligation remains the numeric proof/certificate layer:

1. complete all ten listed-proof rule branches;
2. parse all 23 PA-axiom certificate constructors and structural certificates;
3. prove acceptance equivalence with the existing typed decoder for arbitrary,
   including malformed, inputs;
4. internalize the resulting verifier graph as a fixed PA arithmetic formula;
5. verify the Pudlak conditions and finish the checked minimum-proof lower
   bound.

The live dependency graph is
[`checked_minproof_theorem_dependency_graph_zh.dot`](checked_minproof_theorem_dependency_graph_zh.dot).

## Validation Performed

```text
lake env lean integration/FoundationCompactSyntaxTokenMachine.lean
  exit 0

lake build integration.FoundationCompactSyntaxTokenMachine
  exit 0; 1291 jobs

lake env lean integration/FoundationCompactProofTokenMachine.lean
  exit 0

dot -Tdot docs/checked_minproof_theorem_dependency_graph_zh.dot -o /dev/null
  exit 0
```

The release intentionally excludes generated dependency-graph PNG/SVG files;
the `.dot` source is the authoritative live status artifact.
