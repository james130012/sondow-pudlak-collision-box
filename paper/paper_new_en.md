# A Clean Lean-Checked Collision Threshold in a Sondow-Pudlak Program

This draft is aligned with the clean submission route in
`integration/SondowProjectBigNCleanSubmissionRoute.lean`.

Main theorem:

```lean
cleanUpperProvider_submissionRoute
```

For a clean checker input and a clean measured upper provider, Lean proves that
the rational branch computes

```lean
N = max upperN threshold
```

and the same route proves:

```lean
¬ is_rational euler_mascheroni
```

The audited axiom profile is:

```text
[propext, Classical.choice, Quot.sound]
```

The theorem does not depend on:

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

The older half-denominator formula route is not the main theorem of this draft.
It remains a future refinement target because its existing endpoints still carry
the project-level residual constants above.

For the full manuscript text, see:

```text
paper/submission_bigN_formal_manuscript_en.md
```

For the audit report, see:

```text
docs/clean_submission_route_audit_20260708_zh.md
```
