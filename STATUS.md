# Project Status

Date: 2026-07-08

## Current Main Result

The current submission result is the clean checker/collision route:

```lean
cleanUpperProvider_submissionRoute
```

defined in:

```text
integration/SondowProjectBigNCleanSubmissionRoute.lean
```

It states that, for a clean `ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput`
and a clean checked measured upper provider, the rational branch computes

```lean
N = max upperN threshold
```

where `upperN` is the cutoff in the clean upper tail and `threshold` is the
tail-gap threshold for the same clean measured route. The same theorem also
proves:

```lean
¬ is_rational euler_mascheroni
```

The current theorem is proof-level/collision-level. It intentionally does not
claim a decimal value for `N`, and it does not use the older half-denominator
formula-level project endpoint as its proof source.

## Audit Decision

The older half-denominator formula route was audited and found to still depend
on the project-level residual constants:

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

Therefore that old route is no longer presented as the main paper theorem.
Keeping it as the headline result would weaken the manuscript's credibility.

The clean route was checked with:

```bash
lake build integration.SondowProjectBigNCleanSubmissionRoute
```

and with:

```lean
#print axioms cleanUpperProvider_submissionRoute
#print axioms cleanComputedBigN_eq_tailGapMax
#print axioms cleanProvider_not_rational
#print axioms cleanComputedBigN_eq_halfDenFormulaMax
#print axioms cleanHalfDenUpperProvider_submissionRoute
```

The observed axiom profile for each of these clean route theorems was:

```text
[propext, Classical.choice, Quot.sound]
```

No project-level residual constant appears in the clean theorem profile.

## Release Context

Audited release tag:

```text
bigN-halfden-full-20260708
```

Release URL:

```text
https://github.com/james130012/sondow-pudlak-collision-box/releases/tag/bigN-halfden-full-20260708
```

Release commit:

```text
2a7458c253aae4050a0a3a18424abea952d26bc3
```

The release contains useful old half-denominator formula work, but the clean
submission route is now isolated in the added file
`integration/SondowProjectBigNCleanSubmissionRoute.lean`.

## Paper And Audit Materials

- Clean-route audit report, English:
  `docs/clean_submission_route_audit_20260708_en.md`
- Clean-route audit report, Chinese:
  `docs/clean_submission_route_audit_20260708_zh.md`
- Validation log:
  `docs/bigN_validation_log_20260708_zh.md`
- Submission manuscript, English:
  `paper/submission_bigN_formal_manuscript_en.md`
- Submission manuscript, Chinese:
  `paper/submission_bigN_formal_manuscript_zh.md`
- English paper draft:
  `paper/paper_new_en.md`
- Chinese paper draft:
  `paper/paper_new_zh.md`

## Deferred Work

The clean theorem already provides the correct `N = max upperN threshold`
collision target. The formula-level half-denominator refinement

```lean
17 * (max 3 ((rat.q.den + 1) / 2)) + 8
```

is deferred until its upstream upper-provider construction can be rebuilt on
the same clean route. The file already contains a clean downstream interface:

```lean
cleanHalfDenUpperProvider_submissionRoute
```

but the old formula theorems are not used to instantiate it in the submission.
