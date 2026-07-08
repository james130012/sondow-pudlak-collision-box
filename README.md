# Sondow-Pudlak Clean Collision Route

This repository is a Lean 4 research artifact for a Sondow-Pudlak proof-complexity
collision program around the Euler-Mascheroni constant `gamma`.

**Current submission status, 2026-07-08.** The submission route has been reset to
the clean checker/collision theorem:

```lean
cleanUpperProvider_submissionRoute
```

defined in:

```text
integration/SondowProjectBigNCleanSubmissionRoute.lean
```

For a clean proof-length-free checker input and a clean measured upper provider,
Lean proves that the rational branch computes the collision threshold

```lean
N = max upperN threshold
```

and the same route proves:

```lean
¬ is_rational euler_mascheroni
```

The audited axiom profile of this submission theorem is:

```text
[propext, Classical.choice, Quot.sound]
```

It does **not** depend on the three project-level residual constants:

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

This is the theorem to cite for the clean version of the work. The older
half-denominator formula-level big-`N` route remains useful as a diagnostic and
future engineering target, but it is not the current manuscript's main theorem
because its existing Lean endpoints still carry those three project-level
dependencies.

## Release And Audit Links

- Audited release tag:
  <https://github.com/james130012/sondow-pudlak-collision-box/releases/tag/bigN-halfden-full-20260708>
- Audited release commit:

```text
2a7458c253aae4050a0a3a18424abea952d26bc3
```

- Clean-route audit report:
  [`docs/clean_submission_route_audit_20260708_zh.md`](docs/clean_submission_route_audit_20260708_zh.md)
- Validation log:
  [`docs/bigN_validation_log_20260708_zh.md`](docs/bigN_validation_log_20260708_zh.md)
- Current status:
  [`STATUS.md`](STATUS.md)
- Submission manuscript:
  [`paper/submission_bigN_formal_manuscript_en.md`](paper/submission_bigN_formal_manuscript_en.md)
- English paper draft:
  [`paper/paper_new_en.md`](paper/paper_new_en.md)
- Chinese paper draft:
  [`paper/paper_new_zh.md`](paper/paper_new_zh.md)

## Main Lean Entry

```bash
lake exe cache get
lake build integration.SondowProjectBigNCleanSubmissionRoute
```

After building, run the theorem and axiom probes:

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectBigNCleanSubmissionRoute
open SondowMainCheckedCodeBridge.SondowProjectBigNCleanSubmissionRoute

#check cleanUpperProvider_submissionRoute
#check cleanComputedBigN_eq_tailGapMax
#check cleanProvider_not_rational
#print axioms cleanUpperProvider_submissionRoute
#print axioms cleanComputedBigN_eq_tailGapMax
#print axioms cleanProvider_not_rational
EOF
```

Expected project-level audit result: none of
`partial_consistency_payload`, `proof_length`, or
`strengthened_partial_consistency_payload` appears in the axiom output.

## What Is Proved

The current clean theorem proves a conditional collision route:

1. A clean upper provider supplies an eventual polynomial upper tail with a
   cutoff `upperN`.
2. The clean tail-gap certificate supplies a threshold for the same measured
   checker route.
3. Under the rational branch, the computed collision number is exactly
   `max upperN threshold`.
4. At that computed number the route combines the upper and lower inequalities
   into a contradiction, yielding `¬ is_rational euler_mascheroni` relative to
   the clean input package.

This is not a decimal extraction of `N`, and it is not a claim that every
upstream Sondow/Pudlak witness has already been constructed without external
mathematical input. It is the clean Lean-checked collision core that should be
used for manuscript credit.

## Deferred Work

The half-denominator display

```lean
17 * (max 3 ((rat.q.den + 1) / 2)) + 8
```

has a clean downstream interface:

```lean
cleanHalfDenUpperProvider_submissionRoute
```

Its axiom profile is also clean, but it requires a clean upstream
half-denominator upper provider. The existing old formula-level endpoints do
not yet provide that clean upstream construction, so the formula-level and
numeric `N` refinements are deliberately deferred.

## Citation Boundary

Please cite the repository, release tag, and commit above when using this
artifact. Do not cite the old project-length half-denominator endpoint as the
main theorem of the clean submission route. The clean theorem is
`cleanUpperProvider_submissionRoute`.
