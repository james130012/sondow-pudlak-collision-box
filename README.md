# Sondow-Pudlak Clean Collision Route

This repository is a Lean 4 research artifact for a Sondow-Pudlak
proof-complexity collision program around the Euler-Mascheroni constant
`gamma`.

## Current Submission Theorem

The current submission theorem is

```lean
cleanUpperProvider_submissionRoute
```

Public source link:

<https://github.com/james130012/sondow-pudlak-collision-box/blob/main/integration/SondowProjectBigNCleanSubmissionRoute.lean>

For a clean checker input and a measured upper provider in the same coordinate,
Lean proves that the rationality branch computes the collision threshold

```lean
N = max upperN threshold
```

and that the same formal input package proves

```lean
¬ is_rational euler_mascheroni
```

The observed axiom output for the main theorem is the standard Lean/Mathlib
logical profile:

```text
[propext, Classical.choice, Quot.sound]
```

Detailed dependency and reproducibility checks are recorded in the audit
reports linked below.

## Submission Links

- Polished submission release:
  <https://github.com/james130012/sondow-pudlak-collision-box/releases/tag/clean-bigN-submission-polished-20260708>
- Chinese submission manuscript:
  <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/paper/submission_bigN_formal_manuscript_zh.md>
- English submission manuscript:
  <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/paper/submission_bigN_formal_manuscript_en.md>
- Chinese audit report:
  <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/docs/clean_submission_route_audit_20260708_zh.md>
- English audit report:
  <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/docs/clean_submission_route_audit_20260708_en.md>
- Validation log:
  <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/docs/bigN_validation_log_20260708_zh.md>
- Current status:
  <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/STATUS.md>

## Reproduction

Build the main Lean entry:

```bash
lake exe cache get
lake build integration.SondowProjectBigNCleanSubmissionRoute
```

Check the theorem and axiom profile:

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

Expected main theorem axiom output:

```text
[propext, Classical.choice, Quot.sound]
```

## What Is Proved

The clean theorem proves the following formal collision statement.

1. A measured upper provider supplies an eventual polynomial upper tail with a
   cutoff `upperN`.
2. The tail-gap certificate supplies a threshold for the same measured checker
   function.
3. Under the rationality branch, the computed collision number is exactly
   `max upperN threshold`.
4. At that computed number the upper and strict lower certificates contradict
   each other, yielding `¬ is_rational euler_mascheroni` relative to the clean
   input package.

The current manuscript cites this clean Lean theorem as the submission result.
Numerical extraction of the threshold is future work.
