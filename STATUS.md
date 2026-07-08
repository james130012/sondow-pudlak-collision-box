# Current Status

Date: 2026-07-08

## Submission Route

The current submission route is the clean Lean theorem

```lean
cleanUpperProvider_submissionRoute
```

defined at:

<https://github.com/james130012/sondow-pudlak-collision-box/blob/main/integration/SondowProjectBigNCleanSubmissionRoute.lean>

It proves that, for the clean checker input and a measured upper provider in
the same coordinate, the rationality branch computes

```lean
N = max upperN threshold
```

and the same formal package proves

```lean
¬ is_rational euler_mascheroni
```

The observed axiom output for the main theorem is:

```text
[propext, Classical.choice, Quot.sound]
```

## Public Materials

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

## Reproduction

```bash
lake exe cache get
lake build integration.SondowProjectBigNCleanSubmissionRoute
```

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

## Scope

This release is a clean formal collision result. It does not claim decimal
extraction of the threshold. Numerical extraction is deferred to later work.
