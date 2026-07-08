# Sondow-Pudlak Clean Collision Route

This repository is a Lean 4 research artifact for a Sondow-Pudlak
proof-complexity collision program around the Euler-Mascheroni constant
`gamma`.

## Current Submission Theorem

The current submission theorem is

```lean
singletonMonomialLowerBound_submissionRoute
```

Public source link:

<https://github.com/james130012/sondow-pudlak-collision-box/blob/main/integration/SondowProjectBigNParameterClosureAudit.lean>

This parameter-closed submission route removes the explicit `tail_gap`,
`upper_provider`, and `eventually_strict_length` parameters from the public
theorem surface.  The remaining mathematical input is the monomial growth
certificate

```lean
thresholdOfMonomial coeff degree <= n ->
  coeff * (n + 1)^degree < minCheckedCodeSize n
```

Under that growth input, Lean proves the formula-level collision index

```lean
bigN = thresholdOfMonomial upper_data.coeff upper_data.degree
```

and the corresponding contradiction theorem

```lean
¬ is_rational euler_mascheroni
```

The observed axiom output for the submission theorem is the standard
Lean/Mathlib logical profile:

```lean
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
- Parameter closure audit:
  <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/docs/parameter_closure_audit_20260708_en.md>
- Validation log:
  <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/docs/bigN_validation_log_20260708_zh.md>
- Current status:
  <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/STATUS.md>

## Reproduction

Build the main Lean entry:

```bash
lake exe cache get
lake build integration.SondowProjectBigNParameterClosureAudit
```

Check the theorem and axiom profile:

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectBigNParameterClosureAudit
open SondowMainCheckedCodeBridge.SondowProjectBigNParameterClosureAudit

#check singletonMonomialLowerBound_submissionRoute
#check cleanTailGapFrontier_submissionRoute
#check eventuallyStrictLength_noTailGap_submissionRoute
#print axioms singletonMonomialLowerBound_submissionRoute
EOF
```

Expected main theorem axiom output:

```text
[propext, Classical.choice, Quot.sound]
```

## What Is Proved

The current theorem proves the following formal collision statement.

1. The old `upper_provider` and `tail_gap` inputs can be absorbed into upstream
   project-length data.
2. The public remaining growth obligation is the monomial domination statement
   for `minCheckedCodeSize`.
3. The certified index is exactly
   `thresholdOfMonomial upper_data.coeff upper_data.degree`.
4. At that index Lean derives the same upper/lower collision contradiction.

The current manuscript cites this parameter-closed theorem as the submission
result.  A completely unconditional proof still requires closing the displayed
monomial growth theorem, and numerical extraction of the threshold is future
work.
