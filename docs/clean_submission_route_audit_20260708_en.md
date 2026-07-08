# Clean Submission Route Audit Report

Date: 2026-07-08  
Audited artifact: `bigN-halfden-full-20260708` release copy  
Release URL: <https://github.com/james130012/sondow-pudlak-collision-box/releases/tag/bigN-halfden-full-20260708>  
Release commit:

```text
2a7458c253aae4050a0a3a18424abea952d26bc3
```

## Conclusion

This file records the first-stage clean checker/collision route.  The second
stage has added the parameter-closure route:

```lean
singletonMonomialLowerBound_submissionRoute
```

defined in:

```text
integration/SondowProjectBigNParameterClosureAudit.lean
```

The new submission-facing theorem no longer exposes `upper_provider`,
`tail_gap`, or `eventually_strict_length` on the theorem surface.  It compresses
the remaining mathematical obligation to the monomial growth statement

```lean
thresholdOfMonomial coeff degree <= n ->
  coeff * (n + 1)^degree < minCheckedCodeSize n
```

and proves the formula-level collision index

```lean
bigN = thresholdOfMonomial upper_data.coeff upper_data.degree
```

as well as the corresponding `¬ is_rational euler_mascheroni` conclusion under
that input.  See the detailed parameter-closure audit:

```text
docs/parameter_closure_audit_20260708_en.md
```

The `cleanUpperProvider_submissionRoute` audit below remains valid, but it is
now an intermediate route: it eliminates the three project-level residual
constants while still exposing the explicit `upper_provider` and `tail_gap`
parameters.

## Project-Level Dependencies

For the current submission route, the three project-level residual constants
have been eliminated.

Parameter-closure audit commands:

```bash
lake build integration.SondowProjectBigNParameterClosureAudit
lake env lean --stdin <<'EOF'
import integration.SondowProjectBigNParameterClosureAudit
open SondowMainCheckedCodeBridge.SondowProjectBigNParameterClosureAudit

#check singletonMonomialLowerBound_submissionRoute
#print axioms singletonMonomialLowerBound_submissionRoute
EOF
```

Observed axiom profile:

```text
[propext, Classical.choice, Quot.sound]
```

First-stage clean-route audit commands:

```bash
lake build integration.SondowProjectBigNCleanSubmissionRoute
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

Observed axiom profile:

```text
[propext, Classical.choice, Quot.sound]
```

The following project-level residual constants did not appear:

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

Therefore the current clean submission theorem does not depend on these three
project-level residual constants.

## Audit Of The Old Half-Denominator Formula Route

The old route contains the attractive formula

```lean
17 * (max 3 ((rat.q.den + 1) / 2)) + 8
```

However, `#print axioms` on the old half-denominator formula endpoints showed
that the canonical formula, checked-prefix formula, recognition formula, and
semantic-strong/existence formula still carry the project-level dependencies:

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

This means the old formula route should not be used as the main theorem of the
current submission. Making it the headline result would tie the paper's
credibility to residual constants that have not been removed from that route.

## Current Treatment

The formula-level direction has not been deleted. It has been moved to future
work. The clean downstream interface now includes:

```lean
CleanHalfDenUpperProvider
cleanComputedBigN_eq_halfDenFormulaMax
cleanHalfDenUpperProvider_submissionRoute
```

These theorems have the same clean axiom profile:

```text
[propext, Classical.choice, Quot.sound]
```

Their meaning is precise: if a future clean upstream route constructs a
half-denominator upper provider and proves

```lean
upperN = 17 * max 3 ((rat.q.den + 1) / 2) + 8
```

then the downstream collision theorem immediately gives the clean formula-level
version.

At present, that upstream construction cannot be taken from the old
project-length formula theorem, because that theorem is itself polluted by the
project-level residual constants. Therefore the current paper does not make the
half-denominator formula or a numerical value of `N` a necessary claim.

## Recommended Submission Language

The paper should state:

1. It proves a Lean-checked clean collision theorem.
2. Under a clean upper-provider input, the rational branch has the formal
   collision number `max upperN threshold`.
3. The same clean route proves the rational-branch contradiction.
4. The main theorem's axiom profile does not contain
   `partial_consistency_payload`, `proof_length`, or
   `strengthened_partial_consistency_payload`.
5. Formula-level half-denominator refinement and decimal numerical extraction
   are future refinements, not current submission claims.

The paper should not state:

1. The old `projectLength...halfDen...thresholdFormula` theorem is the current
   main theorem.
2. The work gives an unconditional proof of the irrationality of `gamma`.
3. The rational parameter already produces a clean formula-level
   half-denominator upper provider.

## Reproduction Summary

The following command passed:

```bash
lake build integration.SondowProjectBigNCleanSubmissionRoute
```

The module was then re-imported and checked with:

```lean
#check cleanUpperProvider_submissionRoute
#check cleanComputedBigN_eq_tailGapMax
#check cleanProvider_not_rational
#check CleanHalfDenUpperProvider
#check cleanHalfDenUpperProvider_submissionRoute
```

The core axiom output was only the standard Lean/Mathlib logical dependency
set:

```text
[propext, Classical.choice, Quot.sound]
```

This is the audit conclusion for the current credible proof version.
