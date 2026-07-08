# Parameter Closure Audit Report

Date: 2026-07-08

## Conclusion

This audit adds the parameter-closure file:

```text
integration/SondowProjectBigNParameterClosureAudit.lean
```

The cleanest current submission theorem is:

```lean
singletonMonomialLowerBound_submissionRoute
```

It removes the following explicit objects from the public theorem surface:

```text
upper_provider
tail_gap
eventually_strict_length
```

The remaining mathematical input is the auditable monomial growth statement:

```lean
thresholdOfMonomial coeff degree <= n ->
  coeff * (n + 1)^degree < minCheckedCodeSize n
```

Under that input, Lean proves the formula-level collision index:

```lean
bigN = thresholdOfMonomial upper_data.coeff upper_data.degree
```

and derives:

```lean
¬ is_rational euler_mascheroni
```

## Lean Audit Output

Reproduction commands:

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

The following project-level residual constants do not appear:

```text
partial_consistency_payload
proof_length
strengthened_partial_consistency_payload
```

## Meaning Of The Three Routes

The file records three audit routes.

```lean
cleanTailGapFrontier_submissionRoute
```

This route merges the old `input` and `upper_provider` into one upstream
frontier object.  It closes the scattered-parameter theorem surface, but the
frontier still contains a `tail_gap` field.

```lean
eventuallyStrictLength_noTailGap_submissionRoute
```

This route removes the raw `tail_gap` input by constructing it from
`eventually_strict_length` through
`ComputableGapCertificate.ofEventuallyStrict`.  It shows that `tail_gap` can be
lowered to an eventual strict growth theorem, but that theorem is still a
strong mathematical input.

```lean
singletonMonomialLowerBound_submissionRoute
```

This is the current submission-facing route.  It exposes neither
`upper_provider`, nor `tail_gap`, nor `eventually_strict_length`, and it keeps
the clean formula
`bigN = thresholdOfMonomial upper_data.coeff upper_data.degree`.  The remaining
obligation is to prove that `minCheckedCodeSize` eventually dominates every
natural monomial.

## Claims Not To Overstate

The current result should not be stated as an unconditional proof of the
irrationality of Euler's constant.  The theorem
`singletonMonomialLowerBound_submissionRoute` still requires the monomial
growth input.  This is not a Lean packaging issue; it is the actual
Pudlak/proof-length strength required by the argument.

The correct statement is that the project has compressed the formerly opaque
`tail_gap` and `upper_provider` parameters into one clear, formula-level,
auditable growth obligation.  Under that obligation, Lean proves the clean
collision-index formula and the contradiction theorem.
