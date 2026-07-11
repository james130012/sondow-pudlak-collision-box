# Parameter Closure Audit Report

Date: 2026-07-08

## Conclusion

This audit adds the parameter-closure file:

```text
integration/SondowProjectBigNParameterClosureAudit.lean
```

The cleanest current parameter-closure conditional theorem is:

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

This is the current parameter-closure route.  It exposes neither
`upper_provider`, nor `tail_gap`, nor `eventually_strict_length`, and it keeps
the clean formula
`bigN = thresholdOfMonomial upper_data.coeff upper_data.degree`.  The remaining
obligation is to prove that `minCheckedCodeSize` eventually dominates every
natural monomial.

## Growth-Obligation Reaudit

The July 9, 2026 growth-obligation reaudit adds:

```text
integration/SondowProjectBigNGrowthObligationAudit.lean
```

Lean checks the following key audit theorems:

```lean
conjRightMinCheckedCodeSize_le_explicitLength
conjRightMinCheckedCodeSize_polynomial_of_component_polynomial
monomialDomination_impossible_of_polynomial_bound
singletonMonomialLowerBound_conjSource_obligation_impossible
eventuallyStrictLength_conjSource_impossible
```

Their content is that the `minCheckedCodeSize` in
`singletonMonomialLowerBound_submissionRoute` is carried by
`(left_family.conjIntro right_family).rightConjElim`.  Since `left_family` and
`right_family` are explicit proof families and their lengths are assumed
polynomial, Lean proves that this `minCheckedCodeSize` is itself polynomially
bounded from above.  It therefore cannot carry a Pudlak lower-bound obligation
that eventually dominates every monomial.  If `eventually_strict_length` is
attached to the same `lengthCodeAt`, Lean derives an eventual
`lengthCodeAt < lengthCodeAt` contradiction.

## Correct Forward Route

The same audit file also proves the positive replacement target:

```lean
actualProofLength_searchGap_candidateCarrier
```

This moves the lower-bound carrier to the actual PA proof length of the
theorem-5 power-bound family:

```lean
actualProofLengthMeasured core.scale_data
```

Given

```lean
InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore
```

Lean constructs a search-gap certificate: for every polynomial upper `U` and
every requested cutoff `N`, it computes a witness `w >= N` such that

```lean
U w < actualProofLengthMeasured core.scale_data w
```

This is weaker than a full tail statement `forall n >= threshold`, but it is the
form required by the generic collision core against an eventual Sondow upper
bound.

The verified axiom profile separates the two parts:

```text
monomialDomination_impossible_of_polynomial_bound
singletonMonomialLowerBound_conjSource_obligation_impossible
  [propext, Classical.choice, Quot.sound]

actualProofLength_searchGap_candidateCarrier
checkerExtractorExactness_to_actualProofLength_searchGap
paHilbertCheckerExactnessCore_to_actualProofLength_searchGap
  [proof_length, propext, Classical.choice, Quot.sound]
```

Thus the obstruction to the old carrier is independent of the project-level
payload constants and does not use root `proof_length`.  The positive replacement
still uses the root `proof_length` coordinate because its carrier is
`actualProofLengthMeasured`; a fully proof-length-free refinement must push this
further down to concrete PA/Hilbert proof-code exactness.

## Claims Not To Overstate

The current result should not be stated as an unconditional proof of the
irrationality of Euler's constant.  The monomial tail-growth input of
`singletonMonomialLowerBound_submissionRoute` is not closable on the current
conjunction-source carrier.  The viable Pudlak/proof-length direction is the
search-witness gap over `actualProofLengthMeasured`.

The correct statement is that the project has identified the wrong carrier for
the growth obligation and proved the obstruction in Lean.  The next theorem and
paper draft should use the actual-proof-length search-gap route, or an even
lower concrete proof-code version of that route.  Its full unconditionality
depends on how completely
`InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore` and its upstream
Pudlak/checker/extractor components are formalized.

## 2026-07-09 Upper-Side Same-Object Calibration Update

The new probe file

```lean
integration/SondowProjectSondowUpperCompilerRoute.lean
```

now moves the Sondow upper side away from root `proof_length` and the legacy
`accepted_certificate` branch, onto the same PA semantic proof-length object
used by the Pudlak side:

```lean
semanticBAProofLength PAAxiom
  sondowProjectComponentFormulas.target n
```

Core theorems:

```lean
semanticPAProjectTargetLength_le_combined_of_componentProofObjects
semanticPAProjectTargetUpper_fromHalfDenCheckedTailAndEventualCompiler
semanticPAProjectTargetUpper_fromRationalityAndEventualCompiler
semanticPAProjectTargetUpper_fromRationalityAndFullCompiler
literatureCalibratedSondowUpper_fromRationalityAndEventualCompiler
literatureCalibratedSondowUpper_fromRationalityAndFullCompiler
```

Verified axiom profile:

```text
[propext, Classical.choice, Quot.sound]
```

In particular, these probes do not use:

```text
proof_length
partial_consistency_payload
strengthened_partial_consistency_payload
upper_provider
tail_gap
```

This closes the same-object calibration for the upper side: instead of assuming
an abstract upper-provider condition, it shows that a genuine

```lean
MainSondowEventualFullCertificateComponentProofCompiler bounds
```

turns checked full Sondow certificates into five Buss-S21 proof objects, then
assembles them into a PA proof object for
`sondowProjectComponentFormulas.target`, yielding the polynomial upper
`bounds.combined`.

The submission route can now cite both upper routes:

```lean
literatureCalibratedSondowUpper_fromRationalityAndEventualCompiler
SondowCheckedS21TraceCompiler.closed
s21SondowCertificateUpper_fromHalfDenCheckedTailClosed
```

The root `SondowCheckedS21TraceCompiler` is closed through the Sondow sidecar
slot calibration, not through the old pure structural fallback.

A July 9, 2026 probe confirms this state:

```text
sidecarSondowCertificateCanonicalProofLengthCalibration_closed
  [propext, Classical.choice, Quot.sound]

SondowCheckedS21TraceCompiler.closed
  [propext, Classical.choice, Quot.sound]

s21SondowCertificateUpper_fromHalfDenCheckedTailClosed
  [propext, Classical.choice, Quot.sound]

canonicalSemanticSondowUpper_fromHalfDenCheckedTail
  [propext, Classical.choice, Quot.sound]

literatureCalibratedSondowUpper_fromRationalityAndEventualCompiler
  [propext, Classical.choice, Quot.sound]
```

Conclusion: the Sondow upper side is closed.  The submission upper route can
use the root S21 route or the `semanticBAProofLength` route.

A root-level probe also verifies:

```lean
proof_length_eq_rootFormulaCodeSize
rootProofLength_sondowCertificateValidCode_eq_one
```

Thus root `proof_length` is no longer a free axiom, and on
`S21 / symbolSize / sondowCertificateValidCode` it is equal to `1`, the same
minimum code length proved for the sidecar proof-code semantics.

`EulerLimit/ProofComplexityCore.lean` also exposes the public proof-code
semantics interface:

```lean
RootProofLengthCodeConvention
ProofLengthCodeSemantics.Calibration.proof_length_eq_minProofCodeSize
ProofLengthCodeSemantics.Calibration.proof_length_le_of_hasProofCodeOfSize
RootProofLengthCodeConvention.proof_length_le_of_hasProofCodeOfSize
RootProofLengthCodeConvention.toProjectProofLengthSemantics
```

All of these have the axiom profile:

```text
[propext, Classical.choice, Quot.sound]
```

These interfaces remain useful for auditing proof-length conventions on other
formula families.

The current root convention is also expressed through the same interface:

```lean
rootProofLengthCodeSemantics_calibration
rootStructuralProofLengthCodeConvention
rootStructuralProofLength_eq_minProofCodeSize
```

These also have only:

```text
[propext, Classical.choice, Quot.sound]
```

Thus root `proof_length` has no free axiom.  On the Sondow certificate-valid
family it is calibrated by the sidecar slot; on other families it remains a
structural fallback until separately calibrated.

The root condition for `SondowCheckedS21TraceCompiler` has also been compressed
to a pointwise family equality:

```lean
sidecarSondowCertificateCanonicalProofLengthCalibration_iff_family
SondowCheckedS21TraceCompiler.ofSidecarFamilyRootCalibration
```

It now only asks for:

```text
root proof_length(sondowCertificateValidCode n)
  =
the sidecar checker's minimum accepted proof-code size.
```

The older conditional reconnection theorems had the profile:

```text
[proof_length, propext, Classical.choice, Quot.sound]
```

The new closed theorems have:

```text
[propext, Classical.choice, Quot.sound]
```

with no payload constants, no `upper_provider`, and no `tail_gap`.

The sidecar checker itself has now been closed more sharply.  In
`integration/SondowProjectSondowUpperCompilerRoute.lean`, the minimum accepted
proof-code size on each `sondowCertificateValidCode n` is proved to be exactly
`1`:

```lean
baDerivation_one_le_size
baProofObject_one_le_size
sidecarSondowCertificateProofCodeSemantics_min_eq_one
```

These have the axiom profile:

```text
[propext, Classical.choice, Quot.sound]
```

Consequently the remaining root calibration is now:

```lean
sidecarSondowCertificateCanonicalProofLengthCalibration_iff_rootLengthOne
SondowCheckedS21TraceCompiler.ofRootLengthOne
```

Equivalently, it asks only for:

```text
∀ n,
  proof_length S21 symbolSize (sondowCertificateValidCode n) = 1.
```

The older theorems that reconnect this statement to root `proof_length` have
the profile:

```text
[proof_length, propext, Classical.choice, Quot.sound]
```

The closed route has the reduced profile:

```text
[propext, Classical.choice, Quot.sound]
```

The core file now recalibrates the
`S21 / symbolSize / sondowCertificateValidCode` family to the canonical Sondow
sidecar checker slot of length `1`:

```lean
rootProofLength_sondowCertificateValidCode_eq_one
structuralFallbackFormulaSize_sondowCertificateValidCode_eq_add_six
```

Meaning:

```text
current root proof_length:
  proof_length S21 symbolSize (sondowCertificateValidCode n) = 1

counterfactual structural fallback size:
  without the sidecar slot, the structural formula-code size would be n + 6
```

Profiles:

```text
rootProofLength_sondowCertificateValidCode_eq_one
  [propext, Classical.choice, Quot.sound]

structuralFallbackFormulaSize_sondowCertificateValidCode_eq_add_six
  [propext]
```

The Sondow upper file also exposes the exact predicate budget:

```lean
proofPredicateFormulaSizeSondowCertificateValidCode_eq
proofPredicateFormulaSizeSondowCertificateValidCode_100_lt_106
```

namely:

```text
proof_predicate_formula_size(sondowCertificateValidCode n)
  =
3 * log2(n+1) + 14
```

and at `n = 100`:

```text
proof_predicate_formula_size(sondowCertificateValidCode 100) < 106.
```

This explains why the old pure structural fallback cannot be used as the root
closure route; the current closure uses the root slot calibrated to the sidecar
proof-code semantics.  These two size theorems have the same profile:

```text
[propext, Classical.choice, Quot.sound]
```

New closed root-route theorems:

```lean
sidecarSondowCertificateCanonicalProofLengthCalibration_closed
SondowCheckedS21TraceCompiler.closed
s21SondowCertificateUpper_fromHalfDenCheckedTailClosed
```

All three have the profile:

```text
[propext, Classical.choice, Quot.sound]
```

with no root `proof_length` axiom, no `upper_provider`, no `tail_gap`, and no
payload constants.  Conclusion: `SondowCheckedS21TraceCompiler` is now closed
after the sidecar-slot calibration.

The corresponding proof-length-free upper route is fully closed.  New names:

```lean
sidecarSondowCertificateCanonicalSemanticLength_eq_one
SondowCheckedS21SemanticTraceCompiler.closed
canonicalSemanticSondowUpper_fromHalfDenCheckedTail
```

All three have the axiom profile:

```text
[propext, Classical.choice, Quot.sound]
```

The meaning is that a checked Sondow certificate is sent through an explicit
sidecar proof object whose canonical semantic proof length is exactly `1`; this
lies inside the predicate budget and yields the polynomial upper bound
`17(n+1)`.  This route uses no root `proof_length`, no `upper_provider`, no
`tail_gap`, and no payload constants.

The remaining point must not be hidden: the current bare project atoms are
already audited as not directly derivable in the narrow Buss-S21 object
language.  The next closure task is therefore the real compiler theorem, or a
move to verifier-definability formulas with a matching recalibration of the
Pudlak lower target.
