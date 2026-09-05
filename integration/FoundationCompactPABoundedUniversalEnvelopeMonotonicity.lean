import integration.FoundationCompactPABoundedUniversalPolynomialBounds
import integration.FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
import integration.FoundationCompactPAUnaryAtomicTransportPolynomialBounds

/-! # Monotonicity of the closed bounded-universal syntax envelope -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 140000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactPABoundedUniversalEnvelopeMonotonicity

open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds

private theorem finiteCaseFormulaEnvelope_mono
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    {small large : Nat} (hbound : small <= large) :
    finiteCaseFormulaEnvelope subject small <=
      finiteCaseFormulaEnvelope subject large := by
  have hshift : small + 2 <= large + 2 := by omega
  have hequality := finiteEqualityCasesCodePolynomial_mono subject hshift
  have hlower := finiteLowerBoundFormulaCodePolynomial_mono subject hshift
  have hexhaustion := finiteExhaustionFormulaCodePolynomial_mono subject hshift
  have hsteps : (small + 3) * finiteEqualityCaseStepEnvelope subject <=
      (large + 3) * finiteEqualityCaseStepEnvelope subject :=
    Nat.mul_le_mul_right _ (by omega)
  unfold finiteCaseFormulaEnvelope
  omega

theorem boundedUniversalClosedFormulaEnvelope_mono
    {small large : Nat} (hbound : small <= large) :
    boundedUniversalClosedFormulaEnvelope small <=
      boundedUniversalClosedFormulaEnvelope large := by
  have hseed : boundedUniversalSyntaxSeed small <=
      boundedUniversalSyntaxSeed large := by
    unfold boundedUniversalSyntaxSeed
    omega
  have hbody := substitutionFormulaCodeEnvelope_mono_local hseed hseed
  have hcase := finiteCaseFormulaEnvelope_mono
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0) hbound
  unfold boundedUniversalClosedFormulaEnvelope
    boundedUniversalClosedBodyCodeEnvelope
  omega

#print axioms boundedUniversalClosedFormulaEnvelope_mono

end FoundationCompactPABoundedUniversalEnvelopeMonotonicity
