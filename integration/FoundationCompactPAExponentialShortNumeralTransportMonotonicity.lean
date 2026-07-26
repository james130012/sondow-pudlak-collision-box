import integration.FoundationCompactPAExponentialShortNumeralTransportBounds

/-!
# Monotonicity of the short-numeral exponential payload bound

The exponential proof itself is still compiled at its actual height.  These
lemmas only allow its explicit resource ledger to be widened to a larger
public height bound.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactPAExponentialShortNumeralTransportMonotonicity

open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExponentialRuleCompilerBounds
open FoundationCompactPAExponentialShortNumeralCompilerBounds
open FoundationCompactPAExponentialShortNumeralTransportBounds

theorem exponentialTransportFormulaStageOne_mono
    {small large : Nat} (h : small <= large) :
    exponentialTransportFormulaStageOne small <=
      exponentialTransportFormulaStageOne large := by
  exact substitutionFormulaCodeEnvelope_mono_exponential le_rfl h

theorem exponentialTransportFormulaStageTwo_mono
    {small large : Nat} (h : small <= large) :
    exponentialTransportFormulaStageTwo small <=
      exponentialTransportFormulaStageTwo large := by
  exact substitutionFormulaCodeEnvelope_mono_exponential
    (exponentialTransportFormulaStageOne_mono h) h

theorem exponentialTransportFormulaStageThree_mono
    {small large : Nat} (h : small <= large) :
    exponentialTransportFormulaStageThree small <=
      exponentialTransportFormulaStageThree large := by
  exact substitutionFormulaCodeEnvelope_mono_exponential
    (exponentialTransportFormulaStageTwo_mono h) h

theorem exponentialValueTransportPayloadEnvelope_mono
    {small large : Nat} (h : small <= large) :
    exponentialValueTransportPayloadEnvelope small <=
      exponentialValueTransportPayloadEnvelope large := by
  have hfirst := exponentialSpecializationCostEnvelope_mono
    (smallFormula := exponentialTransportFormulaSeed)
    (largeFormula := exponentialTransportFormulaSeed)
    (smallTerm := small) (largeTerm := large) le_rfl h
  have hsecond := exponentialSpecializationCostEnvelope_mono
    (smallFormula := exponentialTransportFormulaStageOne small)
    (largeFormula := exponentialTransportFormulaStageOne large)
    (smallTerm := small) (largeTerm := large)
    (exponentialTransportFormulaStageOne_mono h) h
  have hthird := exponentialSpecializationCostEnvelope_mono
    (smallFormula := exponentialTransportFormulaStageTwo small)
    (largeFormula := exponentialTransportFormulaStageTwo large)
    (smallTerm := small) (largeTerm := large)
    (exponentialTransportFormulaStageTwo_mono h) h
  unfold exponentialValueTransportPayloadEnvelope
  omega

theorem exponentialExponentTransportPayloadEnvelope_mono
    {small large : Nat} (h : small <= large) :
    exponentialExponentTransportPayloadEnvelope small <=
      exponentialExponentTransportPayloadEnvelope large := by
  have hfirst := exponentialSpecializationCostEnvelope_mono
    (smallFormula := exponentialTransportFormulaSeed)
    (largeFormula := exponentialTransportFormulaSeed)
    (smallTerm := small) (largeTerm := large) le_rfl h
  have hsecond := exponentialSpecializationCostEnvelope_mono
    (smallFormula := exponentialTransportFormulaStageOne small)
    (largeFormula := exponentialTransportFormulaStageOne large)
    (smallTerm := small) (largeTerm := large)
    (exponentialTransportFormulaStageOne_mono h) h
  have hthird := exponentialSpecializationCostEnvelope_mono
    (smallFormula := exponentialTransportFormulaStageTwo small)
    (largeFormula := exponentialTransportFormulaStageTwo large)
    (smallTerm := small) (largeTerm := large)
    (exponentialTransportFormulaStageTwo_mono h) h
  unfold exponentialExponentTransportPayloadEnvelope
  omega

theorem exponentialTransportMPFormulaEnvelope_mono
    {small large : Nat} (h : small <= large) :
    exponentialTransportMPFormulaEnvelope small <=
      exponentialTransportMPFormulaEnvelope large := by
  unfold exponentialTransportMPFormulaEnvelope
  exact Nat.mul_le_mul_left 2 (exponentialTransportFormulaStageThree_mono h)

theorem exponentialTransportMPPayloadEnvelope_mono
    {small large : Nat} (h : small <= large) :
    exponentialTransportMPPayloadEnvelope small <=
      exponentialTransportMPPayloadEnvelope large := by
  have hformula := exponentialTransportMPFormulaEnvelope_mono h
  have hsyntax := paAssemblySyntaxEnvelope_mono_short hformula
  unfold exponentialTransportMPPayloadEnvelope
  omega

theorem exponentialPowerPayloadPolynomial_mono_short
    {small large : Nat} (h : small <= large) :
    exponentialPowerPayloadPolynomial small <=
      exponentialPowerPayloadPolynomial large := by
  have hstep := exponentialPowerPayloadStep_mono h
  unfold exponentialPowerPayloadPolynomial
  gcongr

theorem exponentialExponentShortDirectPayloadPolynomial_mono
    {small large : Nat} (h : small <= large) :
    exponentialExponentShortDirectPayloadPolynomial small <=
      exponentialExponentShortDirectPayloadPolynomial large := by
  have hstep := exponentialShortDirectStepPayloadEnvelope_mono h
  unfold exponentialExponentShortDirectPayloadPolynomial
  gcongr

theorem exponentialValueShortDirectPayloadPolynomial_mono
    {small large : Nat} (h : small <= large) :
    exponentialValueShortDirectPayloadPolynomial small <=
      exponentialValueShortDirectPayloadPolynomial large := by
  have hstep := exponentialShortDirectStepPayloadEnvelope_mono h
  unfold exponentialValueShortDirectPayloadPolynomial
  gcongr

theorem exponentialExponentRecursiveToShortPayloadPolynomial_mono
    {small large : Nat} (h : small <= large) :
    exponentialExponentRecursiveToShortPayloadPolynomial small <=
      exponentialExponentRecursiveToShortPayloadPolynomial large := by
  have hdirect := exponentialExponentShortDirectPayloadPolynomial_mono h
  have hterm := exponentialShortTermCodeEnvelope_mono h
  have hprimitive := paPrimitiveCostEnvelope_mono_short hterm
  unfold exponentialExponentRecursiveToShortPayloadPolynomial
  omega

theorem exponentialValueRecursiveToShortPayloadPolynomial_mono
    {small large : Nat} (h : small <= large) :
    exponentialValueRecursiveToShortPayloadPolynomial small <=
      exponentialValueRecursiveToShortPayloadPolynomial large := by
  have hdirect := exponentialValueShortDirectPayloadPolynomial_mono h
  have hterm := exponentialShortTermCodeEnvelope_mono h
  have hprimitive := paPrimitiveCostEnvelope_mono_short hterm
  unfold exponentialValueRecursiveToShortPayloadPolynomial
  omega

theorem exponentialPowerAtShortNumeralsPayloadPolynomial_mono
    {small large : Nat} (h : small <= large) :
    exponentialPowerAtShortNumeralsPayloadPolynomial small <=
      exponentialPowerAtShortNumeralsPayloadPolynomial large := by
  have hterm := exponentialShortTermCodeEnvelope_mono h
  have hvalueTransport :=
    exponentialValueTransportPayloadEnvelope_mono hterm
  have hexponentTransport :=
    exponentialExponentTransportPayloadEnvelope_mono hterm
  have hvalueRecursive :=
    exponentialValueRecursiveToShortPayloadPolynomial_mono h
  have hexponentRecursive :=
    exponentialExponentRecursiveToShortPayloadPolynomial_mono h
  have hpower := exponentialPowerPayloadPolynomial_mono_short h
  have hmp := exponentialTransportMPPayloadEnvelope_mono hterm
  unfold exponentialPowerAtShortNumeralsPayloadPolynomial
  dsimp only
  omega

#print axioms exponentialPowerAtShortNumeralsPayloadPolynomial_mono

end FoundationCompactPAExponentialShortNumeralTransportMonotonicity
