import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidFixedBoundsCore
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds

/-! # Fixed certificate for the `(2,0)` and `(2,1)` invalid-code tail -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidTail20FixedBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidAtomicFixedBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidPairFixedBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidFixedBoundsCore

private abbrev funcCodeZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate.zeroValuation

noncomputable def funcCodeInvalidTail20Certificate
    (arity code : Nat)
    (h20 : ¬(arity = 2 ∧ code = 0))
    (h21 : ¬(arity = 2 ∧ code = 1)) :
    CheckedHybridValuationBoundedFormulaCertificate funcCodeZeroValuation
      (funcCodeInvalidTail20Formula arity code) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (funcCodeInvalidPairCertificate arity 2 code 0 h20)
    (funcCodeInvalidPairCertificate arity 2 code 1 h21)

theorem funcCodeInvalidTail20Certificate_structuralPayloadBound_le_fixed
    (arity code bitBound : Nat)
    (h20 : ¬(arity = 2 ∧ code = 0))
    (h21 : ¬(arity = 2 ∧ code = 1))
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (funcCodeInvalidTail20Certificate arity code h20 h21) <=
      funcCodeInvalidTail20FixedPayloadEnvelope bitBound := by
  let certificate20 :=
    funcCodeInvalidPairCertificate arity 2 code 0 h20
  let certificate21 :=
    funcCodeInvalidPairCertificate arity 2 code 1 h21
  have hresource20 :=
    funcCodeInvalidPairCertificate_structuralPayloadBound_le_fixed arity 2
      code 0 bitBound h20 haritySize hcodeSize (by omega) (by omega)
  have hresource21 :=
    funcCodeInvalidPairCertificate_structuralPayloadBound_le_fixed arity 2
      code 1 bitBound h21 haritySize hcodeSize (by omega) (by omega)
  have hselected :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral certificate20
      certificate21
      (funcCodeInvalidPairFixedPayloadEnvelope bitBound)
      (funcCodeInvalidPairFixedPayloadEnvelope bitBound)
      (funcCodeFormulaSyntaxFixedPolynomial bitBound)
      hresource20 hresource21 (by
        unfold funcCodeFormulaSyntaxFixedPolynomial
        omega)
      (funcCodeInvalidPair20Formula_freeVariables_eq_empty arity code)
      (funcCodeInvalidPair21Formula_freeVariables_eq_empty arity code)
      (funcCodeInvalidPair20Formula_code_length_le_fixed arity code bitBound
        haritySize hcodeSize)
      (funcCodeInvalidPair21Formula_code_length_le_fixed arity code bitBound
        haritySize hcodeSize)
      (funcCodeInvalidTail20Formula_code_length_le_fixed arity code bitBound
        haritySize hcodeSize)
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        certificate20 certificate21) <= _
  simpa only [funcCodeInvalidTail20FixedPayloadEnvelope] using hselected

#print axioms
  funcCodeInvalidTail20Certificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidTail20FixedBounds
