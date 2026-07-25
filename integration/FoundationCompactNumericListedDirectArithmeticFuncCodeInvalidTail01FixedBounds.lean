import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidTail20FixedBounds

/-! # Fixed certificate for the `(0,1)`, `(2,0)`, `(2,1)` invalid tail -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidTail01FixedBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidAtomicFixedBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidPairFixedBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidFixedBoundsCore
open FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidTail20FixedBounds

private abbrev funcCodeZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate.zeroValuation

noncomputable def funcCodeInvalidTail01Certificate
    (arity code : Nat)
    (h01 : ¬(arity = 0 ∧ code = 1))
    (h20 : ¬(arity = 2 ∧ code = 0))
    (h21 : ¬(arity = 2 ∧ code = 1)) :
    CheckedHybridValuationBoundedFormulaCertificate funcCodeZeroValuation
      (funcCodeInvalidTail01Formula arity code) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (funcCodeInvalidPairCertificate arity 0 code 1 h01)
    (funcCodeInvalidTail20Certificate arity code h20 h21)

theorem funcCodeInvalidTail01Certificate_structuralPayloadBound_le_fixed
    (arity code bitBound : Nat)
    (h01 : ¬(arity = 0 ∧ code = 1))
    (h20 : ¬(arity = 2 ∧ code = 0))
    (h21 : ¬(arity = 2 ∧ code = 1))
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (funcCodeInvalidTail01Certificate arity code h01 h20 h21) <=
      funcCodeInvalidTail01FixedPayloadEnvelope bitBound := by
  let certificate01 :=
    funcCodeInvalidPairCertificate arity 0 code 1 h01
  let certificate20Tail :=
    funcCodeInvalidTail20Certificate arity code h20 h21
  have hresource01 :=
    funcCodeInvalidPairCertificate_structuralPayloadBound_le_fixed arity 0
      code 1 bitBound h01 haritySize hcodeSize (by omega) (by omega)
  have hresource20Tail :=
    funcCodeInvalidTail20Certificate_structuralPayloadBound_le_fixed arity
      code bitBound h20 h21 haritySize hcodeSize
  have hselected :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral certificate01
      certificate20Tail
      (funcCodeInvalidPairFixedPayloadEnvelope bitBound)
      (funcCodeInvalidTail20FixedPayloadEnvelope bitBound)
      (funcCodeFormulaSyntaxFixedPolynomial bitBound)
      hresource01 hresource20Tail (by
        unfold funcCodeFormulaSyntaxFixedPolynomial
        omega)
      (funcCodeInvalidPair01Formula_freeVariables_eq_empty arity code)
      (funcCodeInvalidTail20Formula_freeVariables_eq_empty arity code)
      (funcCodeInvalidPair01Formula_code_length_le_fixed arity code bitBound
        haritySize hcodeSize)
      (funcCodeInvalidTail20Formula_code_length_le_fixed arity code bitBound
        haritySize hcodeSize)
      (funcCodeInvalidTail01Formula_code_length_le_fixed arity code bitBound
        haritySize hcodeSize)
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        certificate01 certificate20Tail) <= _
  simpa only [funcCodeInvalidTail01FixedPayloadEnvelope] using hselected

#print axioms
  funcCodeInvalidTail01Certificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidTail01FixedBounds
