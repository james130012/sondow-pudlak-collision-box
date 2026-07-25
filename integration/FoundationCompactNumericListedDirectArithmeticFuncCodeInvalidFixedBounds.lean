import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidTail01FixedBounds

/-! # Fully fixed graph certificate for invalid arithmetic function codes -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidFixedBounds

open FoundationCompactArithmeticSymbolCode
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidAtomicFixedBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidPairFixedBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidFixedBoundsCore
open FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidTail01FixedBounds

private abbrev funcCodeZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate.zeroValuation

structure ArithmeticFuncCodeInvalidCheckedData (arity code : Nat) : Prop where
  h00 : ¬(arity = 0 ∧ code = 0)
  h01 : ¬(arity = 0 ∧ code = 1)
  h20 : ¬(arity = 2 ∧ code = 0)
  h21 : ¬(arity = 2 ∧ code = 1)

def arithmeticFuncCodeInvalidCheckedDataOfGraph
    (arity code : Nat) (hinvalid : ¬ArithmeticFuncCodeValid arity code) :
    ArithmeticFuncCodeInvalidCheckedData arity code where
  h00 := by
    intro hpair
    exact hinvalid (by simp [ArithmeticFuncCodeValid, hpair])
  h01 := by
    intro hpair
    exact hinvalid (by simp [ArithmeticFuncCodeValid, hpair])
  h20 := by
    intro hpair
    exact hinvalid (by simp [ArithmeticFuncCodeValid, hpair])
  h21 := by
    intro hpair
    exact hinvalid (by simp [ArithmeticFuncCodeValid, hpair])

noncomputable def arithmeticFuncCodeInvalidCertificateFromData
    (arity code : Nat)
    (data : ArithmeticFuncCodeInvalidCheckedData arity code) :
    CheckedHybridValuationBoundedFormulaCertificate funcCodeZeroValuation
      (compactAdditiveArithmeticFuncCodeInvalidExplicitFormula arity code) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (funcCodeInvalidPairCertificate arity 0 code 0 data.h00)
    (funcCodeInvalidTail01Certificate arity code data.h01 data.h20 data.h21)

theorem
    arithmeticFuncCodeInvalidCertificateFromData_structuralPayloadBound_le_fullyFixed
    (arity code bitBound : Nat)
    (data : ArithmeticFuncCodeInvalidCheckedData arity code)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (arithmeticFuncCodeInvalidCertificateFromData arity code data) <=
      compactAdditiveArithmeticFuncCodeInvalidFullyFixedPayloadPolynomial
        bitBound := by
  let certificate00 :=
    funcCodeInvalidPairCertificate arity 0 code 0 data.h00
  let certificate01Tail :=
    funcCodeInvalidTail01Certificate arity code data.h01 data.h20 data.h21
  have hresource00 :=
    funcCodeInvalidPairCertificate_structuralPayloadBound_le_fixed arity 0
      code 0 bitBound data.h00 haritySize hcodeSize (by omega) (by omega)
  have hresource01Tail :=
    funcCodeInvalidTail01Certificate_structuralPayloadBound_le_fixed arity
      code bitBound data.h01 data.h20 data.h21 haritySize hcodeSize
  have hselected :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral certificate00
      certificate01Tail
      (funcCodeInvalidPairFixedPayloadEnvelope bitBound)
      (funcCodeInvalidTail01FixedPayloadEnvelope bitBound)
      (funcCodeFormulaSyntaxFixedPolynomial bitBound)
      hresource00 hresource01Tail (by
        unfold funcCodeFormulaSyntaxFixedPolynomial
        omega)
      (funcCodeInvalidPair00Formula_freeVariables_eq_empty arity code)
      (funcCodeInvalidTail01Formula_freeVariables_eq_empty arity code)
      (funcCodeInvalidPair00Formula_code_length_le_fixed arity code bitBound
        haritySize hcodeSize)
      (funcCodeInvalidTail01Formula_code_length_le_fixed arity code bitBound
        haritySize hcodeSize)
      (by
        simpa only [
          compactAdditiveArithmeticFuncCodeInvalidExplicitFormula_eq_fixedTree,
          funcCodeInvalidPair00Formula]
          using
            compactAdditiveArithmeticFuncCodeInvalidExplicitFormula_code_length_le_fixed
              arity code bitBound haritySize hcodeSize)
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        certificate00 certificate01Tail) <= _
  simpa only [
    compactAdditiveArithmeticFuncCodeInvalidFullyFixedPayloadPolynomial] using
    hselected

noncomputable def
    compactAdditiveArithmeticFuncCodeInvalidFixedCertificateOfGraph
    (arity code : Nat) (hinvalid : ¬ArithmeticFuncCodeValid arity code) :
    CheckedHybridValuationBoundedFormulaCertificate funcCodeZeroValuation
      (compactAdditiveArithmeticFuncCodeInvalidClosedFormula arity code) :=
  .cast
    (compactAdditiveArithmeticFuncCodeInvalidClosedFormula_alignment arity
      code).symm
    (arithmeticFuncCodeInvalidCertificateFromData arity code
      (arithmeticFuncCodeInvalidCheckedDataOfGraph arity code hinvalid))

theorem
    compactAdditiveArithmeticFuncCodeInvalidFixedCertificateOfGraph_structuralPayloadBound_le_fullyFixed
    (arity code bitBound : Nat)
    (hinvalid : ¬ArithmeticFuncCodeValid arity code)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveArithmeticFuncCodeInvalidFixedCertificateOfGraph arity
          code hinvalid) <=
      compactAdditiveArithmeticFuncCodeInvalidFullyFixedPayloadPolynomial
        bitBound := by
  change hybridFormulaStructuralPayloadBound
      (arithmeticFuncCodeInvalidCertificateFromData arity code
        (arithmeticFuncCodeInvalidCheckedDataOfGraph arity code hinvalid)) <= _
  exact
    arithmeticFuncCodeInvalidCertificateFromData_structuralPayloadBound_le_fullyFixed
      arity code bitBound
      (arithmeticFuncCodeInvalidCheckedDataOfGraph arity code hinvalid)
      haritySize hcodeSize

#print axioms
  compactAdditiveArithmeticFuncCodeInvalidFixedCertificateOfGraph_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidFixedBounds
