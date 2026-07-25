import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidAtomicFixedBounds
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds

/-! # Fully fixed resource bound for one invalid function-code pair -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidPairFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidAtomicFixedBounds

def funcCodeInvalidPairFixedPayloadEnvelope (bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (funcCodeFormulaSyntaxFixedPolynomial bitBound)
    (funcCodeFixedNeFixedPayloadPolynomial bitBound)

theorem funcCodeInvalidPairFormula_code_length_le_fixed
    (left leftExpected right rightExpected bitBound : Nat)
    (hleftSize : Nat.size left <= bitBound)
    (hrightSize : Nat.size right <= bitBound)
    (hleftExpected : leftExpected <= 2)
    (hrightExpected : rightExpected <= 2) :
    (binaryFormulaCode
      (funcCodeFixedNeFormula left leftExpected ⋎
        funcCodeFixedNeFormula right rightExpected)).length <=
      funcCodeFormulaSyntaxFixedPolynomial bitBound := by
  have hleftCode :=
    funcCodeFixedNeFormula_code_length_le_fixed left leftExpected bitBound
      hleftSize hleftExpected
  have hrightCode :=
    funcCodeFixedNeFormula_code_length_le_fixed right rightExpected bitBound
      hrightSize hrightExpected
  have hraw := binaryFormulaCode_or_length_le_local
    (funcCodeFixedNeFormula left leftExpected)
    (funcCodeFixedNeFormula right rightExpected)
  unfold funcCodeFormulaSyntaxFixedPolynomial
  omega

theorem funcCodeInvalidPairCertificate_structuralPayloadBound_le_fixed
    (left leftExpected right rightExpected bitBound : Nat)
    (hinvalid : ¬(left = leftExpected ∧ right = rightExpected))
    (hleftSize : Nat.size left <= bitBound)
    (hrightSize : Nat.size right <= bitBound)
    (hleftExpected : leftExpected <= 2)
    (hrightExpected : rightExpected <= 2) :
    hybridFormulaStructuralPayloadBound
        (funcCodeInvalidPairCertificate left leftExpected right rightExpected
          hinvalid) <=
      funcCodeInvalidPairFixedPayloadEnvelope bitBound := by
  have hleftCode :=
    funcCodeFixedNeFormula_code_length_le_fixed left leftExpected bitBound
      hleftSize hleftExpected
  have hrightCode :=
    funcCodeFixedNeFormula_code_length_le_fixed right rightExpected bitBound
      hrightSize hrightExpected
  have hfullCode :=
    funcCodeInvalidPairFormula_code_length_le_fixed left leftExpected right
      rightExpected bitBound hleftSize hrightSize hleftExpected
      hrightExpected
  have hpositive : 1 <= funcCodeFormulaSyntaxFixedPolynomial bitBound := by
    unfold funcCodeFormulaSyntaxFixedPolynomial
    omega
  by_cases hleft : left = leftExpected
  · have hright : right ≠ rightExpected := by
      intro hright
      exact hinvalid ⟨hleft, hright⟩
    have hchild :=
      funcCodeFixedNeCertificate_structuralPayloadBound_le_fixed right
        rightExpected bitBound hright hrightSize hrightExpected
    have hselected :=
      checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
        (left := funcCodeFixedNeFormula left leftExpected)
        (funcCodeFixedNeCertificate right rightExpected hright)
        (funcCodeFixedNeFixedPayloadPolynomial bitBound)
        (funcCodeFormulaSyntaxFixedPolynomial bitBound)
        hchild hpositive
        (funcCodeFixedNeFormula_freeVariables_eq_empty left leftExpected)
        (funcCodeFixedNeFormula_freeVariables_eq_empty right rightExpected)
        (hleftCode.trans (by
          unfold funcCodeFormulaSyntaxFixedPolynomial
          omega))
        (hrightCode.trans (by
          unfold funcCodeFormulaSyntaxFixedPolynomial
          omega))
        hfullCode
    simp only [funcCodeInvalidPairCertificate]
    rw [dif_pos hleft]
    simpa only [funcCodeInvalidPairFixedPayloadEnvelope] using hselected
  · have hchild :=
      funcCodeFixedNeCertificate_structuralPayloadBound_le_fixed left
        leftExpected bitBound hleft hleftSize hleftExpected
    have hselected :=
      checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral
        (right := funcCodeFixedNeFormula right rightExpected)
        (funcCodeFixedNeCertificate left leftExpected hleft)
        (funcCodeFixedNeFixedPayloadPolynomial bitBound)
        (funcCodeFormulaSyntaxFixedPolynomial bitBound)
        hchild hpositive
        (funcCodeFixedNeFormula_freeVariables_eq_empty left leftExpected)
        (funcCodeFixedNeFormula_freeVariables_eq_empty right rightExpected)
        (hleftCode.trans (by
          unfold funcCodeFormulaSyntaxFixedPolynomial
          omega))
        (hrightCode.trans (by
          unfold funcCodeFormulaSyntaxFixedPolynomial
          omega))
        hfullCode
    simp only [funcCodeInvalidPairCertificate]
    rw [dif_neg hleft]
    simpa only [funcCodeInvalidPairFixedPayloadEnvelope] using hselected

#print axioms
  funcCodeInvalidPairCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidPairFixedBounds
