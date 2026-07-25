import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeLeafFixedBounds

/-!
# Fixed syntax for the four-way raw-mode disjunction
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 160000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeLeafFixedBounds

def rawModeInnerFormula (mode : Nat) : ValuationFormula :=
  rawModeTwoFormula mode ⋎ rawModeFiveFormula mode

def rawModeMiddleFormula (mode : Nat) : ValuationFormula :=
  rawModeOneFormula mode ⋎ rawModeInnerFormula mode

theorem rawModeFormula_eq_fixedShape (mode : Nat) :
    rawModeFormula (shortBinaryNumeralTerm mode) =
      rawModeZeroFormula mode ⋎ rawModeMiddleFormula mode := by
  rfl

def outputRowsRawModeSyntaxPolynomial (bitBound : Nat) : Nat :=
  8 * outputRowsRawModeLeafSyntaxPolynomial bitBound + 1024

private theorem rawModeLeafCode_le_fullSyntax
    (formula : ValuationFormula) (bitBound : Nat)
    (hcode : (binaryFormulaCode formula).length <=
      outputRowsRawModeLeafSyntaxPolynomial bitBound) :
    (binaryFormulaCode formula).length <=
      outputRowsRawModeSyntaxPolynomial bitBound :=
  hcode.trans (by
    unfold outputRowsRawModeSyntaxPolynomial
    omega)

theorem rawModeZeroFormula_closed_code_full
    (mode bitBound : Nat) (hmodeSize : Nat.size mode <= bitBound) :
    (rawModeZeroFormula mode).freeVariables = ∅ ∧
      (binaryFormulaCode (rawModeZeroFormula mode)).length <=
        outputRowsRawModeSyntaxPolynomial bitBound := by
  have h := rawModeZeroFormula_closed_code mode bitBound hmodeSize
  exact ⟨h.1, rawModeLeafCode_le_fullSyntax _ bitBound h.2⟩

theorem rawModeOneFormula_closed_code_full
    (mode bitBound : Nat) (hmodeSize : Nat.size mode <= bitBound) :
    (rawModeOneFormula mode).freeVariables = ∅ ∧
      (binaryFormulaCode (rawModeOneFormula mode)).length <=
        outputRowsRawModeSyntaxPolynomial bitBound := by
  have h := rawModeOneFormula_closed_code mode bitBound hmodeSize
  exact ⟨h.1, rawModeLeafCode_le_fullSyntax _ bitBound h.2⟩

theorem rawModeTwoFormula_closed_code_full
    (mode bitBound : Nat) (hmodeSize : Nat.size mode <= bitBound) :
    (rawModeTwoFormula mode).freeVariables = ∅ ∧
      (binaryFormulaCode (rawModeTwoFormula mode)).length <=
        outputRowsRawModeSyntaxPolynomial bitBound := by
  have h := rawModeTwoFormula_closed_code mode bitBound hmodeSize
  exact ⟨h.1, rawModeLeafCode_le_fullSyntax _ bitBound h.2⟩

theorem rawModeFiveFormula_closed_code_full
    (mode bitBound : Nat) (hmodeSize : Nat.size mode <= bitBound) :
    (rawModeFiveFormula mode).freeVariables = ∅ ∧
      (binaryFormulaCode (rawModeFiveFormula mode)).length <=
        outputRowsRawModeSyntaxPolynomial bitBound := by
  have h := rawModeFiveFormula_closed_code mode bitBound hmodeSize
  exact ⟨h.1, rawModeLeafCode_le_fullSyntax _ bitBound h.2⟩

theorem rawModeInnerFormula_closed_code
    (mode bitBound : Nat) (hmodeSize : Nat.size mode <= bitBound) :
    (rawModeInnerFormula mode).freeVariables = ∅ ∧
      (binaryFormulaCode (rawModeInnerFormula mode)).length <=
        outputRowsRawModeSyntaxPolynomial bitBound := by
  have htwo := rawModeTwoFormula_closed_code mode bitBound hmodeSize
  have hfive := rawModeFiveFormula_closed_code mode bitBound hmodeSize
  constructor
  · unfold rawModeInnerFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_or, htwo.1, hfive.1]
    simp
  · unfold rawModeInnerFormula
    simp only [binaryFormulaCode, List.length_append]
    have htag : (binaryNatCode 5).length <= 32 := by decide
    unfold outputRowsRawModeSyntaxPolynomial
    omega

theorem rawModeMiddleFormula_closed_code
    (mode bitBound : Nat) (hmodeSize : Nat.size mode <= bitBound) :
    (rawModeMiddleFormula mode).freeVariables = ∅ ∧
      (binaryFormulaCode (rawModeMiddleFormula mode)).length <=
        outputRowsRawModeSyntaxPolynomial bitBound := by
  have hone := rawModeOneFormula_closed_code mode bitBound hmodeSize
  have htwo := rawModeTwoFormula_closed_code mode bitBound hmodeSize
  have hfive := rawModeFiveFormula_closed_code mode bitBound hmodeSize
  have hinner := rawModeInnerFormula_closed_code mode bitBound hmodeSize
  constructor
  · unfold rawModeMiddleFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_or, hone.1, hinner.1]
    simp
  · unfold rawModeMiddleFormula rawModeInnerFormula at *
    simp only [binaryFormulaCode, List.length_append] at *
    have htag : (binaryNatCode 5).length <= 32 := by decide
    unfold outputRowsRawModeSyntaxPolynomial
    omega

theorem rawModeFormula_closed_code
    (mode bitBound : Nat) (hmodeSize : Nat.size mode <= bitBound) :
    (rawModeFormula (shortBinaryNumeralTerm mode)).freeVariables = ∅ ∧
      (binaryFormulaCode
        (rawModeFormula (shortBinaryNumeralTerm mode))).length <=
          outputRowsRawModeSyntaxPolynomial bitBound := by
  rw [rawModeFormula_eq_fixedShape]
  have hzero := rawModeZeroFormula_closed_code mode bitBound hmodeSize
  have hone := rawModeOneFormula_closed_code mode bitBound hmodeSize
  have htwo := rawModeTwoFormula_closed_code mode bitBound hmodeSize
  have hfive := rawModeFiveFormula_closed_code mode bitBound hmodeSize
  have hmiddle := rawModeMiddleFormula_closed_code mode bitBound hmodeSize
  constructor
  · rw [LO.FirstOrder.Semiformula.freeVariables_or, hzero.1, hmiddle.1]
    simp
  · unfold rawModeMiddleFormula rawModeInnerFormula at *
    simp only [binaryFormulaCode, List.length_append] at *
    have htag : (binaryNatCode 5).length <= 32 := by decide
    unfold outputRowsRawModeSyntaxPolynomial
    omega

#print axioms rawModeInnerFormula_closed_code
#print axioms rawModeMiddleFormula_closed_code
#print axioms rawModeFormula_closed_code

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeSyntaxFixedBounds
