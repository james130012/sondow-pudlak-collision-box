import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsMappedRowsFullyFixedBounds

/-!
# Fixed closed equality leaves for raw output modes
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 160000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeLeafFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAtomicFixedBounds

def rawModeZeroFormula (mode : Nat) : ValuationFormula :=
  nativeEqFormula (shortBinaryNumeralTerm mode) (‘0’ : ValuationTerm)

def rawModeOneFormula (mode : Nat) : ValuationFormula :=
  nativeEqFormula (shortBinaryNumeralTerm mode) (‘1’ : ValuationTerm)

def rawModeTwoFormula (mode : Nat) : ValuationFormula :=
  nativeEqFormula (shortBinaryNumeralTerm mode) (‘2’ : ValuationTerm)

def rawModeFiveFormula (mode : Nat) : ValuationFormula :=
  nativeEqFormula (shortBinaryNumeralTerm mode) (‘5’ : ValuationTerm)

def outputRowsRawModeLeafSyntaxPolynomial (bitBound : Nat) : Nat :=
  outputRowsAtomicLeafFormulaCodePolynomial bitBound + 1

private theorem rawModeLiteralLeaf_closed_code
    (mode bitBound : Nat) (literal : ValuationTerm)
    (hmodeSize : Nat.size mode <= bitBound)
    (hliteral :
      literal = (‘0’ : ValuationTerm) ∨
      literal = (‘1’ : ValuationTerm) ∨
      literal = (‘2’ : ValuationTerm) ∨
      literal = (‘4’ : ValuationTerm) ∨
      literal = (‘5’ : ValuationTerm)) :
    (nativeEqFormula (shortBinaryNumeralTerm mode) literal).freeVariables = ∅ ∧
      (binaryFormulaCode
        (nativeEqFormula (shortBinaryNumeralTerm mode) literal)).length <=
          outputRowsRawModeLeafSyntaxPolynomial bitBound := by
  have hmodeClosed := shortBinaryNumeralTerm_freeVariables_eq_empty mode
  have hliteralClosed := outputRowsModeLiteral_closed literal hliteral
  have hmodeCode := outputRowsShortNumeralCode_le mode bitBound hmodeSize
  have hliteralCode := outputRowsModeLiteralCode_le literal bitBound hliteral
  constructor
  · unfold nativeEqFormula
    exact outputRowsBinaryRelation_closed Language.Eq.eq _ _ hmodeClosed
      hliteralClosed
  · apply Nat.le_trans
      (outputRowsBinaryRelationCode_le Language.Eq.eq _ _ bitBound
        hmodeCode hliteralCode)
    unfold outputRowsRawModeLeafSyntaxPolynomial
    omega

theorem rawModeZeroFormula_closed_code
    (mode bitBound : Nat) (hmodeSize : Nat.size mode <= bitBound) :
    (rawModeZeroFormula mode).freeVariables = ∅ ∧
      (binaryFormulaCode (rawModeZeroFormula mode)).length <=
        outputRowsRawModeLeafSyntaxPolynomial bitBound := by
  unfold rawModeZeroFormula
  exact rawModeLiteralLeaf_closed_code mode bitBound (‘0’ : ValuationTerm)
    hmodeSize (Or.inl rfl)

theorem rawModeOneFormula_closed_code
    (mode bitBound : Nat) (hmodeSize : Nat.size mode <= bitBound) :
    (rawModeOneFormula mode).freeVariables = ∅ ∧
      (binaryFormulaCode (rawModeOneFormula mode)).length <=
        outputRowsRawModeLeafSyntaxPolynomial bitBound := by
  unfold rawModeOneFormula
  exact rawModeLiteralLeaf_closed_code mode bitBound (‘1’ : ValuationTerm)
    hmodeSize (Or.inr (Or.inl rfl))

theorem rawModeTwoFormula_closed_code
    (mode bitBound : Nat) (hmodeSize : Nat.size mode <= bitBound) :
    (rawModeTwoFormula mode).freeVariables = ∅ ∧
      (binaryFormulaCode (rawModeTwoFormula mode)).length <=
        outputRowsRawModeLeafSyntaxPolynomial bitBound := by
  unfold rawModeTwoFormula
  exact rawModeLiteralLeaf_closed_code mode bitBound (‘2’ : ValuationTerm)
    hmodeSize (Or.inr (Or.inr (Or.inl rfl)))

theorem rawModeFiveFormula_closed_code
    (mode bitBound : Nat) (hmodeSize : Nat.size mode <= bitBound) :
    (rawModeFiveFormula mode).freeVariables = ∅ ∧
      (binaryFormulaCode (rawModeFiveFormula mode)).length <=
        outputRowsRawModeLeafSyntaxPolynomial bitBound := by
  unfold rawModeFiveFormula
  exact rawModeLiteralLeaf_closed_code mode bitBound (‘5’ : ValuationTerm)
    hmodeSize (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

#print axioms rawModeZeroFormula_closed_code
#print axioms rawModeOneFormula_closed_code
#print axioms rawModeTwoFormula_closed_code
#print axioms rawModeFiveFormula_closed_code

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeLeafFixedBounds
