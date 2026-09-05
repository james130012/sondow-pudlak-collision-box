import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsNativeLeFixedBounds
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
import integration.FoundationCompactListedLocalCostPrimitives

/-! # Closed fixed syntax for term-output-row guard formulas -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 140000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGuardFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAtomicFixedBounds

def termRowsGuardComponentFormulaCodePolynomial (bitBound : Nat) : Nat :=
  outputRowsAtomicFormulaCodePolynomial bitBound

def termRowsGuardFormulaCodePolynomial (bitBound : Nat) : Nat :=
  3 * termRowsGuardComponentFormulaCodePolynomial bitBound + 16

theorem termRowsGuardFormulaCodePolynomial_positive (bitBound : Nat) :
    1 <= termRowsGuardFormulaCodePolynomial bitBound := by
  unfold termRowsGuardFormulaCodePolynomial
  omega

private theorem termRowsAtomicLeafCode_le_guardComponent (bitBound : Nat) :
    outputRowsAtomicLeafFormulaCodePolynomial bitBound <=
      termRowsGuardComponentFormulaCodePolynomial bitBound := by
  unfold termRowsGuardComponentFormulaCodePolynomial
    outputRowsAtomicFormulaCodePolynomial
  omega

theorem termRowsNativeEqFormula_closed
    (left right : ValuationTerm)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (nativeEqFormula left right).freeVariables = ∅ := by
  rw [show nativeEqFormula left right =
      LO.FirstOrder.Semiformula.rel Language.Eq.eq ![left, right] by
    unfold nativeEqFormula
    exact LO.FirstOrder.Semiformula.Operator.eq_def left right]
  exact outputRowsBinaryRelation_closed Language.Eq.eq left right hleft hright

theorem termRowsNativeLtFormula_closed
    (left right : ValuationTerm)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (nativeLtFormula left right).freeVariables = ∅ := by
  rw [show nativeLtFormula left right =
      LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt ![left, right] by
    unfold nativeLtFormula
    exact LO.FirstOrder.Semiformula.Operator.lt_def left right]
  exact outputRowsBinaryRelation_closed Language.ORing.Rel.lt left right
    hleft hright

theorem termRowsNativeLeFormula_closed
    (left right : ValuationTerm)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (nativeLeFormula left right).freeVariables = ∅ := by
  rw [show nativeLeFormula left right =
      LO.FirstOrder.Semiformula.rel Language.Eq.eq ![left, right] ⋎
        LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt ![left, right] by
    unfold nativeLeFormula
    exact LO.FirstOrder.Semiformula.Operator.le_def left right]
  rw [LO.FirstOrder.Semiformula.freeVariables_or,
    outputRowsBinaryRelation_closed Language.Eq.eq left right hleft hright,
    outputRowsBinaryRelation_closed Language.ORing.Rel.lt left right hleft
      hright]
  simp

theorem termRowsNativeEqFormula_code_le_guardComponent
    (left right : ValuationTerm) (bitBound : Nat)
    (hleft : (binaryTermCode left).length <=
      termOutputFailureTermCodePolynomial bitBound)
    (hright : (binaryTermCode right).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    (binaryFormulaCode (nativeEqFormula left right)).length <=
      termRowsGuardComponentFormulaCodePolynomial bitBound := by
  rw [show nativeEqFormula left right =
      LO.FirstOrder.Semiformula.rel Language.Eq.eq ![left, right] by
    unfold nativeEqFormula
    exact LO.FirstOrder.Semiformula.Operator.eq_def left right]
  exact (outputRowsBinaryRelationCode_le Language.Eq.eq left right bitBound
    (by simpa only [termOutputFailureTermCodePolynomial] using hleft)
    (by simpa only [termOutputFailureTermCodePolynomial] using hright)).trans
      (termRowsAtomicLeafCode_le_guardComponent bitBound)

theorem termRowsNativeLtFormula_code_le_guardComponent
    (left right : ValuationTerm) (bitBound : Nat)
    (hleft : (binaryTermCode left).length <=
      termOutputFailureTermCodePolynomial bitBound)
    (hright : (binaryTermCode right).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    (binaryFormulaCode (nativeLtFormula left right)).length <=
      termRowsGuardComponentFormulaCodePolynomial bitBound := by
  rw [show nativeLtFormula left right =
      LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt ![left, right] by
    unfold nativeLtFormula
    exact LO.FirstOrder.Semiformula.Operator.lt_def left right]
  exact (outputRowsBinaryRelationCode_le Language.ORing.Rel.lt left right
    bitBound
    (by simpa only [termOutputFailureTermCodePolynomial] using hleft)
    (by simpa only [termOutputFailureTermCodePolynomial] using hright)).trans
      (termRowsAtomicLeafCode_le_guardComponent bitBound)

theorem termRowsNativeLeFormula_code_le_guardComponent
    (left right : ValuationTerm) (bitBound : Nat)
    (hleft : (binaryTermCode left).length <=
      termOutputFailureTermCodePolynomial bitBound)
    (hright : (binaryTermCode right).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    (binaryFormulaCode (nativeLeFormula left right)).length <=
      termRowsGuardComponentFormulaCodePolynomial bitBound := by
  let equalityFormula :=
    LO.FirstOrder.Semiformula.rel Language.Eq.eq ![left, right]
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt ![left, right]
  have hequality : (binaryFormulaCode equalityFormula).length <=
      outputRowsAtomicLeafFormulaCodePolynomial bitBound :=
    outputRowsBinaryRelationCode_le Language.Eq.eq left right bitBound
      (by simpa only [termOutputFailureTermCodePolynomial] using hleft)
      (by simpa only [termOutputFailureTermCodePolynomial] using hright)
  have hstrict : (binaryFormulaCode strictFormula).length <=
      outputRowsAtomicLeafFormulaCodePolynomial bitBound :=
    outputRowsBinaryRelationCode_le Language.ORing.Rel.lt left right bitBound
      (by simpa only [termOutputFailureTermCodePolynomial] using hleft)
      (by simpa only [termOutputFailureTermCodePolynomial] using hright)
  rw [show nativeLeFormula left right = equalityFormula ⋎ strictFormula by
    unfold nativeLeFormula equalityFormula strictFormula
    exact LO.FirstOrder.Semiformula.Operator.le_def left right]
  simp [binaryFormulaCode] at *
  unfold termRowsGuardComponentFormulaCodePolynomial
    outputRowsAtomicFormulaCodePolynomial
  omega

theorem termRowsTwoGuardFormula_closed
    (formula1 formula2 : ValuationFormula)
    (hformula1 : formula1.freeVariables = ∅)
    (hformula2 : formula2.freeVariables = ∅) :
    (formula1 ⋏ formula2).freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and, hformula1, hformula2]
  simp

theorem termRowsThreeGuardFormula_closed
    (formula1 formula2 formula3 : ValuationFormula)
    (hformula1 : formula1.freeVariables = ∅)
    (hformula2 : formula2.freeVariables = ∅)
    (hformula3 : formula3.freeVariables = ∅) :
    (formula1 ⋏ (formula2 ⋏ formula3)).freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and,
    LO.FirstOrder.Semiformula.freeVariables_and,
    hformula1, hformula2, hformula3]
  simp

theorem termRowsTwoGuardFormula_code_le
    (formula1 formula2 : ValuationFormula) (bitBound : Nat)
    (hformula1 : (binaryFormulaCode formula1).length <=
      termRowsGuardComponentFormulaCodePolynomial bitBound)
    (hformula2 : (binaryFormulaCode formula2).length <=
      termRowsGuardComponentFormulaCodePolynomial bitBound) :
    (binaryFormulaCode (formula1 ⋏ formula2)).length <=
      termRowsGuardFormulaCodePolynomial bitBound := by
  have hraw := binaryFormulaCode_and_length_le formula1 formula2
  unfold termRowsGuardFormulaCodePolynomial
  omega

theorem termRowsThreeGuardFormula_code_le
    (formula1 formula2 formula3 : ValuationFormula) (bitBound : Nat)
    (hformula1 : (binaryFormulaCode formula1).length <=
      termRowsGuardComponentFormulaCodePolynomial bitBound)
    (hformula2 : (binaryFormulaCode formula2).length <=
      termRowsGuardComponentFormulaCodePolynomial bitBound)
    (hformula3 : (binaryFormulaCode formula3).length <=
      termRowsGuardComponentFormulaCodePolynomial bitBound) :
    (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <=
      termRowsGuardFormulaCodePolynomial bitBound := by
  have hinner := binaryFormulaCode_and_length_le formula2 formula3
  have houter := binaryFormulaCode_and_length_le formula1
    (formula2 ⋏ formula3)
  unfold termRowsGuardFormulaCodePolynomial
  omega

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGuardFixedBounds
