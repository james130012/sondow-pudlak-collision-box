import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPublicBoundsSyntax
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsCoordinateBounds

/-! # Derived value and bit bounds for a bounded transform endpoint -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPublicBounds

open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsCoordinateBounds
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectData
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPublicBoundsSyntax

theorem compactFormulaTransformInitialFinalBoundedDirectPublicValues_le
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    forall coordinate,
      compactFormulaTransformInitialFinalBoundedDirectPublicValues tokenTable
          width tokenCount stateBoundary stateCount fuel inputBoundary
          inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity coordinate <=
        compactFormulaTransformInitialFinalBoundedDirectNumericBound tokenTable
          width tokenCount stateBoundary stateCount fuel inputBoundary
          inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity
          valueBound := by
  intro coordinate
  fin_cases coordinate <;>
    simp [compactFormulaTransformInitialFinalBoundedDirectPublicValues,
      compactFormulaTransformInitialFinalBoundedDirectNumericBound] <;>
    omega

theorem compactFormulaTransformInitialFinalBoundedDirectValueBound_le
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    valueBound <=
      compactFormulaTransformInitialFinalBoundedDirectNumericBound tokenTable
        width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity valueBound := by
  unfold compactFormulaTransformInitialFinalBoundedDirectNumericBound
  omega

theorem formulaTransformInitialFinalBoundedDirectData_valueBound
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat)
    (data : FormulaTransformInitialFinalBoundedDirectData tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound) :
    FormulaTransformInitialFinalRowsValueBound tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity
      (compactFormulaTransformInitialFinalBoundedDirectNumericBound tokenTable
        width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity valueBound) data.witness := by
  intro coordinate
  rw [compactFormulaTransformInitialFinalRowsEnvironment_eq_directAppend]
  simp only [Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · exact compactFormulaTransformInitialFinalBoundedDirectPublicValues_le
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound
      ⟨coordinate, hcoordinate⟩
  · exact (data.closedWitnessValues_le ⟨coordinate - 13, by omega⟩).trans
      (compactFormulaTransformInitialFinalBoundedDirectValueBound_le
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound)

theorem compactFormulaTransformInitialFinalBoundedDirectNumericSize_le_bitBound
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    Nat.size
        (compactFormulaTransformInitialFinalBoundedDirectNumericBound
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity valueBound) <=
      compactFormulaTransformInitialFinalBoundedDirectBitBound tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity valueBound := by
  simp only [compactFormulaTransformInitialFinalBoundedDirectBitBound]
  omega

theorem compactFormulaTransformInitialFinalBoundedDirectNumeric_le_bitBound
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    compactFormulaTransformInitialFinalBoundedDirectNumericBound tokenTable
        width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity valueBound <=
      compactFormulaTransformInitialFinalBoundedDirectBitBound tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity valueBound := by
  simp only [compactFormulaTransformInitialFinalBoundedDirectBitBound]
  omega

theorem formulaTransformInitialFinalBoundedDirectData_sizeBound
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat)
    (data : FormulaTransformInitialFinalBoundedDirectData tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound) :
    FormulaTransformInitialFinalRowsSizeBound tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity
      (compactFormulaTransformInitialFinalBoundedDirectBitBound tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity valueBound) data.witness := by
  intro coordinate
  exact (Nat.size_le_size
    (formulaTransformInitialFinalBoundedDirectData_valueBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound data coordinate)).trans
    (compactFormulaTransformInitialFinalBoundedDirectNumericSize_le_bitBound
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound)

theorem formulaTransformInitialFinalBoundedDirectData_finalTasksFinishSucc
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat)
    (data : FormulaTransformInitialFinalBoundedDirectData tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound) :
    data.witness.finalCoordinates.parserTasksFinish + 1 <=
      compactFormulaTransformInitialFinalBoundedDirectNumericBound tokenTable
        width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity valueBound := by
  have hvalue := data.closedWitnessValues_le (18 : Fin 31)
  simp [compactFormulaTransformInitialFinalBoundedDirectClosedWitnessValues,
    compactFormulaTransformInitialFinalBoundedDirectInitialWitnessValues,
    compactFormulaTransformInitialFinalBoundedDirectFinalWitnessValues,
    Matrix.vecAppend_eq_ite] at hvalue
  unfold compactFormulaTransformInitialFinalBoundedDirectNumericBound
  omega

theorem compactFormulaTransformInitialFinalBoundedDirectBitBound_positive
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    1 <= compactFormulaTransformInitialFinalBoundedDirectBitBound tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound := by
  simp only [compactFormulaTransformInitialFinalBoundedDirectBitBound]
  omega

#print axioms formulaTransformInitialFinalBoundedDirectData_valueBound
#print axioms formulaTransformInitialFinalBoundedDirectData_sizeBound
#print axioms
  formulaTransformInitialFinalBoundedDirectData_finalTasksFinishSucc

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPublicBounds
