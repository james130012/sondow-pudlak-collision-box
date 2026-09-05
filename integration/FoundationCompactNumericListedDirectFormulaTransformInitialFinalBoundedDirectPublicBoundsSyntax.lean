import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectData

/-! # Public scalar bounds for a bounded formula-transform endpoint -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPublicBoundsSyntax

open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax

def compactFormulaTransformInitialFinalBoundedDirectPublicValues
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat) :
    Fin 13 -> Nat :=
  ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
    inputBoundary, inputCount, expectedOutputBoundary, expectedOutputCount,
    expectedSuffixBoundary, expectedSuffixCount, binderArity]

def compactFormulaTransformInitialFinalBoundedDirectNumericBound
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    Nat :=
  tokenTable + width + tokenCount + stateBoundary + stateCount + fuel +
    inputBoundary + inputCount + expectedOutputBoundary +
    expectedOutputCount + expectedSuffixBoundary + expectedSuffixCount +
    binderArity + valueBound + 1

def compactFormulaTransformInitialFinalBoundedDirectBitBound
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    Nat :=
  let numericBound :=
    compactFormulaTransformInitialFinalBoundedDirectNumericBound tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound
  numericBound + Nat.size numericBound + 1

theorem compactFormulaTransformInitialFinalRowsEnvironment_eq_directAppend
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    compactFormulaTransformInitialFinalRowsEnvironment tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity witness =
      Matrix.vecAppend rfl
        (compactFormulaTransformInitialFinalBoundedDirectPublicValues tokenTable
          width tokenCount stateBoundary stateCount fuel inputBoundary
          inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity)
        (compactFormulaTransformInitialFinalBoundedDirectClosedWitnessValues
          witness) := by
  funext coordinate
  fin_cases coordinate <;>
    simp [compactFormulaTransformInitialFinalRowsEnvironment,
      compactFormulaTransformInitialFinalBoundedDirectPublicValues,
      compactFormulaTransformInitialFinalBoundedDirectClosedWitnessValues,
      compactFormulaTransformInitialFinalBoundedDirectInitialWitnessValues,
      compactFormulaTransformInitialFinalBoundedDirectFinalWitnessValues,
      Matrix.vecAppend_eq_ite]

#print axioms
  compactFormulaTransformInitialFinalRowsEnvironment_eq_directAppend

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPublicBoundsSyntax
