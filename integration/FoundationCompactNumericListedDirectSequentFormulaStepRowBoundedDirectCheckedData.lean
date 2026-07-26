import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectTerminalAlignment

/-! # Checked data extracted from one bounded sequent-step row -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData

open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax

structure CompactSequentFormulaStepRowBoundedDirectData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat) where
  row : CompactSequentFormulaStepCoordinates
  values_le : forall coordinate,
    compactSequentFormulaStepRowBoundedDirectWitnessValues row coordinate <=
      valueBound
  graph : CompactSequentFormulaStepGraph tokenTable width tokenCount
    suffixBoundary suffixCount valueBoundary valueCount rowIndex row

noncomputable def compactSequentFormulaStepRowBoundedDirectDataOfBounded
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (hbounded : CompactSequentFormulaStepRowBounded tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex valueBound) :
    CompactSequentFormulaStepRowBoundedDirectData tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex valueBound := by
  have hexists :
      exists row : CompactSequentFormulaStepCoordinates,
        (forall coordinate,
          compactSequentFormulaStepRowBoundedDirectWitnessValues row
            coordinate <= valueBound) ∧
        CompactSequentFormulaStepGraph tokenTable width tokenCount
          suffixBoundary suffixCount valueBoundary valueCount rowIndex row := by
    unfold CompactSequentFormulaStepRowBounded at hbounded
    rcases hbounded with
      ⟨currentStart, hcurrentStart, currentFinish, hcurrentFinish,
        currentBoundary, hcurrentBoundary, currentCount, hcurrentCount,
        currentBoundarySize, hcurrentBoundarySize,
        nextStart, hnextStart, nextFinish, hnextFinish,
        nextBoundary, hnextBoundary, nextCount, hnextCount,
        nextBoundarySize, hnextBoundarySize,
        valueStart, hvalueStart, valueFinish, hvalueFinish,
        valueInnerBoundary, hvalueInnerBoundary,
        valueInnerCount, hvalueInnerCount,
        valueBoundarySize, hvalueBoundarySize,
        parserStateBoundary, hparserStateBoundary,
        parserTableWidth, hparserTableWidth,
        parserValueBound, hparserValueBound, hgraph⟩
    let row := compactSequentFormulaStepRowOfValues
      currentStart currentFinish currentBoundary currentCount
      currentBoundarySize nextStart nextFinish nextBoundary nextCount
      nextBoundarySize valueStart valueFinish valueInnerBoundary
      valueInnerCount valueBoundarySize parserStateBoundary parserTableWidth
      parserValueBound
    refine ⟨row, ?_, ?_⟩
    · intro coordinate
      fin_cases coordinate
      · exact hparserValueBound
      · exact hparserTableWidth
      · exact hparserStateBoundary
      · exact hvalueBoundarySize
      · exact hvalueInnerCount
      · exact hvalueInnerBoundary
      · exact hvalueFinish
      · exact hvalueStart
      · exact hnextBoundarySize
      · exact hnextCount
      · exact hnextBoundary
      · exact hnextFinish
      · exact hnextStart
      · exact hcurrentBoundarySize
      · exact hcurrentCount
      · exact hcurrentBoundary
      · exact hcurrentFinish
      · exact hcurrentStart
    · simpa [row, compactSequentFormulaStepRowOfValues] using hgraph
  let row := Classical.choose hexists
  have hrow := Classical.choose_spec hexists
  exact
    { row := row
      values_le := hrow.1
      graph := hrow.2 }

#print axioms compactSequentFormulaStepRowBoundedDirectDataOfBounded

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
