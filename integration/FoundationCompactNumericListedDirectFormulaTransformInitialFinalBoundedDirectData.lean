import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectAlignment
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectInitialValueBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectFinalValueBounds

/-! # Checked data extracted from a bounded formula-transform endpoint -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectData

open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectInitialValueBounds
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectFinalValueBounds

structure FormulaTransformInitialFinalBoundedDirectData
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat)
    where
  witness : CompactFormulaTransformInitialFinalWitnessCoordinates
  closedWitnessValues_le : forall coordinate,
    compactFormulaTransformInitialFinalBoundedDirectClosedWitnessValues
      witness coordinate <= valueBound
  graph : CompactFormulaTransformInitialFinalRows tokenTable width tokenCount
    stateBoundary stateCount fuel inputBoundary inputCount
    expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
    expectedSuffixCount binderArity witness

theorem FormulaTransformInitialFinalBoundedDirectData.directWitnessValues_le
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat}
    (data : FormulaTransformInitialFinalBoundedDirectData tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound) :
    forall coordinate,
      compactFormulaTransformInitialFinalBoundedDirectWitnessValues
        data.witness coordinate <= valueBound := by
  intro coordinate
  exact data.closedWitnessValues_le
    (compactFormulaTransformInitialFinalBoundedDirectReverseIndex coordinate)

theorem exists_formulaTransformInitialFinalBoundedDirectDataOfBounded
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat)
    (hbounded : CompactFormulaTransformInitialFinalBounded tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound) :
    ∃ witness : CompactFormulaTransformInitialFinalWitnessCoordinates,
      (∀ coordinate,
        compactFormulaTransformInitialFinalBoundedDirectClosedWitnessValues
          witness coordinate <= valueBound) ∧
      CompactFormulaTransformInitialFinalRows tokenTable width tokenCount
        stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity witness := by
  rcases hbounded with
    ⟨initialStart, hinitialStart,
      initialFinish, hinitialFinish,
      initialParserFinish, hinitialParserFinish,
      initialParserTokensFinish, hinitialParserTokensFinish,
      initialParserTasksFinish, hinitialParserTasksFinish,
      initialParserTokensBoundary, hinitialParserTokensBoundary,
      initialParserTokensCount, hinitialParserTokensCount,
      initialParserTasksBoundary, hinitialParserTasksBoundary,
      initialParserTasksCount, hinitialParserTasksCount,
      initialOutputBoundary, hinitialOutputBoundary,
      initialOutputCount, hinitialOutputCount,
      initialParserTokensBoundarySize, hinitialParserTokensBoundarySize,
      initialParserTasksBoundarySize, hinitialParserTasksBoundarySize,
      initialOutputBoundarySize, hinitialOutputBoundarySize,
      finalStart, hfinalStart,
      finalFinish, hfinalFinish,
      finalParserFinish, hfinalParserFinish,
      finalParserTokensFinish, hfinalParserTokensFinish,
      finalParserTasksFinish, hfinalParserTasksFinish,
      finalParserTokensBoundary, hfinalParserTokensBoundary,
      finalParserTokensCount, hfinalParserTokensCount,
      finalParserTasksBoundary, hfinalParserTasksBoundary,
      finalParserTasksCount, hfinalParserTasksCount,
      finalOutputBoundary, hfinalOutputBoundary,
      finalOutputCount, hfinalOutputCount,
      finalParserTokensBoundarySize, hfinalParserTokensBoundarySize,
      finalParserTasksBoundarySize, hfinalParserTasksBoundarySize,
      finalOutputBoundarySize, hfinalOutputBoundarySize,
      finalParserOutputStart, hfinalParserOutputStart,
      finalParserOutputBoundary, hfinalParserOutputBoundary,
      finalParserOutputBoundarySize, hfinalParserOutputBoundarySize,
      hgraph⟩
  let witness := compactFormulaTransformInitialFinalWitnessOfValues
    initialStart initialFinish initialParserFinish initialParserTokensFinish
    initialParserTasksFinish initialParserTokensBoundary
    initialParserTokensCount initialParserTasksBoundary initialParserTasksCount
    initialOutputBoundary initialOutputCount initialParserTokensBoundarySize
    initialParserTasksBoundarySize initialOutputBoundarySize finalStart
    finalFinish finalParserFinish finalParserTokensFinish
    finalParserTasksFinish finalParserTokensBoundary finalParserTokensCount
    finalParserTasksBoundary finalParserTasksCount finalOutputBoundary
    finalOutputCount finalParserTokensBoundarySize
    finalParserTasksBoundarySize finalOutputBoundarySize finalParserOutputStart
    finalParserOutputBoundary finalParserOutputBoundarySize
  refine ⟨witness, ?_, ?_⟩
  · have hinitial :=
      compactFormulaTransformInitialFinalBoundedDirectInitialWitnessValues_le
        valueBound witness
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using hinitialStart)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using hinitialFinish)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hinitialParserFinish)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hinitialParserTokensFinish)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hinitialParserTasksFinish)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hinitialParserTokensBoundary)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hinitialParserTokensCount)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hinitialParserTasksBoundary)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hinitialParserTasksCount)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hinitialOutputBoundary)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hinitialOutputCount)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hinitialParserTokensBoundarySize)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hinitialParserTasksBoundarySize)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hinitialOutputBoundarySize)
    have hfinal :=
      compactFormulaTransformInitialFinalBoundedDirectFinalWitnessValues_le
        valueBound witness
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using hfinalStart)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using hfinalFinish)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hfinalParserFinish)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hfinalParserTokensFinish)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hfinalParserTasksFinish)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hfinalParserTokensBoundary)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hfinalParserTokensCount)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hfinalParserTasksBoundary)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hfinalParserTasksCount)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hfinalOutputBoundary)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hfinalOutputCount)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hfinalParserTokensBoundarySize)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hfinalParserTasksBoundarySize)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hfinalOutputBoundarySize)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hfinalParserOutputStart)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hfinalParserOutputBoundary)
        (by simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
          compactFormulaTransformStateRowCoordinatesOf] using
            hfinalParserOutputBoundarySize)
    intro coordinate
    unfold compactFormulaTransformInitialFinalBoundedDirectClosedWitnessValues
    simp only [Matrix.vecAppend_eq_ite]
    split_ifs with hcoordinate
    · exact hinitial ⟨coordinate, hcoordinate⟩
    · exact hfinal ⟨coordinate - 14, by omega⟩
  · simpa [witness, compactFormulaTransformInitialFinalWitnessOfValues,
      compactFormulaTransformStateRowCoordinatesOf] using hgraph

noncomputable def formulaTransformInitialFinalBoundedDirectDataOfBounded
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat)
    (hbounded : CompactFormulaTransformInitialFinalBounded tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound) :
    FormulaTransformInitialFinalBoundedDirectData tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound := by
  let existsData :=
    exists_formulaTransformInitialFinalBoundedDirectDataOfBounded tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound hbounded
  exact
    { witness := Classical.choose existsData
      closedWitnessValues_le := (Classical.choose_spec existsData).1
      graph := (Classical.choose_spec existsData).2 }

#print axioms exists_formulaTransformInitialFinalBoundedDirectDataOfBounded
#print axioms formulaTransformInitialFinalBoundedDirectDataOfBounded

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectData
