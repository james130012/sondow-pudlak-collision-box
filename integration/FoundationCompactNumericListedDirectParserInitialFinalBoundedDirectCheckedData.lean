import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectOriginalSourceAlignment

/-! # Checked data extracted from the bounded parser endpoint proposition -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectCheckedData

open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax

structure CompactParserInitialFinalBoundedDirectData
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat) where
  witness : CompactParserInitialFinalWitnessCoordinates
  values_le : ∀ coordinate,
    compactParserInitialFinalBoundedDirectWitnessValues witness coordinate ≤
      valueBound
  graph : CompactUnifiedParserInitialFinalRows tokenTable width tokenCount
    stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
    expectedCount taskKind taskBinderArity taskRepeatCount witness

noncomputable def compactParserInitialFinalBoundedDirectDataOfBounded
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat)
    (hbounded : CompactParserInitialFinalBounded tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount valueBound) :
    CompactParserInitialFinalBoundedDirectData tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount valueBound := by
  have hexists :
      ∃ witness : CompactParserInitialFinalWitnessCoordinates,
        (∀ coordinate,
          compactParserInitialFinalBoundedDirectWitnessValues witness
            coordinate ≤ valueBound) ∧
        CompactUnifiedParserInitialFinalRows tokenTable width tokenCount
          stateBoundary stateCount fuel inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount witness := by
    rcases hbounded with
      ⟨initialStart, hinitialStart, initialFinish, hinitialFinish,
        initialTokensFinish, hinitialTokensFinish,
        initialTasksFinish, hinitialTasksFinish,
        initialTokensBoundary, hinitialTokensBoundary,
        initialTokensCount, hinitialTokensCount,
        initialTasksBoundary, hinitialTasksBoundary,
        initialTasksCount, hinitialTasksCount,
        initialTokensBoundarySize, hinitialTokensBoundarySize,
        initialTasksBoundarySize, hinitialTasksBoundarySize,
        finalStart, hfinalStart, finalFinish, hfinalFinish,
        finalTokensFinish, hfinalTokensFinish,
        finalTasksFinish, hfinalTasksFinish,
        finalTokensBoundary, hfinalTokensBoundary,
        finalTokensCount, hfinalTokensCount,
        finalTasksBoundary, hfinalTasksBoundary,
        finalTasksCount, hfinalTasksCount,
        finalTokensBoundarySize, hfinalTokensBoundarySize,
        finalTasksBoundarySize, hfinalTasksBoundarySize,
        outputStart, houtputStart, outputBoundary, houtputBoundary,
        outputBoundarySize, houtputBoundarySize, hgraph⟩
    let witness := compactParserInitialFinalWitnessOfValues
      initialStart initialFinish initialTokensFinish initialTasksFinish
      initialTokensBoundary initialTokensCount initialTasksBoundary
      initialTasksCount initialTokensBoundarySize initialTasksBoundarySize
      finalStart finalFinish finalTokensFinish finalTasksFinish
      finalTokensBoundary finalTokensCount finalTasksBoundary finalTasksCount
      finalTokensBoundarySize finalTasksBoundarySize outputStart outputBoundary
      outputBoundarySize
    refine ⟨witness, ?_, ?_⟩
    · intro coordinate
      fin_cases coordinate
      · exact houtputBoundarySize
      · exact houtputBoundary
      · exact houtputStart
      · exact hfinalTasksBoundarySize
      · exact hfinalTokensBoundarySize
      · exact hfinalTasksCount
      · exact hfinalTasksBoundary
      · exact hfinalTokensCount
      · exact hfinalTokensBoundary
      · exact hfinalTasksFinish
      · exact hfinalTokensFinish
      · exact hfinalFinish
      · exact hfinalStart
      · exact hinitialTasksBoundarySize
      · exact hinitialTokensBoundarySize
      · exact hinitialTasksCount
      · exact hinitialTasksBoundary
      · exact hinitialTokensCount
      · exact hinitialTokensBoundary
      · exact hinitialTasksFinish
      · exact hinitialTokensFinish
      · exact hinitialFinish
      · exact hinitialStart
    · simpa [witness, compactParserInitialFinalWitnessOfValues,
        compactUnifiedParserStateRowCoordinatesOf] using hgraph
  let witness := Classical.choose hexists
  have hwitness := Classical.choose_spec hexists
  exact
    { witness := witness
      values_le := hwitness.1
      graph := hwitness.2 }

#print axioms compactParserInitialFinalBoundedDirectDataOfBounded

end FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectCheckedData
