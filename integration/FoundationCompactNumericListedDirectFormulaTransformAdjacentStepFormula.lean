import integration.FoundationCompactNumericListedDirectFormulaTransformTraceInstallation

/-!
# One bounded row for an adjacent formula-transform trace step

The row binds the current and next state coordinates to consecutive entries
of one state-boundary table and checks the complete shared transform-step
graph.  All thirty-seven row witnesses are explicit natural-number columns.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula

open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformTraceInstallation
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout

structure CompactFormulaTransformAdjacentStepRow where
  currentCoordinates : CompactFormulaTransformStateRowCoordinates
  currentSize : CompactFormulaTransformStateCoreSizeWitness
  nextCoordinates : CompactFormulaTransformStateRowCoordinates
  nextSize : CompactFormulaTransformStateCoreSizeWitness
  stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates
  consumedCount : Nat
  mappedHead : Nat

instance : Inhabited CompactFormulaTransformAdjacentStepRow where
  default :=
    { currentCoordinates :=
        { start := 0
          finish := 0
          parserFinish := 0
          parserTokensFinish := 0
          parserTasksFinish := 0
          parserTokensBoundary := 0
          parserTokensCount := 0
          parserTasksBoundary := 0
          parserTasksCount := 0
          outputBoundary := 0
          outputCount := 0 }
      currentSize :=
        { parserTokensBoundarySize := 0
          parserTasksBoundarySize := 0
          outputBoundarySize := 0 }
      nextCoordinates :=
        { start := 0
          finish := 0
          parserFinish := 0
          parserTokensFinish := 0
          parserTasksFinish := 0
          parserTokensBoundary := 0
          parserTokensCount := 0
          parserTasksBoundary := 0
          parserTasksCount := 0
          outputBoundary := 0
          outputCount := 0 }
      nextSize :=
        { parserTokensBoundarySize := 0
          parserTasksBoundarySize := 0
          outputBoundarySize := 0 }
      stepWitness :=
        { slot0 := 0
          slot1 := 0
          slot2 := 0
          slot3 := 0
          slot4 := 0
          slot5 := 0
          slot6 := 0 }
      consumedCount := 0
      mappedHead := 0 }

def CompactFormulaTransformAdjacentStepRowGraph
    (tokenTable width tokenCount stateBoundary stateCount index mode
      witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) : Prop :=
  CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount index
        row.currentCoordinates row.currentSize ∧
    CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount (index + 1)
        row.nextCoordinates row.nextSize ∧
    CompactFormulaTransformStepRows
      tokenTable width tokenCount
        row.currentCoordinates row.nextCoordinates mode row.stepWitness
          row.consumedCount row.mappedHead
            witnessStart witnessFinish witnessCount

def compactFormulaTransformAdjacentStepRowDef : 𝚺₀.Semisentence 47 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount index mode
      witnessStart witnessFinish witnessCount
      currentStart currentFinish currentParserFinish
      currentParserTokensFinish currentParserTasksFinish
      currentParserTokensBoundary currentParserTokensCount
      currentParserTasksBoundary currentParserTasksCount
      currentOutputBoundary currentOutputCount
      currentParserTokensBoundarySize currentParserTasksBoundarySize
      currentOutputBoundarySize
      nextStart nextFinish nextParserFinish
      nextParserTokensFinish nextParserTasksFinish
      nextParserTokensBoundary nextParserTokensCount
      nextParserTasksBoundary nextParserTasksCount
      nextOutputBoundary nextOutputCount
      nextParserTokensBoundarySize nextParserTasksBoundarySize
      nextOutputBoundarySize
      slot0 slot1 slot2 slot3 slot4 slot5 slot6 consumedCount mappedHead.
    !(compactFormulaTransformStateAtRowsDef)
      tokenTable width tokenCount stateBoundary stateCount index
      currentStart currentFinish currentParserFinish
      currentParserTokensFinish currentParserTasksFinish
      currentParserTokensBoundary currentParserTokensCount
      currentParserTasksBoundary currentParserTasksCount
      currentOutputBoundary currentOutputCount
      currentParserTokensBoundarySize currentParserTasksBoundarySize
      currentOutputBoundarySize ∧
    !(compactFormulaTransformStateAtRowsDef)
      tokenTable width tokenCount stateBoundary stateCount (index + 1)
      nextStart nextFinish nextParserFinish
      nextParserTokensFinish nextParserTasksFinish
      nextParserTokensBoundary nextParserTokensCount
      nextParserTasksBoundary nextParserTasksCount
      nextOutputBoundary nextOutputCount
      nextParserTokensBoundarySize nextParserTasksBoundarySize
      nextOutputBoundarySize ∧
    !(compactFormulaTransformStepRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentParserFinish
      currentParserTokensFinish currentParserTasksFinish
      currentParserTokensBoundary currentParserTokensCount
      currentParserTasksBoundary currentParserTasksCount
      currentOutputBoundary currentOutputCount
      nextStart nextFinish nextParserFinish
      nextParserTokensFinish nextParserTasksFinish
      nextParserTokensBoundary nextParserTokensCount
      nextParserTasksBoundary nextParserTasksCount
      nextOutputBoundary nextOutputCount
      mode slot0 slot1 slot2 slot3 slot4 slot5 slot6
      consumedCount mappedHead witnessStart witnessFinish witnessCount”

def compactFormulaTransformAdjacentStepRowEnvironment
    (tokenTable width tokenCount stateBoundary stateCount index mode
      witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) : Fin 47 → Nat :=
  ![tokenTable, width, tokenCount, stateBoundary, stateCount, index, mode,
    witnessStart, witnessFinish, witnessCount,
    row.currentCoordinates.start, row.currentCoordinates.finish,
    row.currentCoordinates.parserFinish,
    row.currentCoordinates.parserTokensFinish,
    row.currentCoordinates.parserTasksFinish,
    row.currentCoordinates.parserTokensBoundary,
    row.currentCoordinates.parserTokensCount,
    row.currentCoordinates.parserTasksBoundary,
    row.currentCoordinates.parserTasksCount,
    row.currentCoordinates.outputBoundary,
    row.currentCoordinates.outputCount,
    row.currentSize.parserTokensBoundarySize,
    row.currentSize.parserTasksBoundarySize,
    row.currentSize.outputBoundarySize,
    row.nextCoordinates.start, row.nextCoordinates.finish,
    row.nextCoordinates.parserFinish,
    row.nextCoordinates.parserTokensFinish,
    row.nextCoordinates.parserTasksFinish,
    row.nextCoordinates.parserTokensBoundary,
    row.nextCoordinates.parserTokensCount,
    row.nextCoordinates.parserTasksBoundary,
    row.nextCoordinates.parserTasksCount,
    row.nextCoordinates.outputBoundary,
    row.nextCoordinates.outputCount,
    row.nextSize.parserTokensBoundarySize,
    row.nextSize.parserTasksBoundarySize,
    row.nextSize.outputBoundarySize,
    row.stepWitness.slot0, row.stepWitness.slot1,
    row.stepWitness.slot2, row.stepWitness.slot3,
    row.stepWitness.slot4, row.stepWitness.slot5,
    row.stepWitness.slot6, row.consumedCount, row.mappedHead]

set_option maxRecDepth 2048 in
@[simp] theorem compactFormulaTransformAdjacentStepRowDef_spec
    (tokenTable width tokenCount stateBoundary stateCount index mode
      witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) :
    compactFormulaTransformAdjacentStepRowDef.val.Evalb
        (compactFormulaTransformAdjacentStepRowEnvironment
          tokenTable width tokenCount stateBoundary stateCount index mode
            witnessStart witnessFinish witnessCount row) ↔
      CompactFormulaTransformAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount index mode
          witnessStart witnessFinish witnessCount row := by
  let env := compactFormulaTransformAdjacentStepRowEnvironment
    tokenTable width tokenCount stateBoundary stateCount index mode
      witnessStart witnessFinish witnessCount row
  change compactFormulaTransformAdjacentStepRowDef.val.Evalb env ↔ _
  have hcurrentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 47), #1, #2, #3, #4, #5,
          #10, #11, #12, #13, #14, #15, #16, #17, #18, #19, #20,
          #21, #22, #23]) =
        compactFormulaTransformStateAtRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount index
            row.currentCoordinates row.currentSize := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hnextEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 47), #1, #2, #3, #4,
          (‘(#5 + 1)’ : Semiterm ℒₒᵣ Empty 47),
          #24, #25, #26, #27, #28, #29, #30, #31, #32, #33, #34,
          #35, #36, #37]) =
        compactFormulaTransformStateAtRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount (index + 1)
            row.nextCoordinates row.nextSize := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hstepEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 47), #1, #2,
          #10, #11, #12, #13, #14, #15, #16, #17, #18, #19, #20,
          #24, #25, #26, #27, #28, #29, #30, #31, #32, #33, #34,
          #6, #38, #39, #40, #41, #42, #43, #44, #45, #46,
          #7, #8, #9]) =
        compactFormulaTransformStepRowsEnvironment
          tokenTable width tokenCount
            row.currentCoordinates row.nextCoordinates mode row.stepWitness
              row.consumedCount row.mappedHead
                witnessStart witnessFinish witnessCount := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactFormulaTransformAdjacentStepRowDef,
    CompactFormulaTransformAdjacentStepRowGraph,
    hcurrentEnv, hnextEnv, hstepEnv]

theorem compactFormulaTransformAdjacentStepRowDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformAdjacentStepRowDef.val := by
  simp [compactFormulaTransformAdjacentStepRowDef]

theorem stateListAdjacentStepRows_iff_exists_adjacentStepRow
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState} :
    CompactFormulaTransformStateListAdjacentStepRows
        tokenTable width tokenCount stateBoundary mode
          witnessStart witnessFinish witnessCount states ↔
      ∀ index < states.length - 1,
        ∃ row : CompactFormulaTransformAdjacentStepRow,
          CompactFormulaTransformAdjacentStepRowGraph
            tokenTable width tokenCount stateBoundary states.length index mode
              witnessStart witnessFinish witnessCount row ∧
          CompactBinaryNatStreamStatusDirectLayout
            tokenTable width tokenCount
              row.currentCoordinates.parserTasksFinish
              row.currentCoordinates.parserFinish
              (states.getI index).1.2.2 ∧
          CompactBinaryNatStreamStatusDirectLayout
            tokenTable width tokenCount
              row.nextCoordinates.parserTasksFinish
              row.nextCoordinates.parserFinish
              (states.getI (index + 1)).1.2.2 := by
  constructor
  · intro hadjacent index hindex
    rcases hadjacent index hindex with
      ⟨currentCoordinates, currentSize, nextCoordinates, nextSize,
        stepWitness, consumedCount, mappedHead,
        hcurrent, hnext, hstep, hcurrentStatus, hnextStatus⟩
    exact ⟨
      { currentCoordinates := currentCoordinates
        currentSize := currentSize
        nextCoordinates := nextCoordinates
        nextSize := nextSize
        stepWitness := stepWitness
        consumedCount := consumedCount
        mappedHead := mappedHead },
      ⟨hcurrent, hnext, hstep⟩, hcurrentStatus, hnextStatus⟩
  · intro hrows index hindex
    rcases hrows index hindex with
      ⟨row, ⟨hcurrent, hnext, hstep⟩, hcurrentStatus, hnextStatus⟩
    exact ⟨row.currentCoordinates, row.currentSize,
      row.nextCoordinates, row.nextSize, row.stepWitness,
      row.consumedCount, row.mappedHead, hcurrent, hnext, hstep,
      hcurrentStatus, hnextStatus⟩

#print axioms compactFormulaTransformAdjacentStepRowDef_spec
#print axioms compactFormulaTransformAdjacentStepRowDef_sigmaZero
#print axioms stateListAdjacentStepRows_iff_exists_adjacentStepRow

end FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
