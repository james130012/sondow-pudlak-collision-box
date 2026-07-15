import integration.FoundationCompactNumericListedDirectParserSyntaxTraceInstallation

/-!
# One bounded row for an adjacent syntax-parser trace step

The row binds two consecutive entries of one parser-state boundary table and
checks the complete 26-variable syntax-step graph.  All twenty-seven local
witness values are explicit natural-number columns.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula

open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxTraceInstallation

structure CompactParserSyntaxAdjacentStepRow where
  currentCoordinates : CompactUnifiedParserStateRowCoordinates
  currentSize : CompactUnifiedParserStateCoreSizeWitness
  nextCoordinates : CompactUnifiedParserStateRowCoordinates
  nextSize : CompactUnifiedParserStateCoreSizeWitness
  stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates

instance : Inhabited CompactParserSyntaxAdjacentStepRow where
  default :=
    { currentCoordinates :=
        { start := 0
          finish := 0
          tokensFinish := 0
          tasksFinish := 0
          tokensBoundary := 0
          tokensCount := 0
          tasksBoundary := 0
          tasksCount := 0 }
      currentSize :=
        { tokensBoundarySize := 0
          tasksBoundarySize := 0 }
      nextCoordinates :=
        { start := 0
          finish := 0
          tokensFinish := 0
          tasksFinish := 0
          tokensBoundary := 0
          tokensCount := 0
          tasksBoundary := 0
          tasksCount := 0 }
      nextSize :=
        { tokensBoundarySize := 0
          tasksBoundarySize := 0 }
      stepWitness :=
        { slot0 := 0
          slot1 := 0
          slot2 := 0
          slot3 := 0
          slot4 := 0
          slot5 := 0
          slot6 := 0 } }

def CompactParserSyntaxAdjacentStepRowGraph
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow) : Prop :=
  CompactUnifiedParserStateAtRows
      tokenTable width tokenCount stateBoundary stateCount index
        row.currentCoordinates row.currentSize ∧
    CompactUnifiedParserStateAtRows
      tokenTable width tokenCount stateBoundary stateCount (index + 1)
        row.nextCoordinates row.nextSize ∧
    CompactUnifiedParserSyntaxStepRows
      tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
        row.stepWitness

def compactParserSyntaxAdjacentStepRowDef : 𝚺₀.Semisentence 33 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount index
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      currentTokensBoundarySize currentTasksBoundarySize
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      nextTokensBoundarySize nextTasksBoundarySize
      slot0 slot1 slot2 slot3 slot4 slot5 slot6.
    !(compactUnifiedParserStateAtRowsDef)
      tokenTable width tokenCount stateBoundary stateCount index
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      currentTokensBoundarySize currentTasksBoundarySize ∧
    !(compactUnifiedParserStateAtRowsDef)
      tokenTable width tokenCount stateBoundary stateCount (index + 1)
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      nextTokensBoundarySize nextTasksBoundarySize ∧
    !(compactUnifiedParserSyntaxStepRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot0 slot1 slot2 slot3 slot4 slot5 slot6”

def compactParserSyntaxAdjacentStepRowEnvironment
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow) : Fin 33 → Nat :=
  ![tokenTable, width, tokenCount, stateBoundary, stateCount, index,
    row.currentCoordinates.start, row.currentCoordinates.finish,
    row.currentCoordinates.tokensFinish, row.currentCoordinates.tasksFinish,
    row.currentCoordinates.tokensBoundary, row.currentCoordinates.tokensCount,
    row.currentCoordinates.tasksBoundary, row.currentCoordinates.tasksCount,
    row.currentSize.tokensBoundarySize, row.currentSize.tasksBoundarySize,
    row.nextCoordinates.start, row.nextCoordinates.finish,
    row.nextCoordinates.tokensFinish, row.nextCoordinates.tasksFinish,
    row.nextCoordinates.tokensBoundary, row.nextCoordinates.tokensCount,
    row.nextCoordinates.tasksBoundary, row.nextCoordinates.tasksCount,
    row.nextSize.tokensBoundarySize, row.nextSize.tasksBoundarySize,
    row.stepWitness.slot0, row.stepWitness.slot1, row.stepWitness.slot2,
    row.stepWitness.slot3, row.stepWitness.slot4, row.stepWitness.slot5,
    row.stepWitness.slot6]

set_option maxRecDepth 2048 in
@[simp] theorem compactParserSyntaxAdjacentStepRowDef_spec
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow) :
    compactParserSyntaxAdjacentStepRowDef.val.Evalb
        (compactParserSyntaxAdjacentStepRowEnvironment
          tokenTable width tokenCount stateBoundary stateCount index row) ↔
      CompactParserSyntaxAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount index row := by
  let env := compactParserSyntaxAdjacentStepRowEnvironment
    tokenTable width tokenCount stateBoundary stateCount index row
  change compactParserSyntaxAdjacentStepRowDef.val.Evalb env ↔ _
  have hcurrentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2, #3, #4, #5,
          #6, #7, #8, #9, #10, #11, #12, #13, #14, #15]) =
        compactUnifiedParserStateAtRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount index
            row.currentCoordinates row.currentSize := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hnextEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2, #3, #4,
          (‘(#5 + 1)’ : Semiterm ℒₒᵣ Empty 33),
          #16, #17, #18, #19, #20, #21, #22, #23, #24, #25]) =
        compactUnifiedParserStateAtRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount (index + 1)
            row.nextCoordinates row.nextSize := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hstepEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
          #6, #7, #8, #9, #10, #11, #12, #13,
          #16, #17, #18, #19, #20, #21, #22, #23,
          #26, #27, #28, #29, #30, #31, #32]) =
        compactUnifiedParserSyntaxStepFormulaEnvironment
          tokenTable width tokenCount row.currentCoordinates
            row.nextCoordinates row.stepWitness := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactParserSyntaxAdjacentStepRowDef,
    CompactParserSyntaxAdjacentStepRowGraph,
    hcurrentEnv, hnextEnv, hstepEnv]

theorem compactParserSyntaxAdjacentStepRowDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserSyntaxAdjacentStepRowDef.val := by
  simp [compactParserSyntaxAdjacentStepRowDef]

theorem syntaxStateListAdjacentStepRows_iff_exists_adjacentStepRow
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState} :
    CompactUnifiedParserSyntaxStateListAdjacentStepRows
        tokenTable width tokenCount stateBoundary states ↔
      ∀ index < states.length - 1,
        ∃ row : CompactParserSyntaxAdjacentStepRow,
          CompactParserSyntaxAdjacentStepRowGraph
            tokenTable width tokenCount stateBoundary states.length index row := by
  constructor
  · intro hadjacent index hindex
    rcases hadjacent index hindex with
      ⟨currentCoordinates, currentSize, nextCoordinates, nextSize,
        stepWitness, hcurrent, hnext, hstep⟩
    exact ⟨
      { currentCoordinates := currentCoordinates
        currentSize := currentSize
        nextCoordinates := nextCoordinates
        nextSize := nextSize
        stepWitness := stepWitness },
      hcurrent, hnext, hstep⟩
  · intro hrows index hindex
    rcases hrows index hindex with
      ⟨row, hcurrent, hnext, hstep⟩
    exact ⟨row.currentCoordinates, row.currentSize,
      row.nextCoordinates, row.nextSize, row.stepWitness,
      hcurrent, hnext, hstep⟩

#print axioms compactParserSyntaxAdjacentStepRowDef_spec
#print axioms compactParserSyntaxAdjacentStepRowDef_sigmaZero
#print axioms syntaxStateListAdjacentStepRows_iff_exists_adjacentStepRow

end FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
