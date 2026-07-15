import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
import integration.FoundationCompactNumericListedDirectParserClosedStepFormula

/-!
# Exact adjacent-row formula for the closed-formula parser

Two consecutive rows of one canonical parser-state table are tied to the
complete closed-parser step graph.  Unlike the successful closed-parser
formula, this relation also includes the exact free-variable failure step.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserClosedAdjacentStepFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactClosedFormulaTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxTraceInstallation
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserClosedStepFormula

def CompactParserClosedAdjacentStepRowGraph
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow) : Prop :=
  CompactUnifiedParserStateAtRows
      tokenTable width tokenCount stateBoundary stateCount index
        row.currentCoordinates row.currentSize ∧
    CompactUnifiedParserStateAtRows
      tokenTable width tokenCount stateBoundary stateCount (index + 1)
        row.nextCoordinates row.nextSize ∧
    CompactUnifiedParserClosedStepRows
      tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
        row.stepWitness

def compactParserClosedAdjacentStepRowDef :
    𝚺₀.Semisentence 33 := .mkSigma
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
    !(compactUnifiedParserClosedStepRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot0 slot1 slot2 slot3 slot4 slot5 slot6”

@[simp] theorem compactParserClosedAdjacentStepRowDef_spec
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow) :
    compactParserClosedAdjacentStepRowDef.val.Evalb
        (compactParserSyntaxAdjacentStepRowEnvironment
          tokenTable width tokenCount stateBoundary stateCount index row) ↔
      CompactParserClosedAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount index row := by
  let env := compactParserSyntaxAdjacentStepRowEnvironment
    tokenTable width tokenCount stateBoundary stateCount index row
  change compactParserClosedAdjacentStepRowDef.val.Evalb env ↔ _
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
  simp [compactParserClosedAdjacentStepRowDef,
    CompactParserClosedAdjacentStepRowGraph,
    hcurrentEnv, hnextEnv, hstepEnv]

theorem compactParserClosedAdjacentStepRowDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserClosedAdjacentStepRowDef.val := by
  simp [compactParserClosedAdjacentStepRowDef]

def CompactUnifiedParserClosedStateListAdjacentStepRows
    (tokenTable width tokenCount stateBoundary : Nat)
    (states : List CompactUnifiedParserState) : Prop :=
  ∀ index < states.length - 1,
    ∃ row : CompactParserSyntaxAdjacentStepRow,
      CompactParserClosedAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary states.length index row

theorem compactClosedStateListAdjacentStepRows_iff_exists_row
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState} :
    CompactUnifiedParserClosedStateListAdjacentStepRows
        tokenTable width tokenCount stateBoundary states ↔
      ∀ index < states.length - 1,
        ∃ row : CompactParserSyntaxAdjacentStepRow,
          CompactParserClosedAdjacentStepRowGraph
            tokenTable width tokenCount stateBoundary states.length index row :=
  Iff.rfl

theorem compactClosedSyntaxParserStateAt_task_fields_well_formed
    (start : CompactUnifiedParserState)
    (hstart : CompactSyntaxTaskStackFieldsWellFormed start.2.1)
    (stepIndex : Nat) :
    CompactSyntaxTaskStackFieldsWellFormed
      (compactParserStateAt
        compactClosedSyntaxParserStep start stepIndex).2.1 := by
  induction stepIndex with
  | zero =>
      simpa [compactParserStateAt] using hstart
  | succ stepIndex ih =>
      rw [compactParserStateAt, Function.iterate_succ_apply']
      exact compactClosedSyntaxParserStep_preserves_task_fields_well_formed _ ih

theorem CompactParserLocalTraceValid.getI_closed_task_fields_well_formed
    {fuel : Nat} {start : CompactUnifiedParserState}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid
      compactClosedSyntaxParserStep fuel start states)
    (hstart : CompactSyntaxTaskStackFieldsWellFormed start.2.1)
    {stepIndex : Nat} (hstepIndex : stepIndex ≤ fuel) :
    CompactSyntaxTaskStackFieldsWellFormed
      (states.getI stepIndex).2.1 := by
  rw [CompactParserLocalTraceValid.getI_eq_stateAt hvalid hstepIndex]
  exact compactClosedSyntaxParserStateAt_task_fields_well_formed
    start hstart stepIndex

theorem closedStateListAdjacentStepRows_of_localTrace
    {tokenTable width tokenCount stateBoundary fuel : Nat}
    {start : CompactUnifiedParserState}
    {states : List CompactUnifiedParserState}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hvalid : CompactParserLocalTraceValid
      compactClosedSyntaxParserStep fuel start states)
    (hstart : CompactSyntaxTaskStackFieldsWellFormed start.2.1) :
    CompactUnifiedParserClosedStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states := by
  intro index hindex
  have hstepIndex : index < fuel := by
    rw [hvalid.1] at hindex
    omega
  have hcurrentIndex : index < states.length := by
    rw [hvalid.1]
    omega
  have hnextIndex : index + 1 < states.length := by
    rw [hvalid.1]
    omega
  rcases exists_compactUnifiedParserStateAtRows_with_fixed_layout
      hrows hcurrentIndex with
    ⟨currentCoordinates, currentSize, hcurrentRows, hcurrentFixed⟩
  rcases exists_compactUnifiedParserStateAtRows_with_fixed_layout
      hrows hnextIndex with
    ⟨nextCoordinates, nextSize, hnextRows, hnextFixed⟩
  have hwell : CompactSyntaxTaskStackFieldsWellFormed
      (states.getI index).2.1 :=
    CompactParserLocalTraceValid.getI_closed_task_fields_well_formed
      hvalid hstart (Nat.le_of_lt hstepIndex)
  have hstep : states.getI (index + 1) =
      compactClosedSyntaxParserStep (states.getI index) :=
    CompactParserLocalTraceValid.getI_step hvalid hstepIndex
  rcases compactUnifiedParserClosedStepRows_complete
      hcurrentFixed hnextFixed hwell hstep with
    ⟨stepWitness, hstepRows⟩
  exact ⟨
    { currentCoordinates := currentCoordinates
      currentSize := currentSize
      nextCoordinates := nextCoordinates
      nextSize := nextSize
      stepWitness := stepWitness },
    hcurrentRows, hnextRows, hstepRows⟩

theorem closedStateListAdjacentStepRows_of_formulaLocalTrace
    {tokenTable width tokenCount stateBoundary fuel binderArity : Nat}
    {tokens : List Nat} {states : List CompactUnifiedParserState}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hvalid : CompactParserLocalTraceValid compactClosedSyntaxParserStep fuel
      (compactFormulaParserInitialState binderArity tokens) states) :
    CompactUnifiedParserClosedStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states := by
  exact closedStateListAdjacentStepRows_of_localTrace hrows hvalid
    (compactFormulaParserInitialState_task_fields_well_formed
      binderArity tokens)

theorem CompactParserClosedAdjacentStepRowGraph.sound
    {tokenTable width tokenCount stateBoundary stateCount index : Nat}
    {row : CompactParserSyntaxAdjacentStepRow}
    {current next : CompactUnifiedParserState}
    (hgraph : CompactParserClosedAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount index row)
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount row.currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount row.nextCoordinates next) :
    next = compactClosedSyntaxParserStep current :=
  compactUnifiedParserClosedStepRows_sound hcurrent hnext
    ⟨row.stepWitness, hgraph.2.2⟩

#print axioms compactParserClosedAdjacentStepRowDef_spec
#print axioms compactParserClosedAdjacentStepRowDef_sigmaZero
#print axioms compactClosedSyntaxParserStateAt_task_fields_well_formed
#print axioms CompactParserLocalTraceValid.getI_closed_task_fields_well_formed
#print axioms closedStateListAdjacentStepRows_of_localTrace
#print axioms closedStateListAdjacentStepRows_of_formulaLocalTrace
#print axioms CompactParserClosedAdjacentStepRowGraph.sound

end FoundationCompactNumericListedDirectParserClosedAdjacentStepFormula
