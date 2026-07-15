import integration.FoundationCompactNumericListedDirectParserNoOutputInitialFinalBoundedFormula
import integration.FoundationCompactNumericListedDirectParserClosedAdjacentStepBoundedInstallation

/-!
# One bounded formula for a complete no-output closed-parser trace

The endpoint and every adjacent public closed-parser step share one state
table and one power-of-two witness bound.  The endpoint follows the parser's
exact `none` result semantics: either a running status or an explicit failure.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserClosedNoOutputTraceFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserNoOutputInitialFinalFormula
open FoundationCompactNumericListedDirectParserNoOutputInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxTraceInstallation
open FoundationCompactNumericListedDirectParserClosedStepFormula
open FoundationCompactNumericListedDirectParserClosedAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectParserClosedAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserClosedAdjacentStepBoundedInstallation
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

def CompactParserClosedNoOutputTraceBoundedGraph
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound : Nat) : Prop :=
  stateCount = fuel + 1 ∧
    CompactParserNoOutputInitialFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      valueBound ∧
    CompactParserClosedAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
        tableWidth valueBound

def compactParserClosedNoOutputTraceBoundedGraphDef :
    𝚺₀.Semisentence 13 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound.
    stateCount = fuel + 1 ∧
    !(compactParserNoOutputInitialFinalBoundedDef)
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      valueBound ∧
    !(compactParserClosedAdjacentRowsBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount fuel
      tableWidth valueBound”

@[simp] theorem compactParserClosedNoOutputTraceBoundedGraphDef_spec
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound : Nat) :
    compactParserClosedNoOutputTraceBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
          inputBoundary, inputCount, taskKind, taskBinderArity,
          taskRepeatCount, tableWidth, valueBound] ↔
      CompactParserClosedNoOutputTraceBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
        tableWidth valueBound := by
  let env : Fin 13 → Nat :=
    ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
      inputBoundary, inputCount, taskKind, taskBinderArity,
      taskRepeatCount, tableWidth, valueBound]
  change compactParserClosedNoOutputTraceBoundedGraphDef.val.Evalb env ↔ _
  have hinitialFinalEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2, #3, #4, #5,
          #6, #7, #8, #9, #10, #12]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
          inputBoundary, inputCount, taskKind, taskBinderArity,
          taskRepeatCount, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hadjacentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2, #3, #4, #5,
          #11, #12]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
          tableWidth, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hstateCountValue : env 4 = stateCount := rfl
  have hfuelValue : env 5 = fuel := rfl
  simp [compactParserClosedNoOutputTraceBoundedGraphDef,
    CompactParserClosedNoOutputTraceBoundedGraph,
    hinitialFinalEnv, hadjacentEnv, hstateCountValue, hfuelValue]

theorem compactParserClosedNoOutputTraceBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserClosedNoOutputTraceBoundedGraphDef.val := by
  simp [compactParserClosedNoOutputTraceBoundedGraphDef]

private theorem traceState?_eq_some_getI
    {states : List CompactUnifiedParserState} {index : Nat}
    (hindex : index < states.length) :
    compactParserTraceState? states index = some (states.getI index) := by
  unfold compactParserTraceState?
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨hindex, ?_⟩
  rw [List.getI_eq_getElem _ hindex]

private theorem parserNoOutputLocalTraceValid_endpoints
    {fuel taskKind taskBinderArity taskRepeatCount : Nat}
    {input : List Nat} {states : List CompactUnifiedParserState}
    (hvalid : CompactParserOutputLocalTraceValid
      FoundationCompactClosedFormulaTokenMachine.compactClosedSyntaxParserStep fuel
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      none states) :
    states.length = fuel + 1 ∧
      states.getI 0 =
        (input, [(taskKind, taskBinderArity, taskRepeatCount)], none) ∧
      compactSyntaxParserStateOutput (states.getI fuel) = none := by
  have hlocal := hvalid.1
  have hlength : states.length = fuel + 1 := hlocal.1
  have hinitial := CompactParserLocalTraceValid.getI_eq_stateAt
    hlocal (Nat.zero_le fuel)
  have hfuelIndex : fuel < states.length := by omega
  have hfinalTrace := traceState?_eq_some_getI hfuelIndex
  have houtput := hvalid.2
  rw [hfinalTrace] at houtput
  have hstateOutput :
      compactSyntaxParserStateOutput (states.getI fuel) = none := by
    simpa [compactParserStateOutputOption] using houtput
  exact ⟨hlength,
    (by simpa [compactParserStateAt] using hinitial), hstateOutput⟩

theorem CompactParserClosedNoOutputTraceBoundedGraph.sound
    {tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound : Nat}
    {states : List CompactUnifiedParserState}
    {input : List Nat}
    (hgraph : CompactParserClosedNoOutputTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary input.length taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound)
    (hcount : states.length = stateCount)
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input) :
    CompactParserOutputLocalTraceValid
      FoundationCompactClosedFormulaTokenMachine.compactClosedSyntaxParserStep fuel
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      none states := by
  rcases hgraph with ⟨hstateCount, hinitialFinalBounded, hadjacent⟩
  have hvalueBound := hadjacent.1
  subst valueBound
  rcases hinitialFinalBounded.exists_witness with
    ⟨endpointWitness, hendpointRows⟩
  have hendpoints :=
    (exists_compactUnifiedParserNoOutputInitialFinalRows_iff
      hcount hrows hinput).mp ⟨endpointWitness, hendpointRows⟩
  rcases hendpoints with ⟨hlength, hinitial, hfinalNoOutput⟩
  have hsteps : ∀ stepIndex < fuel,
      states.getI (stepIndex + 1) =
        FoundationCompactClosedFormulaTokenMachine.compactClosedSyntaxParserStep
          (states.getI stepIndex) := by
    intro stepIndex hstepIndex
    have hbounded := hadjacent.2 stepIndex hstepIndex
    rcases CompactParserClosedAdjacentRowBounded.exists_row hbounded with
      ⟨row, hrowGraph, _hcurrentStatus, _hnextStatus⟩
    rcases hrowGraph with ⟨hcurrentAt, hnextAt, hstepRows⟩
    have hcurrentLayout := CompactUnifiedParserStateAtRows.fixedLayout_of_rows
      hcount hrows hcurrentAt
    have hnextLayout := CompactUnifiedParserStateAtRows.fixedLayout_of_rows
      hcount hrows hnextAt
    exact compactUnifiedParserClosedStepRows_sound
      hcurrentLayout hnextLayout ⟨row.stepWitness, hstepRows⟩
  have hlocal : CompactParserLocalTraceValid
      FoundationCompactClosedFormulaTokenMachine.compactClosedSyntaxParserStep fuel
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none) states := by
    refine ⟨hlength, ?_, ?_⟩
    · rw [traceState?_eq_some_getI (by omega), hinitial]
    · intro stepIndex hstepIndex
      rw [traceState?_eq_some_getI (by omega),
        traceState?_eq_some_getI (by omega), hsteps stepIndex hstepIndex]
      rfl
  have houtput : compactParserStateOutputOption
      (compactParserTraceState? states fuel) = some none := by
    rw [traceState?_eq_some_getI (by omega)]
    change some (compactSyntaxParserStateOutput (states.getI fuel)) =
      some none
    rw [hfinalNoOutput]
  exact ⟨hlocal, houtput⟩

theorem localTrace_exists_compactParserClosedNoOutputTraceBoundedFormula
    {tokenTable width tokenCount stateBoundary fuel inputBoundary
      taskKind taskBinderArity taskRepeatCount : Nat}
    {states : List CompactUnifiedParserState}
    {input : List Nat}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(taskKind, taskBinderArity, taskRepeatCount)])
    (hvalid : CompactParserOutputLocalTraceValid
      FoundationCompactClosedFormulaTokenMachine.compactClosedSyntaxParserStep fuel
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      none states) :
    ∃ tableWidth,
      compactParserClosedNoOutputTraceBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, states.length, fuel,
          inputBoundary, input.length, taskKind, taskBinderArity,
          taskRepeatCount, tableWidth, 2 ^ tableWidth] := by
  have hendpoints := parserNoOutputLocalTraceValid_endpoints hvalid
  rcases (exists_compactUnifiedParserNoOutputInitialFinalRows_iff
      (Eq.refl states.length) hrows hinput).mpr hendpoints with
    ⟨endpointWitness, hendpointRows⟩
  have hadjacent : CompactUnifiedParserClosedStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states :=
    closedStateListAdjacentStepRows_of_localTrace
      (fuel := fuel)
      (start :=
        (input, [(taskKind, taskBinderArity, taskRepeatCount)], none))
      hrows hvalid.1 hstartWell
  let rows := compactParserClosedFittingAdjacentStepRows hadjacent
  let tableWidth :=
    compactParserSyntaxAdjacentStepDynamicWidth rows +
      (tokenCount + 1) * tokenCount +
      compactParserNoOutputInitialFinalWitnessDynamicWidth endpointWitness
  have hrowsValid : CompactParserClosedAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary states.length rows :=
    compactParserClosedFittingAdjacentStepRows_valid hadjacent
  have hfit : CompactParserSyntaxAdjacentStepRowsFit tableWidth rows := by
    have hdynamic := compactParserSyntaxAdjacentStepRowsFit_dynamic rows
    intro row hrow column hcolumn
    exact (hdynamic row hrow column hcolumn).trans (by
      dsimp only [tableWidth]
      omega)
  have harea : (tokenCount + 1) * tokenCount ≤ tableWidth := by
    dsimp only [tableWidth]
    omega
  have hendpointWidth :
      compactParserNoOutputInitialFinalWitnessDynamicWidth endpointWitness ≤
        tableWidth := by
    simp [tableWidth]
  have hendpointBounded : CompactParserNoOutputInitialFinalBounded
      tokenTable width tokenCount stateBoundary states.length fuel
      inputBoundary input.length taskKind taskBinderArity taskRepeatCount
      (2 ^ tableWidth) :=
    CompactParserNoOutputInitialFinalBounded.of_witness
      hendpointWidth hendpointRows
  have hadjacentBounded : CompactParserClosedAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary states.length fuel
        tableWidth (2 ^ tableWidth) := by
    refine ⟨rfl, ?_⟩
    intro rowIndex hrowIndex
    have hrowIndexSub : rowIndex < states.length - 1 := by
      rw [hvalid.1.1]
      omega
    have hrowIndex' : rowIndex < rows.length := by
      simpa [rows] using hrowIndexSub
    have hrowGraph := hrowsValid rowIndex hrowIndex'
    have hrowMem : rows.getI rowIndex ∈ rows := by
      rw [List.getI_eq_getElem _ hrowIndex']
      exact List.getElem_mem hrowIndex'
    have hcurrentStatusLayout : CompactBinaryNatStreamStatusDirectLayout
        tokenTable width tokenCount
          (rows.getI rowIndex).currentCoordinates.tasksFinish
          (rows.getI rowIndex).currentCoordinates.finish
          (states.getI rowIndex).2.2 :=
      (CompactUnifiedParserStateAtRows.fixedLayout_of_rows
        rfl hrows hrowGraph.1).statusLayout
    have hnextStatusLayout : CompactBinaryNatStreamStatusDirectLayout
        tokenTable width tokenCount
          (rows.getI rowIndex).nextCoordinates.tasksFinish
          (rows.getI rowIndex).nextCoordinates.finish
          (states.getI (rowIndex + 1)).2.2 :=
      (CompactUnifiedParserStateAtRows.fixedLayout_of_rows
        rfl hrows hrowGraph.2.1).statusLayout
    exact CompactParserClosedAdjacentStepRowGraph.toBounded
      hrowGraph (hfit (rows.getI rowIndex) hrowMem)
      (CompactBinaryNatStreamStatusDirectLayout.validBounded
        hcurrentStatusLayout harea)
      (CompactBinaryNatStreamStatusDirectLayout.validBounded
        hnextStatusLayout harea)
  refine ⟨tableWidth,
    (compactParserClosedNoOutputTraceBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary states.length fuel
      inputBoundary input.length taskKind taskBinderArity taskRepeatCount
      tableWidth (2 ^ tableWidth)).mpr ?_⟩
  exact ⟨hvalid.1.1, hendpointBounded, hadjacentBounded⟩

#print axioms compactParserClosedNoOutputTraceBoundedGraphDef_spec
#print axioms compactParserClosedNoOutputTraceBoundedGraphDef_sigmaZero
#print axioms CompactParserClosedNoOutputTraceBoundedGraph.sound
#print axioms localTrace_exists_compactParserClosedNoOutputTraceBoundedFormula

end FoundationCompactNumericListedDirectParserClosedNoOutputTraceFormula
