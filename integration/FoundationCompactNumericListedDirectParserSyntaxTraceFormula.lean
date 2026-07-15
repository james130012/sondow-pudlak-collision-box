import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedInstallation

/-!
# One bounded formula for a complete syntax-parser trace

The endpoint predicate and every adjacent public syntax-parser step share one
state-boundary table and one power-of-two witness bound.  Formula soundness
reconstructs the original typed executable trace, not a detached list of
numeric rows.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxTraceFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxTraceInstallation
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedInstallation
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

def CompactParserSyntaxTraceBoundedGraph
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound : Nat) : Prop :=
  stateCount = fuel + 1 ∧
    CompactParserInitialFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound ∧
    CompactParserSyntaxAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
        tableWidth valueBound

def compactParserSyntaxTraceBoundedGraphDef :
    𝚺₀.Semisentence 15 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound.
    stateCount = fuel + 1 ∧
    !(compactParserInitialFinalBoundedDef)
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound ∧
    !(compactParserSyntaxAdjacentRowsBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount fuel
      tableWidth valueBound”

@[simp] theorem compactParserSyntaxTraceBoundedGraphDef_spec
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound : Nat) :
    compactParserSyntaxTraceBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
          inputBoundary, inputCount, expectedBoundary, expectedCount,
          taskKind, taskBinderArity, taskRepeatCount, tableWidth, valueBound] ↔
      CompactParserSyntaxTraceBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedBoundary expectedCount
        taskKind taskBinderArity taskRepeatCount
        tableWidth valueBound := by
  let env : Fin 15 → Nat :=
    ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
      inputBoundary, inputCount, expectedBoundary, expectedCount,
      taskKind, taskBinderArity, taskRepeatCount, tableWidth, valueBound]
  change compactParserSyntaxTraceBoundedGraphDef.val.Evalb env ↔ _
  have hinitialFinalEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 15), #1, #2, #3, #4, #5,
          #6, #7, #8, #9, #10, #11, #12, #14]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
          inputBoundary, inputCount, expectedBoundary, expectedCount,
          taskKind, taskBinderArity, taskRepeatCount, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hadjacentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 15), #1, #2, #3, #4, #5,
          #13, #14]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
          tableWidth, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hstateCountValue : env 4 = stateCount := rfl
  have hfuelValue : env 5 = fuel := rfl
  simp [compactParserSyntaxTraceBoundedGraphDef,
    CompactParserSyntaxTraceBoundedGraph,
    hinitialFinalEnv, hadjacentEnv, hstateCountValue, hfuelValue]

theorem compactParserSyntaxTraceBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserSyntaxTraceBoundedGraphDef.val := by
  simp [compactParserSyntaxTraceBoundedGraphDef]

private theorem traceState?_eq_some_getI
    {states : List CompactUnifiedParserState} {index : Nat}
    (hindex : index < states.length) :
    compactParserTraceState? states index = some (states.getI index) := by
  unfold compactParserTraceState?
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨hindex, ?_⟩
  rw [List.getI_eq_getElem _ hindex]

private theorem compactSyntaxParserStateOutput_eq_some_iff
    (state : CompactUnifiedParserState) (output : List Nat) :
    compactSyntaxParserStateOutput state = some output ↔
      state.2.2 = some (some output) := by
  rcases state with ⟨tokens, tasks, status⟩
  cases status with
  | none => simp [compactSyntaxParserStateOutput]
  | some inner =>
      cases inner <;> simp [compactSyntaxParserStateOutput]

private theorem parserOutputLocalTraceValid_endpoints
    {fuel taskKind taskBinderArity taskRepeatCount : Nat}
    {input expected : List Nat} {states : List CompactUnifiedParserState}
    (hvalid : CompactParserOutputLocalTraceValid compactSyntaxParserStep fuel
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      (some expected) states) :
    states.length = fuel + 1 ∧
      states.getI 0 =
        (input, [(taskKind, taskBinderArity, taskRepeatCount)], none) ∧
      (states.getI fuel).2.2 = some (some expected) := by
  have hlocal := hvalid.1
  have hlength : states.length = fuel + 1 := hlocal.1
  have hinitial := CompactParserLocalTraceValid.getI_eq_stateAt
    hlocal (Nat.zero_le fuel)
  have hfuelIndex : fuel < states.length := by omega
  have hfinalTrace := traceState?_eq_some_getI hfuelIndex
  have houtput := hvalid.2
  rw [hfinalTrace] at houtput
  have hstateOutput : compactSyntaxParserStateOutput (states.getI fuel) =
      some expected := by
    simpa [compactParserStateOutputOption] using houtput
  exact ⟨hlength,
    (by simpa [compactParserStateAt] using hinitial),
    (compactSyntaxParserStateOutput_eq_some_iff _ _).mp hstateOutput⟩

theorem CompactParserSyntaxTraceBoundedGraph.sound
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary expectedBoundary taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound : Nat}
    {states : List CompactUnifiedParserState}
    {input expected : List Nat}
    (hgraph : CompactParserSyntaxTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary input.length expectedBoundary expected.length
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound)
    (hcount : states.length = stateCount)
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpected : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedBoundary expected) :
    CompactParserOutputLocalTraceValid compactSyntaxParserStep fuel
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      (some expected) states := by
  rcases hgraph with ⟨hstateCount, hinitialFinalBounded, hadjacent⟩
  have hvalueBound := hadjacent.1
  subst valueBound
  rcases hinitialFinalBounded.exists_witness with
    ⟨endpointWitness, hendpointRows⟩
  have hendpoints :=
    (exists_compactUnifiedParserInitialFinalRows_iff
      hcount hrows hinput hexpected).mp ⟨endpointWitness, hendpointRows⟩
  rcases hendpoints with ⟨hlength, hinitial, hfinalStatus⟩
  have hsteps : ∀ stepIndex < fuel,
      states.getI (stepIndex + 1) =
        compactSyntaxParserStep (states.getI stepIndex) := by
    intro stepIndex hstepIndex
    have hbounded := hadjacent.2 stepIndex hstepIndex
    rcases CompactParserSyntaxAdjacentRowBounded.exists_row hbounded with
      ⟨row, hrowGraph, _hcurrentStatus, _hnextStatus⟩
    rcases hrowGraph with ⟨hcurrentAt, hnextAt, hstepRows⟩
    have hcurrentLayout := CompactUnifiedParserStateAtRows.fixedLayout_of_rows
      hcount hrows hcurrentAt
    have hnextLayout := CompactUnifiedParserStateAtRows.fixedLayout_of_rows
      hcount hrows hnextAt
    exact compactUnifiedParserSyntaxStepRows_sound
      hcurrentLayout hnextLayout ⟨row.stepWitness, hstepRows⟩
  have hlocal : CompactParserLocalTraceValid compactSyntaxParserStep fuel
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none) states := by
    refine ⟨hlength, ?_, ?_⟩
    · rw [traceState?_eq_some_getI (by omega), hinitial]
    · intro stepIndex hstepIndex
      rw [traceState?_eq_some_getI (by omega),
        traceState?_eq_some_getI (by omega), hsteps stepIndex hstepIndex]
      rfl
  have houtput : compactParserStateOutputOption
      (compactParserTraceState? states fuel) = some (some expected) := by
    rw [traceState?_eq_some_getI (by omega)]
    change some (compactSyntaxParserStateOutput (states.getI fuel)) =
      some (some expected)
    rw [(compactSyntaxParserStateOutput_eq_some_iff _ _).mpr hfinalStatus]
  exact ⟨hlocal, houtput⟩

theorem localTrace_exists_compactParserSyntaxTraceBoundedFormula
    {tokenTable width tokenCount stateBoundary fuel
      inputBoundary expectedBoundary taskKind taskBinderArity taskRepeatCount :
      Nat}
    {states : List CompactUnifiedParserState}
    {input expected : List Nat}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpected : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedBoundary expected)
    (hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(taskKind, taskBinderArity, taskRepeatCount)])
    (hvalid : CompactParserOutputLocalTraceValid compactSyntaxParserStep fuel
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      (some expected) states) :
    ∃ tableWidth,
      compactParserSyntaxTraceBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, states.length, fuel,
          inputBoundary, input.length, expectedBoundary, expected.length,
          taskKind, taskBinderArity, taskRepeatCount,
          tableWidth, 2 ^ tableWidth] := by
  have hendpoints := parserOutputLocalTraceValid_endpoints hvalid
  rcases (exists_compactUnifiedParserInitialFinalRows_iff
      (Eq.refl states.length) hrows hinput hexpected).mpr hendpoints with
    ⟨endpointWitness, hendpointRows⟩
  have hadjacent : CompactUnifiedParserSyntaxStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states :=
    syntaxStateListAdjacentStepRows_of_localTrace hrows hvalid.1 hstartWell
  let rows := compactParserSyntaxFittingAdjacentStepRows hadjacent
  let tableWidth :=
    compactParserSyntaxAdjacentStepDynamicWidth rows +
      (tokenCount + 1) * tokenCount +
      compactParserInitialFinalWitnessDynamicWidth endpointWitness
  have hrowsValid : CompactParserSyntaxAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary states.length rows :=
    compactParserSyntaxFittingAdjacentStepRows_valid hadjacent
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
      compactParserInitialFinalWitnessDynamicWidth endpointWitness ≤
        tableWidth := by
    simp [tableWidth]
  have hendpointBounded : CompactParserInitialFinalBounded
      tokenTable width tokenCount stateBoundary states.length fuel
      inputBoundary input.length expectedBoundary expected.length
      taskKind taskBinderArity taskRepeatCount (2 ^ tableWidth) :=
    CompactParserInitialFinalBounded.of_witness
      hendpointWidth hendpointRows
  have hadjacentBounded : CompactParserSyntaxAdjacentRowsBoundedGraph
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
    exact CompactParserSyntaxAdjacentStepRowGraph.toBounded
      hrowGraph (hfit (rows.getI rowIndex) hrowMem)
      (CompactBinaryNatStreamStatusDirectLayout.validBounded
        hcurrentStatusLayout harea)
      (CompactBinaryNatStreamStatusDirectLayout.validBounded
        hnextStatusLayout harea)
  refine ⟨tableWidth,
    (compactParserSyntaxTraceBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary states.length fuel
      inputBoundary input.length expectedBoundary expected.length
      taskKind taskBinderArity taskRepeatCount
      tableWidth (2 ^ tableWidth)).mpr ?_⟩
  exact ⟨hvalid.1.1, hendpointBounded, hadjacentBounded⟩

#print axioms compactParserSyntaxTraceBoundedGraphDef_spec
#print axioms compactParserSyntaxTraceBoundedGraphDef_sigmaZero
#print axioms CompactParserSyntaxTraceBoundedGraph.sound
#print axioms localTrace_exists_compactParserSyntaxTraceBoundedFormula

end FoundationCompactNumericListedDirectParserSyntaxTraceFormula
