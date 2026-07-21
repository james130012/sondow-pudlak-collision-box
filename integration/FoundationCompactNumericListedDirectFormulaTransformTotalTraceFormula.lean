import integration.FoundationCompactNumericListedDirectFormulaTransformInitialDefaultFinalBoundedFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedInstallation
import integration.FoundationCompactNumericListedDirectFormulaTransformEndpointWitnessBound
import integration.FoundationCompactNumericListedDirectFormulaTransformTraceBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy

/-!
# One bounded formula for a total formula-transform trace

The graph joins the genuine initial state, every adjacent transform step, and
the public total final result over one shared state table.  Its explicit table
area hypothesis prevents a valid completed status from being misclassified
merely because an internal bounded witness was chosen too small.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformTotalTraceFormula

open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectParserInitialFormula
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectFormulaTransformTraceInstallation
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialDefaultFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialDefaultFinalBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformFinalDefaultFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedInstallation
open FoundationCompactNumericListedDirectFormulaTransformEndpointWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformTraceBounds
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

def CompactFormulaTransformTotalTraceBoundedGraph
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound : Nat) : Prop :=
  stateCount = fuel + 1 ∧
    (tokenCount + 1) * tokenCount ≤ tableWidth ∧
    CompactFormulaTransformInitialDefaultFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound ∧
    CompactFormulaTransformAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount tableWidth valueBound

def compactFormulaTransformTotalTraceBoundedGraphDef :
    𝚺₀.Semisentence 18 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound.
    stateCount = fuel + 1 ∧
    (tokenCount + 1) * tokenCount ≤ tableWidth ∧
    !(compactFormulaTransformInitialDefaultFinalBoundedDef)
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound ∧
    !(compactFormulaTransformAdjacentRowsBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount tableWidth valueBound”

@[simp] theorem compactFormulaTransformTotalTraceBoundedGraphDef_spec
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound : Nat) :
    compactFormulaTransformTotalTraceBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
          mode, witnessStart, witnessFinish, witnessCount,
          inputBoundary, inputCount, expectedOutputBoundary,
          expectedOutputCount, emptyBoundary, binderArity,
          tableWidth, valueBound] ↔
      CompactFormulaTransformTotalTraceBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        emptyBoundary binderArity tableWidth valueBound := by
  let env : Fin 18 → Nat :=
    ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
      mode, witnessStart, witnessFinish, witnessCount,
      inputBoundary, inputCount, expectedOutputBoundary,
      expectedOutputCount, emptyBoundary, binderArity,
      tableWidth, valueBound]
  change compactFormulaTransformTotalTraceBoundedGraphDef.val.Evalb env ↔ _
  have hinitialFinalEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 18), #1, #2, #3, #4, #5,
          #10, #11, #12, #13, #14, #15, #16, #17]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
          inputBoundary, inputCount, expectedOutputBoundary,
          expectedOutputCount, emptyBoundary, binderArity,
          tableWidth, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hadjacentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 18), #1, #2, #3, #4, #5,
          #6, #7, #8, #9, #16, #17]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
          mode, witnessStart, witnessFinish, witnessCount,
          tableWidth, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htokenCountValue : env 2 = tokenCount := rfl
  have hstateCountValue : env 4 = stateCount := rfl
  have hfuelValue : env 5 = fuel := rfl
  have htableWidthValue : env 16 = tableWidth := rfl
  simp [compactFormulaTransformTotalTraceBoundedGraphDef,
    CompactFormulaTransformTotalTraceBoundedGraph,
    hinitialFinalEnv, hadjacentEnv, htokenCountValue,
    hstateCountValue, hfuelValue, htableWidthValue]

theorem compactFormulaTransformTotalTraceBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformTotalTraceBoundedGraphDef.val := by
  simp [compactFormulaTransformTotalTraceBoundedGraphDef]

private theorem traceState?_eq_some_getI
    {states : List CompactFormulaTransformState} {index : Nat}
    (hindex : index < states.length) :
    compactFormulaTransformTraceState? states index =
      some (states.getI index) := by
  unfold compactFormulaTransformTraceState?
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨hindex, ?_⟩
  rw [List.getI_eq_getElem _ hindex]

theorem CompactFormulaTransformTotalTraceBoundedGraph.sound
    {tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary emptyBoundary
      binderArity tableWidth valueBound : Nat}
    {states : List CompactFormulaTransformState}
    {witness input expectedOutput : List Nat}
    (hgraph : CompactFormulaTransformTotalTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length
      emptyBoundary binderArity tableWidth valueBound)
    (hcount : states.length = stateCount)
    (hrows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hwitnessCount : witnessCount = witness.length)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpectedOutput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedOutputBoundary expectedOutput)
    (hempty : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary []) :
    CompactFormulaTransformLocalTraceValid
        (mode, witness) fuel
        (compactFormulaTransformInitialState binderArity input) states ∧
      expectedOutput =
        (compactExactFormulaTransformResult
          (compactFormulaTransformStateOutput
            (states.getI fuel))).getD [] := by
  rcases hgraph with
    ⟨_hstateCount, harea, hinitialFinalBounded, hadjacent⟩
  have hvalueBound := hadjacent.1
  subst valueBound
  rcases hinitialFinalBounded.exists_witness with
    ⟨endpointWitness, hendpointRows⟩
  have hendpoints :=
    (exists_compactFormulaTransformInitialDefaultFinalRows_iff
      hcount hrows hinput hexpectedOutput hempty harea rfl).mp
        ⟨endpointWitness, hendpointRows⟩
  rcases hendpoints with ⟨hlength, hinitial, hfinalResult⟩
  have hsteps : ∀ stepIndex < fuel,
      states.getI (stepIndex + 1) =
        compactFormulaTransformStep (mode, witness)
          (states.getI stepIndex) := by
    intro stepIndex hstepIndex
    have hbounded := hadjacent.2 stepIndex hstepIndex
    rcases CompactFormulaTransformAdjacentCurrentBounded.sound
        hbounded hwitness hwitnessCount with
      ⟨row, current, next, hrowGraph,
        hcurrentLayout, hnextLayout, hstep⟩
    rcases hrowGraph with ⟨hcurrentAt, hnextAt, _hstepRows⟩
    have hcurrentIndex : stepIndex < states.length := by omega
    have hnextIndex : stepIndex + 1 < states.length := by omega
    rcases exists_compactFormulaTransformStateAtRows_with_fixed_layout
        hrows hcurrentIndex with
      ⟨actualCurrentCoordinates, actualCurrentSize,
        hactualCurrentAt, hactualCurrentLayout⟩
    rcases exists_compactFormulaTransformStateAtRows_with_fixed_layout
        hrows hnextIndex with
      ⟨actualNextCoordinates, actualNextSize,
        hactualNextAt, hactualNextLayout⟩
    have hcurrentStart : actualCurrentCoordinates.start =
        row.currentCoordinates.start :=
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualCurrentAt.2.1).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hcurrentAt.2.1).symm
    have hnextStart : actualNextCoordinates.start =
        row.nextCoordinates.start :=
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualNextAt.2.1).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hnextAt.2.1).symm
    have hcurrentActual : states.getI stepIndex = current :=
      (CompactFormulaTransformStateFixedLayout.eq_and_finish_of_same_start
        hcurrentStart hcurrentLayout hactualCurrentLayout).1
    have hnextActual : states.getI (stepIndex + 1) = next :=
      (CompactFormulaTransformStateFixedLayout.eq_and_finish_of_same_start
        hnextStart hnextLayout hactualNextLayout).1
    rw [hcurrentActual, hnextActual]
    exact hstep
  have hlocal : CompactFormulaTransformLocalTraceValid
      (mode, witness) fuel
      (compactFormulaTransformInitialState binderArity input) states := by
    refine ⟨hlength, ?_, ?_⟩
    · rw [traceState?_eq_some_getI (by omega), hinitial]
    · intro stepIndex hstepIndex
      rw [traceState?_eq_some_getI (by omega),
        traceState?_eq_some_getI (by omega), hsteps stepIndex hstepIndex]
      rfl
  exact ⟨hlocal, hfinalResult⟩

theorem CompactFormulaTransformTotalTraceBoundedGraph.finalLayout_selfContained
    {tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary emptyBoundary
      binderArity tableWidth valueBound : Nat}
    {witness input expectedOutput : List Nat}
    (hgraph : CompactFormulaTransformTotalTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length
      emptyBoundary binderArity tableWidth valueBound)
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hwitnessCount : witnessCount = witness.length)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpectedOutput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedOutputBoundary expectedOutput)
    (hempty : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary []) :
    ∃ finalCoordinates finalSizeWitness,
      CompactFormulaTransformStateAtRows
        tokenTable width tokenCount stateBoundary stateCount fuel
          finalCoordinates finalSizeWitness ∧
      CompactFormulaTransformStateFixedLayout
        tokenTable width tokenCount finalCoordinates
          (compactFormulaTransformStateAt (mode, witness)
            (compactFormulaTransformInitialState binderArity input)
            fuel) ∧
      expectedOutput =
        (compactExactFormulaTransformResult
          (compactFormulaTransformStateOutput
            (compactFormulaTransformStateAt (mode, witness)
              (compactFormulaTransformInitialState binderArity input)
              fuel))).getD [] := by
  rcases hgraph with
    ⟨_hstateCount, harea, hinitialFinalBounded, hadjacent⟩
  have hvalueBound := hadjacent.1
  subst valueBound
  rcases hinitialFinalBounded.exists_witness with
    ⟨endpointWitness, hendpointRows⟩
  rcases CompactFormulaTransformInitialDefaultFinalRows.decode
      hendpointRows hinput hexpectedOutput hempty harea rfl with
    ⟨initialDecoded, finalDecoded, hinitialDecoded,
      hinitialLayout, hfinalLayout, hfinalResult⟩
  have hinitialAt := hendpointRows.2.1
  have hfinalAt := hendpointRows.2.2.2.2.1
  have hstateAt : ∀ index ≤ fuel,
      ∃ coordinates sizeWitness,
        CompactFormulaTransformStateAtRows
          tokenTable width tokenCount stateBoundary stateCount index
            coordinates sizeWitness ∧
        CompactFormulaTransformStateFixedLayout
          tokenTable width tokenCount coordinates
            (compactFormulaTransformStateAt (mode, witness)
              (compactFormulaTransformInitialState binderArity input)
              index) := by
    intro index hindex
    induction index with
    | zero =>
        refine ⟨endpointWitness.initialCoordinates,
          endpointWitness.initialSizeWitness, hinitialAt, ?_⟩
        simpa [compactFormulaTransformStateAt, hinitialDecoded] using
          hinitialLayout
    | succ index ih =>
        have hindexLt : index < fuel := by omega
        rcases ih (by omega) with
          ⟨previousCoordinates, previousSizeWitness,
            hpreviousAt, hpreviousLayout⟩
        have hbounded := hadjacent.2 index hindexLt
        rcases CompactFormulaTransformAdjacentCurrentBounded.sound
            hbounded hwitness hwitnessCount with
          ⟨row, current, next, hrowGraph,
            hcurrentLayout, hnextLayout, hstep⟩
        rcases hrowGraph with ⟨hcurrentAt, hnextAt, _hstepRows⟩
        have hcurrentStart : previousCoordinates.start =
            row.currentCoordinates.start :=
          (CompactFixedWidthEntry.value_eq_tableValue
            hpreviousAt.2.1).trans
              (CompactFixedWidthEntry.value_eq_tableValue
                hcurrentAt.2.1).symm
        have hpreviousCurrent :
            compactFormulaTransformStateAt (mode, witness)
                (compactFormulaTransformInitialState binderArity input)
                index = current :=
          (CompactFormulaTransformStateFixedLayout.eq_and_finish_of_same_start
            hcurrentStart hcurrentLayout hpreviousLayout).1
        have hnext : next =
            compactFormulaTransformStateAt (mode, witness)
              (compactFormulaTransformInitialState binderArity input)
              (index + 1) := by
          rw [hstep, ← hpreviousCurrent]
          simp [compactFormulaTransformStateAt,
            Function.iterate_succ_apply']
        refine ⟨row.nextCoordinates, row.nextSize,
          hnextAt, ?_⟩
        simpa only [hnext] using hnextLayout
  rcases hstateAt fuel (Nat.le_refl fuel) with
    ⟨canonicalCoordinates, canonicalSizeWitness,
      hcanonicalAt, hcanonicalLayout⟩
  have hfinalStart : canonicalCoordinates.start =
      endpointWitness.finalCoordinates.start :=
    (CompactFixedWidthEntry.value_eq_tableValue
      hcanonicalAt.2.1).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          hfinalAt.2.1).symm
  have hcanonicalFinal :
      compactFormulaTransformStateAt (mode, witness)
          (compactFormulaTransformInitialState binderArity input) fuel =
        finalDecoded :=
    (CompactFormulaTransformStateFixedLayout.eq_and_finish_of_same_start
      hfinalStart hfinalLayout hcanonicalLayout).1
  refine ⟨canonicalCoordinates, canonicalSizeWitness,
    hcanonicalAt, hcanonicalLayout, ?_⟩
  simpa only [hcanonicalFinal] using hfinalResult

theorem CompactFormulaTransformTotalTraceBoundedGraph.sound_selfContained
    {tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary emptyBoundary
      binderArity tableWidth valueBound : Nat}
    {witness input expectedOutput : List Nat}
    (hgraph : CompactFormulaTransformTotalTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length
      emptyBoundary binderArity tableWidth valueBound)
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hwitnessCount : witnessCount = witness.length)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpectedOutput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedOutputBoundary expectedOutput)
    (hempty : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary []) :
    expectedOutput =
      (compactExactFormulaTransformResult
        (compactFormulaTransformStateOutput
          (compactFormulaTransformStateAt (mode, witness)
            (compactFormulaTransformInitialState binderArity input)
            fuel))).getD [] := by
  rcases hgraph.finalLayout_selfContained hwitness hwitnessCount
      hinput hexpectedOutput hempty with
    ⟨_finalCoordinates, _finalSizeWitness, _hfinalAt,
      _hfinalLayout, hresult⟩
  exact hresult

theorem localTrace_exists_compactFormulaTransformTotalTraceBoundedFormula_with_width_bound
    {tokenTable width tokenCount stateBoundary fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary emptyBoundary binderArity : Nat}
    {states : List CompactFormulaTransformState}
    {witness input expectedOutput : List Nat}
    (hrows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hwitnessCount : witnessCount = witness.length)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpectedOutput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedOutputBoundary expectedOutput)
    (hempty : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary [])
    (hvalid : CompactFormulaTransformLocalTraceValid
      (mode, witness) fuel
        (compactFormulaTransformInitialState binderArity input) states)
    (hfinalResult : expectedOutput =
      (compactExactFormulaTransformResult
        (compactFormulaTransformStateOutput
          (states.getI fuel))).getD []) :
    ∃ tableWidth,
      compactFormulaTransformTotalTraceBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, states.length,
          fuel, mode, witnessStart, witnessFinish, witnessCount,
          inputBoundary, input.length,
          expectedOutputBoundary, expectedOutput.length,
          emptyBoundary, binderArity, tableWidth, 2 ^ tableWidth] ∧
      tableWidth ≤ compactFormulaTransformCanonicalTableWidthBound
        width tokenCount fuel := by
  have hinitial : states.getI 0 =
      compactFormulaTransformInitialState binderArity input := by
    simpa [compactFormulaTransformStateAt] using
      (CompactFormulaTransformLocalTraceValid.getI_eq_stateAt
        hvalid (Nat.zero_le fuel))
  have hlength : states.length = fuel + 1 := hvalid.1
  have hzero : 0 < states.length := by omega
  have hfuel : fuel < states.length := by omega
  rcases exists_compactFormulaTransformStateAtRows_with_fixed_layout
      hrows hzero with
    ⟨initialCoordinates, initialSizeWitness,
      hinitialAt, hinitialLayout⟩
  rcases exists_compactFormulaTransformStateAtRows_with_fixed_layout
      hrows hfuel with
    ⟨finalCoordinates, finalSizeWitness,
      hfinalAt, hfinalLayout⟩
  have hinitialParserState : (states.getI 0).1 =
      (input, [(1, binderArity, 0)], none) := by
    rw [hinitial]
    rfl
  have hinitialParser : CompactUnifiedParserInitialStateRows
      tokenTable width tokenCount initialCoordinates.parser
        inputBoundary input.length 1 binderArity 0 :=
    (compactUnifiedParserInitialStateRows_iff
      hinput hinitialLayout.parserLayout).mpr hinitialParserState
  have hinitialOutputCount : initialCoordinates.outputCount = 0 := by
    rw [hinitialLayout.outputCount_eq, hinitial]
    rfl
  let endpointWitness : CompactFormulaTransformInitialFinalWitnessCoordinates :=
    { initialCoordinates := initialCoordinates
      initialSizeWitness := initialSizeWitness
      finalCoordinates := finalCoordinates
      finalSizeWitness := finalSizeWitness
      finalParserOutputStart := 0
      finalParserOutputBoundary := 0
      finalParserOutputBoundarySize := 0 }
  have hadjacentFit : CompactFormulaTransformStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states :=
    stateListAdjacentStepRowsWithFit_of_localTrace
      hrows hwitness hwitnessCount hvalid
        (compactFormulaTransformInitialState_task_fields_well_formed
          binderArity input)
  let rows := compactFormulaTransformPublicFittingAdjacentStepRows hadjacentFit
  let tableWidth :=
    compactFormulaTransformAdjacentStepDynamicWidth rows +
      (tokenCount + 1) * tokenCount +
      compactFormulaTransformInitialFinalWitnessDynamicWidth endpointWitness
  have hrowsValid : CompactFormulaTransformAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary states.length mode
        witnessStart witnessFinish witnessCount rows :=
    compactFormulaTransformPublicFittingAdjacentStepRows_valid hadjacentFit
  have hfit : CompactFormulaTransformAdjacentStepRowsFit
      tableWidth rows := by
    have hdynamic := compactFormulaTransformAdjacentStepRowsFit_dynamic rows
    intro row hrow column hcolumn
    exact (hdynamic row hrow column hcolumn).trans (by
      dsimp only [tableWidth]
      omega)
  have harea : (tokenCount + 1) * tokenCount ≤ tableWidth := by
    dsimp only [tableWidth]
    omega
  have hfinalDefault : CompactFormulaTransformFinalGetDOutputRows
      tokenTable width tokenCount finalCoordinates
        expectedOutputBoundary expectedOutput.length emptyBoundary
        tableWidth (2 ^ tableWidth) :=
    (compactFormulaTransformFinalGetDOutputRows_iff
      hexpectedOutput hempty hfinalLayout harea rfl).mpr hfinalResult
  have hendpointRows : CompactFormulaTransformInitialDefaultFinalRows
      tokenTable width tokenCount stateBoundary states.length fuel
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length
      emptyBoundary binderArity tableWidth (2 ^ tableWidth)
      endpointWitness := by
    refine ⟨hvalid.1, hinitialAt, hinitialParser,
      hinitialOutputCount, hfinalAt, hfinalDefault, rfl, rfl, rfl⟩
  have hrowFields : ∀ row ∈ rows,
      ∀ value ∈ compactFormulaTransformAdjacentStepRowValues row,
        Nat.size value ≤
          compactFormulaTransformAdjacentStepPublicWidth width tokenCount := by
    intro row hrow value hvalue
    exact (compactFormulaTransformPublicFittingAdjacentStepRows_fit
      hadjacentFit row hrow).value_size_le hvalue
  have hendpointFields : ∀ value ∈
      compactFormulaTransformInitialFinalWitnessValues endpointWitness,
      Nat.size value ≤
        compactFormulaTransformAdjacentStepPublicWidth width tokenCount :=
    CompactFormulaTransformInitialDefaultFinalRows.endpointValuesFit
      hendpointRows
  have htableWidth : tableWidth ≤
      compactFormulaTransformCanonicalTableWidthBound
        width tokenCount fuel := by
    have hwidthRaw :=
      compactFormulaTransformTableWidth_le_of_fieldSizeBounds
        (tokenCount := tokenCount) hrowFields hendpointFields
    dsimp only [tableWidth]
    calc
      compactFormulaTransformAdjacentStepDynamicWidth rows +
            (tokenCount + 1) * tokenCount +
            compactFormulaTransformInitialFinalWitnessDynamicWidth
              endpointWitness ≤
          rows.length * compactFormulaTransformAdjacentStepWitnessColumnCount *
              compactFormulaTransformAdjacentStepPublicWidth width tokenCount +
            (tokenCount + 1) * tokenCount +
            31 * compactFormulaTransformAdjacentStepPublicWidth width tokenCount :=
        hwidthRaw
      _ = compactFormulaTransformCanonicalTableWidthBound
          width tokenCount fuel := by
        simp [rows, hvalid.1,
          compactFormulaTransformCanonicalTableWidthBound]
  have hendpointWidth :
      compactFormulaTransformInitialFinalWitnessDynamicWidth
          endpointWitness ≤ tableWidth := by
    simp [tableWidth]
  have hendpointBounded :
      CompactFormulaTransformInitialDefaultFinalBounded
        tokenTable width tokenCount stateBoundary states.length fuel
        inputBoundary input.length
        expectedOutputBoundary expectedOutput.length
        emptyBoundary binderArity tableWidth (2 ^ tableWidth) :=
    CompactFormulaTransformInitialDefaultFinalBounded.of_witness
      hendpointWidth hendpointRows
  have hadjacentBounded : CompactFormulaTransformAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary states.length fuel mode
        witnessStart witnessFinish witnessCount tableWidth
        (2 ^ tableWidth) := by
    refine ⟨rfl, ?_⟩
    intro rowIndex hrowIndex
    have hrowIndexSub : rowIndex < states.length - 1 := by
      rw [hvalid.1]
      omega
    have hrowIndex' : rowIndex < rows.length := by
      simpa [rows] using hrowIndexSub
    have hrowGraph := hrowsValid rowIndex hrowIndex'
    have hrowMem : rows.getI rowIndex ∈ rows := by
      rw [List.getI_eq_getElem _ hrowIndex']
      exact List.getElem_mem hrowIndex'
    have hcurrentStatusLayout : CompactBinaryNatStreamStatusDirectLayout
        tokenTable width tokenCount
          (rows.getI rowIndex).currentCoordinates.parserTasksFinish
          (rows.getI rowIndex).currentCoordinates.parserFinish
          (states.getI rowIndex).1.2.2 := by
      rw [List.getI_eq_getElem _ hrowIndex']
      simpa [rows, compactFormulaTransformPublicFittingAdjacentStepRows] using
        compactFormulaTransformPublicFittingAdjacentStepRowAt_currentStatusLayout
          hadjacentFit hrowIndexSub
    have hnextStatusLayout : CompactBinaryNatStreamStatusDirectLayout
        tokenTable width tokenCount
          (rows.getI rowIndex).nextCoordinates.parserTasksFinish
          (rows.getI rowIndex).nextCoordinates.parserFinish
          (states.getI (rowIndex + 1)).1.2.2 := by
      rw [List.getI_eq_getElem _ hrowIndex']
      simpa [rows, compactFormulaTransformPublicFittingAdjacentStepRows] using
        compactFormulaTransformPublicFittingAdjacentStepRowAt_nextStatusLayout
          hadjacentFit hrowIndexSub
    exact CompactFormulaTransformAdjacentStepRowGraph.toCurrentBounded
      hrowGraph (hfit (rows.getI rowIndex) hrowMem)
      (CompactBinaryNatStreamStatusDirectLayout.validBounded
        hcurrentStatusLayout harea)
      (CompactBinaryNatStreamStatusDirectLayout.validBounded
        hnextStatusLayout harea)
  refine ⟨tableWidth, ?_, htableWidth⟩
  exact (compactFormulaTransformTotalTraceBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary states.length fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length
      emptyBoundary binderArity tableWidth (2 ^ tableWidth)).mpr
    ⟨hvalid.1, harea, hendpointBounded, hadjacentBounded⟩

theorem localTrace_exists_compactFormulaTransformTotalTraceBoundedFormula
    {tokenTable width tokenCount stateBoundary fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary emptyBoundary binderArity : Nat}
    {states : List CompactFormulaTransformState}
    {witness input expectedOutput : List Nat}
    (hrows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hwitnessCount : witnessCount = witness.length)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpectedOutput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedOutputBoundary expectedOutput)
    (hempty : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary [])
    (hvalid : CompactFormulaTransformLocalTraceValid
      (mode, witness) fuel
        (compactFormulaTransformInitialState binderArity input) states)
    (hfinalResult : expectedOutput =
      (compactExactFormulaTransformResult
        (compactFormulaTransformStateOutput
          (states.getI fuel))).getD []) :
    ∃ tableWidth,
      compactFormulaTransformTotalTraceBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, states.length,
          fuel, mode, witnessStart, witnessFinish, witnessCount,
          inputBoundary, input.length,
          expectedOutputBoundary, expectedOutput.length,
          emptyBoundary, binderArity, tableWidth, 2 ^ tableWidth] := by
  rcases
      localTrace_exists_compactFormulaTransformTotalTraceBoundedFormula_with_width_bound
        hrows hwitness hwitnessCount hinput hexpectedOutput hempty
          hvalid hfinalResult with
    ⟨tableWidth, hformula, _htableWidth⟩
  exact ⟨tableWidth, hformula⟩

#print axioms compactFormulaTransformTotalTraceBoundedGraphDef_spec
#print axioms compactFormulaTransformTotalTraceBoundedGraphDef_sigmaZero
#print axioms CompactFormulaTransformTotalTraceBoundedGraph.sound
#print axioms CompactFormulaTransformTotalTraceBoundedGraph.finalLayout_selfContained
#print axioms CompactFormulaTransformTotalTraceBoundedGraph.sound_selfContained
#print axioms localTrace_exists_compactFormulaTransformTotalTraceBoundedFormula_with_width_bound
#print axioms localTrace_exists_compactFormulaTransformTotalTraceBoundedFormula

end FoundationCompactNumericListedDirectFormulaTransformTotalTraceFormula
