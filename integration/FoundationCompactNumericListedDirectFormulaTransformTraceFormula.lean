import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedInstallation
import integration.FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy

/-!
# One bounded formula for a complete formula-transform trace

The endpoint predicate and all adjacent genuine transform steps are joined
over one state-boundary table and one common power-of-two witness bound.  The
soundness theorem reconstructs a genuine local executable trace; shared rows
are glued by direct-layout determinacy rather than by an assumed equality.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformTraceFormula

open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectFormulaTransformTraceInstallation
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedInstallation
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

def CompactFormulaTransformTraceBoundedGraph
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat) : Prop :=
  stateCount = fuel + 1 ∧
    CompactFormulaTransformInitialFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound ∧
    CompactFormulaTransformAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount tableWidth valueBound

def compactFormulaTransformTraceBoundedGraphDef :
    𝚺₀.Semisentence 19 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound.
    stateCount = fuel + 1 ∧
    !(compactFormulaTransformInitialFinalBoundedDef)
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound ∧
    !(compactFormulaTransformAdjacentRowsBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount tableWidth valueBound”

@[simp] theorem compactFormulaTransformTraceBoundedGraphDef_spec
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound : Nat) :
    compactFormulaTransformTraceBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
          mode, witnessStart, witnessFinish, witnessCount,
          inputBoundary, inputCount, expectedOutputBoundary,
          expectedOutputCount, expectedSuffixBoundary, expectedSuffixCount,
          binderArity, tableWidth, valueBound] ↔
      CompactFormulaTransformTraceBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity
        tableWidth valueBound := by
  let env : Fin 19 → Nat :=
    ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
      mode, witnessStart, witnessFinish, witnessCount,
      inputBoundary, inputCount, expectedOutputBoundary,
      expectedOutputCount, expectedSuffixBoundary, expectedSuffixCount,
      binderArity, tableWidth, valueBound]
  change compactFormulaTransformTraceBoundedGraphDef.val.Evalb env ↔ _
  have hinitialFinalEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2, #3, #4, #5,
          #10, #11, #12, #13, #14, #15, #16, #18]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
          inputBoundary, inputCount, expectedOutputBoundary,
          expectedOutputCount, expectedSuffixBoundary, expectedSuffixCount,
          binderArity, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hadjacentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2, #3, #4, #5,
          #6, #7, #8, #9, #17, #18]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
          mode, witnessStart, witnessFinish, witnessCount,
          tableWidth, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hstateCountValue : env 4 = stateCount := rfl
  have hfuelValue : env 5 = fuel := rfl
  simp [compactFormulaTransformTraceBoundedGraphDef,
    CompactFormulaTransformTraceBoundedGraph,
    hinitialFinalEnv, hadjacentEnv, hstateCountValue, hfuelValue]

theorem compactFormulaTransformTraceBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformTraceBoundedGraphDef.val := by
  simp [compactFormulaTransformTraceBoundedGraphDef]

private theorem traceState?_eq_some_getI
    {states : List CompactFormulaTransformState} {index : Nat}
    (hindex : index < states.length) :
    compactFormulaTransformTraceState? states index =
      some (states.getI index) := by
  unfold compactFormulaTransformTraceState?
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨hindex, ?_⟩
  rw [List.getI_eq_getElem _ hindex]

theorem CompactFormulaTransformTraceBoundedGraph.sound
    {tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary expectedSuffixBoundary
      binderArity tableWidth valueBound : Nat}
    {states : List CompactFormulaTransformState}
    {witness input expectedOutput expectedSuffix : List Nat}
    (hgraph : CompactFormulaTransformTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length
      expectedSuffixBoundary expectedSuffix.length binderArity
      tableWidth valueBound)
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
    (hexpectedSuffix : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedSuffixBoundary expectedSuffix) :
    CompactFormulaTransformLocalTraceValid
        (mode, witness) fuel
        (compactFormulaTransformInitialState binderArity input) states ∧
      (states.getI fuel).1.2.2 = some (some expectedSuffix) ∧
      (states.getI fuel).2 = expectedOutput := by
  rcases hgraph with ⟨hstateCount, hinitialFinalBounded, hadjacent⟩
  have hvalueBound := hadjacent.1
  subst valueBound
  rcases hinitialFinalBounded.exists_witness with
    ⟨endpointWitness, hendpointRows⟩
  have hendpoints :=
    (exists_compactFormulaTransformInitialFinalRows_iff
      hcount hrows hinput hexpectedOutput hexpectedSuffix).mp
        ⟨endpointWitness, hendpointRows⟩
  rcases hendpoints with
    ⟨hlength, hinitial, hfinalStatus, hfinalOutput⟩
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
  exact ⟨hlocal, hfinalStatus, hfinalOutput⟩

theorem localTrace_exists_compactFormulaTransformTraceBoundedFormula
    {tokenTable width tokenCount stateBoundary fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary expectedSuffixBoundary
      binderArity : Nat}
    {states : List CompactFormulaTransformState}
    {witness input expectedOutput expectedSuffix : List Nat}
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
    (hexpectedSuffix : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedSuffixBoundary expectedSuffix)
    (hvalid : CompactFormulaTransformLocalTraceValid
      (mode, witness) fuel
        (compactFormulaTransformInitialState binderArity input) states)
    (hfinalStatus : (states.getI fuel).1.2.2 =
      some (some expectedSuffix))
    (hfinalOutput : (states.getI fuel).2 = expectedOutput) :
    ∃ tableWidth,
      compactFormulaTransformTraceBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, states.length,
          fuel, mode, witnessStart, witnessFinish, witnessCount,
          inputBoundary, input.length,
          expectedOutputBoundary, expectedOutput.length,
          expectedSuffixBoundary, expectedSuffix.length, binderArity,
          tableWidth, 2 ^ tableWidth] := by
  have hinitial : states.getI 0 =
      compactFormulaTransformInitialState binderArity input := by
    simpa [compactFormulaTransformStateAt] using
      (CompactFormulaTransformLocalTraceValid.getI_eq_stateAt
        hvalid (Nat.zero_le fuel))
  rcases (exists_compactFormulaTransformInitialFinalRows_iff
      (Eq.refl states.length) hrows hinput
        hexpectedOutput hexpectedSuffix).mpr
      ⟨hvalid.1, hinitial, hfinalStatus, hfinalOutput⟩ with
    ⟨endpointWitness, hendpointRows⟩
  have hadjacent : CompactFormulaTransformStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states :=
    stateListAdjacentStepRows_of_initialLocalTrace
      hrows hwitness hwitnessCount hvalid
  let rows := compactFormulaTransformFittingAdjacentStepRows hadjacent
  let tableWidth :=
    compactFormulaTransformAdjacentStepDynamicWidth rows +
      (tokenCount + 1) * tokenCount +
      compactFormulaTransformInitialFinalWitnessDynamicWidth endpointWitness
  have hrowsValid : CompactFormulaTransformAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary states.length mode
        witnessStart witnessFinish witnessCount rows :=
    compactFormulaTransformFittingAdjacentStepRows_valid hadjacent
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
  have hendpointWidth :
      compactFormulaTransformInitialFinalWitnessDynamicWidth
          endpointWitness ≤ tableWidth := by
    simp [tableWidth]
  have hendpointBounded : CompactFormulaTransformInitialFinalBounded
      tokenTable width tokenCount stateBoundary states.length fuel
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length
      expectedSuffixBoundary expectedSuffix.length binderArity
      (2 ^ tableWidth) :=
    CompactFormulaTransformInitialFinalBounded.of_witness
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
      simpa [rows, compactFormulaTransformFittingAdjacentStepRows] using
        compactFormulaTransformFittingAdjacentStepRowAt_currentStatusLayout
          hadjacent hrowIndexSub
    have hnextStatusLayout : CompactBinaryNatStreamStatusDirectLayout
        tokenTable width tokenCount
          (rows.getI rowIndex).nextCoordinates.parserTasksFinish
          (rows.getI rowIndex).nextCoordinates.parserFinish
          (states.getI (rowIndex + 1)).1.2.2 := by
      rw [List.getI_eq_getElem _ hrowIndex']
      simpa [rows, compactFormulaTransformFittingAdjacentStepRows] using
        compactFormulaTransformFittingAdjacentStepRowAt_nextStatusLayout
          hadjacent hrowIndexSub
    exact CompactFormulaTransformAdjacentStepRowGraph.toCurrentBounded
      hrowGraph (hfit (rows.getI rowIndex) hrowMem)
      (CompactBinaryNatStreamStatusDirectLayout.validBounded
        hcurrentStatusLayout harea)
      (CompactBinaryNatStreamStatusDirectLayout.validBounded
        hnextStatusLayout harea)
  refine ⟨tableWidth,
    (compactFormulaTransformTraceBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary states.length fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length
      expectedSuffixBoundary expectedSuffix.length binderArity
      tableWidth (2 ^ tableWidth)).mpr ?_⟩
  exact ⟨hvalid.1, hendpointBounded, hadjacentBounded⟩

#print axioms compactFormulaTransformTraceBoundedGraphDef_spec
#print axioms compactFormulaTransformTraceBoundedGraphDef_sigmaZero
#print axioms CompactFormulaTransformTraceBoundedGraph.sound
#print axioms localTrace_exists_compactFormulaTransformTraceBoundedFormula

end FoundationCompactNumericListedDirectFormulaTransformTraceFormula
