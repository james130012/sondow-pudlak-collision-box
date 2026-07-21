import integration.FoundationCompactNumericListedDirectFormulaTransformTotalTraceFormula

/-!
# Total exact formula-transform results

The complete total trace is fixed at the public syntax-machine fuel bound.
Its output is exactly the executable transform result under `Option.getD []`,
including malformed, failed, running, and nonempty-suffix inputs.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectFormulaTransformTraceInstallation
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformTotalTraceFormula

def CompactFormulaTransformTotalExactBoundedGraph
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound : Nat) : Prop :=
  CompactFormulaTransformTotalTraceBoundedGraph
    tokenTable width tokenCount stateBoundary stateCount
      (16 * (inputCount + 1) * (inputCount + 1) + 8) mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound

def compactFormulaTransformTotalExactBoundedGraphDef :
    𝚺₀.Semisentence 17 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound.
    !(compactFormulaTransformTotalTraceBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount
      (16 * (inputCount + 1) * (inputCount + 1) + 8) mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound”

@[simp] theorem compactFormulaTransformTotalExactBoundedGraphDef_spec
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound : Nat) :
    compactFormulaTransformTotalExactBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, mode,
          witnessStart, witnessFinish, witnessCount,
          inputBoundary, inputCount, expectedOutputBoundary,
          expectedOutputCount, emptyBoundary, binderArity,
          tableWidth, valueBound] ↔
      CompactFormulaTransformTotalExactBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount mode
        witnessStart witnessFinish witnessCount
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        emptyBoundary binderArity tableWidth valueBound := by
  let env : Fin 17 → Nat :=
    ![tokenTable, width, tokenCount, stateBoundary, stateCount, mode,
      witnessStart, witnessFinish, witnessCount,
      inputBoundary, inputCount, expectedOutputBoundary,
      expectedOutputCount, emptyBoundary, binderArity,
      tableWidth, valueBound]
  change compactFormulaTransformTotalExactBoundedGraphDef.val.Evalb env ↔ _
  have htraceEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #3, #4,
          (‘(16 * (#10 + 1) * (#10 + 1) + 8)’ :
            Semiterm ℒₒᵣ Empty 17), #5,
          #6, #7, #8, #9, #10, #11, #12, #13, #14, #15, #16]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount,
          16 * (inputCount + 1) * (inputCount + 1) + 8, mode,
          witnessStart, witnessFinish, witnessCount,
          inputBoundary, inputCount, expectedOutputBoundary,
          expectedOutputCount, emptyBoundary, binderArity,
          tableWidth, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  have htraceSpec :
      (Semiformula.Eval
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #3, #4,
            (‘(16 * (#10 + 1) * (#10 + 1) + 8)’ :
              Semiterm ℒₒᵣ Empty 17), #5,
            #6, #7, #8, #9, #10, #11, #12, #13, #14, #15, #16])
          Empty.elim)
        compactFormulaTransformTotalTraceBoundedGraphDef.val ↔
      CompactFormulaTransformTotalTraceBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount
        (16 * (inputCount + 1) * (inputCount + 1) + 8) mode
        witnessStart witnessFinish witnessCount
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        emptyBoundary binderArity tableWidth valueBound := by
    rw [htraceEnv]
    exact compactFormulaTransformTotalTraceBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary stateCount
      (16 * (inputCount + 1) * (inputCount + 1) + 8) mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound
  simp [compactFormulaTransformTotalExactBoundedGraphDef,
    CompactFormulaTransformTotalExactBoundedGraph, htraceSpec]

theorem compactFormulaTransformTotalExactBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformTotalExactBoundedGraphDef.val := by
  simp [compactFormulaTransformTotalExactBoundedGraphDef]

theorem CompactFormulaTransformTotalExactBoundedGraph.sound
    {tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary emptyBoundary
      binderArity tableWidth valueBound : Nat}
    {states : List CompactFormulaTransformState}
    {witness input expectedOutput : List Nat}
    (hgraph : CompactFormulaTransformTotalExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length emptyBoundary
      binderArity tableWidth valueBound)
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
    expectedOutput =
      (compactExactFormulaTransformResult
        (compactFormulaTransformResult
          (mode, witness) (binderArity, input))).getD [] := by
  let fuel := compactSyntaxRunFuelBound input
  have hgraph' : CompactFormulaTransformTotalTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length
      emptyBoundary binderArity tableWidth valueBound := by
    simpa [CompactFormulaTransformTotalExactBoundedGraph,
      compactSyntaxRunFuelBound, fuel] using hgraph
  rcases CompactFormulaTransformTotalTraceBoundedGraph.sound
      hgraph' hcount hrows hwitness hwitnessCount hinput
        hexpectedOutput hempty with
    ⟨hvalid, hfinalResult⟩
  have hrun : compactFormulaTransformRun
      (mode, witness) (binderArity, input) = states.getI fuel := by
    symm
    simpa [compactFormulaTransformRun,
      compactFormulaTransformStateAt, fuel] using
      (CompactFormulaTransformLocalTraceValid.getI_eq_stateAt
        hvalid (Nat.le_refl fuel))
  simpa [compactFormulaTransformResult, hrun] using hfinalResult

theorem CompactFormulaTransformTotalExactBoundedGraph.sound_selfContained
    {tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary emptyBoundary
      binderArity tableWidth valueBound : Nat}
    {witness input expectedOutput : List Nat}
    (hgraph : CompactFormulaTransformTotalExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length emptyBoundary
      binderArity tableWidth valueBound)
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
        (compactFormulaTransformResult
          (mode, witness) (binderArity, input))).getD [] := by
  let fuel := compactSyntaxRunFuelBound input
  have hgraph' : CompactFormulaTransformTotalTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length
      emptyBoundary binderArity tableWidth valueBound := by
    simpa [CompactFormulaTransformTotalExactBoundedGraph,
      compactSyntaxRunFuelBound, fuel] using hgraph
  have hfinalResult :=
    CompactFormulaTransformTotalTraceBoundedGraph.sound_selfContained
      hgraph' hwitness hwitnessCount hinput hexpectedOutput hempty
  simpa [compactFormulaTransformResult, compactFormulaTransformRun,
    compactFormulaTransformStateAt, fuel] using hfinalResult

theorem CompactFormulaTransformTotalExactBoundedGraph.finalLayout_selfContained
    {tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary emptyBoundary
      binderArity tableWidth valueBound : Nat}
    {witness input expectedOutput : List Nat}
    (hgraph : CompactFormulaTransformTotalExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length emptyBoundary
      binderArity tableWidth valueBound)
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
        tokenTable width tokenCount stateBoundary stateCount
          (compactSyntaxRunFuelBound input)
          finalCoordinates finalSizeWitness ∧
      CompactFormulaTransformStateFixedLayout
        tokenTable width tokenCount finalCoordinates
          (compactFormulaTransformStateAt (mode, witness)
            (compactFormulaTransformInitialState binderArity input)
            (compactSyntaxRunFuelBound input)) ∧
      expectedOutput =
        (compactExactFormulaTransformResult
          (compactFormulaTransformResult
            (mode, witness) (binderArity, input))).getD [] := by
  let fuel := compactSyntaxRunFuelBound input
  have hgraph' : CompactFormulaTransformTotalTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length
      emptyBoundary binderArity tableWidth valueBound := by
    simpa [CompactFormulaTransformTotalExactBoundedGraph,
      compactSyntaxRunFuelBound, fuel] using hgraph
  rcases hgraph'.finalLayout_selfContained hwitness hwitnessCount
      hinput hexpectedOutput hempty with
    ⟨finalCoordinates, finalSizeWitness, hfinalAt,
      hfinalLayout, hresult⟩
  refine ⟨finalCoordinates, finalSizeWitness, ?_, ?_, ?_⟩
  · simpa [fuel] using hfinalAt
  · simpa [fuel] using hfinalLayout
  · simpa [compactFormulaTransformResult, compactFormulaTransformRun,
      compactFormulaTransformStateAt, fuel] using hresult

theorem totalResult_exists_compactFormulaTransformTotalExactBoundedFormula_with_width_bound
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary emptyBoundary binderArity : Nat}
    {witness input expectedOutput : List Nat}
    (hrows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary
        (compactFormulaTransformStateTrace (mode, witness)
          (compactSyntaxRunFuelBound input)
          (compactFormulaTransformInitialState binderArity input)))
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
    (hresult : expectedOutput =
      (compactExactFormulaTransformResult
        (compactFormulaTransformResult
          (mode, witness) (binderArity, input))).getD []) :
    ∃ tableWidth,
      compactFormulaTransformTotalExactBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary,
          (compactSyntaxRunFuelBound input) + 1, mode,
          witnessStart, witnessFinish, witnessCount,
          inputBoundary, input.length,
          expectedOutputBoundary, expectedOutput.length,
          emptyBoundary, binderArity,
          tableWidth, 2 ^ tableWidth] ∧
      tableWidth ≤ compactFormulaTransformCanonicalTableWidthBound
        width tokenCount (compactSyntaxRunFuelBound input) := by
  let fuel := compactSyntaxRunFuelBound input
  let start := compactFormulaTransformInitialState binderArity input
  let states := compactFormulaTransformStateTrace
    (mode, witness) fuel start
  have hlocal : CompactFormulaTransformLocalTraceValid
      (mode, witness) fuel start states :=
    compactFormulaTransformStateTrace_localValid
      (mode, witness) fuel start
  have hfinalEq : states.getI fuel =
      compactFormulaTransformRun
        (mode, witness) (binderArity, input) := by
    simpa [states, start, compactFormulaTransformRun,
      compactFormulaTransformStateAt, fuel] using
      (CompactFormulaTransformLocalTraceValid.getI_eq_stateAt
        hlocal (Nat.le_refl fuel))
  have hfinalResult : expectedOutput =
      (compactExactFormulaTransformResult
        (compactFormulaTransformStateOutput
          (states.getI fuel))).getD [] := by
    simpa [hfinalEq, compactFormulaTransformResult] using hresult
  have hrows' : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary states := by
    simpa [states, start, fuel] using hrows
  rcases
      localTrace_exists_compactFormulaTransformTotalTraceBoundedFormula_with_width_bound
      hrows' hwitness hwitnessCount hinput hexpectedOutput hempty
      hlocal hfinalResult with
    ⟨tableWidth, htrace, htableWidth⟩
  refine ⟨tableWidth, ?_, ?_⟩
  · exact (compactFormulaTransformTotalExactBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary
      (compactSyntaxRunFuelBound input + 1) mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length
      emptyBoundary binderArity tableWidth
      (2 ^ tableWidth)).mpr (by
        have htraceGraph :=
          (compactFormulaTransformTotalTraceBoundedGraphDef_spec
            tokenTable width tokenCount stateBoundary states.length fuel mode
            witnessStart witnessFinish witnessCount
            inputBoundary input.length
            expectedOutputBoundary expectedOutput.length
            emptyBoundary binderArity tableWidth
            (2 ^ tableWidth)).mp htrace
        simpa [CompactFormulaTransformTotalExactBoundedGraph, states, fuel,
          compactSyntaxRunFuelBound] using htraceGraph)
  · simpa [fuel] using htableWidth

theorem totalResult_exists_compactFormulaTransformTotalExactBoundedFormula
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary emptyBoundary binderArity : Nat}
    {witness input expectedOutput : List Nat}
    (hrows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary
        (compactFormulaTransformStateTrace (mode, witness)
          (compactSyntaxRunFuelBound input)
          (compactFormulaTransformInitialState binderArity input)))
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
    (hresult : expectedOutput =
      (compactExactFormulaTransformResult
        (compactFormulaTransformResult
          (mode, witness) (binderArity, input))).getD []) :
    ∃ tableWidth,
      compactFormulaTransformTotalExactBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary,
          (compactSyntaxRunFuelBound input) + 1, mode,
          witnessStart, witnessFinish, witnessCount,
          inputBoundary, input.length,
          expectedOutputBoundary, expectedOutput.length,
          emptyBoundary, binderArity,
          tableWidth, 2 ^ tableWidth] := by
  rcases
      totalResult_exists_compactFormulaTransformTotalExactBoundedFormula_with_width_bound
        hrows hwitness hwitnessCount hinput hexpectedOutput hempty hresult with
    ⟨tableWidth, hformula, _htableWidth⟩
  exact ⟨tableWidth, hformula⟩

#print axioms compactFormulaTransformTotalExactBoundedGraphDef_spec
#print axioms compactFormulaTransformTotalExactBoundedGraphDef_sigmaZero
#print axioms CompactFormulaTransformTotalExactBoundedGraph.sound
#print axioms CompactFormulaTransformTotalExactBoundedGraph.sound_selfContained
#print axioms CompactFormulaTransformTotalExactBoundedGraph.finalLayout_selfContained
#print axioms totalResult_exists_compactFormulaTransformTotalExactBoundedFormula_with_width_bound
#print axioms totalResult_exists_compactFormulaTransformTotalExactBoundedFormula

end FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
