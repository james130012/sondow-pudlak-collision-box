import integration.FoundationCompactNumericListedDirectFormulaTransformTraceFormula

/-!
# Exact formula-transform results from the complete direct trace

This module fixes the complete transform trace at the public syntax-machine
fuel bound.  A successful final row with empty suffix is therefore exactly
the result returned by the executable transform, rather than an arbitrary
accepted prefix trace.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformExactFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformTraceInstallation
open FoundationCompactNumericListedDirectFormulaTransformTraceFormula

def CompactFormulaTransformExactBoundedGraph
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptySuffixBoundary binderArity tableWidth valueBound : Nat) : Prop :=
  CompactFormulaTransformTraceBoundedGraph
    tokenTable width tokenCount stateBoundary stateCount
      (16 * (inputCount + 1) * (inputCount + 1) + 8) mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptySuffixBoundary 0 binderArity tableWidth valueBound

def compactFormulaTransformExactBoundedGraphDef :
    𝚺₀.Semisentence 17 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptySuffixBoundary binderArity tableWidth valueBound.
    !(compactFormulaTransformTraceBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount
      (16 * (inputCount + 1) * (inputCount + 1) + 8) mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptySuffixBoundary 0 binderArity tableWidth valueBound”

@[simp] theorem compactFormulaTransformExactBoundedGraphDef_spec
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptySuffixBoundary binderArity tableWidth valueBound : Nat) :
    compactFormulaTransformExactBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, mode,
          witnessStart, witnessFinish, witnessCount,
          inputBoundary, inputCount, expectedOutputBoundary,
          expectedOutputCount, emptySuffixBoundary, binderArity,
          tableWidth, valueBound] ↔
      CompactFormulaTransformExactBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount mode
        witnessStart witnessFinish witnessCount
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        emptySuffixBoundary binderArity tableWidth valueBound := by
  let env : Fin 17 → Nat :=
    ![tokenTable, width, tokenCount, stateBoundary, stateCount, mode,
      witnessStart, witnessFinish, witnessCount,
      inputBoundary, inputCount, expectedOutputBoundary,
      expectedOutputCount, emptySuffixBoundary, binderArity,
      tableWidth, valueBound]
  change compactFormulaTransformExactBoundedGraphDef.val.Evalb env ↔ _
  have htraceEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #3, #4,
          (‘(16 * (#10 + 1) * (#10 + 1) + 8)’ :
            Semiterm ℒₒᵣ Empty 17), #5,
          #6, #7, #8, #9, #10, #11, #12, #13,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 17), #14, #15, #16]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount,
          16 * (inputCount + 1) * (inputCount + 1) + 8, mode,
          witnessStart, witnessFinish, witnessCount,
          inputBoundary, inputCount, expectedOutputBoundary,
          expectedOutputCount, emptySuffixBoundary, 0, binderArity,
          tableWidth, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  have htraceSpec :
      (Semiformula.Eval
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #3, #4,
            (‘(16 * (#10 + 1) * (#10 + 1) + 8)’ :
              Semiterm ℒₒᵣ Empty 17), #5,
            #6, #7, #8, #9, #10, #11, #12, #13,
            (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 17), #14, #15, #16])
          Empty.elim)
        compactFormulaTransformTraceBoundedGraphDef.val ↔
      CompactFormulaTransformTraceBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount
        (16 * (inputCount + 1) * (inputCount + 1) + 8) mode
        witnessStart witnessFinish witnessCount
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        emptySuffixBoundary 0 binderArity tableWidth valueBound := by
    rw [htraceEnv]
    exact compactFormulaTransformTraceBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary stateCount
      (16 * (inputCount + 1) * (inputCount + 1) + 8) mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptySuffixBoundary 0 binderArity tableWidth valueBound
  simp [compactFormulaTransformExactBoundedGraphDef,
    CompactFormulaTransformExactBoundedGraph, htraceSpec]

theorem compactFormulaTransformExactBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformExactBoundedGraphDef.val := by
  simp [compactFormulaTransformExactBoundedGraphDef]

theorem compactExactFormulaTransformResult_eq_some_iff
    {result : Option (List Nat × List Nat)} {output : List Nat} :
    compactExactFormulaTransformResult result = some output ↔
      result = some (output, []) := by
  cases result with
  | none => simp [compactExactFormulaTransformResult]
  | some outputAndSuffix =>
      rcases outputAndSuffix with ⟨actualOutput, suffix⟩
      by_cases hsuffix : suffix = []
      · subst suffix
        simp [compactExactFormulaTransformResult]
      · simp [compactExactFormulaTransformResult, hsuffix]

theorem compactFormulaTransformStateOutput_eq_some_iff
    {state : CompactFormulaTransformState}
    {output suffix : List Nat} :
    compactFormulaTransformStateOutput state = some (output, suffix) ↔
      state.1.2.2 = some (some suffix) ∧ state.2 = output := by
  rcases state with ⟨⟨tokens, tasks, status⟩, actualOutput⟩
  cases status with
  | none => simp [compactFormulaTransformStateOutput]
  | some result =>
      cases result with
      | none => simp [compactFormulaTransformStateOutput]
      | some actualSuffix =>
          simp [compactFormulaTransformStateOutput, Prod.ext_iff]
          aesop

theorem CompactFormulaTransformExactBoundedGraph.sound_result
    {tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary emptySuffixBoundary
      binderArity tableWidth valueBound : Nat}
    {states : List CompactFormulaTransformState}
    {witness input expectedOutput : List Nat}
    (hgraph : CompactFormulaTransformExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length emptySuffixBoundary
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
    (hemptySuffix : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptySuffixBoundary []) :
    compactFormulaTransformResult
        (mode, witness) (binderArity, input) =
      some (expectedOutput, []) := by
  let fuel := compactSyntaxRunFuelBound input
  have hgraph' : CompactFormulaTransformTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length
      emptySuffixBoundary 0 binderArity tableWidth valueBound := by
    simpa [CompactFormulaTransformExactBoundedGraph,
      compactSyntaxRunFuelBound, fuel] using hgraph
  rcases CompactFormulaTransformTraceBoundedGraph.sound
      hgraph' hcount hrows hwitness hwitnessCount hinput
        hexpectedOutput hemptySuffix with
    ⟨hvalid, hfinalStatus, hfinalOutput⟩
  have hrun : compactFormulaTransformRun
      (mode, witness) (binderArity, input) = states.getI fuel := by
    symm
    simpa [compactFormulaTransformRun,
      compactFormulaTransformStateAt, fuel] using
      (CompactFormulaTransformLocalTraceValid.getI_eq_stateAt
        hvalid (Nat.le_refl fuel))
  apply compactFormulaTransformStateOutput_eq_some_iff.mpr
  rw [hrun]
  exact ⟨hfinalStatus, hfinalOutput⟩

theorem CompactFormulaTransformExactBoundedGraph.sound_exact
    {tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary emptySuffixBoundary
      binderArity tableWidth valueBound : Nat}
    {states : List CompactFormulaTransformState}
    {witness input expectedOutput : List Nat}
    (hgraph : CompactFormulaTransformExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length emptySuffixBoundary
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
    (hemptySuffix : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptySuffixBoundary []) :
    compactExactFormulaTransformResult
        (compactFormulaTransformResult
          (mode, witness) (binderArity, input)) = some expectedOutput := by
  apply compactExactFormulaTransformResult_eq_some_iff.mpr
  exact CompactFormulaTransformExactBoundedGraph.sound_result
    hgraph hcount hrows hwitness hwitnessCount hinput
      hexpectedOutput hemptySuffix

theorem exactResult_exists_compactFormulaTransformExactBoundedFormula
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary emptySuffixBoundary
      binderArity : Nat}
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
    (hemptySuffix : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptySuffixBoundary [])
    (hexact : compactExactFormulaTransformResult
      (compactFormulaTransformResult
        (mode, witness) (binderArity, input)) = some expectedOutput) :
    ∃ tableWidth,
      compactFormulaTransformExactBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary,
          (compactSyntaxRunFuelBound input) + 1, mode,
          witnessStart, witnessFinish, witnessCount,
          inputBoundary, input.length,
          expectedOutputBoundary, expectedOutput.length,
          emptySuffixBoundary, binderArity,
          tableWidth, 2 ^ tableWidth] := by
  let fuel := compactSyntaxRunFuelBound input
  let start := compactFormulaTransformInitialState binderArity input
  let states := compactFormulaTransformStateTrace
    (mode, witness) fuel start
  have hlocal : CompactFormulaTransformLocalTraceValid
      (mode, witness) fuel start states := by
    exact compactFormulaTransformStateTrace_localValid
      (mode, witness) fuel start
  have hrunOutput : compactFormulaTransformStateOutput
      (compactFormulaTransformRun
        (mode, witness) (binderArity, input)) =
      some (expectedOutput, []) :=
    compactExactFormulaTransformResult_eq_some_iff.mp hexact
  have hrunFields :=
    compactFormulaTransformStateOutput_eq_some_iff.mp hrunOutput
  have hfinalEq : states.getI fuel =
      compactFormulaTransformRun
        (mode, witness) (binderArity, input) := by
    simpa [states, start, compactFormulaTransformRun,
      compactFormulaTransformStateAt, fuel] using
      (CompactFormulaTransformLocalTraceValid.getI_eq_stateAt
        hlocal (Nat.le_refl fuel))
  have hfinalStatus : (states.getI fuel).1.2.2 = some (some []) := by
    rw [hfinalEq]
    exact hrunFields.1
  have hfinalOutput : (states.getI fuel).2 = expectedOutput := by
    rw [hfinalEq]
    exact hrunFields.2
  have hrows' : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary states := by
    simpa [states, start, fuel] using hrows
  rcases localTrace_exists_compactFormulaTransformTraceBoundedFormula
      hrows' hwitness hwitnessCount hinput hexpectedOutput hemptySuffix
      hlocal hfinalStatus hfinalOutput with
    ⟨tableWidth, htrace⟩
  refine ⟨tableWidth,
    (compactFormulaTransformExactBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary
      (compactSyntaxRunFuelBound input + 1) mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length
      emptySuffixBoundary binderArity tableWidth
      (2 ^ tableWidth)).mpr ?_⟩
  have htraceGraph :=
    (compactFormulaTransformTraceBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary states.length fuel mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length
      emptySuffixBoundary 0 binderArity tableWidth
      (2 ^ tableWidth)).mp htrace
  simpa [CompactFormulaTransformExactBoundedGraph, states, fuel,
    compactSyntaxRunFuelBound] using htraceGraph

#print axioms compactFormulaTransformExactBoundedGraphDef_spec
#print axioms compactFormulaTransformExactBoundedGraphDef_sigmaZero
#print axioms compactExactFormulaTransformResult_eq_some_iff
#print axioms compactFormulaTransformStateOutput_eq_some_iff
#print axioms CompactFormulaTransformExactBoundedGraph.sound_result
#print axioms CompactFormulaTransformExactBoundedGraph.sound_exact
#print axioms exactResult_exists_compactFormulaTransformExactBoundedFormula

end FoundationCompactNumericListedDirectFormulaTransformExactFormula
