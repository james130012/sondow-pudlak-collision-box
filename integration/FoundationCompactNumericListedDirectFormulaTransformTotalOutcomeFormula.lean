import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula

/-!
# Total formula-transform outcome rows

The public rule checks need both the defaulted output and the success bit of
an exact transform.  The success bit is read from the same unconditional
execution trace as the output, so a failed result cannot be forged by
omitting a successful-transform witness.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformTotalOutcomeFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectFormulaTransformFinalDefaultFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformTotalTraceFormula
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula

def CompactFormulaTransformTotalOutcomeRows
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound successValue : Nat)
    (finalCoordinates : CompactFormulaTransformStateRowCoordinates)
    (finalSizeWitness : CompactFormulaTransformStateCoreSizeWitness) : Prop :=
  CompactFormulaTransformTotalExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound ∧
    CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount
        (16 * (inputCount + 1) * (inputCount + 1) + 8)
        finalCoordinates finalSizeWitness ∧
    CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount finalCoordinates.parserTasksFinish
        finalCoordinates.parserFinish valueBound ∧
    successValue ≤ 1 ∧
    (successValue = 1 ↔
      CompactUnifiedParserEmptyFinalStateBounded
        tokenTable width tokenCount finalCoordinates.parser
          emptyBoundary valueBound)

def compactFormulaTransformTotalOutcomeRowsDef :
    𝚺₀.Semisentence 32 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound successValue
      finalStart finalFinish finalParserFinish
      finalParserTokensFinish finalParserTasksFinish
      finalParserTokensBoundary finalParserTokensCount
      finalParserTasksBoundary finalParserTasksCount
      finalOutputBoundary finalOutputCount
      finalParserTokensBoundarySize finalParserTasksBoundarySize
      finalOutputBoundarySize.
    !(compactFormulaTransformTotalExactBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound ∧
    !(compactFormulaTransformStateAtRowsDef)
      tokenTable width tokenCount stateBoundary stateCount
      (16 * (inputCount + 1) * (inputCount + 1) + 8)
      finalStart finalFinish finalParserFinish
      finalParserTokensFinish finalParserTasksFinish
      finalParserTokensBoundary finalParserTokensCount
      finalParserTasksBoundary finalParserTasksCount
      finalOutputBoundary finalOutputCount
      finalParserTokensBoundarySize finalParserTasksBoundarySize
      finalOutputBoundarySize ∧
    !(compactBinaryNatStatusValidBoundedDef)
      tokenTable width tokenCount finalParserTasksFinish
        finalParserFinish valueBound ∧
    successValue ≤ 1 ∧
    (successValue = 1 ↔
      !(compactUnifiedParserEmptyFinalStateBoundedDef)
        tokenTable width tokenCount
        finalStart finalParserFinish
        finalParserTokensFinish finalParserTasksFinish
        finalParserTokensBoundary finalParserTokensCount
        finalParserTasksBoundary finalParserTasksCount
        emptyBoundary valueBound)”

def compactFormulaTransformTotalOutcomeRowsEnvironment
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound successValue : Nat)
    (finalCoordinates : CompactFormulaTransformStateRowCoordinates)
    (finalSizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    Fin 32 → Nat :=
  ![tokenTable, width, tokenCount, stateBoundary, stateCount, mode,
    witnessStart, witnessFinish, witnessCount,
    inputBoundary, inputCount, expectedOutputBoundary, expectedOutputCount,
    emptyBoundary, binderArity, tableWidth, valueBound, successValue,
    finalCoordinates.start, finalCoordinates.finish,
    finalCoordinates.parserFinish,
    finalCoordinates.parserTokensFinish,
    finalCoordinates.parserTasksFinish,
    finalCoordinates.parserTokensBoundary,
    finalCoordinates.parserTokensCount,
    finalCoordinates.parserTasksBoundary,
    finalCoordinates.parserTasksCount,
    finalCoordinates.outputBoundary, finalCoordinates.outputCount,
    finalSizeWitness.parserTokensBoundarySize,
    finalSizeWitness.parserTasksBoundarySize,
    finalSizeWitness.outputBoundarySize]

@[simp] theorem compactFormulaTransformTotalOutcomeRowsDef_spec
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound successValue : Nat)
    (finalCoordinates : CompactFormulaTransformStateRowCoordinates)
    (finalSizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    compactFormulaTransformTotalOutcomeRowsDef.val.Evalb
        (compactFormulaTransformTotalOutcomeRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount mode
          witnessStart witnessFinish witnessCount
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          emptyBoundary binderArity tableWidth valueBound successValue
          finalCoordinates finalSizeWitness) ↔
      CompactFormulaTransformTotalOutcomeRows
        tokenTable width tokenCount stateBoundary stateCount mode
        witnessStart witnessFinish witnessCount
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        emptyBoundary binderArity tableWidth valueBound successValue
        finalCoordinates finalSizeWitness := by
  let env := compactFormulaTransformTotalOutcomeRowsEnvironment
    tokenTable width tokenCount stateBoundary stateCount mode
    witnessStart witnessFinish witnessCount
    inputBoundary inputCount expectedOutputBoundary expectedOutputCount
    emptyBoundary binderArity tableWidth valueBound successValue
    finalCoordinates finalSizeWitness
  change compactFormulaTransformTotalOutcomeRowsDef.val.Evalb env ↔ _
  have htransformEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 32), #1, #2, #3, #4, #5,
          #6, #7, #8, #9, #10, #11, #12, #13, #14, #15, #16]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, mode,
          witnessStart, witnessFinish, witnessCount,
          inputBoundary, inputCount, expectedOutputBoundary,
          expectedOutputCount, emptyBoundary, binderArity,
          tableWidth, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hstateEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 32), #1, #2, #3, #4,
          (‘(16 * (#10 + 1) * (#10 + 1) + 8)’ :
            Semiterm ℒₒᵣ Empty 32),
          #18, #19, #20, #21, #22, #23, #24, #25, #26, #27, #28,
          #29, #30, #31]) =
        compactFormulaTransformStateAtRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount
          (16 * (inputCount + 1) * (inputCount + 1) + 8)
          finalCoordinates finalSizeWitness := by
    funext coordinate
    fin_cases coordinate <;>
      simp [env, compactFormulaTransformTotalOutcomeRowsEnvironment,
        compactFormulaTransformStateAtRowsEnvironment]
  have hstatusEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 32), #1, #2,
          #22, #20, #16]) =
        ![tokenTable, width, tokenCount,
          finalCoordinates.parserTasksFinish,
          finalCoordinates.parserFinish, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hemptyEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 32), #1, #2,
          #18, #20, #21, #22, #23, #24, #25, #26, #13, #16]) =
        compactUnifiedParserEmptyFinalStateBoundedEnvironment
          tokenTable width tokenCount finalCoordinates.parser
            emptyBoundary valueBound := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsuccessValue : env 17 = successValue := rfl
  simp [compactFormulaTransformTotalOutcomeRowsDef,
    CompactFormulaTransformTotalOutcomeRows,
    htransformEnv, hstateEnv, hstatusEnv, hemptyEnv,
    hsuccessValue]

theorem compactFormulaTransformTotalOutcomeRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformTotalOutcomeRowsDef.val := by
  simp [compactFormulaTransformTotalOutcomeRowsDef]

private theorem exactStateOutput_isSome_eq_true_iff
    (state : CompactFormulaTransformState) :
    (compactExactFormulaTransformResult
        (compactFormulaTransformStateOutput state)).isSome = true ↔
      state.1.2.2 = some (some []) := by
  rcases state with ⟨⟨tokens, tasks, status⟩, output⟩
  cases status with
  | none => simp [compactFormulaTransformStateOutput,
      compactExactFormulaTransformResult]
  | some result =>
      cases result with
      | none => simp [compactFormulaTransformStateOutput,
          compactExactFormulaTransformResult]
      | some suffix =>
          by_cases hsuffix : suffix = []
          · subst suffix
            simp [compactFormulaTransformStateOutput,
              compactExactFormulaTransformResult]
          · simp [compactFormulaTransformStateOutput,
              compactExactFormulaTransformResult, hsuffix]

theorem CompactFormulaTransformTotalOutcomeRows.of_canonical_trace_with_width_bound
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
    ∃ tableWidth finalCoordinates finalSizeWitness,
      CompactFormulaTransformTotalOutcomeRows
        tokenTable width tokenCount stateBoundary
          (compactSyntaxRunFuelBound input + 1) mode
        witnessStart witnessFinish witnessCount
        inputBoundary input.length expectedOutputBoundary expectedOutput.length
        emptyBoundary binderArity tableWidth (2 ^ tableWidth)
        (compactAdditiveBoolTag
          (compactExactFormulaTransformResult
            (compactFormulaTransformResult
              (mode, witness) (binderArity, input))).isSome)
        finalCoordinates finalSizeWitness ∧
      tableWidth ≤ compactFormulaTransformCanonicalTableWidthBound
        width tokenCount (compactSyntaxRunFuelBound input) := by
  rcases
      totalResult_exists_compactFormulaTransformTotalExactBoundedFormula_with_width_bound
      hrows hwitness hwitnessCount hinput hexpectedOutput hempty hresult with
    ⟨tableWidth, hformula, htableWidth⟩
  have htransform : CompactFormulaTransformTotalExactBoundedGraph
      tokenTable width tokenCount stateBoundary
        (compactSyntaxRunFuelBound input + 1) mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length expectedOutputBoundary expectedOutput.length
      emptyBoundary binderArity tableWidth (2 ^ tableWidth) :=
    (compactFormulaTransformTotalExactBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary
      (compactSyntaxRunFuelBound input + 1) mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length expectedOutputBoundary expectedOutput.length
      emptyBoundary binderArity tableWidth (2 ^ tableWidth)).mp hformula
  rcases htransform.finalLayout_selfContained
      hwitness hwitnessCount hinput hexpectedOutput hempty with
    ⟨finalCoordinates, finalSizeWitness,
      hfinalAt, hfinalLayout, _hfinalOutput⟩
  have htrace := htransform
  change CompactFormulaTransformTotalTraceBoundedGraph
      tokenTable width tokenCount stateBoundary
        (compactSyntaxRunFuelBound input + 1)
        (compactSyntaxRunFuelBound input) mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length expectedOutputBoundary expectedOutput.length
      emptyBoundary binderArity tableWidth (2 ^ tableWidth) at htrace
  have harea : (tokenCount + 1) * tokenCount ≤ tableWidth := htrace.2.1
  have hstatus : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount finalCoordinates.parserTasksFinish
        finalCoordinates.parserFinish (2 ^ tableWidth) :=
    CompactBinaryNatStreamStatusDirectLayout.validBounded
      hfinalLayout.parserLayout.statusLayout harea
  let finalState := compactFormulaTransformStateAt
    (mode, witness) (compactFormulaTransformInitialState binderArity input)
      (compactSyntaxRunFuelBound input)
  let result := compactExactFormulaTransformResult
    (compactFormulaTransformResult
      (mode, witness) (binderArity, input))
  let successValue := compactAdditiveBoolTag result.isSome
  have hresultStatus : result.isSome = true ↔
      finalState.1.2.2 = some (some []) := by
    simpa [result, finalState, compactFormulaTransformResult,
      compactFormulaTransformRun, compactFormulaTransformStateAt] using
      (exactStateOutput_isSome_eq_true_iff finalState)
  have hemptyStatus :
      CompactUnifiedParserEmptyFinalStateBounded
          tokenTable width tokenCount finalCoordinates.parser
            emptyBoundary (2 ^ tableWidth) ↔
        finalState.1.2.2 = some (some []) := by
    simpa [finalState] using
      (compactUnifiedParserEmptyFinalStateBounded_iff
        hempty hfinalLayout.parserLayout harea rfl)
  have hsuccessBound : successValue ≤ 1 := by
    cases hsome : result.isSome <;>
      simp [successValue, compactAdditiveBoolTag, hsome]
  have hsuccess : successValue = 1 ↔
      CompactUnifiedParserEmptyFinalStateBounded
        tokenTable width tokenCount finalCoordinates.parser
          emptyBoundary (2 ^ tableWidth) := by
    have htag : successValue = 1 ↔ result.isSome = true := by
      cases hsome : result.isSome <;>
        simp [successValue, compactAdditiveBoolTag, hsome]
    exact htag.trans (hresultStatus.trans hemptyStatus.symm)
  exact ⟨tableWidth, finalCoordinates, finalSizeWitness,
    ⟨htransform, hfinalAt, hstatus, hsuccessBound, hsuccess⟩,
    htableWidth⟩

theorem CompactFormulaTransformTotalOutcomeRows.of_canonical_trace
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
    ∃ tableWidth finalCoordinates finalSizeWitness,
      CompactFormulaTransformTotalOutcomeRows
        tokenTable width tokenCount stateBoundary
          (compactSyntaxRunFuelBound input + 1) mode
        witnessStart witnessFinish witnessCount
        inputBoundary input.length expectedOutputBoundary expectedOutput.length
        emptyBoundary binderArity tableWidth (2 ^ tableWidth)
        (compactAdditiveBoolTag
          (compactExactFormulaTransformResult
            (compactFormulaTransformResult
              (mode, witness) (binderArity, input))).isSome)
        finalCoordinates finalSizeWitness := by
  rcases CompactFormulaTransformTotalOutcomeRows.of_canonical_trace_with_width_bound
      hrows hwitness hwitnessCount hinput hexpectedOutput hempty hresult with
    ⟨tableWidth, finalCoordinates, finalSizeWitness, houtcome, _htableWidth⟩
  exact ⟨tableWidth, finalCoordinates, finalSizeWitness, houtcome⟩

theorem CompactFormulaTransformTotalOutcomeRows.sound
    {tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary emptyBoundary
      binderArity tableWidth valueBound successValue : Nat}
    {finalCoordinates : CompactFormulaTransformStateRowCoordinates}
    {finalSizeWitness : CompactFormulaTransformStateCoreSizeWitness}
    {witness input expectedOutput : List Nat}
    (hrows : CompactFormulaTransformTotalOutcomeRows
      tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length expectedOutputBoundary expectedOutput.length
      emptyBoundary binderArity tableWidth valueBound successValue
      finalCoordinates finalSizeWitness)
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
    successValue = compactAdditiveBoolTag
        (compactExactFormulaTransformResult
          (compactFormulaTransformResult
            (mode, witness) (binderArity, input))).isSome ∧
      expectedOutput =
        (compactExactFormulaTransformResult
          (compactFormulaTransformResult
            (mode, witness) (binderArity, input))).getD [] := by
  rcases hrows with
    ⟨htransform, hfinalAt, hstatus, hsuccessBound, hsuccess⟩
  have htransformCopy := htransform
  change CompactFormulaTransformTotalTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
        (compactSyntaxRunFuelBound input) mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length expectedOutputBoundary expectedOutput.length
      emptyBoundary binderArity tableWidth valueBound at htransformCopy
  have harea : (tokenCount + 1) * tokenCount ≤ tableWidth :=
    htransformCopy.2.1
  have hvalueBound : valueBound = 2 ^ tableWidth :=
    htransformCopy.2.2.2.1
  rcases htransform.finalLayout_selfContained
      hwitness hwitnessCount hinput hexpectedOutput hempty with
    ⟨canonicalCoordinates, canonicalSizeWitness,
      hcanonicalAt, hcanonicalLayout, houtput⟩
  rcases CompactFormulaTransformStateCoreGraph.realizeWithStatusBounded
      hfinalAt.2.2.2 hstatus with
    ⟨decodedFinal, hdecodedLayout⟩
  have hsameStart : finalCoordinates.start = canonicalCoordinates.start :=
    (CompactFixedWidthEntry.value_eq_tableValue hfinalAt.2.1).trans
      (CompactFixedWidthEntry.value_eq_tableValue hcanonicalAt.2.1).symm
  have hdecodedCanonical : decodedFinal =
      compactFormulaTransformStateAt (mode, witness)
        (compactFormulaTransformInitialState binderArity input)
        (compactSyntaxRunFuelBound input) :=
    (CompactFormulaTransformStateFixedLayout.eq_and_finish_of_same_start
      hsameStart hcanonicalLayout hdecodedLayout).1
  let result := compactExactFormulaTransformResult
    (compactFormulaTransformResult
      (mode, witness) (binderArity, input))
  have hemptySuccess :
      CompactUnifiedParserEmptyFinalStateBounded
          tokenTable width tokenCount finalCoordinates.parser
            emptyBoundary valueBound ↔
        result.isSome = true := by
    rw [compactUnifiedParserEmptyFinalStateBounded_iff
      hempty hdecodedLayout.parserLayout harea hvalueBound]
    have hstateSuccess :=
      exactStateOutput_isSome_eq_true_iff
        (compactFormulaTransformStateAt (mode, witness)
          (compactFormulaTransformInitialState binderArity input)
          (compactSyntaxRunFuelBound input))
    rw [hdecodedCanonical]
    simpa [result, compactFormulaTransformResult,
      compactFormulaTransformRun, compactFormulaTransformStateAt] using
        hstateSuccess.symm
  have hsuccessIff : successValue = 1 ↔ result.isSome = true :=
    hsuccess.trans hemptySuccess
  have hsuccessTag : successValue =
      compactAdditiveBoolTag result.isSome := by
    cases hresult : result.isSome with
    | false =>
        have hnotOne : successValue ≠ 1 := by
          intro hone
          have := hsuccessIff.mp hone
          simp [hresult] at this
        simp [compactAdditiveBoolTag]
        omega
    | true =>
        have hone : successValue = 1 :=
          hsuccessIff.mpr (by simp [hresult])
        simpa [compactAdditiveBoolTag, hresult] using hone
  exact ⟨hsuccessTag, houtput⟩

#print axioms compactFormulaTransformTotalOutcomeRowsDef_spec
#print axioms compactFormulaTransformTotalOutcomeRowsDef_sigmaZero
#print axioms CompactFormulaTransformTotalOutcomeRows.of_canonical_trace_with_width_bound
#print axioms CompactFormulaTransformTotalOutcomeRows.of_canonical_trace
#print axioms CompactFormulaTransformTotalOutcomeRows.sound

end FoundationCompactNumericListedDirectFormulaTransformTotalOutcomeFormula
