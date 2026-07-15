import integration.FoundationCompactNumericListedDirectFormulaTransformExactFormula

/-!
# Total final result of a formula-transform trace

The public rule checks use `Option.getD []`: a completed transform with empty
suffix returns its emitted output, while running, failed, or nonempty-suffix
states return the empty list.  This module gives that total behavior a direct
bounded arithmetic graph.  It is therefore exact even on malformed numeric
proof fields, not only on canonical typed formulas.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformFinalDefaultFormula

open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectParserFinalFormula
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformExactFormula
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

def CompactUnifiedParserEmptyFinalStateBounded
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (emptyBoundary valueBound : Nat) : Prop :=
  ∃ outputStart, outputStart ≤ valueBound ∧
  ∃ outputBoundary, outputBoundary ≤ valueBound ∧
  ∃ outputBoundarySize, outputBoundarySize ≤ valueBound ∧
    CompactUnifiedParserFinalStateRows
      tokenTable width tokenCount coordinates emptyBoundary 0
        outputStart outputBoundary outputBoundarySize

def compactUnifiedParserEmptyFinalStateBoundedDef :
    𝚺₀.Semisentence 13 := .mkSigma
  “tokenTable width tokenCount
      start finish tokensFinish tasksFinish
      tokensBoundary tokensCount tasksBoundary tasksCount
      emptyBoundary valueBound.
    ∃ outputStart <⁺ valueBound,
    ∃ outputBoundary <⁺ valueBound,
    ∃ outputBoundarySize <⁺ valueBound,
      !(compactUnifiedParserFinalStateRowsDef)
        tokenTable width tokenCount
        start finish tokensFinish tasksFinish
        tokensBoundary tokensCount tasksBoundary tasksCount
        emptyBoundary 0 outputStart outputBoundary outputBoundarySize”

def compactUnifiedParserEmptyFinalStateBoundedEnvironment
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (emptyBoundary valueBound : Nat) : Fin 13 → Nat :=
  ![tokenTable, width, tokenCount,
    coordinates.start, coordinates.finish,
    coordinates.tokensFinish, coordinates.tasksFinish,
    coordinates.tokensBoundary, coordinates.tokensCount,
    coordinates.tasksBoundary, coordinates.tasksCount,
    emptyBoundary, valueBound]

@[simp] theorem compactUnifiedParserEmptyFinalStateBoundedDef_spec
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (emptyBoundary valueBound : Nat) :
    compactUnifiedParserEmptyFinalStateBoundedDef.val.Evalb
        (compactUnifiedParserEmptyFinalStateBoundedEnvironment
          tokenTable width tokenCount coordinates emptyBoundary valueBound) ↔
      CompactUnifiedParserEmptyFinalStateBounded
        tokenTable width tokenCount coordinates emptyBoundary valueBound := by
  let env := compactUnifiedParserEmptyFinalStateBoundedEnvironment
    tokenTable width tokenCount coordinates emptyBoundary valueBound
  change compactUnifiedParserEmptyFinalStateBoundedDef.val.Evalb env ↔ _
  have hfinal (outputBoundarySize outputBoundary outputStart : Nat) :
      (Semiformula.Eval
        (Semiterm.val
          (outputBoundarySize :> outputBoundary :> outputStart :> env)
          Empty.elim ∘
          ![(#3 : Semiterm ℒₒᵣ Empty 16), #4, #5,
            #6, #7, #8, #9, #10, #11, #12, #13,
            #14, (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 16), #2, #1, #0])
          Empty.elim)
        compactUnifiedParserFinalStateRowsDef.val ↔
      CompactUnifiedParserFinalStateRows
        tokenTable width tokenCount coordinates emptyBoundary 0
          outputStart outputBoundary outputBoundarySize := by
    have henv :
        (Semiterm.val
          (outputBoundarySize :> outputBoundary :> outputStart :> env)
          Empty.elim ∘
          ![(#3 : Semiterm ℒₒᵣ Empty 16), #4, #5,
            #6, #7, #8, #9, #10, #11, #12, #13,
            #14, (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 16), #2, #1, #0]) =
        compactUnifiedParserFinalStateRowsEnvironment
          tokenTable width tokenCount coordinates emptyBoundary 0
            outputStart outputBoundary outputBoundarySize := by
      funext index
      fin_cases index <;> simp [env,
        compactUnifiedParserEmptyFinalStateBoundedEnvironment,
        compactUnifiedParserFinalStateRowsEnvironment]
    rw [henv]
    exact compactUnifiedParserFinalStateRowsDef_spec
      tokenTable width tokenCount coordinates emptyBoundary 0
        outputStart outputBoundary outputBoundarySize
  have hvalueBoundValue : env 12 = valueBound := rfl
  simp [compactUnifiedParserEmptyFinalStateBoundedDef,
    CompactUnifiedParserEmptyFinalStateBounded, hfinal,
    hvalueBoundValue]

theorem compactUnifiedParserEmptyFinalStateBoundedDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserEmptyFinalStateBoundedDef.val := by
  simp [compactUnifiedParserEmptyFinalStateBoundedDef]

theorem compactUnifiedParserEmptyFinalStateBounded_iff
    {tokenTable width tokenCount emptyBoundary tableWidth valueBound : Nat}
    {coordinates : CompactUnifiedParserStateRowCoordinates}
    {state : FoundationCompactParserDirectTrace.CompactUnifiedParserState}
    (hempty : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary [])
    (hstate : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount coordinates state)
    (harea : (tokenCount + 1) * tokenCount ≤ tableWidth)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    CompactUnifiedParserEmptyFinalStateBounded
        tokenTable width tokenCount coordinates emptyBoundary valueBound ↔
      state.2.2 = some (some []) := by
  subst valueBound
  constructor
  · rintro ⟨outputStart, _houtputStart,
      outputBoundary, _houtputBoundary,
      outputBoundarySize, _houtputBoundarySize, hfinal⟩
    exact (exists_compactUnifiedParserFinalStateRows_iff
      hempty hstate).mp ⟨outputStart, outputBoundary,
        outputBoundarySize, hfinal⟩
  · intro hstatus
    rcases (exists_compactUnifiedParserFinalStateRows_iff
        hempty hstate).mpr hstatus with
      ⟨outputStart, outputBoundary, outputBoundarySize, hfinal⟩
    have hwidthPower : tableWidth ≤ 2 ^ tableWidth :=
      Nat.le_of_lt tableWidth.lt_two_pow_self
    have htokenWidth : tokenCount ≤ tableWidth := by
      have htokenArea : tokenCount ≤ (tokenCount + 1) * tokenCount := by
        calc
          tokenCount = 1 * tokenCount := by simp
          _ ≤ (tokenCount + 1) * tokenCount :=
            Nat.mul_le_mul_right tokenCount (by omega)
      exact htokenArea.trans harea
    have htokenPower : tokenCount ≤ 2 ^ tableWidth :=
      htokenWidth.trans hwidthPower
    rcases hfinal with
      ⟨⟨⟨innerStart, _hinnerStart, _houterCell, hinnerCell⟩,
          _houtputLayout, _hsameRows⟩,
        hsizeEq, hsizeBound⟩
    have houtputStartToken : outputStart ≤ tokenCount := by
      have hstartLt := hinnerCell.1
      have hfinishEq := hinnerCell.2.1
      omega
    have houtputStart : outputStart ≤ 2 ^ tableWidth :=
      houtputStartToken.trans htokenPower
    have hsizeToken : outputBoundarySize ≤ tokenCount := by
      simpa using hsizeBound
    have houtputBoundarySize :
        outputBoundarySize ≤ 2 ^ tableWidth :=
      hsizeToken.trans htokenPower
    have hboundarySize : Nat.size outputBoundary ≤ tableWidth := by
      rw [← hsizeEq]
      exact hsizeToken.trans htokenWidth
    have houtputBoundary : outputBoundary ≤ 2 ^ tableWidth :=
      (Nat.size_le.mp hboundarySize).le
    exact ⟨outputStart, houtputStart,
      outputBoundary, houtputBoundary,
      outputBoundarySize, houtputBoundarySize,
      ⟨⟨innerStart, by omega, _houterCell, hinnerCell⟩,
        _houtputLayout, _hsameRows⟩, hsizeEq, hsizeBound⟩

def CompactFormulaTransformFinalGetDOutputRows
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (expectedOutputBoundary expectedOutputCount emptyBoundary
      tableWidth valueBound : Nat) : Prop :=
  valueBound = 2 ^ tableWidth ∧
    CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount coordinates.parserTasksFinish
        coordinates.parserFinish valueBound ∧
    ((CompactUnifiedParserEmptyFinalStateBounded
        tokenTable width tokenCount coordinates.parser
          emptyBoundary valueBound ∧
      CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          expectedOutputBoundary expectedOutputCount
          coordinates.outputBoundary coordinates.outputCount) ∨
     (¬ CompactUnifiedParserEmptyFinalStateBounded
        tokenTable width tokenCount coordinates.parser
          emptyBoundary valueBound) ∧
      expectedOutputCount = 0)

def compactFormulaTransformFinalGetDOutputRowsDef :
    𝚺₀.Semisentence 19 := .mkSigma
  “tokenTable width tokenCount
      start finish parserFinish
      parserTokensFinish parserTasksFinish
      parserTokensBoundary parserTokensCount
      parserTasksBoundary parserTasksCount
      outputBoundary outputCount
      expectedOutputBoundary expectedOutputCount emptyBoundary
      tableWidth valueBound.
    !expDef valueBound tableWidth ∧
    !(compactBinaryNatStatusValidBoundedDef)
      tokenTable width tokenCount parserTasksFinish parserFinish valueBound ∧
    ((!(compactUnifiedParserEmptyFinalStateBoundedDef)
        tokenTable width tokenCount
        start parserFinish parserTokensFinish parserTasksFinish
        parserTokensBoundary parserTokensCount
        parserTasksBoundary parserTasksCount
        emptyBoundary valueBound ∧
      !(compactAdditiveNatListSameRowsDef)
        tokenTable width tokenCount
        expectedOutputBoundary expectedOutputCount
        outputBoundary outputCount) ∨
     (¬ !(compactUnifiedParserEmptyFinalStateBoundedDef)
        tokenTable width tokenCount
        start parserFinish parserTokensFinish parserTasksFinish
        parserTokensBoundary parserTokensCount
        parserTasksBoundary parserTasksCount
        emptyBoundary valueBound) ∧
      expectedOutputCount = 0)”

def compactFormulaTransformFinalGetDOutputRowsEnvironment
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (expectedOutputBoundary expectedOutputCount emptyBoundary
      tableWidth valueBound : Nat) : Fin 19 → Nat :=
  ![tokenTable, width, tokenCount,
    coordinates.start, coordinates.finish, coordinates.parserFinish,
    coordinates.parserTokensFinish, coordinates.parserTasksFinish,
    coordinates.parserTokensBoundary, coordinates.parserTokensCount,
    coordinates.parserTasksBoundary, coordinates.parserTasksCount,
    coordinates.outputBoundary, coordinates.outputCount,
    expectedOutputBoundary, expectedOutputCount, emptyBoundary,
    tableWidth, valueBound]

@[simp] theorem compactFormulaTransformFinalGetDOutputRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (expectedOutputBoundary expectedOutputCount emptyBoundary
      tableWidth valueBound : Nat) :
    compactFormulaTransformFinalGetDOutputRowsDef.val.Evalb
        (compactFormulaTransformFinalGetDOutputRowsEnvironment
          tokenTable width tokenCount coordinates
          expectedOutputBoundary expectedOutputCount emptyBoundary
          tableWidth valueBound) ↔
      CompactFormulaTransformFinalGetDOutputRows
        tokenTable width tokenCount coordinates
        expectedOutputBoundary expectedOutputCount emptyBoundary
        tableWidth valueBound := by
  let env := compactFormulaTransformFinalGetDOutputRowsEnvironment
    tokenTable width tokenCount coordinates
    expectedOutputBoundary expectedOutputCount emptyBoundary
    tableWidth valueBound
  change compactFormulaTransformFinalGetDOutputRowsDef.val.Evalb env ↔ _
  have hemptyEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2,
          #3, #5, #6, #7, #8, #9, #10, #11, #16, #18]) =
        compactUnifiedParserEmptyFinalStateBoundedEnvironment
          tokenTable width tokenCount coordinates.parser
            emptyBoundary valueBound := by
    funext index
    fin_cases index <;> rfl
  have hsameEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2,
          #14, #15, #12, #13]) =
        ![tokenTable, width, tokenCount,
          expectedOutputBoundary, expectedOutputCount,
          coordinates.outputBoundary, coordinates.outputCount] := by
    funext index
    fin_cases index <;> rfl
  have hstatusEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2, #7, #5, #18]) =
        ![tokenTable, width, tokenCount,
          coordinates.parserTasksFinish, coordinates.parserFinish,
          valueBound] := by
    funext index
    fin_cases index <;> rfl
  have hvalueBoundValue : env 18 = valueBound := rfl
  have htableWidthValue : env 17 = tableWidth := rfl
  have hexpectedCountValue : env 15 = expectedOutputCount := rfl
  simp [compactFormulaTransformFinalGetDOutputRowsDef,
    CompactFormulaTransformFinalGetDOutputRows,
    hemptyEnv, hsameEnv, hstatusEnv,
    hvalueBoundValue, htableWidthValue,
    hexpectedCountValue]

theorem compactFormulaTransformFinalGetDOutputRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformFinalGetDOutputRowsDef.val := by
  simp [compactFormulaTransformFinalGetDOutputRowsDef]

theorem compactFormulaTransformFinalGetDOutputRows_iff
    {tokenTable width tokenCount expectedOutputBoundary emptyBoundary
      tableWidth valueBound : Nat}
    {coordinates : CompactFormulaTransformStateRowCoordinates}
    {state : CompactFormulaTransformState}
    {expectedOutput : List Nat}
    (hexpectedOutput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedOutputBoundary expectedOutput)
    (hempty : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary [])
    (hstate : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount coordinates state)
    (harea : (tokenCount + 1) * tokenCount ≤ tableWidth)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    CompactFormulaTransformFinalGetDOutputRows
        tokenTable width tokenCount coordinates
        expectedOutputBoundary expectedOutput.length emptyBoundary
        tableWidth valueBound ↔
      expectedOutput =
        (compactExactFormulaTransformResult
          (compactFormulaTransformStateOutput state)).getD [] := by
  simp only [CompactFormulaTransformFinalGetDOutputRows]
  constructor
  · rintro ⟨hvalueBound', _hstatusValid, hsuccess | hdefault⟩
    · have hstatus :=
        (compactUnifiedParserEmptyFinalStateBounded_iff
          hempty hstate.parserLayout harea hvalueBound').mp hsuccess.1
      have houtput : state.2 = expectedOutput :=
        (compactAdditiveNatListSameRows_iff_eq_of_rows
          hexpectedOutput hstate.outputRows).mp (by
            simpa only [hstate.outputCount_eq] using hsuccess.2)
      rw [← houtput]
      have hsome : compactExactFormulaTransformResult
          (compactFormulaTransformStateOutput state) = some state.2 := by
        apply compactExactFormulaTransformResult_eq_some_iff.mpr
        apply compactFormulaTransformStateOutput_eq_some_iff.mpr
        exact ⟨hstatus, rfl⟩
      simp [hsome]
    · have hstatus : state.1.2.2 ≠ some (some []) := by
        intro hstatus
        exact hdefault.1
          ((compactUnifiedParserEmptyFinalStateBounded_iff
            hempty hstate.parserLayout harea hvalueBound').mpr hstatus)
      have hexpectedEmpty : expectedOutput = [] :=
        List.eq_nil_of_length_eq_zero hdefault.2
      rw [hexpectedEmpty]
      rcases state with ⟨⟨tokens, tasks, status⟩, output⟩
      cases status with
      | none => simp [compactFormulaTransformStateOutput,
          compactExactFormulaTransformResult]
      | some result =>
          cases result with
          | none => simp [compactFormulaTransformStateOutput,
              compactExactFormulaTransformResult]
          | some suffix =>
              have hsuffix : suffix ≠ [] := by
                simpa using hstatus
              simp [compactFormulaTransformStateOutput,
                compactExactFormulaTransformResult, hsuffix]
  · intro hresult
    have hstatusValid : CompactBinaryNatStatusValidBounded
        tokenTable width tokenCount coordinates.parserTasksFinish
          coordinates.parserFinish valueBound := by
      rw [hvalueBound]
      exact CompactBinaryNatStreamStatusDirectLayout.validBounded
        hstate.parserLayout.statusLayout harea
    refine ⟨hvalueBound, hstatusValid, ?_⟩
    by_cases hstatus : state.1.2.2 = some (some [])
    · left
      have hemptyFinal :=
        (compactUnifiedParserEmptyFinalStateBounded_iff
          hempty hstate.parserLayout harea hvalueBound).mpr hstatus
      have hstateResult :
          (compactExactFormulaTransformResult
            (compactFormulaTransformStateOutput state)).getD [] = state.2 := by
        have hsome : compactExactFormulaTransformResult
            (compactFormulaTransformStateOutput state) = some state.2 := by
          apply compactExactFormulaTransformResult_eq_some_iff.mpr
          apply compactFormulaTransformStateOutput_eq_some_iff.mpr
          exact ⟨hstatus, rfl⟩
        simp [hsome]
      have hexpected : state.2 = expectedOutput :=
        (hresult.trans hstateResult).symm
      exact ⟨hemptyFinal,
        (by
          simpa only [hstate.outputCount_eq] using
            (compactAdditiveNatListSameRows_iff_eq_of_rows
              hexpectedOutput hstate.outputRows).mpr hexpected)⟩
    · right
      have hnotEmptyFinal :
          ¬ CompactUnifiedParserEmptyFinalStateBounded
            tokenTable width tokenCount coordinates.parser
              emptyBoundary valueBound := by
        intro hemptyFinal
        exact hstatus
          ((compactUnifiedParserEmptyFinalStateBounded_iff
            hempty hstate.parserLayout harea hvalueBound).mp hemptyFinal)
      have hdefault :
          (compactExactFormulaTransformResult
            (compactFormulaTransformStateOutput state)).getD [] = [] := by
        rcases state with ⟨⟨tokens, tasks, status⟩, output⟩
        cases status with
        | none => simp [compactFormulaTransformStateOutput,
            compactExactFormulaTransformResult]
        | some result =>
            cases result with
            | none => simp [compactFormulaTransformStateOutput,
                compactExactFormulaTransformResult]
            | some suffix =>
                have hsuffix : suffix ≠ [] := by simpa using hstatus
                simp [compactFormulaTransformStateOutput,
                  compactExactFormulaTransformResult, hsuffix]
      have hexpectedEmpty : expectedOutput = [] := by
        rw [hresult, hdefault]
      exact ⟨hnotEmptyFinal, by simpa [hexpectedEmpty]⟩

#print axioms compactUnifiedParserEmptyFinalStateBoundedDef_spec
#print axioms compactUnifiedParserEmptyFinalStateBoundedDef_sigmaZero
#print axioms compactUnifiedParserEmptyFinalStateBounded_iff
#print axioms compactFormulaTransformFinalGetDOutputRowsDef_spec
#print axioms compactFormulaTransformFinalGetDOutputRowsDef_sigmaZero
#print axioms compactFormulaTransformFinalGetDOutputRows_iff

end FoundationCompactNumericListedDirectFormulaTransformFinalDefaultFormula
