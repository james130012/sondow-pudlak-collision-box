import integration.FoundationCompactNumericListedDirectParserDoneRows

/-!
# Handwritten bounded formula for the finished parser branch

Two parser-state cores share one public token table.  Remaining tokens and
tasks are compared by their exact row formulas.  Failed statuses are compared
directly; completed statuses carry seven explicit output-table coordinates,
including exact size fields and public area bounds.  The resulting formula is
Delta-zero and, under fixed state layouts, exists exactly when the parser is
already finished and the next state equals the current state.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserDoneFormula

open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectCompletedStatusSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserDoneRows

structure CompactUnifiedParserDoneWitnessCoordinates where
  sourceOutputStart : Nat
  sourceOutputBoundary : Nat
  sourceOutputBoundarySize : Nat
  targetOutputStart : Nat
  targetOutputBoundary : Nat
  targetOutputBoundarySize : Nat
  outputCount : Nat

def compactUnifiedParserDoneWitnessCoordinatesOf
    (sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) : CompactUnifiedParserDoneWitnessCoordinates where
  sourceOutputStart := sourceOutputStart
  sourceOutputBoundary := sourceOutputBoundary
  sourceOutputBoundarySize := sourceOutputBoundarySize
  targetOutputStart := targetOutputStart
  targetOutputBoundary := targetOutputBoundary
  targetOutputBoundarySize := targetOutputBoundarySize
  outputCount := outputCount

def CompactUnifiedParserDoneGraphRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates) : Prop :=
  CompactAdditiveNatListSameRows
      tokenTable width tokenCount
        current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount ∧
    CompactAdditiveSyntaxTaskListSameRows
      tokenTable width tokenCount
        current.tasksBoundary current.tasksCount
        next.tasksBoundary next.tasksCount ∧
    ((CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount current.tasksFinish current.finish ∧
      CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount next.tasksFinish next.finish) ∨
      CompactBinaryNatCompletedStatusSameRowsWithSize
        tokenTable width tokenCount
          current.tasksFinish current.finish
          next.tasksFinish next.finish
          witness.sourceOutputStart witness.sourceOutputBoundary
          witness.sourceOutputBoundarySize
          witness.targetOutputStart witness.targetOutputBoundary
          witness.targetOutputBoundarySize witness.outputCount)

def compactUnifiedParserDoneGraphRowsDef :
    𝚺₀.Semisentence 26 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount.
    !(compactAdditiveNatListSameRowsDef)
      tokenTable width tokenCount
        currentTokensBoundary currentTokensCount
        nextTokensBoundary nextTokensCount ∧
    !(compactAdditiveSyntaxTaskListSameRowsDef)
      tokenTable width tokenCount
        currentTasksBoundary currentTasksCount
        nextTasksBoundary nextTasksCount ∧
    ((!(compactBinaryNatFailedStatusSliceDef)
        tokenTable width tokenCount currentTasksFinish currentFinish ∧
      !(compactBinaryNatFailedStatusSliceDef)
        tokenTable width tokenCount nextTasksFinish nextFinish) ∨
      (!(compactBinaryNatCompletedStatusPrefixDef)
          tokenTable width tokenCount currentTasksFinish sourceOutputStart ∧
       !(compactAdditiveStructuredListLayoutDef)
          tokenTable width tokenCount sourceOutputStart outputCount
            currentFinish sourceOutputBoundary ∧
       !(compactBinaryNatCompletedStatusPrefixDef)
          tokenTable width tokenCount nextTasksFinish targetOutputStart ∧
       !(compactAdditiveStructuredListLayoutDef)
          tokenTable width tokenCount targetOutputStart outputCount
            nextFinish targetOutputBoundary ∧
       !(compactAdditiveNatListSameRowsDef)
          tokenTable width tokenCount sourceOutputBoundary outputCount
            targetOutputBoundary outputCount ∧
       !(compactNatSizeDef)
          sourceOutputBoundarySize sourceOutputBoundary ∧
       sourceOutputBoundarySize ≤ (outputCount + 1) * tokenCount ∧
       !(compactNatSizeDef)
          targetOutputBoundarySize targetOutputBoundary ∧
       targetOutputBoundarySize ≤ (outputCount + 1) * tokenCount))”

def compactUnifiedParserDoneFormulaEnvironment
    (tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) : Fin 26 → Nat :=
  ![tokenTable, width, tokenCount,
    currentStart, currentFinish, currentTokensFinish, currentTasksFinish,
    currentTokensBoundary, currentTokensCount,
    currentTasksBoundary, currentTasksCount,
    nextStart, nextFinish, nextTokensFinish, nextTasksFinish,
    nextTokensBoundary, nextTokensCount, nextTasksBoundary, nextTasksCount,
    sourceOutputStart, sourceOutputBoundary, sourceOutputBoundarySize,
    targetOutputStart, targetOutputBoundary, targetOutputBoundarySize,
    outputCount]

@[simp] theorem compactUnifiedParserDoneGraphRowsDef_spec
    (tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) :
    compactUnifiedParserDoneGraphRowsDef.val.Evalb
        (compactUnifiedParserDoneFormulaEnvironment
          tokenTable width tokenCount
          currentStart currentFinish currentTokensFinish currentTasksFinish
          currentTokensBoundary currentTokensCount
          currentTasksBoundary currentTasksCount
          nextStart nextFinish nextTokensFinish nextTasksFinish
          nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) ↔
      CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
        (compactUnifiedParserStateRowCoordinatesOf
          currentStart currentFinish currentTokensFinish currentTasksFinish
          currentTokensBoundary currentTokensCount
          currentTasksBoundary currentTasksCount)
        (compactUnifiedParserStateRowCoordinatesOf
          nextStart nextFinish nextTokensFinish nextTasksFinish
          nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount)
        (compactUnifiedParserDoneWitnessCoordinatesOf
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) := by
  let env := compactUnifiedParserDoneFormulaEnvironment
    tokenTable width tokenCount
    currentStart currentFinish currentTokensFinish currentTasksFinish
    currentTokensBoundary currentTokensCount
    currentTasksBoundary currentTasksCount
    nextStart nextFinish nextTokensFinish nextTasksFinish
    nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
    sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
    targetOutputStart targetOutputBoundary targetOutputBoundarySize
    outputCount
  change compactUnifiedParserDoneGraphRowsDef.val.Evalb env ↔ _
  have htokensEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #7, #8, #15, #16]) =
        ![tokenTable, width, tokenCount,
          currentTokensBoundary, currentTokensCount,
          nextTokensBoundary, nextTokensCount] := by
    funext index
    fin_cases index <;> rfl
  have htasksEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #9, #10, #17, #18]) =
        ![tokenTable, width, tokenCount,
          currentTasksBoundary, currentTasksCount,
          nextTasksBoundary, nextTasksCount] := by
    funext index
    fin_cases index <;> rfl
  have hcurrentFailedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #6, #4]) =
        ![tokenTable, width, tokenCount,
          currentTasksFinish, currentFinish] := by
    funext index
    fin_cases index <;> rfl
  have hnextFailedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #14, #12]) =
        ![tokenTable, width, tokenCount,
          nextTasksFinish, nextFinish] := by
    funext index
    fin_cases index <;> rfl
  have hsourcePrefixEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #6, #19]) =
        ![tokenTable, width, tokenCount,
          currentTasksFinish, sourceOutputStart] := by
    funext index
    fin_cases index <;> rfl
  have hsourceLayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #19, #25, #4, #20]) =
        ![tokenTable, width, tokenCount, sourceOutputStart, outputCount,
          currentFinish, sourceOutputBoundary] := by
    funext index
    fin_cases index <;> rfl
  have htargetPrefixEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #14, #22]) =
        ![tokenTable, width, tokenCount,
          nextTasksFinish, targetOutputStart] := by
    funext index
    fin_cases index <;> rfl
  have htargetLayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #22, #25, #12, #23]) =
        ![tokenTable, width, tokenCount, targetOutputStart, outputCount,
          nextFinish, targetOutputBoundary] := by
    funext index
    fin_cases index <;> rfl
  have houtputRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #20, #25, #23, #25]) =
        ![tokenTable, width, tokenCount,
          sourceOutputBoundary, outputCount,
          targetOutputBoundary, outputCount] := by
    funext index
    fin_cases index <;> rfl
  simp [compactUnifiedParserDoneGraphRowsDef,
    compactUnifiedParserStateRowCoordinatesOf,
    compactUnifiedParserDoneWitnessCoordinatesOf,
    CompactUnifiedParserDoneGraphRows,
    CompactBinaryNatCompletedStatusSameRowsWithSize,
    CompactBinaryNatCompletedStatusSameRows,
    htokensEnv, htasksEnv, hcurrentFailedEnv, hnextFailedEnv,
    hsourcePrefixEnv, hsourceLayoutEnv,
    htargetPrefixEnv, htargetLayoutEnv, houtputRowsEnv]
  tauto

theorem compactUnifiedParserDoneGraphRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserDoneGraphRowsDef.val := by
  simp [compactUnifiedParserDoneGraphRowsDef]

theorem exists_compactUnifiedParserDoneGraphRows_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    (∃ witness,
        CompactUnifiedParserDoneGraphRows
          tokenTable width tokenCount
            currentCoordinates nextCoordinates witness) ↔
      CompactUnifiedParserStepDoneCase current next := by
  constructor
  · rintro ⟨witness, htokens, htasks, hstatus⟩
    apply (compactUnifiedParserDoneRows_iff hcurrent hnext).mp
    refine ⟨htokens, htasks, ?_⟩
    rcases hstatus with hfailed | hcompleted
    · exact Or.inl hfailed
    · exact Or.inr ⟨witness.sourceOutputStart,
        witness.sourceOutputBoundary,
        witness.targetOutputStart, witness.targetOutputBoundary,
        witness.outputCount, hcompleted.1⟩
  · intro hdone
    have hrows :=
      (compactUnifiedParserDoneRows_iff hcurrent hnext).mpr hdone
    rcases hrows with ⟨htokens, htasks, _hstatus⟩
    rcases hdone with ⟨result, hcurrentStatus, hstate⟩
    subst next
    cases result with
    | none =>
        let witness : CompactUnifiedParserDoneWitnessCoordinates :=
          compactUnifiedParserDoneWitnessCoordinatesOf 0 0 0 0 0 0 0
        refine ⟨witness, htokens, htasks, Or.inl ?_⟩
        exact
          ⟨(FoundationCompactNumericListedDirectBinaryNatStatusCases.CompactBinaryNatStreamStatusDirectLayout.failed_iff
              hcurrent.statusLayout).mpr hcurrentStatus,
            (FoundationCompactNumericListedDirectBinaryNatStatusCases.CompactBinaryNatStreamStatusDirectLayout.failed_iff
              hnext.statusLayout).mpr hcurrentStatus⟩
    | some output =>
        rcases
            (completedStatusSameRowsWithSize_iff
              hcurrent.statusLayout hnext.statusLayout).mpr
                ⟨output, hcurrentStatus, hcurrentStatus⟩ with
          ⟨sourceOutputStart, sourceOutputBoundary,
            sourceOutputBoundarySize, targetOutputStart,
            targetOutputBoundary, targetOutputBoundarySize,
            outputCount, hcompleted⟩
        let witness : CompactUnifiedParserDoneWitnessCoordinates :=
          compactUnifiedParserDoneWitnessCoordinatesOf
            sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
            targetOutputStart targetOutputBoundary targetOutputBoundarySize
            outputCount
        exact ⟨witness, htokens, htasks, Or.inr hcompleted⟩

def compactUnifiedParserDoneFormulaEnvironmentOf
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates) : Fin 26 → Nat :=
  compactUnifiedParserDoneFormulaEnvironment
    tokenTable width tokenCount
    current.start current.finish current.tokensFinish current.tasksFinish
    current.tokensBoundary current.tokensCount
    current.tasksBoundary current.tasksCount
    next.start next.finish next.tokensFinish next.tasksFinish
    next.tokensBoundary next.tokensCount next.tasksBoundary next.tasksCount
    witness.sourceOutputStart witness.sourceOutputBoundary
    witness.sourceOutputBoundarySize
    witness.targetOutputStart witness.targetOutputBoundary
    witness.targetOutputBoundarySize witness.outputCount

@[simp] theorem compactUnifiedParserDoneGraphRowsDef_environmentOf_iff
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates) :
    compactUnifiedParserDoneGraphRowsDef.val.Evalb
        (compactUnifiedParserDoneFormulaEnvironmentOf
          tokenTable width tokenCount current next witness) ↔
      CompactUnifiedParserDoneGraphRows
        tokenTable width tokenCount current next witness := by
  simpa [compactUnifiedParserDoneFormulaEnvironmentOf,
    compactUnifiedParserStateRowCoordinatesOf,
    compactUnifiedParserDoneWitnessCoordinatesOf] using
    compactUnifiedParserDoneGraphRowsDef_spec
      tokenTable width tokenCount
      current.start current.finish current.tokensFinish current.tasksFinish
      current.tokensBoundary current.tokensCount
      current.tasksBoundary current.tasksCount
      next.start next.finish next.tokensFinish next.tasksFinish
      next.tokensBoundary next.tokensCount next.tasksBoundary next.tasksCount
      witness.sourceOutputStart witness.sourceOutputBoundary
      witness.sourceOutputBoundarySize
      witness.targetOutputStart witness.targetOutputBoundary
      witness.targetOutputBoundarySize witness.outputCount

#print axioms compactUnifiedParserDoneGraphRowsDef_spec
#print axioms compactUnifiedParserDoneGraphRowsDef_sigmaZero
#print axioms exists_compactUnifiedParserDoneGraphRows_iff
#print axioms compactUnifiedParserDoneGraphRowsDef_environmentOf_iff

end FoundationCompactNumericListedDirectParserDoneFormula
