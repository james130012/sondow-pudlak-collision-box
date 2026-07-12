import integration.FoundationCompactNumericListedDirectParserEmptyRows

/-!
# Handwritten bounded formula for parser completion with an empty task stack

The current and next parser states use the same public token table.  Three
explicit witness coordinates describe the completed output table in the next
state.  The Delta-zero graph forces both task counts to zero, preserves the
remaining token rows, and identifies the completed output with those rows.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserEmptyFormula

open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectCompletedOutputSameRows
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserEmptyRows

structure CompactUnifiedParserEmptyWitnessCoordinates where
  targetOutputStart : Nat
  targetOutputBoundary : Nat
  targetOutputBoundarySize : Nat

def compactUnifiedParserEmptyWitnessCoordinatesOf
    (targetOutputStart targetOutputBoundary targetOutputBoundarySize : Nat) :
    CompactUnifiedParserEmptyWitnessCoordinates where
  targetOutputStart := targetOutputStart
  targetOutputBoundary := targetOutputBoundary
  targetOutputBoundarySize := targetOutputBoundarySize

def CompactUnifiedParserEmptyGraphRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserEmptyWitnessCoordinates) : Prop :=
  current.tasksCount = 0 ∧
    next.tasksCount = 0 ∧
    CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount current.tasksFinish current.finish ∧
    CompactAdditiveNatListSameRows
      tokenTable width tokenCount
        current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount ∧
    CompactBinaryNatCompletedOutputSameRowsWithSize
      tokenTable width tokenCount next.tasksFinish next.finish
        current.tokensBoundary current.tokensCount
        witness.targetOutputStart witness.targetOutputBoundary
        witness.targetOutputBoundarySize

def compactUnifiedParserEmptyGraphRowsDef : 𝚺₀.Semisentence 22 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      targetOutputStart targetOutputBoundary targetOutputBoundarySize.
    currentTasksCount = 0 ∧
    nextTasksCount = 0 ∧
    !(compactBinaryNatRunningStatusSliceDef)
      tokenTable width tokenCount currentTasksFinish currentFinish ∧
    !(compactAdditiveNatListSameRowsDef)
      tokenTable width tokenCount
        currentTokensBoundary currentTokensCount
        nextTokensBoundary nextTokensCount ∧
    !(compactBinaryNatCompletedStatusPrefixDef)
      tokenTable width tokenCount nextTasksFinish targetOutputStart ∧
    !(compactAdditiveStructuredListLayoutDef)
      tokenTable width tokenCount targetOutputStart currentTokensCount
        nextFinish targetOutputBoundary ∧
    !(compactAdditiveNatListSameRowsDef)
      tokenTable width tokenCount
        currentTokensBoundary currentTokensCount
        targetOutputBoundary currentTokensCount ∧
    !(compactNatSizeDef)
      targetOutputBoundarySize targetOutputBoundary ∧
    targetOutputBoundarySize ≤ (currentTokensCount + 1) * tokenCount”

def compactUnifiedParserEmptyFormulaEnvironment
    (tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      targetOutputStart targetOutputBoundary targetOutputBoundarySize : Nat) :
    Fin 22 → Nat :=
  ![tokenTable, width, tokenCount,
    currentStart, currentFinish, currentTokensFinish, currentTasksFinish,
    currentTokensBoundary, currentTokensCount,
    currentTasksBoundary, currentTasksCount,
    nextStart, nextFinish, nextTokensFinish, nextTasksFinish,
    nextTokensBoundary, nextTokensCount, nextTasksBoundary, nextTasksCount,
    targetOutputStart, targetOutputBoundary, targetOutputBoundarySize]

@[simp] theorem compactUnifiedParserEmptyGraphRowsDef_spec
    (tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      targetOutputStart targetOutputBoundary targetOutputBoundarySize : Nat) :
    compactUnifiedParserEmptyGraphRowsDef.val.Evalb
        (compactUnifiedParserEmptyFormulaEnvironment
          tokenTable width tokenCount
          currentStart currentFinish currentTokensFinish currentTasksFinish
          currentTokensBoundary currentTokensCount
          currentTasksBoundary currentTasksCount
          nextStart nextFinish nextTokensFinish nextTasksFinish
          nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
          targetOutputStart targetOutputBoundary targetOutputBoundarySize) ↔
      CompactUnifiedParserEmptyGraphRows tokenTable width tokenCount
        (compactUnifiedParserStateRowCoordinatesOf
          currentStart currentFinish currentTokensFinish currentTasksFinish
          currentTokensBoundary currentTokensCount
          currentTasksBoundary currentTasksCount)
        (compactUnifiedParserStateRowCoordinatesOf
          nextStart nextFinish nextTokensFinish nextTasksFinish
          nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount)
        (compactUnifiedParserEmptyWitnessCoordinatesOf
          targetOutputStart targetOutputBoundary targetOutputBoundarySize) := by
  let env := compactUnifiedParserEmptyFormulaEnvironment
    tokenTable width tokenCount
    currentStart currentFinish currentTokensFinish currentTasksFinish
    currentTokensBoundary currentTokensCount
    currentTasksBoundary currentTasksCount
    nextStart nextFinish nextTokensFinish nextTasksFinish
    nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
    targetOutputStart targetOutputBoundary targetOutputBoundarySize
  change compactUnifiedParserEmptyGraphRowsDef.val.Evalb env ↔ _
  have hcurrentRunningEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2, #6, #4]) =
        ![tokenTable, width, tokenCount,
          currentTasksFinish, currentFinish] := by
    funext index
    fin_cases index <;> rfl
  have htokenRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2, #7, #8, #15, #16]) =
        ![tokenTable, width, tokenCount,
          currentTokensBoundary, currentTokensCount,
          nextTokensBoundary, nextTokensCount] := by
    funext index
    fin_cases index <;> rfl
  have htargetPrefixEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2, #14, #19]) =
        ![tokenTable, width, tokenCount,
          nextTasksFinish, targetOutputStart] := by
    funext index
    fin_cases index <;> rfl
  have htargetLayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2, #19, #8, #12, #20]) =
        ![tokenTable, width, tokenCount, targetOutputStart,
          currentTokensCount, nextFinish, targetOutputBoundary] := by
    funext index
    fin_cases index <;> rfl
  have houtputRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2, #7, #8, #20, #8]) =
        ![tokenTable, width, tokenCount,
          currentTokensBoundary, currentTokensCount,
          targetOutputBoundary, currentTokensCount] := by
    funext index
    fin_cases index <;> rfl
  have htokenCountValue : env 2 = tokenCount := rfl
  have hcurrentTokensCountValue : env 8 = currentTokensCount := rfl
  have hcurrentTasksCountValue : env 10 = currentTasksCount := rfl
  have hnextTasksCountValue : env 18 = nextTasksCount := rfl
  have htargetOutputBoundaryValue : env 20 = targetOutputBoundary := rfl
  have htargetOutputBoundarySizeValue :
      env 21 = targetOutputBoundarySize := rfl
  simp [compactUnifiedParserEmptyGraphRowsDef,
    compactUnifiedParserStateRowCoordinatesOf,
    compactUnifiedParserEmptyWitnessCoordinatesOf,
    CompactUnifiedParserEmptyGraphRows,
    CompactBinaryNatCompletedOutputSameRowsWithSize,
    CompactBinaryNatCompletedOutputSameRows,
    hcurrentRunningEnv, htokenRowsEnv, htargetPrefixEnv,
    htargetLayoutEnv, houtputRowsEnv,
    htokenCountValue, hcurrentTokensCountValue,
    hcurrentTasksCountValue, hnextTasksCountValue,
    htargetOutputBoundaryValue, htargetOutputBoundarySizeValue]
  tauto

theorem compactUnifiedParserEmptyGraphRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserEmptyGraphRowsDef.val := by
  simp [compactUnifiedParserEmptyGraphRowsDef]

theorem exists_compactUnifiedParserEmptyGraphRows_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    (∃ witness,
        CompactUnifiedParserEmptyGraphRows
          tokenTable width tokenCount
            currentCoordinates nextCoordinates witness) ↔
      CompactUnifiedParserStepEmptyCase current next := by
  constructor
  · rintro ⟨witness, hcurrentCount, hnextCount,
      hcurrentRunning, htokenRows, hcompleted⟩
    apply (compactUnifiedParserEmptyRows_iff hcurrent hnext).mp
    exact ⟨hcurrentCount, hnextCount, hcurrentRunning, htokenRows,
      witness.targetOutputStart, witness.targetOutputBoundary, hcompleted.1⟩
  · intro hempty
    have hrows :=
      (compactUnifiedParserEmptyRows_iff hcurrent hnext).mpr hempty
    rcases hrows with
      ⟨hcurrentCount, hnextCount, hcurrentRunning,
        htokenRows, outputStart, outputBoundary, hcompleted⟩
    have hnextStatus : next.2.2 = some (some current.1) :=
      (completedOutputSameRows_iff
        hcurrent.tokensRows hnext.statusLayout).mp
          ⟨outputStart, outputBoundary, by
            simpa only [hcurrent.tokensCount_eq] using hcompleted⟩
    rcases
        (completedOutputSameRowsWithSize_iff
          hcurrent.tokensRows hnext.statusLayout).mpr hnextStatus with
      ⟨targetOutputStart, targetOutputBoundary,
        targetOutputBoundarySize, hcompletedWithSize⟩
    let witness : CompactUnifiedParserEmptyWitnessCoordinates :=
      compactUnifiedParserEmptyWitnessCoordinatesOf
        targetOutputStart targetOutputBoundary targetOutputBoundarySize
    have hcompletedWithSize' :
        CompactBinaryNatCompletedOutputSameRowsWithSize
          tokenTable width tokenCount
            nextCoordinates.tasksFinish nextCoordinates.finish
            currentCoordinates.tokensBoundary currentCoordinates.tokensCount
            targetOutputStart targetOutputBoundary
            targetOutputBoundarySize := by
      simpa only [hcurrent.tokensCount_eq] using hcompletedWithSize
    exact ⟨witness, hcurrentCount, hnextCount,
      hcurrentRunning, htokenRows, hcompletedWithSize'⟩

def compactUnifiedParserEmptyFormulaEnvironmentOf
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserEmptyWitnessCoordinates) : Fin 22 → Nat :=
  compactUnifiedParserEmptyFormulaEnvironment
    tokenTable width tokenCount
    current.start current.finish current.tokensFinish current.tasksFinish
    current.tokensBoundary current.tokensCount
    current.tasksBoundary current.tasksCount
    next.start next.finish next.tokensFinish next.tasksFinish
    next.tokensBoundary next.tokensCount next.tasksBoundary next.tasksCount
    witness.targetOutputStart witness.targetOutputBoundary
    witness.targetOutputBoundarySize

@[simp] theorem compactUnifiedParserEmptyGraphRowsDef_environmentOf_iff
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserEmptyWitnessCoordinates) :
    compactUnifiedParserEmptyGraphRowsDef.val.Evalb
        (compactUnifiedParserEmptyFormulaEnvironmentOf
          tokenTable width tokenCount current next witness) ↔
      CompactUnifiedParserEmptyGraphRows
        tokenTable width tokenCount current next witness := by
  simp [compactUnifiedParserEmptyFormulaEnvironmentOf,
    compactUnifiedParserStateRowCoordinatesOf,
    compactUnifiedParserEmptyWitnessCoordinatesOf]

#print axioms compactUnifiedParserEmptyGraphRowsDef_spec
#print axioms compactUnifiedParserEmptyGraphRowsDef_sigmaZero
#print axioms exists_compactUnifiedParserEmptyGraphRows_iff
#print axioms compactUnifiedParserEmptyGraphRowsDef_environmentOf_iff

end FoundationCompactNumericListedDirectParserEmptyFormula
