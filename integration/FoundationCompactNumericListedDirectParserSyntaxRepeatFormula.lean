import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatRows

/-!
# Handwritten bounded formula for the repeated-term syntax task

The formula shares two parser-state coordinate blocks, binds the current head
task through the canonical uncons graph, and distinguishes zero from successor
repeat counts.  The positive branch carries an explicit predecessor coordinate
so the arithmetic formula uses addition rather than meta-level subtraction.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatFormula

open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows

def compactSyntaxRepeatTaskWitnessCoordinatesOf
    (tailBoundary tailCount tailBoundarySize decrementedCount : Nat) :
    CompactSyntaxRepeatTaskWitnessCoordinates where
  tailBoundary := tailBoundary
  tailCount := tailCount
  tailBoundarySize := tailBoundarySize
  decrementedCount := decrementedCount

def compactUnifiedParserSyntaxRepeatRowsDef : 𝚺₀.Semisentence 25 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      binderArity repeatCount
      tailBoundary tailCount tailBoundarySize decrementedCount.
    !(compactBinaryNatRunningStatusSliceDef)
      tokenTable width tokenCount currentTasksFinish currentFinish ∧
    !(compactBinaryNatRunningStatusSliceDef)
      tokenTable width tokenCount nextTasksFinish nextFinish ∧
    !(compactAdditiveNatListSameRowsDef)
      tokenTable width tokenCount
        currentTokensBoundary currentTokensCount
        nextTokensBoundary nextTokensCount ∧
    !(compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef)
      tokenTable width tokenCount
        currentTasksBoundary currentTasksCount
        tailBoundary tailCount tailBoundarySize
        2 binderArity repeatCount ∧
    ((repeatCount = 0 ∧
      !(compactAdditiveSyntaxTaskListSameRowsDef)
        tokenTable width tokenCount
          tailBoundary tailCount nextTasksBoundary nextTasksCount) ∨
     (repeatCount = decrementedCount + 1 ∧
      !(compactAdditiveSyntaxTaskListDropRowsDef)
        tokenTable width tokenCount
          nextTasksBoundary nextTasksCount tailBoundary tailCount 2 ∧
      !(compactAdditiveSyntaxTaskListAtRowsDef)
        tokenTable width tokenCount nextTasksBoundary nextTasksCount
          0 0 binderArity 0 ∧
      !(compactAdditiveSyntaxTaskListAtRowsDef)
        tokenTable width tokenCount nextTasksBoundary nextTasksCount
          1 2 binderArity decrementedCount))”

def compactUnifiedParserSyntaxRepeatFormulaEnvironment
    (tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      binderArity repeatCount
      tailBoundary tailCount tailBoundarySize decrementedCount : Nat) :
    Fin 25 → Nat :=
  ![tokenTable, width, tokenCount,
    currentStart, currentFinish, currentTokensFinish, currentTasksFinish,
    currentTokensBoundary, currentTokensCount,
    currentTasksBoundary, currentTasksCount,
    nextStart, nextFinish, nextTokensFinish, nextTasksFinish,
    nextTokensBoundary, nextTokensCount, nextTasksBoundary, nextTasksCount,
    binderArity, repeatCount,
    tailBoundary, tailCount, tailBoundarySize, decrementedCount]

@[simp] theorem compactUnifiedParserSyntaxRepeatRowsDef_spec
    (tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      binderArity repeatCount
      tailBoundary tailCount tailBoundarySize decrementedCount : Nat) :
    compactUnifiedParserSyntaxRepeatRowsDef.val.Evalb
        (compactUnifiedParserSyntaxRepeatFormulaEnvironment
          tokenTable width tokenCount
          currentStart currentFinish currentTokensFinish currentTasksFinish
          currentTokensBoundary currentTokensCount
          currentTasksBoundary currentTasksCount
          nextStart nextFinish nextTokensFinish nextTasksFinish
          nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
          binderArity repeatCount
          tailBoundary tailCount tailBoundarySize decrementedCount) ↔
      CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount
        (compactUnifiedParserStateRowCoordinatesOf
          currentStart currentFinish currentTokensFinish currentTasksFinish
          currentTokensBoundary currentTokensCount
          currentTasksBoundary currentTasksCount)
        (compactUnifiedParserStateRowCoordinatesOf
          nextStart nextFinish nextTokensFinish nextTasksFinish
          nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount)
        binderArity repeatCount
        (compactSyntaxRepeatTaskWitnessCoordinatesOf
          tailBoundary tailCount tailBoundarySize decrementedCount) := by
  let env := compactUnifiedParserSyntaxRepeatFormulaEnvironment
    tokenTable width tokenCount
    currentStart currentFinish currentTokensFinish currentTasksFinish
    currentTokensBoundary currentTokensCount
    currentTasksBoundary currentTasksCount
    nextStart nextFinish nextTokensFinish nextTasksFinish
    nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
    binderArity repeatCount
    tailBoundary tailCount tailBoundarySize decrementedCount
  change compactUnifiedParserSyntaxRepeatRowsDef.val.Evalb env ↔ _
  have hcurrentRunningEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #6, #4]) =
        ![tokenTable, width, tokenCount,
          currentTasksFinish, currentFinish] := by
    funext index
    fin_cases index <;> rfl
  have hnextRunningEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #14, #12]) =
        ![tokenTable, width, tokenCount, nextTasksFinish, nextFinish] := by
    funext index
    fin_cases index <;> rfl
  have htokensEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #7, #8, #15, #16]) =
        ![tokenTable, width, tokenCount,
          currentTokensBoundary, currentTokensCount,
          nextTokensBoundary, nextTokensCount] := by
    funext index
    fin_cases index <;> rfl
  have hunconsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #9, #10, #21, #22,
          #23, (↑(2 : Nat) : Semiterm ℒₒᵣ Empty 25), #19, #20]) =
        ![tokenTable, width, tokenCount,
          currentTasksBoundary, currentTasksCount,
          tailBoundary, tailCount, tailBoundarySize,
          2, binderArity, repeatCount] := by
    funext index
    fin_cases index <;> rfl
  have hsameEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #21, #22, #17, #18]) =
        ![tokenTable, width, tokenCount,
          tailBoundary, tailCount, nextTasksBoundary, nextTasksCount] := by
    funext index
    fin_cases index <;> rfl
  have hdropEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #17, #18, #21, #22,
          (↑(2 : Nat) : Semiterm ℒₒᵣ Empty 25)]) =
        ![tokenTable, width, tokenCount,
          nextTasksBoundary, nextTasksCount, tailBoundary, tailCount, 2] := by
    funext index
    fin_cases index <;> rfl
  have htaskZeroEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #17, #18,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 25),
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 25), #19,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 25)]) =
        ![tokenTable, width, tokenCount,
          nextTasksBoundary, nextTasksCount, 0, 0, binderArity, 0] := by
    funext index
    fin_cases index <;> rfl
  have htaskOneEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #17, #18,
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 25),
          (↑(2 : Nat) : Semiterm ℒₒᵣ Empty 25), #19, #24]) =
        ![tokenTable, width, tokenCount,
          nextTasksBoundary, nextTasksCount, 1, 2,
          binderArity, decrementedCount] := by
    funext index
    fin_cases index <;> rfl
  have hunconsSpec :
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef.val.Evalb
          ![tokenTable, width, tokenCount,
            currentTasksBoundary, currentTasksCount,
            tailBoundary, tailCount, tailBoundarySize,
            2, binderArity, repeatCount] ↔
        CompactAdditiveSyntaxTaskListUnconsRowsWithSize
          tokenTable width tokenCount
            currentTasksBoundary currentTasksCount
            tailBoundary tailCount tailBoundarySize
            2 binderArity repeatCount := by
    simpa [compactAdditiveSyntaxTaskListUnconsRowsWithSizeEnvironment] using
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef_spec
        tokenTable width tokenCount
        currentTasksBoundary currentTasksCount
        tailBoundary tailCount tailBoundarySize
        2 binderArity repeatCount
  have htaskZeroSpec :
      compactAdditiveSyntaxTaskListAtRowsDef.val.Evalb
          ![tokenTable, width, tokenCount,
            nextTasksBoundary, nextTasksCount, 0, 0, binderArity, 0] ↔
        CompactAdditiveSyntaxTaskListAtRows
          tokenTable width tokenCount
            nextTasksBoundary nextTasksCount 0 0 binderArity 0 := by
    simpa [compactAdditiveSyntaxTaskListAtRowsEnvironment] using
      compactAdditiveSyntaxTaskListAtRowsDef_spec
        tokenTable width tokenCount
        nextTasksBoundary nextTasksCount 0 0 binderArity 0
  have htaskOneSpec :
      compactAdditiveSyntaxTaskListAtRowsDef.val.Evalb
          ![tokenTable, width, tokenCount,
            nextTasksBoundary, nextTasksCount, 1, 2,
            binderArity, decrementedCount] ↔
        CompactAdditiveSyntaxTaskListAtRows
          tokenTable width tokenCount
            nextTasksBoundary nextTasksCount 1 2
            binderArity decrementedCount := by
    simpa [compactAdditiveSyntaxTaskListAtRowsEnvironment] using
      compactAdditiveSyntaxTaskListAtRowsDef_spec
        tokenTable width tokenCount
        nextTasksBoundary nextTasksCount 1 2
        binderArity decrementedCount
  have hrepeatCountValue : env 20 = repeatCount := rfl
  have hdecrementedCountValue : env 24 = decrementedCount := rfl
  simp [compactUnifiedParserSyntaxRepeatRowsDef,
    compactUnifiedParserStateRowCoordinatesOf,
    compactSyntaxRepeatTaskWitnessCoordinatesOf,
    CompactUnifiedParserSyntaxRepeatRows,
    hcurrentRunningEnv, hnextRunningEnv, htokensEnv, hunconsEnv,
    hsameEnv, hdropEnv, htaskZeroEnv, htaskOneEnv,
    hunconsSpec, htaskZeroSpec, htaskOneSpec,
    hrepeatCountValue, hdecrementedCountValue]

theorem compactUnifiedParserSyntaxRepeatRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserSyntaxRepeatRowsDef.val := by
  simp [compactUnifiedParserSyntaxRepeatRowsDef]

def compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) : Fin 25 → Nat :=
  compactUnifiedParserSyntaxRepeatFormulaEnvironment
    tokenTable width tokenCount
    current.start current.finish current.tokensFinish current.tasksFinish
    current.tokensBoundary current.tokensCount
    current.tasksBoundary current.tasksCount
    next.start next.finish next.tokensFinish next.tasksFinish
    next.tokensBoundary next.tokensCount next.tasksBoundary next.tasksCount
    binderArity repeatCount
    witness.tailBoundary witness.tailCount witness.tailBoundarySize
    witness.decrementedCount

@[simp] theorem compactUnifiedParserSyntaxRepeatRowsDef_environmentOf_iff
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) :
    compactUnifiedParserSyntaxRepeatRowsDef.val.Evalb
        (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf
          tokenTable width tokenCount current next
            binderArity repeatCount witness) ↔
      CompactUnifiedParserSyntaxRepeatRows
        tokenTable width tokenCount current next
          binderArity repeatCount witness := by
  simp [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
    compactUnifiedParserStateRowCoordinatesOf,
    compactSyntaxRepeatTaskWitnessCoordinatesOf]

theorem exists_compactUnifiedParserSyntaxRepeatFormula_iff
    {tokenTable width tokenCount binderArity repeatCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : FoundationCompactParserDirectTrace.CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    (∃ witness,
        compactUnifiedParserSyntaxRepeatRowsDef.val.Evalb
          (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf
            tokenTable width tokenCount currentCoordinates nextCoordinates
              binderArity repeatCount witness)) ↔
      CompactSyntaxParserRepeatTaskCase
        binderArity repeatCount current next := by
  simp only [compactUnifiedParserSyntaxRepeatRowsDef_environmentOf_iff]
  exact compactUnifiedParserSyntaxRepeatRows_iff hcurrent hnext

#print axioms compactUnifiedParserSyntaxRepeatRowsDef_spec
#print axioms compactUnifiedParserSyntaxRepeatRowsDef_sigmaZero
#print axioms compactUnifiedParserSyntaxRepeatRowsDef_environmentOf_iff
#print axioms exists_compactUnifiedParserSyntaxRepeatFormula_iff

end FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
