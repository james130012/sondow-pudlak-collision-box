import integration.FoundationCompactNumericListedDirectParserSyntaxTermRows
import integration.FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula

/-!
# Handwritten bounded formula for the syntax term task

Three small formulas expose the exact failed, continuing, and function-task
state transformations.  The final formula combines them with direct token
lookup and the finite ordered-ring function-code predicate, following the
public `compactTermTokenStep` branch order exactly.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxTermFormula

open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows

def compactUnifiedParserSyntaxTermFailureRowsDef :
    𝚺₀.Semisentence 21 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      tailBoundary tailCount.
    !(compactBinaryNatFailedStatusSliceDef)
      tokenTable width tokenCount nextTasksFinish nextFinish ∧
    !(compactAdditiveNatListSameRowsDef)
      tokenTable width tokenCount
        currentTokensBoundary currentTokensCount
        nextTokensBoundary nextTokensCount ∧
    !(compactAdditiveSyntaxTaskListSameRowsDef)
      tokenTable width tokenCount
        tailBoundary tailCount nextTasksBoundary nextTasksCount”

def compactUnifiedParserSyntaxTermFailureEnvironment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat) : Fin 21 → Nat :=
  ![tokenTable, width, tokenCount,
    current.start, current.finish, current.tokensFinish, current.tasksFinish,
    current.tokensBoundary, current.tokensCount,
    current.tasksBoundary, current.tasksCount,
    next.start, next.finish, next.tokensFinish, next.tasksFinish,
    next.tokensBoundary, next.tokensCount, next.tasksBoundary, next.tasksCount,
    tailBoundary, tailCount]

@[simp] theorem compactUnifiedParserSyntaxTermFailureRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat) :
    compactUnifiedParserSyntaxTermFailureRowsDef.val.Evalb
        (compactUnifiedParserSyntaxTermFailureEnvironment
          tokenTable width tokenCount current next tailBoundary tailCount) ↔
      CompactUnifiedParserSyntaxTermFailureRows
        tokenTable width tokenCount current next tailBoundary tailCount := by
  let env := compactUnifiedParserSyntaxTermFailureEnvironment
    tokenTable width tokenCount current next tailBoundary tailCount
  change compactUnifiedParserSyntaxTermFailureRowsDef.val.Evalb env ↔ _
  have hfailedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 21), #1, #2, #14, #12]) =
        ![tokenTable, width, tokenCount, next.tasksFinish, next.finish] := by
    funext index
    fin_cases index <;> rfl
  have htokenEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 21), #1, #2, #7, #8, #15, #16]) =
        ![tokenTable, width, tokenCount,
          current.tokensBoundary, current.tokensCount,
          next.tokensBoundary, next.tokensCount] := by
    funext index
    fin_cases index <;> rfl
  have htaskEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 21), #1, #2, #19, #20, #17, #18]) =
        ![tokenTable, width, tokenCount,
          tailBoundary, tailCount, next.tasksBoundary, next.tasksCount] := by
    funext index
    fin_cases index <;> rfl
  simp [compactUnifiedParserSyntaxTermFailureRowsDef,
    CompactUnifiedParserSyntaxTermFailureRows,
    hfailedEnv, htokenEnv, htaskEnv]

theorem compactUnifiedParserSyntaxTermFailureRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserSyntaxTermFailureRowsDef.val := by
  simp [compactUnifiedParserSyntaxTermFailureRowsDef]

def compactUnifiedParserSyntaxTermContinueRowsDef :
    𝚺₀.Semisentence 22 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      tailBoundary tailCount consumed.
    !(compactBinaryNatRunningStatusSliceDef)
      tokenTable width tokenCount nextTasksFinish nextFinish ∧
    !(compactAdditiveNatListDropRowsDef)
      tokenTable width tokenCount
        currentTokensBoundary currentTokensCount
        nextTokensBoundary nextTokensCount consumed ∧
    !(compactAdditiveSyntaxTaskListSameRowsDef)
      tokenTable width tokenCount
        tailBoundary tailCount nextTasksBoundary nextTasksCount”

def compactUnifiedParserSyntaxTermContinueEnvironment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount consumed : Nat) : Fin 22 → Nat :=
  ![tokenTable, width, tokenCount,
    current.start, current.finish, current.tokensFinish, current.tasksFinish,
    current.tokensBoundary, current.tokensCount,
    current.tasksBoundary, current.tasksCount,
    next.start, next.finish, next.tokensFinish, next.tasksFinish,
    next.tokensBoundary, next.tokensCount, next.tasksBoundary, next.tasksCount,
    tailBoundary, tailCount, consumed]

@[simp] theorem compactUnifiedParserSyntaxTermContinueRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount consumed : Nat) :
    compactUnifiedParserSyntaxTermContinueRowsDef.val.Evalb
        (compactUnifiedParserSyntaxTermContinueEnvironment
          tokenTable width tokenCount current next
            tailBoundary tailCount consumed) ↔
      CompactUnifiedParserSyntaxTermContinueRows
        tokenTable width tokenCount current next
          tailBoundary tailCount consumed := by
  let env := compactUnifiedParserSyntaxTermContinueEnvironment
    tokenTable width tokenCount current next
      tailBoundary tailCount consumed
  change compactUnifiedParserSyntaxTermContinueRowsDef.val.Evalb env ↔ _
  have hrunningEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2, #14, #12]) =
        ![tokenTable, width, tokenCount, next.tasksFinish, next.finish] := by
    funext index
    fin_cases index <;> rfl
  have htokenEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2,
          #7, #8, #15, #16, #21]) =
        ![tokenTable, width, tokenCount,
          current.tokensBoundary, current.tokensCount,
          next.tokensBoundary, next.tokensCount, consumed] := by
    funext index
    fin_cases index <;> rfl
  have htaskEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2, #19, #20, #17, #18]) =
        ![tokenTable, width, tokenCount,
          tailBoundary, tailCount, next.tasksBoundary, next.tasksCount] := by
    funext index
    fin_cases index <;> rfl
  simp [compactUnifiedParserSyntaxTermContinueRowsDef,
    CompactUnifiedParserSyntaxTermContinueRows,
    hrunningEnv, htokenEnv, htaskEnv]

theorem compactUnifiedParserSyntaxTermContinueRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserSyntaxTermContinueRowsDef.val := by
  simp [compactUnifiedParserSyntaxTermContinueRowsDef]

def compactUnifiedParserSyntaxTermFunctionRowsDef :
    𝚺₀.Semisentence 23 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      tailBoundary tailCount binderArity functionArity.
    !(compactBinaryNatRunningStatusSliceDef)
      tokenTable width tokenCount nextTasksFinish nextFinish ∧
    !(compactAdditiveNatListDropRowsDef)
      tokenTable width tokenCount
        currentTokensBoundary currentTokensCount
        nextTokensBoundary nextTokensCount 3 ∧
    !(compactAdditiveSyntaxTaskListConsRowsDef)
      tokenTable width tokenCount
        tailBoundary tailCount nextTasksBoundary nextTasksCount
        2 binderArity functionArity”

def compactUnifiedParserSyntaxTermFunctionEnvironment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity : Nat) :
    Fin 23 → Nat :=
  ![tokenTable, width, tokenCount,
    current.start, current.finish, current.tokensFinish, current.tasksFinish,
    current.tokensBoundary, current.tokensCount,
    current.tasksBoundary, current.tasksCount,
    next.start, next.finish, next.tokensFinish, next.tasksFinish,
    next.tokensBoundary, next.tokensCount, next.tasksBoundary, next.tasksCount,
    tailBoundary, tailCount, binderArity, functionArity]

@[simp] theorem compactUnifiedParserSyntaxTermFunctionRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity : Nat) :
    compactUnifiedParserSyntaxTermFunctionRowsDef.val.Evalb
        (compactUnifiedParserSyntaxTermFunctionEnvironment
          tokenTable width tokenCount current next
            tailBoundary tailCount binderArity functionArity) ↔
      CompactUnifiedParserSyntaxTermFunctionRows
        tokenTable width tokenCount current next
          tailBoundary tailCount binderArity functionArity := by
  let env := compactUnifiedParserSyntaxTermFunctionEnvironment
    tokenTable width tokenCount current next
      tailBoundary tailCount binderArity functionArity
  change compactUnifiedParserSyntaxTermFunctionRowsDef.val.Evalb env ↔ _
  have hrunningEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 23), #1, #2, #14, #12]) =
        ![tokenTable, width, tokenCount, next.tasksFinish, next.finish] := by
    funext index
    fin_cases index <;> rfl
  have htokenEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 23), #1, #2,
          #7, #8, #15, #16, (↑(3 : Nat) : Semiterm ℒₒᵣ Empty 23)]) =
        ![tokenTable, width, tokenCount,
          current.tokensBoundary, current.tokensCount,
          next.tokensBoundary, next.tokensCount, 3] := by
    funext index
    fin_cases index <;> rfl
  have htaskEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 23), #1, #2,
          #19, #20, #17, #18,
          (↑(2 : Nat) : Semiterm ℒₒᵣ Empty 23), #21, #22]) =
        ![tokenTable, width, tokenCount,
          tailBoundary, tailCount, next.tasksBoundary, next.tasksCount,
          2, binderArity, functionArity] := by
    funext index
    fin_cases index <;> rfl
  simp [compactUnifiedParserSyntaxTermFunctionRowsDef,
    CompactUnifiedParserSyntaxTermFunctionRows,
    hrunningEnv, htokenEnv, htaskEnv]

theorem compactUnifiedParserSyntaxTermFunctionRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserSyntaxTermFunctionRowsDef.val := by
  simp [compactUnifiedParserSyntaxTermFunctionRowsDef]

def compactSyntaxTermTaskWitnessCoordinatesOf
    (tailBoundary tailCount tailBoundarySize tag argument functionCode : Nat) :
    CompactSyntaxTermTaskWitnessCoordinates where
  tailBoundary := tailBoundary
  tailCount := tailCount
  tailBoundarySize := tailBoundarySize
  tag := tag
  argument := argument
  functionCode := functionCode

def compactUnifiedParserSyntaxTermRowsDef : 𝚺₀.Semisentence 26 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      binderArity tailBoundary tailCount tailBoundarySize
      tag argument functionCode.
    !(compactBinaryNatRunningStatusSliceDef)
      tokenTable width tokenCount currentTasksFinish currentFinish ∧
    !(compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef)
      tokenTable width tokenCount
        currentTasksBoundary currentTasksCount
        tailBoundary tailCount tailBoundarySize
        0 binderArity 0 ∧
    ((currentTokensCount ≤ 1 ∧
      !(compactUnifiedParserSyntaxTermFailureRowsDef)
        tokenTable width tokenCount
        currentStart currentFinish currentTokensFinish currentTasksFinish
        currentTokensBoundary currentTokensCount
        currentTasksBoundary currentTasksCount
        nextStart nextFinish nextTokensFinish nextTasksFinish
        nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
        tailBoundary tailCount) ∨
     (2 ≤ currentTokensCount ∧
      !(compactAdditiveNatListAtRowsDef)
        tokenTable width tokenCount
          currentTokensBoundary currentTokensCount 0 tag ∧
      !(compactAdditiveNatListAtRowsDef)
        tokenTable width tokenCount
          currentTokensBoundary currentTokensCount 1 argument ∧
      (((tag = 0 ∧ argument < binderArity ∧
          !(compactUnifiedParserSyntaxTermContinueRowsDef)
            tokenTable width tokenCount
            currentStart currentFinish currentTokensFinish currentTasksFinish
            currentTokensBoundary currentTokensCount
            currentTasksBoundary currentTasksCount
            nextStart nextFinish nextTokensFinish nextTasksFinish
            nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
            tailBoundary tailCount 2) ∨
        (tag = 0 ∧ binderArity ≤ argument ∧
          !(compactUnifiedParserSyntaxTermFailureRowsDef)
            tokenTable width tokenCount
            currentStart currentFinish currentTokensFinish currentTasksFinish
            currentTokensBoundary currentTokensCount
            currentTasksBoundary currentTasksCount
            nextStart nextFinish nextTokensFinish nextTasksFinish
            nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
            tailBoundary tailCount)) ∨
       (tag = 1 ∧
          !(compactUnifiedParserSyntaxTermContinueRowsDef)
            tokenTable width tokenCount
            currentStart currentFinish currentTokensFinish currentTasksFinish
            currentTokensBoundary currentTokensCount
            currentTasksBoundary currentTasksCount
            nextStart nextFinish nextTokensFinish nextTasksFinish
            nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
            tailBoundary tailCount 2) ∨
       (tag = 2 ∧
          ((currentTokensCount ≤ 2 ∧
            !(compactUnifiedParserSyntaxTermFailureRowsDef)
              tokenTable width tokenCount
              currentStart currentFinish currentTokensFinish currentTasksFinish
              currentTokensBoundary currentTokensCount
              currentTasksBoundary currentTasksCount
              nextStart nextFinish nextTokensFinish nextTasksFinish
              nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
              tailBoundary tailCount) ∨
           (3 ≤ currentTokensCount ∧
            !(compactAdditiveNatListAtRowsDef)
              tokenTable width tokenCount
                currentTokensBoundary currentTokensCount 2 functionCode ∧
            ((!(compactAdditiveArithmeticFuncCodeValidDef)
                argument functionCode ∧
              !(compactUnifiedParserSyntaxTermFunctionRowsDef)
                tokenTable width tokenCount
                currentStart currentFinish currentTokensFinish currentTasksFinish
                currentTokensBoundary currentTokensCount
                currentTasksBoundary currentTasksCount
                nextStart nextFinish nextTokensFinish nextTasksFinish
                nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
                tailBoundary tailCount binderArity argument) ∨
             (¬ ((argument = 0 ∧ functionCode = 0) ∨
                 (argument = 0 ∧ functionCode = 1) ∨
                 (argument = 2 ∧ functionCode = 0) ∨
                 (argument = 2 ∧ functionCode = 1)) ∧
              !(compactUnifiedParserSyntaxTermFailureRowsDef)
                tokenTable width tokenCount
                currentStart currentFinish currentTokensFinish currentTasksFinish
                currentTokensBoundary currentTokensCount
                currentTasksBoundary currentTasksCount
                nextStart nextFinish nextTokensFinish nextTasksFinish
                nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
                tailBoundary tailCount))))) ∨
       (tag ≠ 0 ∧ tag ≠ 1 ∧ tag ≠ 2 ∧
          !(compactUnifiedParserSyntaxTermFailureRowsDef)
            tokenTable width tokenCount
            currentStart currentFinish currentTokensFinish currentTasksFinish
            currentTokensBoundary currentTokensCount
            currentTasksBoundary currentTasksCount
            nextStart nextFinish nextTokensFinish nextTasksFinish
            nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
            tailBoundary tailCount))))”

def compactUnifiedParserSyntaxTermFormulaEnvironment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : Fin 26 → Nat :=
  ![tokenTable, width, tokenCount,
    current.start, current.finish, current.tokensFinish, current.tasksFinish,
    current.tokensBoundary, current.tokensCount,
    current.tasksBoundary, current.tasksCount,
    next.start, next.finish, next.tokensFinish, next.tasksFinish,
    next.tokensBoundary, next.tokensCount, next.tasksBoundary, next.tasksCount,
    binderArity, witness.tailBoundary, witness.tailCount,
    witness.tailBoundarySize, witness.tag, witness.argument,
    witness.functionCode]

@[simp] theorem compactUnifiedParserSyntaxTermRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) :
    compactUnifiedParserSyntaxTermRowsDef.val.Evalb
        (compactUnifiedParserSyntaxTermFormulaEnvironment
          tokenTable width tokenCount current next binderArity witness) ↔
      CompactUnifiedParserSyntaxTermRows
        tokenTable width tokenCount current next binderArity witness := by
  let env := compactUnifiedParserSyntaxTermFormulaEnvironment
    tokenTable width tokenCount current next binderArity witness
  change compactUnifiedParserSyntaxTermRowsDef.val.Evalb env ↔ _
  have hrunningEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #6, #4]) =
        ![tokenTable, width, tokenCount, current.tasksFinish, current.finish] := by
    funext index
    fin_cases index <;> rfl
  have hunconsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #9, #10,
          #20, #21, #22,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 26), #19,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 26)]) =
        ![tokenTable, width, tokenCount,
          current.tasksBoundary, current.tasksCount,
          witness.tailBoundary, witness.tailCount, witness.tailBoundarySize,
          0, binderArity, 0] := by
    funext index
    fin_cases index <;> rfl
  have hfailureEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2,
          #3, #4, #5, #6, #7, #8, #9, #10,
          #11, #12, #13, #14, #15, #16, #17, #18, #20, #21]) =
        compactUnifiedParserSyntaxTermFailureEnvironment
          tokenTable width tokenCount current next
            witness.tailBoundary witness.tailCount := by
    funext index
    fin_cases index <;> rfl
  have hcontinueEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2,
          #3, #4, #5, #6, #7, #8, #9, #10,
          #11, #12, #13, #14, #15, #16, #17, #18, #20, #21,
          (↑(2 : Nat) : Semiterm ℒₒᵣ Empty 26)]) =
        compactUnifiedParserSyntaxTermContinueEnvironment
          tokenTable width tokenCount current next
            witness.tailBoundary witness.tailCount 2 := by
    funext index
    fin_cases index <;> rfl
  have hfunctionEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2,
          #3, #4, #5, #6, #7, #8, #9, #10,
          #11, #12, #13, #14, #15, #16, #17, #18,
          #20, #21, #19, #24]) =
        compactUnifiedParserSyntaxTermFunctionEnvironment
          tokenTable width tokenCount current next
            witness.tailBoundary witness.tailCount binderArity witness.argument := by
    funext index
    fin_cases index <;> rfl
  have htagEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #7, #8,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 26), #23]) =
        compactAdditiveNatListAtRowsEnvironment
          tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 0 witness.tag := by
    funext index
    fin_cases index <;> rfl
  have hargumentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #7, #8,
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 26), #24]) =
        compactAdditiveNatListAtRowsEnvironment
          tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 1 witness.argument := by
    funext index
    fin_cases index <;> rfl
  have hfunctionCodeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #7, #8,
          (↑(2 : Nat) : Semiterm ℒₒᵣ Empty 26), #25]) =
        compactAdditiveNatListAtRowsEnvironment
          tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 2 witness.functionCode := by
    funext index
    fin_cases index <;> rfl
  have hvalidEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#24 : Semiterm ℒₒᵣ Empty 26), #25]) =
        ![witness.argument, witness.functionCode] := by
    funext index
    fin_cases index <;> rfl
  have hunconsSpec :
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef.val.Evalb
          ![tokenTable, width, tokenCount,
            current.tasksBoundary, current.tasksCount,
            witness.tailBoundary, witness.tailCount, witness.tailBoundarySize,
            0, binderArity, 0] ↔
        CompactAdditiveSyntaxTaskListUnconsRowsWithSize
          tokenTable width tokenCount
            current.tasksBoundary current.tasksCount
            witness.tailBoundary witness.tailCount witness.tailBoundarySize
            0 binderArity 0 := by
    simpa [compactAdditiveSyntaxTaskListUnconsRowsWithSizeEnvironment] using
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef_spec
        tokenTable width tokenCount
        current.tasksBoundary current.tasksCount
        witness.tailBoundary witness.tailCount witness.tailBoundarySize
        0 binderArity 0
  have htagSpec := compactAdditiveNatListAtRowsDef_spec
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
      0 witness.tag
  have hargumentSpec := compactAdditiveNatListAtRowsDef_spec
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
      1 witness.argument
  have hfunctionCodeSpec := compactAdditiveNatListAtRowsDef_spec
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
      2 witness.functionCode
  have hcurrentTokensCountValue : env 8 = current.tokensCount := rfl
  have hbinderArityValue : env 19 = binderArity := rfl
  have htagValue : env 23 = witness.tag := rfl
  have hargumentValue : env 24 = witness.argument := rfl
  have hfunctionCodeValue : env 25 = witness.functionCode := rfl
  simp [compactUnifiedParserSyntaxTermRowsDef,
    CompactUnifiedParserSyntaxTermRows,
    hrunningEnv, hunconsEnv, hfailureEnv, hcontinueEnv, hfunctionEnv,
    htagEnv, hargumentEnv, hfunctionCodeEnv, hvalidEnv,
    hunconsSpec, htagSpec, hargumentSpec, hfunctionCodeSpec,
    hcurrentTokensCountValue, hbinderArityValue,
    htagValue, hargumentValue, hfunctionCodeValue,
    FoundationCompactArithmeticSymbolCode.ArithmeticFuncCodeValid]
  intro _hcurrentRunning _huncons
  simp [imp_iff_not_or]
  rfl

theorem compactUnifiedParserSyntaxTermRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserSyntaxTermRowsDef.val := by
  simp [compactUnifiedParserSyntaxTermRowsDef]

theorem exists_compactUnifiedParserSyntaxTermFormula_iff
    {tokenTable width tokenCount binderArity : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : FoundationCompactParserDirectTrace.CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    (∃ witness,
        compactUnifiedParserSyntaxTermRowsDef.val.Evalb
          (compactUnifiedParserSyntaxTermFormulaEnvironment
            tokenTable width tokenCount currentCoordinates nextCoordinates
              binderArity witness)) ↔
      CompactSyntaxParserTermTaskCase binderArity current next := by
  simp only [compactUnifiedParserSyntaxTermRowsDef_spec]
  exact compactUnifiedParserSyntaxTermRows_iff hcurrent hnext

#print axioms compactUnifiedParserSyntaxTermFailureRowsDef_spec
#print axioms compactUnifiedParserSyntaxTermFailureRowsDef_sigmaZero
#print axioms compactUnifiedParserSyntaxTermContinueRowsDef_spec
#print axioms compactUnifiedParserSyntaxTermContinueRowsDef_sigmaZero
#print axioms compactUnifiedParserSyntaxTermFunctionRowsDef_spec
#print axioms compactUnifiedParserSyntaxTermFunctionRowsDef_sigmaZero
#print axioms compactUnifiedParserSyntaxTermRowsDef_spec
#print axioms compactUnifiedParserSyntaxTermRowsDef_sigmaZero
#print axioms exists_compactUnifiedParserSyntaxTermFormula_iff

end FoundationCompactNumericListedDirectParserSyntaxTermFormula
