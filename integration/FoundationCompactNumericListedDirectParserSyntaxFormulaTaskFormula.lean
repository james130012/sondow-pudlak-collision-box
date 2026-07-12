import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaRows
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFormula

/-!
# Handwritten bounded formula for the syntax formula task

The two helper formulas expose the exact task-stack transformations for binary
connectives and quantifiers.  The final formula then follows all eight public
`compactFormulaTokenStep` tags, including every malformed-input branch.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula

open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows

def compactUnifiedParserSyntaxFormulaBinaryRowsDef :
    𝚺₀.Semisentence 22 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      tailBoundary tailCount binderArity.
    !(compactBinaryNatRunningStatusSliceDef)
      tokenTable width tokenCount nextTasksFinish nextFinish ∧
    !(compactAdditiveNatListDropRowsDef)
      tokenTable width tokenCount
        currentTokensBoundary currentTokensCount
        nextTokensBoundary nextTokensCount 1 ∧
    !(compactAdditiveSyntaxTaskListDropRowsDef)
      tokenTable width tokenCount
        nextTasksBoundary nextTasksCount tailBoundary tailCount 2 ∧
    !(compactAdditiveSyntaxTaskListAtRowsDef)
      tokenTable width tokenCount nextTasksBoundary nextTasksCount
        0 1 binderArity 0 ∧
    !(compactAdditiveSyntaxTaskListAtRowsDef)
      tokenTable width tokenCount nextTasksBoundary nextTasksCount
        1 1 binderArity 0”

def compactUnifiedParserSyntaxFormulaBinaryEnvironment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat) : Fin 22 → Nat :=
  ![tokenTable, width, tokenCount,
    current.start, current.finish, current.tokensFinish, current.tasksFinish,
    current.tokensBoundary, current.tokensCount,
    current.tasksBoundary, current.tasksCount,
    next.start, next.finish, next.tokensFinish, next.tasksFinish,
    next.tokensBoundary, next.tokensCount, next.tasksBoundary, next.tasksCount,
    tailBoundary, tailCount, binderArity]

@[simp] theorem compactUnifiedParserSyntaxFormulaBinaryRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat) :
    compactUnifiedParserSyntaxFormulaBinaryRowsDef.val.Evalb
        (compactUnifiedParserSyntaxFormulaBinaryEnvironment
          tokenTable width tokenCount current next
            tailBoundary tailCount binderArity) ↔
      CompactUnifiedParserSyntaxFormulaBinaryRows
        tokenTable width tokenCount current next
          tailBoundary tailCount binderArity := by
  let env := compactUnifiedParserSyntaxFormulaBinaryEnvironment
    tokenTable width tokenCount current next
      tailBoundary tailCount binderArity
  change compactUnifiedParserSyntaxFormulaBinaryRowsDef.val.Evalb env ↔ _
  have hrunningEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2, #14, #12]) =
        ![tokenTable, width, tokenCount, next.tasksFinish, next.finish] := by
    funext index
    fin_cases index <;> rfl
  have htokenEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2,
          #7, #8, #15, #16,
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 22)]) =
        ![tokenTable, width, tokenCount,
          current.tokensBoundary, current.tokensCount,
          next.tokensBoundary, next.tokensCount, 1] := by
    funext index
    fin_cases index <;> rfl
  have hdropEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2,
          #17, #18, #19, #20,
          (↑(2 : Nat) : Semiterm ℒₒᵣ Empty 22)]) =
        ![tokenTable, width, tokenCount,
          next.tasksBoundary, next.tasksCount,
          tailBoundary, tailCount, 2] := by
    funext index
    fin_cases index <;> rfl
  have htaskZeroEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2, #17, #18,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 22),
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 22), #21,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 22)]) =
        compactAdditiveSyntaxTaskListAtRowsEnvironment
          tokenTable width tokenCount next.tasksBoundary next.tasksCount
            0 1 binderArity 0 := by
    funext index
    fin_cases index <;> rfl
  have htaskOneEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2, #17, #18,
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 22),
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 22), #21,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 22)]) =
        compactAdditiveSyntaxTaskListAtRowsEnvironment
          tokenTable width tokenCount next.tasksBoundary next.tasksCount
            1 1 binderArity 0 := by
    funext index
    fin_cases index <;> rfl
  have htaskZeroSpec := compactAdditiveSyntaxTaskListAtRowsDef_spec
    tokenTable width tokenCount next.tasksBoundary next.tasksCount
      0 1 binderArity 0
  have htaskOneSpec := compactAdditiveSyntaxTaskListAtRowsDef_spec
    tokenTable width tokenCount next.tasksBoundary next.tasksCount
      1 1 binderArity 0
  simp [compactUnifiedParserSyntaxFormulaBinaryRowsDef,
    CompactUnifiedParserSyntaxFormulaBinaryRows,
    hrunningEnv, htokenEnv, hdropEnv, htaskZeroEnv, htaskOneEnv,
    htaskZeroSpec, htaskOneSpec]

theorem compactUnifiedParserSyntaxFormulaBinaryRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserSyntaxFormulaBinaryRowsDef.val := by
  simp [compactUnifiedParserSyntaxFormulaBinaryRowsDef]

def compactUnifiedParserSyntaxFormulaQuantifierRowsDef :
    𝚺₀.Semisentence 22 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      tailBoundary tailCount binderArity.
    !(compactBinaryNatRunningStatusSliceDef)
      tokenTable width tokenCount nextTasksFinish nextFinish ∧
    !(compactAdditiveNatListDropRowsDef)
      tokenTable width tokenCount
        currentTokensBoundary currentTokensCount
        nextTokensBoundary nextTokensCount 1 ∧
    !(compactAdditiveSyntaxTaskListConsRowsDef)
      tokenTable width tokenCount
        tailBoundary tailCount nextTasksBoundary nextTasksCount
        1 (binderArity + 1) 0”

def compactUnifiedParserSyntaxFormulaQuantifierEnvironment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat) : Fin 22 → Nat :=
  ![tokenTable, width, tokenCount,
    current.start, current.finish, current.tokensFinish, current.tasksFinish,
    current.tokensBoundary, current.tokensCount,
    current.tasksBoundary, current.tasksCount,
    next.start, next.finish, next.tokensFinish, next.tasksFinish,
    next.tokensBoundary, next.tokensCount, next.tasksBoundary, next.tasksCount,
    tailBoundary, tailCount, binderArity]

@[simp] theorem compactUnifiedParserSyntaxFormulaQuantifierRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat) :
    compactUnifiedParserSyntaxFormulaQuantifierRowsDef.val.Evalb
        (compactUnifiedParserSyntaxFormulaQuantifierEnvironment
          tokenTable width tokenCount current next
            tailBoundary tailCount binderArity) ↔
      CompactUnifiedParserSyntaxFormulaQuantifierRows
        tokenTable width tokenCount current next
          tailBoundary tailCount binderArity := by
  let env := compactUnifiedParserSyntaxFormulaQuantifierEnvironment
    tokenTable width tokenCount current next
      tailBoundary tailCount binderArity
  change compactUnifiedParserSyntaxFormulaQuantifierRowsDef.val.Evalb env ↔ _
  have hrunningEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2, #14, #12]) =
        ![tokenTable, width, tokenCount, next.tasksFinish, next.finish] := by
    funext index
    fin_cases index <;> rfl
  have htokenEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2,
          #7, #8, #15, #16,
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 22)]) =
        ![tokenTable, width, tokenCount,
          current.tokensBoundary, current.tokensCount,
          next.tokensBoundary, next.tokensCount, 1] := by
    funext index
    fin_cases index <;> rfl
  have htaskEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2,
          #19, #20, #17, #18,
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 22),
          (‘(#21 + 1)’ : Semiterm ℒₒᵣ Empty 22),
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 22)]) =
        ![tokenTable, width, tokenCount,
          tailBoundary, tailCount, next.tasksBoundary, next.tasksCount,
          1, binderArity + 1, 0] := by
    funext index
    fin_cases index <;> rfl
  simp [compactUnifiedParserSyntaxFormulaQuantifierRowsDef,
    CompactUnifiedParserSyntaxFormulaQuantifierRows,
    hrunningEnv, htokenEnv, htaskEnv]

theorem compactUnifiedParserSyntaxFormulaQuantifierRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserSyntaxFormulaQuantifierRowsDef.val := by
  simp [compactUnifiedParserSyntaxFormulaQuantifierRowsDef]

def compactSyntaxFormulaTaskWitnessCoordinatesOf
    (tailBoundary tailCount tailBoundarySize tag relationArity relationCode : Nat) :
    CompactSyntaxFormulaTaskWitnessCoordinates where
  tailBoundary := tailBoundary
  tailCount := tailCount
  tailBoundarySize := tailBoundarySize
  tag := tag
  relationArity := relationArity
  relationCode := relationCode

def compactUnifiedParserSyntaxFormulaRowsDef : 𝚺₀.Semisentence 26 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      binderArity tailBoundary tailCount tailBoundarySize
      tag relationArity relationCode.
    !(compactBinaryNatRunningStatusSliceDef)
      tokenTable width tokenCount currentTasksFinish currentFinish ∧
    !(compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef)
      tokenTable width tokenCount
        currentTasksBoundary currentTasksCount
        tailBoundary tailCount tailBoundarySize
        1 binderArity 0 ∧
    ((currentTokensCount = 0 ∧
      !(compactUnifiedParserSyntaxTermFailureRowsDef)
        tokenTable width tokenCount
        currentStart currentFinish currentTokensFinish currentTasksFinish
        currentTokensBoundary currentTokensCount
        currentTasksBoundary currentTasksCount
        nextStart nextFinish nextTokensFinish nextTasksFinish
        nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
        tailBoundary tailCount) ∨
     (1 ≤ currentTokensCount ∧
      !(compactAdditiveNatListAtRowsDef)
        tokenTable width tokenCount
          currentTokensBoundary currentTokensCount 0 tag ∧
      ((((tag = 0 ∨ tag = 1) ∧
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
                currentTokensBoundary currentTokensCount 1 relationArity ∧
            !(compactAdditiveNatListAtRowsDef)
              tokenTable width tokenCount
                currentTokensBoundary currentTokensCount 2 relationCode ∧
            ((!(compactAdditiveArithmeticRelCodeValidDef)
                relationArity relationCode ∧
              !(compactUnifiedParserSyntaxTermFunctionRowsDef)
                tokenTable width tokenCount
                currentStart currentFinish currentTokensFinish currentTasksFinish
                currentTokensBoundary currentTokensCount
                currentTasksBoundary currentTasksCount
                nextStart nextFinish nextTokensFinish nextTasksFinish
                nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
                tailBoundary tailCount binderArity relationArity) ∨
             (¬ ((relationArity = 2 ∧ relationCode = 0) ∨
                 (relationArity = 2 ∧ relationCode = 1)) ∧
              !(compactUnifiedParserSyntaxTermFailureRowsDef)
                tokenTable width tokenCount
                currentStart currentFinish currentTokensFinish currentTasksFinish
                currentTokensBoundary currentTokensCount
                currentTasksBoundary currentTasksCount
                nextStart nextFinish nextTokensFinish nextTasksFinish
                nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
                tailBoundary tailCount))))) ∨
        ((tag = 2 ∨ tag = 3) ∧
          !(compactUnifiedParserSyntaxTermContinueRowsDef)
            tokenTable width tokenCount
            currentStart currentFinish currentTokensFinish currentTasksFinish
            currentTokensBoundary currentTokensCount
            currentTasksBoundary currentTasksCount
            nextStart nextFinish nextTokensFinish nextTasksFinish
            nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
            tailBoundary tailCount 1) ∨
        ((tag = 4 ∨ tag = 5) ∧
          !(compactUnifiedParserSyntaxFormulaBinaryRowsDef)
            tokenTable width tokenCount
            currentStart currentFinish currentTokensFinish currentTasksFinish
            currentTokensBoundary currentTokensCount
            currentTasksBoundary currentTasksCount
            nextStart nextFinish nextTokensFinish nextTasksFinish
            nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
            tailBoundary tailCount binderArity) ∨
        ((tag = 6 ∨ tag = 7) ∧
          !(compactUnifiedParserSyntaxFormulaQuantifierRowsDef)
            tokenTable width tokenCount
            currentStart currentFinish currentTokensFinish currentTasksFinish
            currentTokensBoundary currentTokensCount
            currentTasksBoundary currentTasksCount
            nextStart nextFinish nextTokensFinish nextTasksFinish
            nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
            tailBoundary tailCount binderArity) ∨
        (tag ≠ 0 ∧ tag ≠ 1 ∧ tag ≠ 2 ∧ tag ≠ 3 ∧
          tag ≠ 4 ∧ tag ≠ 5 ∧ tag ≠ 6 ∧ tag ≠ 7 ∧
          !(compactUnifiedParserSyntaxTermFailureRowsDef)
            tokenTable width tokenCount
            currentStart currentFinish currentTokensFinish currentTasksFinish
            currentTokensBoundary currentTokensCount
            currentTasksBoundary currentTasksCount
            nextStart nextFinish nextTokensFinish nextTasksFinish
            nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
            tailBoundary tailCount)))))”

def compactUnifiedParserSyntaxFormulaTaskEnvironment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : Fin 26 → Nat :=
  ![tokenTable, width, tokenCount,
    current.start, current.finish, current.tokensFinish, current.tasksFinish,
    current.tokensBoundary, current.tokensCount,
    current.tasksBoundary, current.tasksCount,
    next.start, next.finish, next.tokensFinish, next.tasksFinish,
    next.tokensBoundary, next.tokensCount, next.tasksBoundary, next.tasksCount,
    binderArity, witness.tailBoundary, witness.tailCount,
    witness.tailBoundarySize, witness.tag, witness.relationArity,
    witness.relationCode]

@[simp] theorem compactUnifiedParserSyntaxFormulaRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) :
    compactUnifiedParserSyntaxFormulaRowsDef.val.Evalb
        (compactUnifiedParserSyntaxFormulaTaskEnvironment
          tokenTable width tokenCount current next binderArity witness) ↔
      CompactUnifiedParserSyntaxFormulaRows
        tokenTable width tokenCount current next binderArity witness := by
  let env := compactUnifiedParserSyntaxFormulaTaskEnvironment
    tokenTable width tokenCount current next binderArity witness
  change compactUnifiedParserSyntaxFormulaRowsDef.val.Evalb env ↔ _
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
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 26), #19,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 26)]) =
        ![tokenTable, width, tokenCount,
          current.tasksBoundary, current.tasksCount,
          witness.tailBoundary, witness.tailCount, witness.tailBoundarySize,
          1, binderArity, 0] := by
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
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 26)]) =
        compactUnifiedParserSyntaxTermContinueEnvironment
          tokenTable width tokenCount current next
            witness.tailBoundary witness.tailCount 1 := by
    funext index
    fin_cases index <;> rfl
  have hrelationPushEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2,
          #3, #4, #5, #6, #7, #8, #9, #10,
          #11, #12, #13, #14, #15, #16, #17, #18,
          #20, #21, #19, #24]) =
        compactUnifiedParserSyntaxTermFunctionEnvironment
          tokenTable width tokenCount current next
            witness.tailBoundary witness.tailCount
            binderArity witness.relationArity := by
    funext index
    fin_cases index <;> rfl
  have hbinaryEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2,
          #3, #4, #5, #6, #7, #8, #9, #10,
          #11, #12, #13, #14, #15, #16, #17, #18,
          #20, #21, #19]) =
        compactUnifiedParserSyntaxFormulaBinaryEnvironment
          tokenTable width tokenCount current next
            witness.tailBoundary witness.tailCount binderArity := by
    funext index
    fin_cases index <;> rfl
  have hquantifierAtBinaryEnvironmentSpec :
      compactUnifiedParserSyntaxFormulaQuantifierRowsDef.val.Evalb
          (compactUnifiedParserSyntaxFormulaBinaryEnvironment
            tokenTable width tokenCount current next
              witness.tailBoundary witness.tailCount binderArity) ↔
        CompactUnifiedParserSyntaxFormulaQuantifierRows
          tokenTable width tokenCount current next
            witness.tailBoundary witness.tailCount binderArity := by
    simpa [compactUnifiedParserSyntaxFormulaBinaryEnvironment,
      compactUnifiedParserSyntaxFormulaQuantifierEnvironment] using
      compactUnifiedParserSyntaxFormulaQuantifierRowsDef_spec
        tokenTable width tokenCount current next
          witness.tailBoundary witness.tailCount binderArity
  have htagEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #7, #8,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 26), #23]) =
        compactAdditiveNatListAtRowsEnvironment
          tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 0 witness.tag := by
    funext index
    fin_cases index <;> rfl
  have harityEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #7, #8,
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 26), #24]) =
        compactAdditiveNatListAtRowsEnvironment
          tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 1 witness.relationArity := by
    funext index
    fin_cases index <;> rfl
  have hcodeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #7, #8,
          (↑(2 : Nat) : Semiterm ℒₒᵣ Empty 26), #25]) =
        compactAdditiveNatListAtRowsEnvironment
          tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 2 witness.relationCode := by
    funext index
    fin_cases index <;> rfl
  have hvalidEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#24 : Semiterm ℒₒᵣ Empty 26), #25]) =
        ![witness.relationArity, witness.relationCode] := by
    funext index
    fin_cases index <;> rfl
  have hunconsSpec :
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef.val.Evalb
          ![tokenTable, width, tokenCount,
            current.tasksBoundary, current.tasksCount,
            witness.tailBoundary, witness.tailCount, witness.tailBoundarySize,
            1, binderArity, 0] ↔
        CompactAdditiveSyntaxTaskListUnconsRowsWithSize
          tokenTable width tokenCount
            current.tasksBoundary current.tasksCount
            witness.tailBoundary witness.tailCount witness.tailBoundarySize
            1 binderArity 0 := by
    simpa [compactAdditiveSyntaxTaskListUnconsRowsWithSizeEnvironment] using
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef_spec
        tokenTable width tokenCount
        current.tasksBoundary current.tasksCount
        witness.tailBoundary witness.tailCount witness.tailBoundarySize
        1 binderArity 0
  have htagSpec := compactAdditiveNatListAtRowsDef_spec
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
      0 witness.tag
  have haritySpec := compactAdditiveNatListAtRowsDef_spec
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
      1 witness.relationArity
  have hcodeSpec := compactAdditiveNatListAtRowsDef_spec
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
      2 witness.relationCode
  have hcurrentTokensCountValue : env 8 = current.tokensCount := rfl
  have htagValue : env 23 = witness.tag := rfl
  have harityValue : env 24 = witness.relationArity := rfl
  have hcodeValue : env 25 = witness.relationCode := rfl
  simp [compactUnifiedParserSyntaxFormulaRowsDef,
    CompactUnifiedParserSyntaxFormulaRows,
    hrunningEnv, hunconsEnv, hfailureEnv, hcontinueEnv, hrelationPushEnv,
    hbinaryEnv, hquantifierAtBinaryEnvironmentSpec,
    htagEnv, harityEnv, hcodeEnv, hvalidEnv,
    hunconsSpec, htagSpec, haritySpec, hcodeSpec,
    hcurrentTokensCountValue, htagValue, harityValue, hcodeValue,
    FoundationCompactArithmeticSymbolCode.ArithmeticRelCodeValid]
  intro _hcurrentRunning _huncons
  simp [imp_iff_not_or]
  rfl

theorem compactUnifiedParserSyntaxFormulaRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserSyntaxFormulaRowsDef.val := by
  simp [compactUnifiedParserSyntaxFormulaRowsDef]

theorem exists_compactUnifiedParserSyntaxFormulaTaskFormula_iff
    {tokenTable width tokenCount binderArity : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : FoundationCompactParserDirectTrace.CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    (∃ witness,
        compactUnifiedParserSyntaxFormulaRowsDef.val.Evalb
          (compactUnifiedParserSyntaxFormulaTaskEnvironment
            tokenTable width tokenCount currentCoordinates nextCoordinates
              binderArity witness)) ↔
      CompactSyntaxParserFormulaTaskCase binderArity current next := by
  simp only [compactUnifiedParserSyntaxFormulaRowsDef_spec]
  exact compactUnifiedParserSyntaxFormulaRows_iff hcurrent hnext

#print axioms compactUnifiedParserSyntaxFormulaBinaryRowsDef_spec
#print axioms compactUnifiedParserSyntaxFormulaBinaryRowsDef_sigmaZero
#print axioms compactUnifiedParserSyntaxFormulaQuantifierRowsDef_spec
#print axioms compactUnifiedParserSyntaxFormulaQuantifierRowsDef_sigmaZero
#print axioms compactUnifiedParserSyntaxFormulaRowsDef_spec
#print axioms compactUnifiedParserSyntaxFormulaRowsDef_sigmaZero
#print axioms exists_compactUnifiedParserSyntaxFormulaTaskFormula_iff

end FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula
