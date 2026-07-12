import integration.FoundationCompactNumericListedDirectParserSyntaxInvalidRows
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFormula

/-!
# Handwritten bounded formula for an invalid syntax-task kind

The formula binds all three fields of the real task head and rejects exactly
when its kind is outside the public set `{0, 1, 2}`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxInvalidFormula

open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectParserSyntaxInvalidRows

def compactSyntaxInvalidTaskWitnessCoordinatesOf
    (tailBoundary tailCount tailBoundarySize kind binderArity repeatCount : Nat) :
    CompactSyntaxInvalidTaskWitnessCoordinates where
  tailBoundary := tailBoundary
  tailCount := tailCount
  tailBoundarySize := tailBoundarySize
  kind := kind
  binderArity := binderArity
  repeatCount := repeatCount

def compactUnifiedParserSyntaxInvalidRowsDef : 𝚺₀.Semisentence 25 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      tailBoundary tailCount tailBoundarySize kind binderArity repeatCount.
    !(compactBinaryNatRunningStatusSliceDef)
      tokenTable width tokenCount currentTasksFinish currentFinish ∧
    !(compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef)
      tokenTable width tokenCount
        currentTasksBoundary currentTasksCount
        tailBoundary tailCount tailBoundarySize
        kind binderArity repeatCount ∧
    kind ≠ 0 ∧ kind ≠ 1 ∧ kind ≠ 2 ∧
    !(compactUnifiedParserSyntaxTermFailureRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      tailBoundary tailCount”

def compactUnifiedParserSyntaxInvalidFormulaEnvironment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates) : Fin 25 → Nat :=
  ![tokenTable, width, tokenCount,
    current.start, current.finish, current.tokensFinish, current.tasksFinish,
    current.tokensBoundary, current.tokensCount,
    current.tasksBoundary, current.tasksCount,
    next.start, next.finish, next.tokensFinish, next.tasksFinish,
    next.tokensBoundary, next.tokensCount, next.tasksBoundary, next.tasksCount,
    witness.tailBoundary, witness.tailCount, witness.tailBoundarySize,
    witness.kind, witness.binderArity, witness.repeatCount]

@[simp] theorem compactUnifiedParserSyntaxInvalidRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates) :
    compactUnifiedParserSyntaxInvalidRowsDef.val.Evalb
        (compactUnifiedParserSyntaxInvalidFormulaEnvironment
          tokenTable width tokenCount current next witness) ↔
      CompactUnifiedParserSyntaxInvalidRows
        tokenTable width tokenCount current next witness := by
  let env := compactUnifiedParserSyntaxInvalidFormulaEnvironment
    tokenTable width tokenCount current next witness
  change compactUnifiedParserSyntaxInvalidRowsDef.val.Evalb env ↔ _
  have hrunningEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #6, #4]) =
        ![tokenTable, width, tokenCount, current.tasksFinish, current.finish] := by
    funext index
    fin_cases index <;> rfl
  have hunconsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #9, #10,
          #19, #20, #21, #22, #23, #24]) =
        ![tokenTable, width, tokenCount,
          current.tasksBoundary, current.tasksCount,
          witness.tailBoundary, witness.tailCount, witness.tailBoundarySize,
          witness.kind, witness.binderArity, witness.repeatCount] := by
    funext index
    fin_cases index <;> rfl
  have hfailureEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2,
          #3, #4, #5, #6, #7, #8, #9, #10,
          #11, #12, #13, #14, #15, #16, #17, #18, #19, #20]) =
        compactUnifiedParserSyntaxTermFailureEnvironment
          tokenTable width tokenCount current next
            witness.tailBoundary witness.tailCount := by
    funext index
    fin_cases index <;> rfl
  have hunconsSpec :
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef.val.Evalb
          ![tokenTable, width, tokenCount,
            current.tasksBoundary, current.tasksCount,
            witness.tailBoundary, witness.tailCount, witness.tailBoundarySize,
            witness.kind, witness.binderArity, witness.repeatCount] ↔
        CompactAdditiveSyntaxTaskListUnconsRowsWithSize
          tokenTable width tokenCount
            current.tasksBoundary current.tasksCount
            witness.tailBoundary witness.tailCount witness.tailBoundarySize
            witness.kind witness.binderArity witness.repeatCount := by
    simpa [compactAdditiveSyntaxTaskListUnconsRowsWithSizeEnvironment] using
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef_spec
        tokenTable width tokenCount
        current.tasksBoundary current.tasksCount
        witness.tailBoundary witness.tailCount witness.tailBoundarySize
        witness.kind witness.binderArity witness.repeatCount
  have hkindValue : env 22 = witness.kind := rfl
  simp [compactUnifiedParserSyntaxInvalidRowsDef,
    CompactUnifiedParserSyntaxInvalidRows,
    hrunningEnv, hunconsEnv, hfailureEnv, hunconsSpec, hkindValue]
  intro _hcurrentRunning _huncons _hkindZero _hkindOne _hfailure
  rfl

theorem compactUnifiedParserSyntaxInvalidRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserSyntaxInvalidRowsDef.val := by
  simp [compactUnifiedParserSyntaxInvalidRowsDef]

theorem exists_compactUnifiedParserSyntaxInvalidFormula_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : FoundationCompactParserDirectTrace.CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    (∃ witness,
        compactUnifiedParserSyntaxInvalidRowsDef.val.Evalb
          (compactUnifiedParserSyntaxInvalidFormulaEnvironment
            tokenTable width tokenCount currentCoordinates nextCoordinates
              witness)) ↔
      CompactSyntaxParserInvalidTaskCase current next := by
  simp only [compactUnifiedParserSyntaxInvalidRowsDef_spec]
  exact compactUnifiedParserSyntaxInvalidRows_iff hcurrent hnext

#print axioms compactUnifiedParserSyntaxInvalidRowsDef_spec
#print axioms compactUnifiedParserSyntaxInvalidRowsDef_sigmaZero
#print axioms exists_compactUnifiedParserSyntaxInvalidFormula_iff

end FoundationCompactNumericListedDirectParserSyntaxInvalidFormula
