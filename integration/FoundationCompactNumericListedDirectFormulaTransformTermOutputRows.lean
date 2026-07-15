import integration.FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives

/-!
# Exact direct output rows for syntax-term transformation steps

The relation below exposes every output update used by the six shared
formula transformations on a term task.  Its only list operations are the
already checked direct append graphs; the executable transform is recovered
after the row relation has been interpreted under fixed layouts.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRows

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactParserDirectTrace
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAppendSourcePrefix
open FoundationCompactNumericListedDirectNatListAppendTwoValues
open FoundationCompactNumericListedDirectNatListAppendOneValue
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives

/-- The emitted token list described without an opaque executable predicate. -/
def compactFormulaTransformTermEmission
    (mode binderArity tag argument consumedCount : Nat)
    (witness source : List Nat) : List Nat :=
  if consumedCount = 0 then
    []
  else if mode = 0 then
    if consumedCount = 2 ∧ tag = 0 ∧ argument + 1 = binderArity then
      [1, 0]
    else if consumedCount = 2 ∧ tag = 1 then
      [1, argument + 1]
    else
      source.take consumedCount
  else if mode = 1 then
    if consumedCount = 2 ∧ tag = 1 then
      [1, argument + 1]
    else
      source.take consumedCount
  else if mode = 2 then
    if consumedCount = 2 ∧ tag = 0 ∧ argument + 1 = binderArity then
      witness
    else
      source.take consumedCount
  else if mode = 4 then
    if consumedCount = 2 ∧ tag = 1 then
      [argument]
    else
      []
  else if mode = 5 then
    if consumedCount = 2 ∧ tag = 1 then
      if argument < witness.length then
        [0, binderArity + argument]
      else
        [1, argument - witness.length]
    else
      source.take consumedCount
  else
    source.take consumedCount

def compactFormulaTransformTransitionEmission
    (mode : Nat) (witness : List Nat)
    (current next : CompactSyntaxParserState) : List Nat :=
  let consumed := consumedTokenPrefix current.1 next.1
  if mode = 0 then
    FoundationCompactNumericFormulaFree.compactFormulaFreeEmission
      (FoundationCompactNumericFormulaFree.compactSyntaxCurrentTask current)
      consumed
  else if mode = 1 then
    FoundationCompactNumericFormulaShift.compactFormulaShiftEmission
      (FoundationCompactNumericFormulaShift.compactSyntaxCurrentTaskKind current)
      consumed
  else if mode = 2 then
    FoundationCompactNumericFormulaSubstitution.compactFormulaSubstitutionEmission
      (FoundationCompactNumericFormulaSubstitution.compactSyntaxCurrentTask current)
      (witness, consumed)
  else if mode = 4 then
    FoundationCompactNumericFormulaFvSup.compactFormulaFvListEmission
      (FoundationCompactNumericFormulaFvSup.compactSyntaxCurrentTaskKind current)
      consumed
  else if mode = 5 then
    FoundationCompactNumericFormulaFixitr.compactFormulaFixitrEmission
      (FoundationCompactNumericFormulaFixitr.compactSyntaxCurrentTask current)
      (witness.length, consumed)
  else
    FoundationCompactNumericFormulaNegation.compactFormulaNegationEmission
      (FoundationCompactNumericFormulaNegation.compactSyntaxCurrentTaskKind current)
      consumed

def CompactFormulaTransformTermOutputRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) : Prop :=
  current.parserTokensCount =
      consumedCount + next.parserTokensCount ∧
    ((consumedCount = 0 ∧
        CompactFormulaTransformOutputSameRows
          tokenTable width tokenCount current next) ∨
     (1 ≤ consumedCount ∧
       ((mode = 0 ∧
          (((consumedCount = 2 ∧ tag = 0 ∧
                argument + 1 = binderArity) ∧
              CompactFormulaTransformOutputTwoValuesRows
                tokenTable width tokenCount current next 1 0) ∨
           (¬ (consumedCount = 2 ∧ tag = 0 ∧
                argument + 1 = binderArity) ∧
              (consumedCount = 2 ∧ tag = 1) ∧
              CompactFormulaTransformOutputTwoValuesRows
                tokenTable width tokenCount current next
                  1 (argument + 1)) ∨
           (¬ (consumedCount = 2 ∧ tag = 0 ∧
                argument + 1 = binderArity) ∧
              ¬ (consumedCount = 2 ∧ tag = 1) ∧
              CompactFormulaTransformOutputRawPrefixRows
                tokenTable width tokenCount current next consumedCount))) ∨
        (mode = 1 ∧
          (((consumedCount = 2 ∧ tag = 1) ∧
              CompactFormulaTransformOutputTwoValuesRows
                tokenTable width tokenCount current next
                  1 (argument + 1)) ∨
           (¬ (consumedCount = 2 ∧ tag = 1) ∧
              CompactFormulaTransformOutputRawPrefixRows
                tokenTable width tokenCount current next consumedCount))) ∨
        (mode = 2 ∧
          (((consumedCount = 2 ∧ tag = 0 ∧
                argument + 1 = binderArity) ∧
              CompactFormulaTransformOutputWitnessRows
                tokenTable width tokenCount current next
                  witnessStart witnessFinish witnessCount) ∨
           (¬ (consumedCount = 2 ∧ tag = 0 ∧
                argument + 1 = binderArity) ∧
              CompactFormulaTransformOutputRawPrefixRows
                tokenTable width tokenCount current next consumedCount))) ∨
        (mode = 4 ∧
          (((consumedCount = 2 ∧ tag = 1) ∧
              CompactFormulaTransformOutputOneValueRows
                tokenTable width tokenCount current next argument) ∨
           (¬ (consumedCount = 2 ∧ tag = 1) ∧
              CompactFormulaTransformOutputSameRows
                tokenTable width tokenCount current next))) ∨
        (mode = 5 ∧
          (((consumedCount = 2 ∧ tag = 1 ∧ argument < witnessCount) ∧
              CompactFormulaTransformOutputTwoValuesRows
                tokenTable width tokenCount current next
                  0 (binderArity + argument)) ∨
           ((consumedCount = 2 ∧ tag = 1 ∧ witnessCount ≤ argument) ∧
              ∃ residual ≤ argument,
                argument = witnessCount + residual ∧
                CompactFormulaTransformOutputTwoValuesRows
                  tokenTable width tokenCount current next 1 residual) ∨
           (¬ (consumedCount = 2 ∧ tag = 1) ∧
              CompactFormulaTransformOutputRawPrefixRows
                tokenTable width tokenCount current next consumedCount))) ∨
        (mode ≠ 0 ∧ mode ≠ 1 ∧ mode ≠ 2 ∧ mode ≠ 4 ∧ mode ≠ 5 ∧
          CompactFormulaTransformOutputRawPrefixRows
            tokenTable width tokenCount current next consumedCount))))

def compactFormulaTransformTermOutputRowsDef :
    𝚺₀.Semisentence 33 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentParserFinish
      currentParserTokensFinish currentParserTasksFinish
      currentParserTokensBoundary currentParserTokensCount
      currentParserTasksBoundary currentParserTasksCount
      currentOutputBoundary currentOutputCount
      nextStart nextFinish nextParserFinish
      nextParserTokensFinish nextParserTasksFinish
      nextParserTokensBoundary nextParserTokensCount
      nextParserTasksBoundary nextParserTasksCount
      nextOutputBoundary nextOutputCount
      mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount.
    currentParserTokensCount = consumedCount + nextParserTokensCount ∧
    ((consumedCount = 0 ∧
      !(compactAdditiveNatListSameRowsDef)
        tokenTable width tokenCount
        currentOutputBoundary currentOutputCount
        nextOutputBoundary nextOutputCount) ∨
     (1 ≤ consumedCount ∧
      ((mode = 0 ∧
        (((consumedCount = 2 ∧ tag = 0 ∧
            argument + 1 = binderArity) ∧
          !(compactAdditiveNatListAppendTwoValuesDef)
            tokenTable width tokenCount
            currentParserFinish currentFinish currentOutputCount
            nextParserFinish nextFinish nextOutputBoundary nextOutputCount
            1 0) ∨
         ((consumedCount = 2 → tag = 0 →
              argument + 1 ≠ binderArity) ∧
            (consumedCount = 2 ∧ tag = 1) ∧
          !(compactAdditiveNatListAppendTwoValuesDef)
            tokenTable width tokenCount
            currentParserFinish currentFinish currentOutputCount
            nextParserFinish nextFinish nextOutputBoundary nextOutputCount
            1 (argument + 1)) ∨
         ((consumedCount = 2 → tag = 0 →
              argument + 1 ≠ binderArity) ∧
            (consumedCount = 2 → tag ≠ 1) ∧
          !(compactAdditiveNatListAppendSourcePrefixDef)
            tokenTable width tokenCount
            currentParserFinish currentFinish currentOutputCount
            currentStart currentParserTokensFinish
              currentParserTokensCount consumedCount
            nextParserFinish nextFinish nextOutputCount))) ∨
       (mode = 1 ∧
        (((consumedCount = 2 ∧ tag = 1) ∧
          !(compactAdditiveNatListAppendTwoValuesDef)
            tokenTable width tokenCount
            currentParserFinish currentFinish currentOutputCount
            nextParserFinish nextFinish nextOutputBoundary nextOutputCount
            1 (argument + 1)) ∨
         ((consumedCount = 2 → tag ≠ 1) ∧
          !(compactAdditiveNatListAppendSourcePrefixDef)
            tokenTable width tokenCount
            currentParserFinish currentFinish currentOutputCount
            currentStart currentParserTokensFinish
              currentParserTokensCount consumedCount
            nextParserFinish nextFinish nextOutputCount))) ∨
       (mode = 2 ∧
        (((consumedCount = 2 ∧ tag = 0 ∧
            argument + 1 = binderArity) ∧
          !(compactAdditiveNatListAppendSlicesDef)
            tokenTable width tokenCount
            currentParserFinish currentFinish currentOutputCount
            witnessStart witnessFinish witnessCount
            nextParserFinish nextFinish nextOutputCount) ∨
         ((consumedCount = 2 → tag = 0 →
              argument + 1 ≠ binderArity) ∧
          !(compactAdditiveNatListAppendSourcePrefixDef)
            tokenTable width tokenCount
            currentParserFinish currentFinish currentOutputCount
            currentStart currentParserTokensFinish
              currentParserTokensCount consumedCount
            nextParserFinish nextFinish nextOutputCount))) ∨
       (mode = 4 ∧
        (((consumedCount = 2 ∧ tag = 1) ∧
          !(compactAdditiveNatListAppendOneValueDef)
            tokenTable width tokenCount
            currentParserFinish currentFinish currentOutputCount
            nextParserFinish nextFinish nextOutputBoundary nextOutputCount
            argument) ∨
         ((consumedCount = 2 → tag ≠ 1) ∧
          !(compactAdditiveNatListSameRowsDef)
            tokenTable width tokenCount
            currentOutputBoundary currentOutputCount
            nextOutputBoundary nextOutputCount))) ∨
       (mode = 5 ∧
        (((consumedCount = 2 ∧ tag = 1 ∧ argument < witnessCount) ∧
          !(compactAdditiveNatListAppendTwoValuesDef)
            tokenTable width tokenCount
            currentParserFinish currentFinish currentOutputCount
            nextParserFinish nextFinish nextOutputBoundary nextOutputCount
            0 (binderArity + argument)) ∨
         ((consumedCount = 2 ∧ tag = 1 ∧ witnessCount ≤ argument) ∧
          ∃ residual <⁺ argument,
            argument = witnessCount + residual ∧
            !(compactAdditiveNatListAppendTwoValuesDef)
              tokenTable width tokenCount
              currentParserFinish currentFinish currentOutputCount
              nextParserFinish nextFinish nextOutputBoundary nextOutputCount
              1 residual) ∨
         ((consumedCount = 2 → tag ≠ 1) ∧
          !(compactAdditiveNatListAppendSourcePrefixDef)
            tokenTable width tokenCount
            currentParserFinish currentFinish currentOutputCount
            currentStart currentParserTokensFinish
              currentParserTokensCount consumedCount
            nextParserFinish nextFinish nextOutputCount))) ∨
       (mode ≠ 0 ∧ mode ≠ 1 ∧ mode ≠ 2 ∧ mode ≠ 4 ∧ mode ≠ 5 ∧
        !(compactAdditiveNatListAppendSourcePrefixDef)
          tokenTable width tokenCount
          currentParserFinish currentFinish currentOutputCount
          currentStart currentParserTokensFinish
            currentParserTokensCount consumedCount
          nextParserFinish nextFinish nextOutputCount))))”

def compactFormulaTransformTermOutputRowsEnvironment
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) : Fin 33 → Nat :=
  ![tokenTable, width, tokenCount,
    current.start, current.finish, current.parserFinish,
    current.parserTokensFinish, current.parserTasksFinish,
    current.parserTokensBoundary, current.parserTokensCount,
    current.parserTasksBoundary, current.parserTasksCount,
    current.outputBoundary, current.outputCount,
    next.start, next.finish, next.parserFinish,
    next.parserTokensFinish, next.parserTasksFinish,
    next.parserTokensBoundary, next.parserTokensCount,
    next.parserTasksBoundary, next.parserTasksCount,
    next.outputBoundary, next.outputCount,
    mode, binderArity, tag, argument, consumedCount,
    witnessStart, witnessFinish, witnessCount]

@[simp] theorem compactFormulaTransformTermOutputRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) :
    compactFormulaTransformTermOutputRowsDef.val.Evalb
        (compactFormulaTransformTermOutputRowsEnvironment
          tokenTable width tokenCount current next
          mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount) ↔
      CompactFormulaTransformTermOutputRows
        tokenTable width tokenCount current next
          mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount := by
  let env := compactFormulaTransformTermOutputRowsEnvironment
    tokenTable width tokenCount current next
      mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount
  change compactFormulaTransformTermOutputRowsDef.val.Evalb env ↔ _
  have hsameEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
          #12, #13, #23, #24]) =
        ![tokenTable, width, tokenCount,
          current.outputBoundary, current.outputCount,
          next.outputBoundary, next.outputCount] := by
    funext index
    fin_cases index <;> simp [env,
      compactFormulaTransformTermOutputRowsEnvironment]
  have htwoLowerEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
          #5, #4, #13, #16, #15, #23, #24, ‘1’, ‘0’]) =
        ![tokenTable, width, tokenCount,
          current.parserFinish, current.finish, current.outputCount,
          next.parserFinish, next.finish, next.outputBoundary,
          next.outputCount, 1, 0] := by
    funext index
    fin_cases index <;> simp [env,
      compactFormulaTransformTermOutputRowsEnvironment]
  have htwoShiftEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
          #5, #4, #13, #16, #15, #23, #24,
          ‘1’, ‘(#28 + 1)’]) =
        ![tokenTable, width, tokenCount,
          current.parserFinish, current.finish, current.outputCount,
          next.parserFinish, next.finish, next.outputBoundary,
          next.outputCount, 1, argument + 1] := by
    funext index
    fin_cases index <;> simp [env,
      compactFormulaTransformTermOutputRowsEnvironment]
  have honeValueEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
          #5, #4, #13, #16, #15, #23, #24, #28]) =
        ![tokenTable, width, tokenCount,
          current.parserFinish, current.finish, current.outputCount,
          next.parserFinish, next.finish, next.outputBoundary,
          next.outputCount, argument] := by
    funext index
    fin_cases index <;> simp [env,
      compactFormulaTransformTermOutputRowsEnvironment]
  have htwoCapturedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
          #5, #4, #13, #16, #15, #23, #24,
          ‘0’, ‘(#26 + #28)’]) =
        ![tokenTable, width, tokenCount,
          current.parserFinish, current.finish, current.outputCount,
          next.parserFinish, next.finish, next.outputBoundary,
          next.outputCount, 0, binderArity + argument] := by
    funext index
    fin_cases index <;> simp [env,
      compactFormulaTransformTermOutputRowsEnvironment]
  have hrawEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
          #5, #4, #13, #3, #6, #9, #29, #16, #15, #24]) =
        ![tokenTable, width, tokenCount,
          current.parserFinish, current.finish, current.outputCount,
          current.start, current.parserTokensFinish,
          current.parserTokensCount, consumedCount,
          next.parserFinish, next.finish, next.outputCount] := by
    funext index
    fin_cases index <;> simp [env,
      compactFormulaTransformTermOutputRowsEnvironment]
  have hwitnessEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
          #5, #4, #13, #30, #31, #32, #16, #15, #24]) =
        ![tokenTable, width, tokenCount,
          current.parserFinish, current.finish, current.outputCount,
          witnessStart, witnessFinish, witnessCount,
          next.parserFinish, next.finish, next.outputCount] := by
    funext index
    fin_cases index <;> simp [env,
      compactFormulaTransformTermOutputRowsEnvironment]
  have hsameSpec : compactAdditiveNatListSameRowsDef.val.Evalb
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
            #12, #13, #23, #24]) ↔
      CompactAdditiveNatListSameRows tokenTable width tokenCount
        current.outputBoundary current.outputCount
        next.outputBoundary next.outputCount := by
    rw [hsameEnv]
    exact compactAdditiveNatListSameRowsDef_spec
      tokenTable width tokenCount current.outputBoundary current.outputCount
        next.outputBoundary next.outputCount
  have htwoLowerSpec : compactAdditiveNatListAppendTwoValuesDef.val.Evalb
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
            #5, #4, #13, #16, #15, #23, #24, ‘1’, ‘0’]) ↔
      CompactAdditiveNatListAppendTwoValues tokenTable width tokenCount
        current.parserFinish current.finish current.outputCount
        next.parserFinish next.finish next.outputBoundary next.outputCount
        1 0 := by
    rw [htwoLowerEnv]
    exact compactAdditiveNatListAppendTwoValuesDef_spec
      tokenTable width tokenCount
      current.parserFinish current.finish current.outputCount
      next.parserFinish next.finish next.outputBoundary next.outputCount 1 0
  have htwoShiftSpec : compactAdditiveNatListAppendTwoValuesDef.val.Evalb
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
            #5, #4, #13, #16, #15, #23, #24,
            ‘1’, ‘(#28 + 1)’]) ↔
      CompactAdditiveNatListAppendTwoValues tokenTable width tokenCount
        current.parserFinish current.finish current.outputCount
        next.parserFinish next.finish next.outputBoundary next.outputCount
        1 (argument + 1) := by
    rw [htwoShiftEnv]
    exact compactAdditiveNatListAppendTwoValuesDef_spec
      tokenTable width tokenCount
      current.parserFinish current.finish current.outputCount
      next.parserFinish next.finish next.outputBoundary next.outputCount
      1 (argument + 1)
  have honeValueSpec : compactAdditiveNatListAppendOneValueDef.val.Evalb
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
            #5, #4, #13, #16, #15, #23, #24, #28]) ↔
      CompactAdditiveNatListAppendOneValue tokenTable width tokenCount
        current.parserFinish current.finish current.outputCount
        next.parserFinish next.finish next.outputBoundary next.outputCount
        argument := by
    rw [honeValueEnv]
    exact compactAdditiveNatListAppendOneValueDef_spec
      tokenTable width tokenCount
      current.parserFinish current.finish current.outputCount
      next.parserFinish next.finish next.outputBoundary next.outputCount
      argument
  have htwoCapturedSpec :
      compactAdditiveNatListAppendTwoValuesDef.val.Evalb
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
            #5, #4, #13, #16, #15, #23, #24,
            ‘0’, ‘(#26 + #28)’]) ↔
      CompactAdditiveNatListAppendTwoValues tokenTable width tokenCount
        current.parserFinish current.finish current.outputCount
        next.parserFinish next.finish next.outputBoundary next.outputCount
        0 (binderArity + argument) := by
    rw [htwoCapturedEnv]
    exact compactAdditiveNatListAppendTwoValuesDef_spec
      tokenTable width tokenCount
      current.parserFinish current.finish current.outputCount
      next.parserFinish next.finish next.outputBoundary next.outputCount
      0 (binderArity + argument)
  have htwoResidualSpec (residual : Nat) :
      (Semiformula.Eval
          (Semiterm.val (residual :> env) Empty.elim ∘
            ![(#1 : Semiterm ℒₒᵣ Empty 34), #2, #3,
              #6, #5, #14, #17, #16, #24, #25, ‘1’, #0])
          Empty.elim) compactAdditiveNatListAppendTwoValuesDef.val ↔
      CompactAdditiveNatListAppendTwoValues tokenTable width tokenCount
        current.parserFinish current.finish current.outputCount
        next.parserFinish next.finish next.outputBoundary next.outputCount
        1 residual := by
    have henv :
        (Semiterm.val
            (residual :> env) Empty.elim ∘
          ![(#1 : Semiterm ℒₒᵣ Empty 34), #2, #3,
            #6, #5, #14, #17, #16, #24, #25, ‘1’, #0]) =
          ![tokenTable, width, tokenCount,
            current.parserFinish, current.finish, current.outputCount,
            next.parserFinish, next.finish, next.outputBoundary,
            next.outputCount, 1, residual] := by
      funext index
      fin_cases index <;> simp [env,
        compactFormulaTransformTermOutputRowsEnvironment]
    rw [henv]
    exact compactAdditiveNatListAppendTwoValuesDef_spec
      tokenTable width tokenCount
      current.parserFinish current.finish current.outputCount
      next.parserFinish next.finish next.outputBoundary next.outputCount
      1 residual
  have hrawSpec : compactAdditiveNatListAppendSourcePrefixDef.val.Evalb
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
            #5, #4, #13, #3, #6, #9, #29, #16, #15, #24]) ↔
      CompactAdditiveNatListAppendSourcePrefix tokenTable width tokenCount
        current.parserFinish current.finish current.outputCount
        current.start current.parserTokensFinish current.parserTokensCount
        consumedCount next.parserFinish next.finish next.outputCount := by
    rw [hrawEnv]
    exact compactAdditiveNatListAppendSourcePrefixDef_spec
      tokenTable width tokenCount
      current.parserFinish current.finish current.outputCount
      current.start current.parserTokensFinish current.parserTokensCount
      consumedCount next.parserFinish next.finish next.outputCount
  have hwitnessSpec : compactAdditiveNatListAppendSlicesDef.val.Evalb
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
            #5, #4, #13, #30, #31, #32, #16, #15, #24]) ↔
      CompactAdditiveNatListAppendSlices tokenTable width tokenCount
        current.parserFinish current.finish current.outputCount
        witnessStart witnessFinish witnessCount
        next.parserFinish next.finish next.outputCount := by
    rw [hwitnessEnv]
    exact compactAdditiveNatListAppendSlicesDef_spec
      tokenTable width tokenCount
      current.parserFinish current.finish current.outputCount
      witnessStart witnessFinish witnessCount
      next.parserFinish next.finish next.outputCount
  have hcurrentCountValue : env 9 = current.parserTokensCount := rfl
  have hnextCountValue : env 20 = next.parserTokensCount := rfl
  have hmodeValue : env 25 = mode := rfl
  have hbinderValue : env 26 = binderArity := rfl
  have htagValue : env 27 = tag := rfl
  have hargumentValue : env 28 = argument := rfl
  have hconsumedValue : env 29 = consumedCount := rfl
  have hwitnessCountValue : env 32 = witnessCount := rfl
  simp [compactFormulaTransformTermOutputRowsDef,
    CompactFormulaTransformTermOutputRows,
    CompactFormulaTransformStateRowCoordinates.parser,
    CompactFormulaTransformOutputSameRows,
    CompactFormulaTransformOutputRawPrefixRows,
    CompactFormulaTransformOutputTwoValuesRows,
    CompactFormulaTransformOutputOneValueRows,
    CompactFormulaTransformOutputWitnessRows,
    hsameSpec, htwoLowerSpec, htwoShiftSpec, honeValueSpec,
    htwoCapturedSpec, htwoResidualSpec, hrawSpec, hwitnessSpec,
    hcurrentCountValue, hnextCountValue, hmodeValue, hbinderValue,
    htagValue, hargumentValue, hconsumedValue, hwitnessCountValue]
  intro _hcount
  rfl

theorem compactFormulaTransformTermOutputRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformTermOutputRowsDef.val := by
  simp [compactFormulaTransformTermOutputRowsDef]

theorem compactUnifiedParserSyntaxTermRows_consumption_cases
    {tokenTable width tokenCount binderArity : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current : CompactUnifiedParserState}
    {witness : CompactSyntaxTermTaskWitnessCoordinates}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hrows : CompactUnifiedParserSyntaxTermRows
      tokenTable width tokenCount currentCoordinates nextCoordinates
        binderArity witness) :
    nextCoordinates.tokensCount = currentCoordinates.tokensCount ∨
      (currentCoordinates.tokensCount = 2 + nextCoordinates.tokensCount ∧
        compactTokenAt 0 current.1 = witness.tag ∧
        compactTokenAt 1 current.1 = witness.argument) ∨
      (currentCoordinates.tokensCount = 3 + nextCoordinates.tokensCount ∧
        compactTokenAt 0 current.1 = witness.tag ∧
        compactTokenAt 1 current.1 = witness.argument ∧
        witness.tag = 2) := by
  rcases hrows with ⟨_hcurrentRunning, _huncons, hshort | henough⟩
  · exact Or.inl hshort.2.2.1.1
  · rcases henough with
      ⟨_hlength, htagRows, hargumentRows, hcontrol⟩
    have htag :=
      (compactAdditiveNatListAtRows_iff_getI
        hcurrent.tokensRows 0 witness.tag).mp (by
          simpa only [hcurrent.tokensCount_eq] using htagRows)
    have hargument :=
      (compactAdditiveNatListAtRows_iff_getI
        hcurrent.tokensRows 1 witness.argument).mp (by
          simpa only [hcurrent.tokensCount_eq] using hargumentRows)
    have htagToken : compactTokenAt 0 current.1 = witness.tag :=
      (compactTokenAt_eq_getI 0 current.1).trans htag.2
    have hargumentToken :
        compactTokenAt 1 current.1 = witness.argument :=
      (compactTokenAt_eq_getI 1 current.1).trans hargument.2
    rcases hcontrol with htagZero | htagOne | htagTwo | htagInvalid
    · rcases htagZero with hsuccess | hfailure
      · rcases hsuccess with ⟨_htag, _hbound, hcontinue⟩
        exact Or.inr (Or.inl
          ⟨hcontinue.2.1.2.1, htagToken, hargumentToken⟩)
      · exact Or.inl hfailure.2.2.2.1.1
    · rcases htagOne with ⟨_htag, hcontinue⟩
      exact Or.inr (Or.inl
        ⟨hcontinue.2.1.2.1, htagToken, hargumentToken⟩)
    · rcases htagTwo with ⟨htagValue, hfunction⟩
      rcases hfunction with hshortFunction | henoughFunction
      · exact Or.inl hshortFunction.2.2.1.1
      · rcases henoughFunction with
          ⟨_hlength, _hfunctionCode, hvalid | hinvalid⟩
        · exact Or.inr (Or.inr
            ⟨hvalid.2.2.1.2.1, htagToken, hargumentToken, htagValue⟩)
        · exact Or.inl hinvalid.2.2.1.1
    · exact Or.inl htagInvalid.2.2.2.2.1.1

theorem compactTokenAt_take_of_lt
    (index count : Nat) (tokens : List Nat) (hindex : index < count) :
    compactTokenAt index (tokens.take count) = compactTokenAt index tokens := by
  simp [compactTokenAt, hindex]

theorem compactFormulaTransformTermOutputRows_iff
    {tokenTable width tokenCount mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates}
    {current next : CompactFormulaTransformState}
    {witness : List Nat}
    (hcurrent : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hwitnessCount : witnessCount = witness.length) :
    CompactFormulaTransformTermOutputRows
        tokenTable width tokenCount currentCoordinates nextCoordinates
          mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount ↔
      currentCoordinates.parserTokensCount =
          consumedCount + nextCoordinates.parserTokensCount ∧
        next.2 = current.2 ++
          compactFormulaTransformTermEmission
            mode binderArity tag argument consumedCount witness current.1.1 := by
  subst witnessCount
  have hsame := compactFormulaTransformOutputSameRows_iff hcurrent hnext
  have hraw := compactFormulaTransformOutputRawPrefixRows_iff
    (consumedCount := consumedCount) hcurrent hnext
  have htwoLower := compactFormulaTransformOutputTwoValuesRows_iff
    (first := 1) (second := 0) hcurrent hnext
  have htwoShift := compactFormulaTransformOutputTwoValuesRows_iff
    (first := 1) (second := argument + 1) hcurrent hnext
  have honeValue := compactFormulaTransformOutputOneValueRows_iff
    (value := argument) hcurrent hnext
  have htwoCaptured := compactFormulaTransformOutputTwoValuesRows_iff
    (first := 0) (second := binderArity + argument) hcurrent hnext
  have htwoResidual (residual : Nat) :=
    compactFormulaTransformOutputTwoValuesRows_iff
      (first := 1) (second := residual) hcurrent hnext
  have hwitnessRows :=
    compactFormulaTransformOutputWitnessRows_iff hcurrent hnext hwitness
  constructor
  · rintro ⟨hcount, hzero | hpositive⟩
    · rcases hzero with ⟨hconsumed, hsameRows⟩
      have hout : next.2 = current.2 := hsame.mp hsameRows
      exact ⟨hcount, by
        simpa [compactFormulaTransformTermEmission, hconsumed] using hout⟩
    · rcases hpositive with ⟨hconsumed, hmode⟩
      have hconsumedNe : consumedCount ≠ 0 := by omega
      rcases hmode with hfree | hshift | hsubstitution | hfvList | hfixitr | hother
      · rcases hfree with ⟨rfl, hlower | hshifted | hrawCase⟩
        · rcases hlower with ⟨hlower, hrows⟩
          exact ⟨hcount, by
            simpa [compactFormulaTransformTermEmission, hconsumedNe, hlower]
              using htwoLower.mp hrows⟩
        · rcases hshifted with ⟨hnotLower, hshiftCase, hrows⟩
          exact ⟨hcount, by
            simpa [compactFormulaTransformTermEmission, hconsumedNe,
              hnotLower, hshiftCase] using htwoShift.mp hrows⟩
        · rcases hrawCase with ⟨hnotLower, hnotShift, hrows⟩
          exact ⟨hcount, by
            simpa [compactFormulaTransformTermEmission, hconsumedNe,
              hnotLower, hnotShift] using (hraw.mp hrows).2⟩
      · rcases hshift with ⟨rfl, hshifted | hrawCase⟩
        · rcases hshifted with ⟨hshiftCase, hrows⟩
          exact ⟨hcount, by
            simpa [compactFormulaTransformTermEmission, hconsumedNe,
              hshiftCase] using htwoShift.mp hrows⟩
        · rcases hrawCase with ⟨hnotShift, hrows⟩
          exact ⟨hcount, by
            simpa [compactFormulaTransformTermEmission, hconsumedNe,
              hnotShift] using (hraw.mp hrows).2⟩
      · rcases hsubstitution with ⟨rfl, hlower | hrawCase⟩
        · rcases hlower with ⟨hlowerCase, hrows⟩
          exact ⟨hcount, by
            simpa [compactFormulaTransformTermEmission, hconsumedNe,
              hlowerCase] using hwitnessRows.mp hrows⟩
        · rcases hrawCase with ⟨hnotLower, hrows⟩
          exact ⟨hcount, by
            simpa [compactFormulaTransformTermEmission, hconsumedNe,
              hnotLower] using (hraw.mp hrows).2⟩
      · rcases hfvList with ⟨rfl, hfreeCase | hnotFree⟩
        · rcases hfreeCase with ⟨hfreeCase, hrows⟩
          exact ⟨hcount, by
            simpa [compactFormulaTransformTermEmission, hconsumedNe,
              hfreeCase] using honeValue.mp hrows⟩
        · rcases hnotFree with ⟨hnotFree, hrows⟩
          exact ⟨hcount, by
            simpa [compactFormulaTransformTermEmission, hconsumedNe,
              hnotFree] using hsame.mp hrows⟩
      · rcases hfixitr with ⟨rfl, hcaptured | hremaining | hrawCase⟩
        · rcases hcaptured with ⟨hcaptured, hrows⟩
          exact ⟨hcount, by
            simpa [compactFormulaTransformTermEmission, hconsumedNe,
              hcaptured] using htwoCaptured.mp hrows⟩
        · rcases hremaining with
            ⟨hremaining, residual, _hresidualLe, hargument, hrows⟩
          have hresidual : argument - witness.length = residual := by omega
          exact ⟨hcount, by
            simpa [compactFormulaTransformTermEmission, hconsumedNe,
              hremaining, show ¬ argument < witness.length by omega,
              hresidual] using (htwoResidual residual).mp hrows⟩
        · rcases hrawCase with ⟨hnotFree, hrows⟩
          exact ⟨hcount, by
            simpa [compactFormulaTransformTermEmission, hconsumedNe,
              hnotFree] using (hraw.mp hrows).2⟩
      · rcases hother with ⟨hzero, hone, htwoMode, hfour, hfive, hrows⟩
        exact ⟨hcount, by
          simpa [compactFormulaTransformTermEmission, hconsumedNe,
            hzero, hone, htwoMode, hfour, hfive] using (hraw.mp hrows).2⟩
  · rintro ⟨hcount, hout⟩
    have hcurrentTokenCount :
        currentCoordinates.parserTokensCount = current.1.1.length := by
      simpa [CompactFormulaTransformStateRowCoordinates.parser] using
        hcurrent.parserLayout.tokensCount_eq
    have hconsumedLe : consumedCount ≤ current.1.1.length := by
      rw [← hcurrentTokenCount]
      omega
    refine ⟨hcount, ?_⟩
    by_cases hconsumed : consumedCount = 0
    · exact Or.inl ⟨hconsumed, hsame.mpr (by
        simpa [compactFormulaTransformTermEmission, hconsumed] using hout)⟩
    · refine Or.inr ⟨by omega, ?_⟩
      by_cases hmodeZero : mode = 0
      · refine Or.inl ⟨hmodeZero, ?_⟩
        by_cases hlower : consumedCount = 2 ∧ tag = 0 ∧
            argument + 1 = binderArity
        · exact Or.inl ⟨hlower, htwoLower.mpr (by
            simpa [compactFormulaTransformTermEmission,
              hconsumed, hmodeZero, hlower] using hout)⟩
        · by_cases hshiftCase : consumedCount = 2 ∧ tag = 1
          · exact Or.inr (Or.inl ⟨hlower, hshiftCase, htwoShift.mpr (by
              simpa [compactFormulaTransformTermEmission,
                hconsumed, hmodeZero, hlower, hshiftCase] using hout)⟩)
          · exact Or.inr (Or.inr ⟨hlower, hshiftCase,
              hraw.mpr ⟨hconsumedLe, by
                simpa [compactFormulaTransformTermEmission,
                  hconsumed, hmodeZero, hlower, hshiftCase] using hout⟩⟩)
      · by_cases hmodeOne : mode = 1
        · refine Or.inr (Or.inl ⟨hmodeOne, ?_⟩)
          by_cases hshiftCase : consumedCount = 2 ∧ tag = 1
          · exact Or.inl ⟨hshiftCase, htwoShift.mpr (by
              simpa [compactFormulaTransformTermEmission,
                hconsumed, hmodeZero, hmodeOne, hshiftCase] using hout)⟩
          · exact Or.inr ⟨hshiftCase, hraw.mpr ⟨hconsumedLe, by
              simpa [compactFormulaTransformTermEmission,
                hconsumed, hmodeZero, hmodeOne, hshiftCase] using hout⟩⟩
        · by_cases hmodeTwo : mode = 2
          · refine Or.inr (Or.inr (Or.inl ⟨hmodeTwo, ?_⟩))
            by_cases hlower : consumedCount = 2 ∧ tag = 0 ∧
                argument + 1 = binderArity
            · exact Or.inl ⟨hlower, hwitnessRows.mpr (by
                simpa [compactFormulaTransformTermEmission, hconsumed,
                  hmodeZero, hmodeOne, hmodeTwo, hlower] using hout)⟩
            · exact Or.inr ⟨hlower, hraw.mpr ⟨hconsumedLe, by
                simpa [compactFormulaTransformTermEmission, hconsumed,
                  hmodeZero, hmodeOne, hmodeTwo, hlower] using hout⟩⟩
          · by_cases hmodeFour : mode = 4
            · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hmodeFour, ?_⟩)))
              by_cases hfreeCase : consumedCount = 2 ∧ tag = 1
              · exact Or.inl ⟨hfreeCase, honeValue.mpr (by
                  simpa [compactFormulaTransformTermEmission, hconsumed,
                    hmodeZero, hmodeOne, hmodeTwo, hmodeFour,
                    hfreeCase] using hout)⟩
              · exact Or.inr ⟨hfreeCase, hsame.mpr (by
                  simpa [compactFormulaTransformTermEmission, hconsumed,
                    hmodeZero, hmodeOne, hmodeTwo, hmodeFour,
                    hfreeCase] using hout)⟩
            · by_cases hmodeFive : mode = 5
              · refine Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inl ⟨hmodeFive, ?_⟩))))
                by_cases hfreeCase : consumedCount = 2 ∧ tag = 1
                · by_cases hcaptured : argument < witness.length
                  · exact Or.inl ⟨⟨hfreeCase.1, hfreeCase.2,
                        hcaptured⟩, htwoCaptured.mpr (by
                        simpa [compactFormulaTransformTermEmission, hconsumed,
                          hmodeZero, hmodeOne, hmodeTwo, hmodeFour,
                          hmodeFive, hfreeCase, hcaptured] using hout)⟩
                  · let residual := argument - witness.length
                    have hargument : argument = witness.length + residual := by
                      dsimp [residual]
                      omega
                    exact Or.inr (Or.inl
                      ⟨⟨hfreeCase.1, hfreeCase.2, by omega⟩,
                        residual, by dsimp [residual]; omega, hargument,
                        (htwoResidual residual).mpr (by
                          simpa [compactFormulaTransformTermEmission,
                            hconsumed, hmodeZero, hmodeOne, hmodeTwo,
                            hmodeFour, hmodeFive, hfreeCase, hcaptured,
                            residual] using hout)⟩)
                · exact Or.inr (Or.inr ⟨hfreeCase,
                    hraw.mpr ⟨hconsumedLe, by
                      simpa [compactFormulaTransformTermEmission, hconsumed,
                        hmodeZero, hmodeOne, hmodeTwo, hmodeFour,
                        hmodeFive, hfreeCase] using hout⟩⟩)
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  ⟨hmodeZero, hmodeOne, hmodeTwo, hmodeFour, hmodeFive,
                    hraw.mpr ⟨hconsumedLe, by
                      simpa [compactFormulaTransformTermEmission, hconsumed,
                        hmodeZero, hmodeOne, hmodeTwo, hmodeFour,
                        hmodeFive] using hout⟩⟩))))

theorem compactFormulaTransformTermEmission_eq_transition
    {tokenTable width tokenCount mode binderArity consumedCount
      witnessStart witnessFinish : Nat}
    {currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates}
    {current next : CompactFormulaTransformState}
    {termWitness : CompactSyntaxTermTaskWitnessCoordinates}
    {witness : List Nat}
    (hcurrent : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (_hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hterm : CompactUnifiedParserSyntaxTermRows
      tokenTable width tokenCount currentCoordinates.parser
        nextCoordinates.parser binderArity termWitness)
    (hcount : currentCoordinates.parserTokensCount =
      consumedCount + nextCoordinates.parserTokensCount) :
    compactFormulaTransformTermEmission
        mode binderArity termWitness.tag termWitness.argument
          consumedCount witness current.1.1 =
      compactFormulaTransformTransitionEmission
        mode witness current.1 next.1 := by
  have hcase : CompactSyntaxParserTermTaskCase
      binderArity current.1 next.1 :=
    (compactUnifiedParserSyntaxTermRows_iff
      hcurrent.parserLayout hnext.parserLayout).mp ⟨termWitness, hterm⟩
  rcases hcase with ⟨_hstatus, tail, htasks, _hstep⟩
  have hfreeTask :
      FoundationCompactNumericFormulaFree.compactSyntaxCurrentTask current.1 =
        (0, binderArity, 0) := by
    simp [FoundationCompactNumericFormulaFree.compactSyntaxCurrentTask,
      htasks]
  have hshiftKind :
      FoundationCompactNumericFormulaShift.compactSyntaxCurrentTaskKind
          current.1 = 0 := by
    simp [FoundationCompactNumericFormulaShift.compactSyntaxCurrentTaskKind,
      htasks]
  have hsubstitutionTask :
      FoundationCompactNumericFormulaSubstitution.compactSyntaxCurrentTask
          current.1 = (0, binderArity, 0) := by
    simp [FoundationCompactNumericFormulaSubstitution.compactSyntaxCurrentTask,
      htasks]
  have hnegationKind :
      FoundationCompactNumericFormulaNegation.compactSyntaxCurrentTaskKind
          current.1 = 0 := by
    simp [FoundationCompactNumericFormulaNegation.compactSyntaxCurrentTaskKind,
      htasks]
  have hfvListKind :
      FoundationCompactNumericFormulaFvSup.compactSyntaxCurrentTaskKind
          current.1 = 0 := by
    simp [FoundationCompactNumericFormulaFvSup.compactSyntaxCurrentTaskKind,
      htasks]
  have hfixitrTask :
      FoundationCompactNumericFormulaFixitr.compactSyntaxCurrentTask current.1 =
        (0, binderArity, 0) := by
    simp [FoundationCompactNumericFormulaFixitr.compactSyntaxCurrentTask,
      htasks]
  have hcurrentTokenCount :
      currentCoordinates.parserTokensCount = current.1.1.length := by
    simpa [CompactFormulaTransformStateRowCoordinates.parser] using
      hcurrent.parserLayout.tokensCount_eq
  have hnextTokenCount :
      nextCoordinates.parserTokensCount = next.1.1.length := by
    simpa [CompactFormulaTransformStateRowCoordinates.parser] using
      hnext.parserLayout.tokensCount_eq
  have hprefix : consumedTokenPrefix current.1.1 next.1.1 =
      current.1.1.take consumedCount := by
    unfold consumedTokenPrefix
    congr 1
    rw [← hcurrentTokenCount, ← hnextTokenCount]
    omega
  have hconsumptionRaw := compactUnifiedParserSyntaxTermRows_consumption_cases
    hcurrent.parserLayout hterm
  have hconsumption :
      nextCoordinates.parserTokensCount =
          currentCoordinates.parserTokensCount ∨
        (currentCoordinates.parserTokensCount =
            2 + nextCoordinates.parserTokensCount ∧
          compactTokenAt 0 current.1.1 = termWitness.tag ∧
          compactTokenAt 1 current.1.1 = termWitness.argument) ∨
        (currentCoordinates.parserTokensCount =
            3 + nextCoordinates.parserTokensCount ∧
          compactTokenAt 0 current.1.1 = termWitness.tag ∧
          compactTokenAt 1 current.1.1 = termWitness.argument ∧
          termWitness.tag = 2) := by
    simpa [CompactFormulaTransformStateRowCoordinates.parser] using
      hconsumptionRaw
  rcases hconsumption with hsame | htwo | hthree
  · have hconsumed : consumedCount = 0 := by omega
    subst consumedCount
    simp [compactFormulaTransformTermEmission,
      compactFormulaTransformTransitionEmission, hprefix,
      hfreeTask, hshiftKind, hsubstitutionTask, hnegationKind,
      hfvListKind, hfixitrTask,
      FoundationCompactNumericFormulaFree.compactFormulaFreeEmission,
      FoundationCompactNumericFormulaFree.compactFreeConsumedTermHeader,
      FoundationCompactNumericFormulaShift.compactFormulaShiftEmission,
      FoundationCompactNumericFormulaShift.compactShiftConsumedTermHeader,
      FoundationCompactNumericFormulaSubstitution.compactFormulaSubstitutionEmission,
      FoundationCompactNumericFormulaSubstitution.compactSubstituteConsumedTermHeader,
      FoundationCompactNumericFormulaNegation.compactFormulaNegationEmission,
      FoundationCompactNumericFormulaFvSup.compactFormulaFvListEmission,
      FoundationCompactNumericFormulaFvSup.compactFvListConsumedTermHeader,
      FoundationCompactNumericFormulaFixitr.compactFormulaFixitrEmission,
      FoundationCompactNumericFormulaFixitr.compactFixitrConsumedTermHeader,
      compactTokenAt]
  · rcases htwo with ⟨htwoCount, htag, hargument⟩
    have hconsumed : consumedCount = 2 := by omega
    subst consumedCount
    have hsourceLength : 2 ≤ current.1.1.length := by
      rw [← hcurrentTokenCount]
      omega
    have htakeLength : (current.1.1.take 2).length = 2 := by
      simp [List.length_take, hsourceLength]
    have htakeTag : compactTokenAt 0 (current.1.1.take 2) =
        termWitness.tag :=
      (compactTokenAt_take_of_lt 0 2 current.1.1 (by omega)).trans htag
    have htakeArgument : compactTokenAt 1 (current.1.1.take 2) =
        termWitness.argument :=
      (compactTokenAt_take_of_lt 1 2 current.1.1 (by omega)).trans hargument
    by_cases hmodeZero : mode = 0
    · by_cases htagZero : termWitness.tag = 0
      <;> by_cases hlast : termWitness.argument + 1 = binderArity
      <;> by_cases htagOne : termWitness.tag = 1
      <;> simp [compactFormulaTransformTermEmission,
          compactFormulaTransformTransitionEmission, hmodeZero, hprefix,
          hfreeTask,
          FoundationCompactNumericFormulaFree.compactFormulaFreeEmission,
          FoundationCompactNumericFormulaFree.compactFreeConsumedTermHeader,
          htakeLength, htakeTag, htakeArgument,
          htagZero, hlast, htagOne]
    · by_cases hmodeOne : mode = 1
      · simp [compactFormulaTransformTermEmission,
          compactFormulaTransformTransitionEmission,
          hmodeOne, hprefix, hshiftKind,
          FoundationCompactNumericFormulaShift.compactFormulaShiftEmission,
          FoundationCompactNumericFormulaShift.compactShiftConsumedTermHeader,
          htakeTag, htakeArgument]
      · by_cases hmodeTwo : mode = 2
        · by_cases htagZero : termWitness.tag = 0
          <;> by_cases hlast : termWitness.argument + 1 = binderArity
          <;> simp [compactFormulaTransformTermEmission,
              compactFormulaTransformTransitionEmission,
              hmodeTwo, hprefix, hsubstitutionTask,
              FoundationCompactNumericFormulaSubstitution.compactFormulaSubstitutionEmission,
              FoundationCompactNumericFormulaSubstitution.compactSubstituteConsumedTermHeader,
              htakeLength, htakeTag, htakeArgument, htagZero, hlast]
        · by_cases hmodeFour : mode = 4
          · simp [compactFormulaTransformTermEmission,
              compactFormulaTransformTransitionEmission,
              hmodeFour, hprefix, hfvListKind,
              FoundationCompactNumericFormulaFvSup.compactFormulaFvListEmission,
              FoundationCompactNumericFormulaFvSup.compactFvListConsumedTermHeader,
              htakeLength, htakeTag, htakeArgument]
          · by_cases hmodeFive : mode = 5
            · simp [compactFormulaTransformTermEmission,
                compactFormulaTransformTransitionEmission,
                hmodeFive, hprefix, hfixitrTask,
                FoundationCompactNumericFormulaFixitr.compactFormulaFixitrEmission,
                FoundationCompactNumericFormulaFixitr.compactFixitrConsumedTermHeader,
                htakeLength, htakeTag, htakeArgument]
            · simp [compactFormulaTransformTermEmission,
                compactFormulaTransformTransitionEmission,
                hmodeZero, hmodeOne, hmodeTwo, hmodeFour, hmodeFive,
                hprefix, hnegationKind,
                FoundationCompactNumericFormulaNegation.compactFormulaNegationEmission]
  · rcases hthree with ⟨hthreeCount, htag, _hargument, htagValue⟩
    have hconsumed : consumedCount = 3 := by omega
    subst consumedCount
    have hsourceLength : 3 ≤ current.1.1.length := by
      rw [← hcurrentTokenCount]
      omega
    have htakeLength : (current.1.1.take 3).length = 3 := by
      simp [List.length_take, hsourceLength]
    have htakeTag : compactTokenAt 0 (current.1.1.take 3) = 2 := by
      rw [compactTokenAt_take_of_lt 0 3 current.1.1 (by omega),
        htag, htagValue]
    by_cases hmodeZero : mode = 0
    · simp [compactFormulaTransformTermEmission,
        compactFormulaTransformTransitionEmission, hmodeZero, hprefix,
        hfreeTask,
        FoundationCompactNumericFormulaFree.compactFormulaFreeEmission,
        FoundationCompactNumericFormulaFree.compactFreeConsumedTermHeader,
        htakeLength]
    · by_cases hmodeOne : mode = 1
      · simp [compactFormulaTransformTermEmission,
          compactFormulaTransformTransitionEmission,
          hmodeOne, hprefix, hshiftKind,
          FoundationCompactNumericFormulaShift.compactFormulaShiftEmission,
          FoundationCompactNumericFormulaShift.compactShiftConsumedTermHeader,
          htakeTag]
      · by_cases hmodeTwo : mode = 2
        · simp [compactFormulaTransformTermEmission,
            compactFormulaTransformTransitionEmission,
            hmodeTwo, hprefix, hsubstitutionTask,
            FoundationCompactNumericFormulaSubstitution.compactFormulaSubstitutionEmission,
            FoundationCompactNumericFormulaSubstitution.compactSubstituteConsumedTermHeader,
            htakeLength]
        · by_cases hmodeFour : mode = 4
          · simp [compactFormulaTransformTermEmission,
              compactFormulaTransformTransitionEmission,
              hmodeFour, hprefix, hfvListKind,
              FoundationCompactNumericFormulaFvSup.compactFormulaFvListEmission,
              FoundationCompactNumericFormulaFvSup.compactFvListConsumedTermHeader,
              htakeLength]
          · by_cases hmodeFive : mode = 5
            · simp [compactFormulaTransformTermEmission,
                compactFormulaTransformTransitionEmission,
                hmodeFive, hprefix, hfixitrTask,
                FoundationCompactNumericFormulaFixitr.compactFormulaFixitrEmission,
                FoundationCompactNumericFormulaFixitr.compactFixitrConsumedTermHeader,
                htakeLength]
            · simp [compactFormulaTransformTermEmission,
                compactFormulaTransformTransitionEmission,
                hmodeZero, hmodeOne, hmodeTwo, hmodeFour, hmodeFive,
                hprefix, hnegationKind,
                FoundationCompactNumericFormulaNegation.compactFormulaNegationEmission]

theorem compactFormulaTransformStep_eq_transition
    (mode : Nat) (witness : List Nat)
    (current : CompactFormulaTransformState)
    (nextParser : CompactSyntaxParserState)
    (hparser : compactSyntaxParserStep current.1 = nextParser) :
    compactFormulaTransformStep (mode, witness) current =
      (nextParser,
        current.2 ++ compactFormulaTransformTransitionEmission
          mode witness current.1 nextParser) := by
  by_cases hmodeZero : mode = 0
  · subst mode
    simp [compactFormulaTransformStep,
      compactFormulaTransformTransitionEmission,
      FoundationCompactNumericFormulaFree.compactFormulaFreeStep,
      hparser]
  · by_cases hmodeOne : mode = 1
    · subst mode
      simp [compactFormulaTransformStep,
        compactFormulaTransformTransitionEmission,
        FoundationCompactNumericFormulaShift.compactFormulaShiftStep,
        hparser]
    · by_cases hmodeTwo : mode = 2
      · subst mode
        simp [compactFormulaTransformStep,
          compactFormulaTransformTransitionEmission,
          FoundationCompactNumericFormulaSubstitution.compactFormulaSubstitutionStep,
          hparser]
      · by_cases hmodeFour : mode = 4
        · subst mode
          simp [compactFormulaTransformStep,
            compactFormulaTransformTransitionEmission,
            FoundationCompactNumericFormulaFvSup.compactFormulaFvListStep,
            hparser]
        · by_cases hmodeFive : mode = 5
          · subst mode
            simp [compactFormulaTransformStep,
              compactFormulaTransformTransitionEmission,
              FoundationCompactNumericFormulaFixitr.compactFormulaFixitrStep,
              hparser]
          · simp [compactFormulaTransformStep,
              compactFormulaTransformTransitionEmission,
              FoundationCompactNumericFormulaNegation.compactFormulaNegationStep,
              hparser, hmodeZero, hmodeOne, hmodeTwo, hmodeFour, hmodeFive]

theorem compactUnifiedParserSyntaxTermRows_parserStep
    {tokenTable width tokenCount binderArity : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    {termWitness : CompactSyntaxTermTaskWitnessCoordinates}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hterm : CompactUnifiedParserSyntaxTermRows
      tokenTable width tokenCount currentCoordinates nextCoordinates
        binderArity termWitness) :
    next = compactSyntaxParserStep current := by
  have hcase : CompactSyntaxParserTermTaskCase binderArity current next :=
    (compactUnifiedParserSyntaxTermRows_iff hcurrent hnext).mp
      ⟨termWitness, hterm⟩
  rcases hcase with ⟨hstatus, tail, htasks, htermStep⟩
  rcases current with ⟨tokens, tasks, status⟩
  simp only at hstatus htasks htermStep ⊢
  subst status
  subst tasks
  simpa [compactSyntaxParserStep, compactSyntaxRunningStep,
    compactSyntaxTaskTokenStep] using htermStep

theorem exists_compactFormulaTransformTermOutputRows_iff_step
    {tokenTable width tokenCount mode binderArity
      witnessStart witnessFinish witnessCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates}
    {current next : CompactFormulaTransformState}
    {termWitness : CompactSyntaxTermTaskWitnessCoordinates}
    {witness : List Nat}
    (hcurrent : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hwitnessCount : witnessCount = witness.length)
    (hterm : CompactUnifiedParserSyntaxTermRows
      tokenTable width tokenCount currentCoordinates.parser
        nextCoordinates.parser binderArity termWitness) :
    (∃ consumedCount,
        CompactFormulaTransformTermOutputRows
          tokenTable width tokenCount currentCoordinates nextCoordinates
            mode binderArity termWitness.tag termWitness.argument
            consumedCount witnessStart witnessFinish witnessCount) ↔
      next = compactFormulaTransformStep (mode, witness) current := by
  have hparser : next.1 = compactSyntaxParserStep current.1 :=
    compactUnifiedParserSyntaxTermRows_parserStep
      hcurrent.parserLayout hnext.parserLayout hterm
  have hstepTransition := compactFormulaTransformStep_eq_transition
    mode witness current next.1 hparser.symm
  constructor
  · rintro ⟨consumedCount, hrows⟩
    have hsemantic := (compactFormulaTransformTermOutputRows_iff
      hcurrent hnext hwitness hwitnessCount).mp hrows
    have hemitted := compactFormulaTransformTermEmission_eq_transition
      (mode := mode) hcurrent hnext hwitness hterm hsemantic.1
    have houtput : next.2 = current.2 ++
        compactFormulaTransformTransitionEmission
          mode witness current.1 next.1 := by
      rw [← hemitted]
      exact hsemantic.2
    calc
      next = (next.1, next.2) := rfl
      _ = (next.1, current.2 ++
          compactFormulaTransformTransitionEmission
            mode witness current.1 next.1) := by rw [houtput]
      _ = compactFormulaTransformStep (mode, witness) current :=
        hstepTransition.symm
  · intro hstep
    have hconsumptionRaw :=
      compactUnifiedParserSyntaxTermRows_consumption_cases
        hcurrent.parserLayout hterm
    have hconsumption :
        nextCoordinates.parserTokensCount ≤
          currentCoordinates.parserTokensCount := by
      rcases hconsumptionRaw with hsame | htwo | hthree
      · simpa [CompactFormulaTransformStateRowCoordinates.parser] using
          Nat.le_of_eq hsame
      · simp [CompactFormulaTransformStateRowCoordinates.parser] at htwo
        omega
      · simp [CompactFormulaTransformStateRowCoordinates.parser] at hthree
        omega
    let consumedCount := currentCoordinates.parserTokensCount -
      nextCoordinates.parserTokensCount
    have hcount : currentCoordinates.parserTokensCount =
        consumedCount + nextCoordinates.parserTokensCount := by
      dsimp only [consumedCount]
      omega
    have hnextPair : next =
        (next.1, current.2 ++
          compactFormulaTransformTransitionEmission
            mode witness current.1 next.1) :=
      hstep.trans hstepTransition
    have houtput : next.2 = current.2 ++
        compactFormulaTransformTransitionEmission
          mode witness current.1 next.1 :=
      congrArg Prod.snd hnextPair
    have hemitted := compactFormulaTransformTermEmission_eq_transition
      (mode := mode) hcurrent hnext hwitness hterm hcount
    refine ⟨consumedCount,
      (compactFormulaTransformTermOutputRows_iff
        hcurrent hnext hwitness hwitnessCount).mpr ⟨hcount, ?_⟩⟩
    rw [hemitted]
    exact houtput

theorem exists_compactFormulaTransformTermOutputFormula_iff_step
    {tokenTable width tokenCount mode binderArity
      witnessStart witnessFinish witnessCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates}
    {current next : CompactFormulaTransformState}
    {termWitness : CompactSyntaxTermTaskWitnessCoordinates}
    {witness : List Nat}
    (hcurrent : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hwitnessCount : witnessCount = witness.length)
    (hterm : CompactUnifiedParserSyntaxTermRows
      tokenTable width tokenCount currentCoordinates.parser
        nextCoordinates.parser binderArity termWitness) :
    (∃ consumedCount,
        compactFormulaTransformTermOutputRowsDef.val.Evalb
          (compactFormulaTransformTermOutputRowsEnvironment
            tokenTable width tokenCount currentCoordinates nextCoordinates
            mode binderArity termWitness.tag termWitness.argument
            consumedCount witnessStart witnessFinish witnessCount)) ↔
      next = compactFormulaTransformStep (mode, witness) current := by
  simpa only [compactFormulaTransformTermOutputRowsDef_spec] using
    exists_compactFormulaTransformTermOutputRows_iff_step
      hcurrent hnext hwitness hwitnessCount hterm

#print axioms compactFormulaTransformTermOutputRowsDef_spec
#print axioms compactFormulaTransformTermOutputRowsDef_sigmaZero
#print axioms compactFormulaTransformTermOutputRows_iff
#print axioms compactUnifiedParserSyntaxTermRows_consumption_cases
#print axioms compactFormulaTransformTermEmission_eq_transition
#print axioms compactFormulaTransformStep_eq_transition
#print axioms compactUnifiedParserSyntaxTermRows_parserStep
#print axioms exists_compactFormulaTransformTermOutputRows_iff_step
#print axioms exists_compactFormulaTransformTermOutputFormula_iff_step

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
