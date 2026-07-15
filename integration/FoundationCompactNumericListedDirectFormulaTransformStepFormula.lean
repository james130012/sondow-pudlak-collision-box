import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRows

/-!
# One bounded graph for a shared formula-transform step

The six arithmeticized syntax-parser branches are connected to the exact
output update used by the four formula-transform modes.  Finished, empty,
repeat, and invalid branches preserve the output list.  Term and formula
branches use their checked direct output graphs.  No executable transform is
embedded as an opaque predicate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformStepFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactParserDirectTrace
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula
open FoundationCompactNumericListedDirectParserSyntaxInvalidRows
open FoundationCompactNumericListedDirectParserSyntaxInvalidFormula
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRows

def CompactFormulaTransformQuietParserRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) : Prop :=
  CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
      current.parser next.parser witness.done ∨
    CompactUnifiedParserEmptyGraphRows tokenTable width tokenCount
      current.parser next.parser witness.empty ∨
    CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount
      current.parser next.parser witness.slot0 witness.slot1 witness.repeat ∨
    CompactUnifiedParserSyntaxInvalidRows tokenTable width tokenCount
      current.parser next.parser witness.invalid

def CompactFormulaTransformStepRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    Prop :=
  (CompactFormulaTransformQuietParserRows tokenTable width tokenCount
        current next stepWitness ∧
      CompactFormulaTransformOutputSameRows tokenTable width tokenCount
        current next) ∨
    (CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
        current.parser next.parser stepWitness.slot0 stepWitness.term ∧
      CompactFormulaTransformTermOutputRows tokenTable width tokenCount
        current next mode stepWitness.slot0 stepWitness.term.tag
          stepWitness.term.argument consumedCount
          witnessStart witnessFinish witnessCount) ∨
    (CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
        current.parser next.parser stepWitness.slot0 stepWitness.formula ∧
      CompactFormulaTransformFormulaOutputRows tokenTable width tokenCount
        current next mode stepWitness.formula.tag consumedCount mappedHead)

def compactFormulaTransformStepRowsDef : 𝚺₀.Semisentence 38 := .mkSigma
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
      mode slot0 slot1 slot2 slot3 slot4 slot5 slot6
      consumedCount mappedHead witnessStart witnessFinish witnessCount.
    (((!(compactUnifiedParserDoneGraphRowsDef)
          tokenTable width tokenCount
          currentStart currentParserFinish
            currentParserTokensFinish currentParserTasksFinish
            currentParserTokensBoundary currentParserTokensCount
            currentParserTasksBoundary currentParserTasksCount
          nextStart nextParserFinish
            nextParserTokensFinish nextParserTasksFinish
            nextParserTokensBoundary nextParserTokensCount
            nextParserTasksBoundary nextParserTasksCount
          slot0 slot1 slot2 slot3 slot4 slot5 slot6 ∨
        !(compactUnifiedParserEmptyGraphRowsDef)
          tokenTable width tokenCount
          currentStart currentParserFinish
            currentParserTokensFinish currentParserTasksFinish
            currentParserTokensBoundary currentParserTokensCount
            currentParserTasksBoundary currentParserTasksCount
          nextStart nextParserFinish
            nextParserTokensFinish nextParserTasksFinish
            nextParserTokensBoundary nextParserTokensCount
            nextParserTasksBoundary nextParserTasksCount
          slot0 slot1 slot2 ∨
        !(compactUnifiedParserSyntaxRepeatRowsDef)
          tokenTable width tokenCount
          currentStart currentParserFinish
            currentParserTokensFinish currentParserTasksFinish
            currentParserTokensBoundary currentParserTokensCount
            currentParserTasksBoundary currentParserTasksCount
          nextStart nextParserFinish
            nextParserTokensFinish nextParserTasksFinish
            nextParserTokensBoundary nextParserTokensCount
            nextParserTasksBoundary nextParserTasksCount
          slot0 slot1 slot2 slot3 slot4 slot5 ∨
        !(compactUnifiedParserSyntaxInvalidRowsDef)
          tokenTable width tokenCount
          currentStart currentParserFinish
            currentParserTokensFinish currentParserTasksFinish
            currentParserTokensBoundary currentParserTokensCount
            currentParserTasksBoundary currentParserTasksCount
          nextStart nextParserFinish
            nextParserTokensFinish nextParserTasksFinish
            nextParserTokensBoundary nextParserTokensCount
            nextParserTasksBoundary nextParserTasksCount
          slot0 slot1 slot2 slot3 slot4 slot5) ∧
       !(compactAdditiveNatListSameRowsDef)
          tokenTable width tokenCount
          currentOutputBoundary currentOutputCount
          nextOutputBoundary nextOutputCount) ∨
     (!(compactUnifiedParserSyntaxTermRowsDef)
        tokenTable width tokenCount
        currentStart currentParserFinish
          currentParserTokensFinish currentParserTasksFinish
          currentParserTokensBoundary currentParserTokensCount
          currentParserTasksBoundary currentParserTasksCount
        nextStart nextParserFinish
          nextParserTokensFinish nextParserTasksFinish
          nextParserTokensBoundary nextParserTokensCount
          nextParserTasksBoundary nextParserTasksCount
        slot0 slot1 slot2 slot3 slot4 slot5 slot6 ∧
      !(compactFormulaTransformTermOutputRowsDef)
        tokenTable width tokenCount
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
        mode slot0 slot4 slot5 consumedCount
          witnessStart witnessFinish witnessCount) ∨
     (!(compactUnifiedParserSyntaxFormulaRowsDef)
        tokenTable width tokenCount
        currentStart currentParserFinish
          currentParserTokensFinish currentParserTasksFinish
          currentParserTokensBoundary currentParserTokensCount
          currentParserTasksBoundary currentParserTasksCount
        nextStart nextParserFinish
          nextParserTokensFinish nextParserTasksFinish
          nextParserTokensBoundary nextParserTokensCount
          nextParserTasksBoundary nextParserTasksCount
        slot0 slot1 slot2 slot3 slot4 slot5 slot6 ∧
      !(compactFormulaTransformFormulaOutputRowsDef)
        tokenTable width tokenCount
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
        mode slot4 consumedCount mappedHead))”

def compactFormulaTransformStepRowsEnvironment
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    Fin 38 → Nat :=
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
    mode, stepWitness.slot0, stepWitness.slot1, stepWitness.slot2,
    stepWitness.slot3, stepWitness.slot4, stepWitness.slot5,
    stepWitness.slot6, consumedCount, mappedHead,
    witnessStart, witnessFinish, witnessCount]

set_option maxRecDepth 2048 in
@[simp] theorem compactFormulaTransformStepRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    compactFormulaTransformStepRowsDef.val.Evalb
        (compactFormulaTransformStepRowsEnvironment
          tokenTable width tokenCount current next mode stepWitness
            consumedCount mappedHead witnessStart witnessFinish witnessCount) ↔
      CompactFormulaTransformStepRows tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead
          witnessStart witnessFinish witnessCount := by
  let env := compactFormulaTransformStepRowsEnvironment
    tokenTable width tokenCount current next mode stepWitness
      consumedCount mappedHead witnessStart witnessFinish witnessCount
  change compactFormulaTransformStepRowsDef.val.Evalb env ↔ _
  have hdoneEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
          #3, #5, #6, #7, #8, #9, #10, #11,
          #14, #16, #17, #18, #19, #20, #21, #22,
          #26, #27, #28, #29, #30, #31, #32]) =
        compactUnifiedParserDoneFormulaEnvironmentOf
          tokenTable width tokenCount current.parser next.parser
            stepWitness.done := by
    funext index
    fin_cases index <;> rfl
  have hemptyEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
          #3, #5, #6, #7, #8, #9, #10, #11,
          #14, #16, #17, #18, #19, #20, #21, #22,
          #26, #27, #28]) =
        compactUnifiedParserEmptyFormulaEnvironmentOf
          tokenTable width tokenCount current.parser next.parser
            stepWitness.empty := by
    funext index
    fin_cases index <;> rfl
  have hrepeatEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
          #3, #5, #6, #7, #8, #9, #10, #11,
          #14, #16, #17, #18, #19, #20, #21, #22,
          #26, #27, #28, #29, #30, #31]) =
        compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf
          tokenTable width tokenCount current.parser next.parser
            stepWitness.slot0 stepWitness.slot1 stepWitness.repeat := by
    funext index
    fin_cases index <;> rfl
  have hinvalidEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
          #3, #5, #6, #7, #8, #9, #10, #11,
          #14, #16, #17, #18, #19, #20, #21, #22,
          #26, #27, #28, #29, #30, #31]) =
        compactUnifiedParserSyntaxInvalidFormulaEnvironment
          tokenTable width tokenCount current.parser next.parser
            stepWitness.invalid := by
    funext index
    fin_cases index <;> rfl
  have hsameEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
          #12, #13, #23, #24]) =
        ![tokenTable, width, tokenCount,
          current.outputBoundary, current.outputCount,
          next.outputBoundary, next.outputCount] := by
    funext index
    fin_cases index <;> rfl
  have htermEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
          #3, #5, #6, #7, #8, #9, #10, #11,
          #14, #16, #17, #18, #19, #20, #21, #22,
          #26, #27, #28, #29, #30, #31, #32]) =
        compactUnifiedParserSyntaxTermFormulaEnvironment
          tokenTable width tokenCount current.parser next.parser
            stepWitness.slot0 stepWitness.term := by
    funext index
    fin_cases index <;> rfl
  have htermOutputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
          #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13,
          #14, #15, #16, #17, #18, #19, #20, #21, #22, #23, #24,
          #25, #26, #30, #31, #33, #35, #36, #37]) =
        compactFormulaTransformTermOutputRowsEnvironment
          tokenTable width tokenCount current next mode stepWitness.slot0
            stepWitness.term.tag stepWitness.term.argument consumedCount
            witnessStart witnessFinish witnessCount := by
    funext index
    fin_cases index <;> rfl
  have hformulaEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
          #3, #5, #6, #7, #8, #9, #10, #11,
          #14, #16, #17, #18, #19, #20, #21, #22,
          #26, #27, #28, #29, #30, #31, #32]) =
        compactUnifiedParserSyntaxFormulaTaskEnvironment
          tokenTable width tokenCount current.parser next.parser
            stepWitness.slot0 stepWitness.formula := by
    funext index
    fin_cases index <;> rfl
  have hformulaOutputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
          #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13,
          #14, #15, #16, #17, #18, #19, #20, #21, #22, #23, #24,
          #25, #30, #33, #34]) =
        compactFormulaTransformFormulaOutputRowsEnvironment
          tokenTable width tokenCount current next mode
            stepWitness.formula.tag consumedCount mappedHead := by
    funext index
    fin_cases index <;> rfl
  have hdoneSpec :
      compactUnifiedParserDoneGraphRowsDef.val.Evalb
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
              #3, #5, #6, #7, #8, #9, #10, #11,
              #14, #16, #17, #18, #19, #20, #21, #22,
              #26, #27, #28, #29, #30, #31, #32]) ↔
        CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
          current.parser next.parser stepWitness.done := by
    rw [hdoneEnv]
    exact compactUnifiedParserDoneGraphRowsDef_environmentOf_iff
      tokenTable width tokenCount current.parser next.parser stepWitness.done
  have hemptySpec :
      compactUnifiedParserEmptyGraphRowsDef.val.Evalb
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
              #3, #5, #6, #7, #8, #9, #10, #11,
              #14, #16, #17, #18, #19, #20, #21, #22,
              #26, #27, #28]) ↔
        CompactUnifiedParserEmptyGraphRows tokenTable width tokenCount
          current.parser next.parser stepWitness.empty := by
    rw [hemptyEnv]
    exact compactUnifiedParserEmptyGraphRowsDef_environmentOf_iff
      tokenTable width tokenCount current.parser next.parser stepWitness.empty
  have hrepeatSpec :
      compactUnifiedParserSyntaxRepeatRowsDef.val.Evalb
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
              #3, #5, #6, #7, #8, #9, #10, #11,
              #14, #16, #17, #18, #19, #20, #21, #22,
              #26, #27, #28, #29, #30, #31]) ↔
        CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount
          current.parser next.parser stepWitness.slot0 stepWitness.slot1
            stepWitness.repeat := by
    rw [hrepeatEnv]
    exact compactUnifiedParserSyntaxRepeatRowsDef_environmentOf_iff
      tokenTable width tokenCount current.parser next.parser
        stepWitness.slot0 stepWitness.slot1 stepWitness.repeat
  have hinvalidSpec :
      compactUnifiedParserSyntaxInvalidRowsDef.val.Evalb
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
              #3, #5, #6, #7, #8, #9, #10, #11,
              #14, #16, #17, #18, #19, #20, #21, #22,
              #26, #27, #28, #29, #30, #31]) ↔
        CompactUnifiedParserSyntaxInvalidRows tokenTable width tokenCount
          current.parser next.parser stepWitness.invalid := by
    rw [hinvalidEnv]
    exact compactUnifiedParserSyntaxInvalidRowsDef_spec
      tokenTable width tokenCount current.parser next.parser
        stepWitness.invalid
  have hsameSpec :
      compactAdditiveNatListSameRowsDef.val.Evalb
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
              #12, #13, #23, #24]) ↔
        CompactFormulaTransformOutputSameRows tokenTable width tokenCount
          current next := by
    rw [hsameEnv]
    exact compactAdditiveNatListSameRowsDef_spec
      tokenTable width tokenCount current.outputBoundary current.outputCount
        next.outputBoundary next.outputCount
  have htermSpec :
      compactUnifiedParserSyntaxTermRowsDef.val.Evalb
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
              #3, #5, #6, #7, #8, #9, #10, #11,
              #14, #16, #17, #18, #19, #20, #21, #22,
              #26, #27, #28, #29, #30, #31, #32]) ↔
        CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
          current.parser next.parser stepWitness.slot0 stepWitness.term := by
    rw [htermEnv]
    exact compactUnifiedParserSyntaxTermRowsDef_spec
      tokenTable width tokenCount current.parser next.parser
        stepWitness.slot0 stepWitness.term
  have htermOutputSpec :
      compactFormulaTransformTermOutputRowsDef.val.Evalb
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
              #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13,
              #14, #15, #16, #17, #18, #19, #20, #21, #22, #23, #24,
              #25, #26, #30, #31, #33, #35, #36, #37]) ↔
        CompactFormulaTransformTermOutputRows tokenTable width tokenCount
          current next mode stepWitness.slot0 stepWitness.term.tag
            stepWitness.term.argument consumedCount
            witnessStart witnessFinish witnessCount := by
    rw [htermOutputEnv]
    exact compactFormulaTransformTermOutputRowsDef_spec
      tokenTable width tokenCount current next mode stepWitness.slot0
        stepWitness.term.tag stepWitness.term.argument consumedCount
        witnessStart witnessFinish witnessCount
  have hformulaSpec :
      compactUnifiedParserSyntaxFormulaRowsDef.val.Evalb
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
              #3, #5, #6, #7, #8, #9, #10, #11,
              #14, #16, #17, #18, #19, #20, #21, #22,
              #26, #27, #28, #29, #30, #31, #32]) ↔
        CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
          current.parser next.parser stepWitness.slot0 stepWitness.formula := by
    rw [hformulaEnv]
    exact compactUnifiedParserSyntaxFormulaRowsDef_spec
      tokenTable width tokenCount current.parser next.parser
        stepWitness.slot0 stepWitness.formula
  have hformulaOutputSpec :
      compactFormulaTransformFormulaOutputRowsDef.val.Evalb
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
              #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13,
              #14, #15, #16, #17, #18, #19, #20, #21, #22, #23, #24,
              #25, #30, #33, #34]) ↔
        CompactFormulaTransformFormulaOutputRows tokenTable width tokenCount
          current next mode stepWitness.formula.tag consumedCount mappedHead := by
    rw [hformulaOutputEnv]
    exact compactFormulaTransformFormulaOutputRowsDef_spec
      tokenTable width tokenCount current next mode stepWitness.formula.tag
        consumedCount mappedHead
  simp [compactFormulaTransformStepRowsDef,
    CompactFormulaTransformStepRows,
    CompactFormulaTransformQuietParserRows,
    hdoneSpec, hemptySpec, hrepeatSpec, hinvalidSpec, hsameSpec,
    htermSpec, htermOutputSpec, hformulaSpec, hformulaOutputSpec]

theorem compactFormulaTransformStepRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformStepRowsDef.val := by
  simp [compactFormulaTransformStepRowsDef]

theorem compactFormulaTransformTransitionEmission_eq_nil_of_tokens_eq
    (mode : Nat) (witness : List Nat)
    (current next : CompactSyntaxParserState)
    (htokens : next.1 = current.1) :
    compactFormulaTransformTransitionEmission
        mode witness current next = [] := by
  simp [compactFormulaTransformTransitionEmission,
    consumedTokenPrefix, htokens,
    FoundationCompactNumericFormulaFree.compactFormulaFreeEmission,
    FoundationCompactNumericFormulaFree.compactFreeConsumedTermHeader,
    FoundationCompactNumericFormulaShift.compactFormulaShiftEmission,
    FoundationCompactNumericFormulaShift.compactShiftConsumedTermHeader,
    FoundationCompactNumericFormulaSubstitution.compactFormulaSubstitutionEmission,
    FoundationCompactNumericFormulaSubstitution.compactSubstituteConsumedTermHeader,
    FoundationCompactNumericFormulaNegation.compactFormulaNegationEmission,
    FoundationCompactNumericFormulaNegation.compactNegateConsumedFormulaHeader,
    FoundationCompactNumericFormulaFvSup.compactFormulaFvListEmission,
    FoundationCompactNumericFormulaFvSup.compactFvListConsumedTermHeader,
    FoundationCompactNumericFormulaFixitr.compactFormulaFixitrEmission,
    FoundationCompactNumericFormulaFixitr.compactFixitrConsumedTermHeader,
    compactTokenAt]

theorem compactFormulaTransformStep_parser
    (mode : Nat) (witness : List Nat)
    (current : CompactFormulaTransformState) :
    (compactFormulaTransformStep (mode, witness) current).1 =
      compactSyntaxParserStep current.1 := by
  simp only [compactFormulaTransformStep]
  split_ifs <;> rfl

theorem compactFormulaTransformQuietParserRows_parser_and_tokens
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates}
    {current next : CompactFormulaTransformState}
    {stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates}
    (hcurrent : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hquiet : CompactFormulaTransformQuietParserRows
      tokenTable width tokenCount currentCoordinates nextCoordinates
        stepWitness) :
    next.1 = compactSyntaxParserStep current.1 ∧
      next.1.1 = current.1.1 := by
  rcases hquiet with hdone | hempty | hrepeat | hinvalid
  · have hparser := compactUnifiedParserSyntaxStepRows_sound
      hcurrent.parserLayout hnext.parserLayout
      ⟨stepWitness, Or.inl hdone⟩
    rcases (exists_compactUnifiedParserDoneGraphRows_iff
      hcurrent.parserLayout hnext.parserLayout).mp
        ⟨stepWitness.done, hdone⟩ with
      ⟨result, hstatus, hstate⟩
    exact ⟨hparser,
      congrArg (fun state : CompactSyntaxParserState => state.1) hstate⟩
  · have hparser := compactUnifiedParserSyntaxStepRows_sound
      hcurrent.parserLayout hnext.parserLayout
      ⟨stepWitness, Or.inr (Or.inl hempty)⟩
    rcases (exists_compactUnifiedParserEmptyGraphRows_iff
      hcurrent.parserLayout hnext.parserLayout).mp
        ⟨stepWitness.empty, hempty⟩ with
      ⟨hstatus, htasks, hstate⟩
    have htokens :=
      congrArg (fun state : CompactSyntaxParserState => state.1) hstate
    exact ⟨hparser, by simpa using htokens⟩
  · have hparser := compactUnifiedParserSyntaxStepRows_sound
      hcurrent.parserLayout hnext.parserLayout
      ⟨stepWitness, Or.inr (Or.inr (Or.inl hrepeat))⟩
    rcases (compactUnifiedParserSyntaxRepeatRows_iff
      hcurrent.parserLayout hnext.parserLayout).mp
        ⟨stepWitness.repeat, hrepeat⟩ with
      ⟨hstatus, tail, htasks, hstate⟩
    have htokens : next.1.1 = current.1.1 := by
      rw [hstate]
      simp only [compactRepeatTermTokenStep]
      split_ifs <;> rfl
    exact ⟨hparser, htokens⟩
  · have hparser := compactUnifiedParserSyntaxStepRows_sound
      hcurrent.parserLayout hnext.parserLayout
      ⟨stepWitness,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hinvalid))))⟩
    rcases (compactUnifiedParserSyntaxInvalidRows_iff
      hcurrent.parserLayout hnext.parserLayout).mp
        ⟨stepWitness.invalid, hinvalid⟩ with
      ⟨hstatus, kind, binderArity, repeatCount, tail,
        htasks, hzero, hone, htwo, hstate⟩
    have htokens : next.1.1 = current.1.1 := by
      rw [hstate]
      rfl
    exact ⟨hparser, htokens⟩

theorem compactFormulaTransformStep_output_eq_of_tokens_eq
    {mode : Nat} {witness : List Nat}
    {current next : CompactFormulaTransformState}
    (hstep : next = compactFormulaTransformStep (mode, witness) current)
    (hparser : next.1 = compactSyntaxParserStep current.1)
    (htokens : next.1.1 = current.1.1) :
    next.2 = current.2 := by
  have htransition := compactFormulaTransformStep_eq_transition
    mode witness current next.1 hparser.symm
  have hpair : next =
      (next.1, current.2 ++
        compactFormulaTransformTransitionEmission
          mode witness current.1 next.1) :=
    hstep.trans htransition
  have hout := congrArg Prod.snd hpair
  have hempty :=
    compactFormulaTransformTransitionEmission_eq_nil_of_tokens_eq
      mode witness current.1 next.1 htokens
  simpa [hempty] using hout

theorem compactFormulaTransformStepRows_sound
    {tokenTable width tokenCount mode
      witnessStart witnessFinish witnessCount : Nat}
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
    (hwitnessCount : witnessCount = witness.length)
    (hrows : ∃ stepWitness consumedCount mappedHead,
      CompactFormulaTransformStepRows tokenTable width tokenCount
        currentCoordinates nextCoordinates mode stepWitness
          consumedCount mappedHead witnessStart witnessFinish witnessCount) :
    next = compactFormulaTransformStep (mode, witness) current := by
  rcases hrows with
    ⟨stepWitness, consumedCount, mappedHead,
      hquiet | hterm | hformula⟩
  · rcases hquiet with ⟨hquietParser, houtputRows⟩
    have hparserTokens :=
      compactFormulaTransformQuietParserRows_parser_and_tokens
        hcurrent hnext hquietParser
    have houtput :=
      (compactFormulaTransformOutputSameRows_iff hcurrent hnext).mp
        houtputRows
    have hempty :=
      compactFormulaTransformTransitionEmission_eq_nil_of_tokens_eq
        mode witness current.1 next.1 hparserTokens.2
    have htransition := compactFormulaTransformStep_eq_transition
      mode witness current next.1 hparserTokens.1.symm
    calc
      next = (next.1, next.2) := rfl
      _ = (next.1, current.2 ++
          compactFormulaTransformTransitionEmission
            mode witness current.1 next.1) := by
        rw [houtput, hempty]
        simp
      _ = compactFormulaTransformStep (mode, witness) current :=
        htransition.symm
  · exact (exists_compactFormulaTransformTermOutputRows_iff_step
      hcurrent hnext hwitness hwitnessCount hterm.1).mp
        ⟨consumedCount, hterm.2⟩
  · exact (exists_compactFormulaTransformFormulaOutputRows_iff_step
      (witness := witness) hcurrent hnext hformula.1).mp
        ⟨consumedCount, mappedHead, hformula.2⟩

theorem compactFormulaTransformStepRows_complete
    {tokenTable width tokenCount mode
      witnessStart witnessFinish witnessCount : Nat}
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
    (hwitnessCount : witnessCount = witness.length)
    (hwell : CompactSyntaxTaskStackFieldsWellFormed current.1.2.1)
    (hstep : next = compactFormulaTransformStep (mode, witness) current) :
    ∃ stepWitness consumedCount mappedHead,
      CompactFormulaTransformStepRows tokenTable width tokenCount
        currentCoordinates nextCoordinates mode stepWitness
          consumedCount mappedHead witnessStart witnessFinish witnessCount := by
  have hparser : next.1 = compactSyntaxParserStep current.1 := by
    calc
      next.1 = (compactFormulaTransformStep (mode, witness) current).1 :=
        congrArg Prod.fst hstep
      _ = compactSyntaxParserStep current.1 :=
        compactFormulaTransformStep_parser mode witness current
  rcases compactUnifiedParserSyntaxStepRows_complete
      hcurrent.parserLayout hnext.parserLayout hwell hparser with
    ⟨stepWitness, hdone | hempty | hrepeat | hterm | hformula | hinvalid⟩
  · have hquiet : CompactFormulaTransformQuietParserRows
        tokenTable width tokenCount currentCoordinates nextCoordinates
          stepWitness := Or.inl hdone
    have hparserTokens :=
      compactFormulaTransformQuietParserRows_parser_and_tokens
        hcurrent hnext hquiet
    have houtput := compactFormulaTransformStep_output_eq_of_tokens_eq
      hstep hparserTokens.1 hparserTokens.2
    have houtputRows :=
      (compactFormulaTransformOutputSameRows_iff hcurrent hnext).mpr houtput
    exact ⟨stepWitness, 0, 0, Or.inl ⟨hquiet, houtputRows⟩⟩
  · have hquiet : CompactFormulaTransformQuietParserRows
        tokenTable width tokenCount currentCoordinates nextCoordinates
          stepWitness := Or.inr (Or.inl hempty)
    have hparserTokens :=
      compactFormulaTransformQuietParserRows_parser_and_tokens
        hcurrent hnext hquiet
    have houtput := compactFormulaTransformStep_output_eq_of_tokens_eq
      hstep hparserTokens.1 hparserTokens.2
    have houtputRows :=
      (compactFormulaTransformOutputSameRows_iff hcurrent hnext).mpr houtput
    exact ⟨stepWitness, 0, 0, Or.inl ⟨hquiet, houtputRows⟩⟩
  · have hquiet : CompactFormulaTransformQuietParserRows
        tokenTable width tokenCount currentCoordinates nextCoordinates
          stepWitness := Or.inr (Or.inr (Or.inl hrepeat))
    have hparserTokens :=
      compactFormulaTransformQuietParserRows_parser_and_tokens
        hcurrent hnext hquiet
    have houtput := compactFormulaTransformStep_output_eq_of_tokens_eq
      hstep hparserTokens.1 hparserTokens.2
    have houtputRows :=
      (compactFormulaTransformOutputSameRows_iff hcurrent hnext).mpr houtput
    exact ⟨stepWitness, 0, 0, Or.inl ⟨hquiet, houtputRows⟩⟩
  · rcases (exists_compactFormulaTransformTermOutputRows_iff_step
      hcurrent hnext hwitness hwitnessCount hterm).mpr hstep with
      ⟨consumedCount, houtputRows⟩
    exact ⟨stepWitness, consumedCount, 0,
      Or.inr (Or.inl ⟨hterm, houtputRows⟩)⟩
  · rcases (exists_compactFormulaTransformFormulaOutputRows_iff_step
      (witness := witness) hcurrent hnext hformula).mpr hstep with
      ⟨consumedCount, mappedHead, houtputRows⟩
    exact ⟨stepWitness, consumedCount, mappedHead,
      Or.inr (Or.inr ⟨hformula, houtputRows⟩)⟩
  · have hquiet : CompactFormulaTransformQuietParserRows
        tokenTable width tokenCount currentCoordinates nextCoordinates
          stepWitness := Or.inr (Or.inr (Or.inr hinvalid))
    have hparserTokens :=
      compactFormulaTransformQuietParserRows_parser_and_tokens
        hcurrent hnext hquiet
    have houtput := compactFormulaTransformStep_output_eq_of_tokens_eq
      hstep hparserTokens.1 hparserTokens.2
    have houtputRows :=
      (compactFormulaTransformOutputSameRows_iff hcurrent hnext).mpr houtput
    exact ⟨stepWitness, 0, 0, Or.inl ⟨hquiet, houtputRows⟩⟩

theorem exists_compactFormulaTransformStepRows_iff_step
    {tokenTable width tokenCount mode
      witnessStart witnessFinish witnessCount : Nat}
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
    (hwitnessCount : witnessCount = witness.length)
    (hwell : CompactSyntaxTaskStackFieldsWellFormed current.1.2.1) :
    (∃ stepWitness consumedCount mappedHead,
      CompactFormulaTransformStepRows tokenTable width tokenCount
        currentCoordinates nextCoordinates mode stepWitness
          consumedCount mappedHead witnessStart witnessFinish witnessCount) ↔
      next = compactFormulaTransformStep (mode, witness) current := by
  exact ⟨compactFormulaTransformStepRows_sound
      hcurrent hnext hwitness hwitnessCount,
    compactFormulaTransformStepRows_complete
      hcurrent hnext hwitness hwitnessCount hwell⟩

theorem exists_compactFormulaTransformStepFormula_iff_step
    {tokenTable width tokenCount mode
      witnessStart witnessFinish witnessCount : Nat}
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
    (hwitnessCount : witnessCount = witness.length)
    (hwell : CompactSyntaxTaskStackFieldsWellFormed current.1.2.1) :
    (∃ stepWitness consumedCount mappedHead,
      compactFormulaTransformStepRowsDef.val.Evalb
        (compactFormulaTransformStepRowsEnvironment
          tokenTable width tokenCount currentCoordinates nextCoordinates
            mode stepWitness consumedCount mappedHead
              witnessStart witnessFinish witnessCount)) ↔
      next = compactFormulaTransformStep (mode, witness) current := by
  simpa only [compactFormulaTransformStepRowsDef_spec] using
    exists_compactFormulaTransformStepRows_iff_step
      hcurrent hnext hwitness hwitnessCount hwell

#print axioms compactFormulaTransformStepRowsDef_spec
#print axioms compactFormulaTransformStepRowsDef_sigmaZero
#print axioms compactFormulaTransformTransitionEmission_eq_nil_of_tokens_eq
#print axioms compactFormulaTransformStep_parser
#print axioms compactFormulaTransformQuietParserRows_parser_and_tokens
#print axioms compactFormulaTransformStep_output_eq_of_tokens_eq
#print axioms compactFormulaTransformStepRows_sound
#print axioms compactFormulaTransformStepRows_complete
#print axioms exists_compactFormulaTransformStepRows_iff_step
#print axioms exists_compactFormulaTransformStepFormula_iff_step

end FoundationCompactNumericListedDirectFormulaTransformStepFormula
