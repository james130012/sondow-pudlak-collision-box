import integration.FoundationCompactNumericListedDirectParserInitialFinalFormula
import integration.FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate

/-!
# Explicit hybrid certificate for the combined parser endpoints

The exact initial and final rows are assembled in the source-formula order.
The trace-length equation keeps the original unary `1`, and the two state-row
certificates select the original rows `0` and `fuel`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserInitialFinalExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      Rewriting.app right := by
  cases h
  rfl

def compactUnifiedParserInitialFinalRowsClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserInitialFinalRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      shortBinaryNumeralTerm fuel,
      shortBinaryNumeralTerm inputBoundary,
      shortBinaryNumeralTerm inputCount,
      shortBinaryNumeralTerm expectedBoundary,
      shortBinaryNumeralTerm expectedCount,
      shortBinaryNumeralTerm taskKind,
      shortBinaryNumeralTerm taskBinderArity,
      shortBinaryNumeralTerm taskRepeatCount,
      shortBinaryNumeralTerm witness.initialCoordinates.start,
      shortBinaryNumeralTerm witness.initialCoordinates.finish,
      shortBinaryNumeralTerm witness.initialCoordinates.tokensFinish,
      shortBinaryNumeralTerm witness.initialCoordinates.tasksFinish,
      shortBinaryNumeralTerm witness.initialCoordinates.tokensBoundary,
      shortBinaryNumeralTerm witness.initialCoordinates.tokensCount,
      shortBinaryNumeralTerm witness.initialCoordinates.tasksBoundary,
      shortBinaryNumeralTerm witness.initialCoordinates.tasksCount,
      shortBinaryNumeralTerm witness.initialSizeWitness.tokensBoundarySize,
      shortBinaryNumeralTerm witness.initialSizeWitness.tasksBoundarySize,
      shortBinaryNumeralTerm witness.finalCoordinates.start,
      shortBinaryNumeralTerm witness.finalCoordinates.finish,
      shortBinaryNumeralTerm witness.finalCoordinates.tokensFinish,
      shortBinaryNumeralTerm witness.finalCoordinates.tasksFinish,
      shortBinaryNumeralTerm witness.finalCoordinates.tokensBoundary,
      shortBinaryNumeralTerm witness.finalCoordinates.tokensCount,
      shortBinaryNumeralTerm witness.finalCoordinates.tasksBoundary,
      shortBinaryNumeralTerm witness.finalCoordinates.tasksCount,
      shortBinaryNumeralTerm witness.finalSizeWitness.tokensBoundarySize,
      shortBinaryNumeralTerm witness.finalSizeWitness.tasksBoundarySize,
      shortBinaryNumeralTerm witness.outputStart,
      shortBinaryNumeralTerm witness.outputBoundary,
      shortBinaryNumeralTerm witness.outputBoundarySize]

def compactUnifiedParserInitialFinalRowsExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm stateCount) =
      !!(shortBinaryNumeralTerm fuel) + 1” ⋏
    (compactUnifiedParserStateAtRowsClosedFormula
        tokenTable width tokenCount stateBoundary stateCount 0
        witness.initialCoordinates witness.initialSizeWitness ⋏
      (compactUnifiedParserInitialStateRowsClosedFormula
          tokenTable width tokenCount witness.initialCoordinates
          inputBoundary inputCount taskKind taskBinderArity taskRepeatCount ⋏
        (compactUnifiedParserStateAtRowsClosedFormula
            tokenTable width tokenCount stateBoundary stateCount fuel
            witness.finalCoordinates witness.finalSizeWitness ⋏
          compactUnifiedParserFinalStateRowsClosedFormula
            tokenTable width tokenCount witness.finalCoordinates
            expectedBoundary expectedCount witness.outputStart
            witness.outputBoundary witness.outputBoundarySize)))

theorem compactUnifiedParserInitialFinalRowsClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    compactUnifiedParserInitialFinalRowsClosedFormula
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedBoundary expectedCount
        taskKind taskBinderArity taskRepeatCount witness =
      compactUnifiedParserInitialFinalRowsExplicitFormula
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedBoundary expectedCount
        taskKind taskBinderArity taskRepeatCount witness := by
  unfold compactUnifiedParserInitialFinalRowsClosedFormula
  unfold compactUnifiedParserInitialFinalRowsExplicitFormula
  unfold compactUnifiedParserInitialFinalRowsDef
  unfold compactUnifiedParserStateAtRowsClosedFormula
  unfold compactUnifiedParserInitialStateRowsClosedFormula
  unfold compactUnifiedParserFinalStateRowsClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar,
          arithmeticZeroTerm, Semiterm.Operator.operator,
          Semiterm.Operator.numeral_zero,
          Semiterm.Operator.Zero.term_eq, Rew.func, Matrix.empty_eq]
    · intro coordinate
      exact Empty.elim coordinate

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private noncomputable def stateCountCertificate
    (stateCount fuel : Nat) (hcount : stateCount = fuel + 1) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm stateCount) =
        !!(shortBinaryNumeralTerm fuel) + 1” := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm fuel) + 1’
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm stateCount, rightTerm] (by
      change termValue zeroValuation (shortBinaryNumeralTerm stateCount) =
        termValue zeroValuation rightTerm
      simpa [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticOne] using hcount)
  exact .cast (Semiformula.Operator.eq_def _ _).symm direct

noncomputable def
    compactUnifiedParserInitialFinalRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates)
    (hgraph : CompactUnifiedParserInitialFinalRows
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount witness) :
    HybridCertificate
      (compactUnifiedParserInitialFinalRowsClosedFormula
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedBoundary expectedCount
        taskKind taskBinderArity taskRepeatCount witness) := by
  rcases hgraph with
    ⟨hcount, hinitialAt, hinitial, hfinalAt, hfinal⟩
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (stateCountCertificate stateCount fuel hcount)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactUnifiedParserStateAtRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount stateBoundary stateCount 0
        witness.initialCoordinates witness.initialSizeWitness hinitialAt)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactUnifiedParserInitialStateRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount witness.initialCoordinates
          inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
          hinitial)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactUnifiedParserStateAtRowsExplicitHybridCertificateOfGraph
            tokenTable width tokenCount stateBoundary stateCount fuel
            witness.finalCoordinates witness.finalSizeWitness hfinalAt)
          (compactUnifiedParserFinalStateRowsExplicitHybridCertificateOfGraph
            tokenTable width tokenCount witness.finalCoordinates
            expectedBoundary expectedCount witness.outputStart
            witness.outputBoundary witness.outputBoundarySize hfinal))))
  exact .cast
    (compactUnifiedParserInitialFinalRowsClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount witness).symm parts

#print axioms compactUnifiedParserInitialFinalRowsClosedFormula_alignment
#print axioms
  compactUnifiedParserInitialFinalRowsExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectParserInitialFinalExplicitHybridCertificate
