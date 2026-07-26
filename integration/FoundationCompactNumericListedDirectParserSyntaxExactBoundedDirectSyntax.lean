import integration.FoundationCompactNumericListedDirectParserSyntaxExactFormula
import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSourceAlignment
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectGraph
import integration.FoundationCompactPAExponentialRuleCompiler

/-! # Direct closed syntax for the exact bounded parser graph -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExponentialRuleCompiler
open FoundationCompactNumericListedDirectParserSyntaxTraceFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSourceAlignment
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectGraph

def compactParserSyntaxTraceBoundedExactFuelDirectTerms
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) :
    Fin 15 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm stateBoundary,
    shortBinaryNumeralTerm stateCount,
    compactParserSyntaxExactFuelTerm inputCount,
    shortBinaryNumeralTerm inputBoundary,
    shortBinaryNumeralTerm inputCount,
    shortBinaryNumeralTerm expectedBoundary,
    shortBinaryNumeralTerm expectedCount,
    shortBinaryNumeralTerm taskKind,
    shortBinaryNumeralTerm taskBinderArity,
    shortBinaryNumeralTerm taskRepeatCount,
    shortBinaryNumeralTerm tableWidth,
    shortBinaryNumeralTerm valueBound]

def compactParserSyntaxTraceBoundedExactFuelDirectClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactParserSyntaxTraceBoundedGraphDef.val) ⇜
    compactParserSyntaxTraceBoundedExactFuelDirectTerms tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound

def compactParserSyntaxTraceBoundedExactFuelDirectExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) :
    ValuationFormula :=
  compactParserInitialFinalExactFuelCountFormula stateCount inputCount ⋏
    (compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound ⋏
      compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputCount tableWidth
        valueBound)

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

private theorem rewriting_embeddedTermSubstitution
    {sourceVariables targetVariables : Type*}
    {termArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (term : ArithmeticSemiterm Empty termArity)
    (terms : Fin termArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting
        ((Rew.subst terms)
          ((Rew.emb : Rew ℒₒᵣ Empty termArity
            sourceVariables termArity) term)) =
      (Rew.subst (rewriting ∘ terms))
        ((Rew.emb : Rew ℒₒᵣ Empty termArity
          targetVariables termArity) term) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty termArity
            sourceVariables termArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty termArity
            targetVariables termArity) := by
    apply Rew.ext
    · intro coordinate
      simp [Rew.comp_app]
    · intro coordinate
      exact Empty.elim coordinate
  have happ := congrArg (fun candidate => candidate term) hcomposition
  simpa only [Rew.comp_app] using happ

private theorem arithmeticTermSubstitution_congr
    {variableType : Type*}
    {termArity targetArity : Nat}
    {left right : Fin termArity ->
      ArithmeticSemiterm variableType targetArity}
    (hterms : ∀ coordinate, left coordinate = right coordinate) :
    Rew.subst left = Rew.subst right := by
  apply Rew.ext
  · intro coordinate
    simpa [Rew.subst_bvar] using hterms coordinate
  · intro coordinate
    rfl

theorem compactParserSyntaxTraceBoundedExactFuelDirectClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) :
    compactParserSyntaxTraceBoundedExactFuelDirectClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound =
      compactParserSyntaxTraceBoundedExactFuelDirectExplicitFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound := by
  unfold compactParserSyntaxTraceBoundedExactFuelDirectClosedFormula
  unfold compactParserSyntaxTraceBoundedExactFuelDirectExplicitFormula
  rw [
    compactParserInitialFinalBoundedExactFuelDirectClosedFormula_eq_original]
  unfold compactParserInitialFinalExactFuelCountFormula
  unfold compactParserSyntaxTraceBoundedGraphDef
  unfold compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    first
    | rfl
    | (
      congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [compactParserSyntaxTraceBoundedExactFuelDirectTerms,
            compactParserInitialFinalBoundedExactFuelDirectSourceTerms,
            compactParserInitialFinalBoundedExactFuelDirectPublicTerms,
            Rew.comp_app, Rew.subst_bvar, Matrix.vecAppend_eq_ite]
      · intro coordinate
        exact Empty.elim coordinate)

def compactParserSyntaxExactBoundedDirectPublicTerms
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) :
    Fin 14 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm stateBoundary,
    shortBinaryNumeralTerm stateCount,
    shortBinaryNumeralTerm inputBoundary,
    shortBinaryNumeralTerm inputCount,
    shortBinaryNumeralTerm expectedBoundary,
    shortBinaryNumeralTerm expectedCount,
    shortBinaryNumeralTerm taskKind,
    shortBinaryNumeralTerm taskBinderArity,
    shortBinaryNumeralTerm taskRepeatCount,
    shortBinaryNumeralTerm tableWidth,
    shortBinaryNumeralTerm valueBound]

def compactParserSyntaxExactBoundedDirectClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactParserSyntaxExactBoundedGraphDef.val) ⇜
    compactParserSyntaxExactBoundedDirectPublicTerms tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound

theorem compactParserSyntaxExactBoundedDirectClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) :
    compactParserSyntaxExactBoundedDirectClosedFormula tokenTable width
        tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound =
      compactParserSyntaxTraceBoundedExactFuelDirectClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound := by
  unfold compactParserSyntaxExactBoundedDirectClosedFormula
  unfold compactParserSyntaxTraceBoundedExactFuelDirectClosedFormula
  unfold compactParserSyntaxExactBoundedGraphDef
  simp [← TransitiveRewriting.comp_app]
  congr 1
  apply arithmeticRewritingApp_congr
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [compactParserSyntaxExactBoundedDirectPublicTerms,
        compactParserSyntaxTraceBoundedExactFuelDirectTerms,
        compactParserSyntaxExactFuelTerm,
        compactParserSyntaxExactNativeNumeralTerm,
        rewriting_embeddedTermSubstitution,
        emb_subst_term_eq_subst_emb,
        Rew.comp_app, Rew.subst_bvar,
        Semiterm.Operator.operator, Function.comp_def]
    all_goals
      congr 1
      apply arithmeticTermSubstitution_congr
      intro child
      fin_cases child <;>
        simp [rewriting_embeddedTermSubstitution,
          emb_subst_term_eq_subst_emb,
          Function.comp_def]
    all_goals
      congr 1
      apply arithmeticTermSubstitution_congr
      intro child
      fin_cases child <;>
        simp [rewriting_embeddedTermSubstitution,
          emb_subst_term_eq_subst_emb,
          Function.comp_def]
    all_goals
      congr 1
      apply arithmeticTermSubstitution_congr
      intro child
      fin_cases child <;>
        simp [rewriting_embeddedTermSubstitution,
          emb_subst_term_eq_subst_emb,
          Rew.subst_bvar, Function.comp_def]
    all_goals
      congr 1
      apply arithmeticTermSubstitution_congr
      intro child
      fin_cases child <;>
        simp [rewriting_embeddedTermSubstitution,
          emb_subst_term_eq_subst_emb,
          Rew.subst_bvar, Function.comp_def]
  · intro coordinate
    exact Empty.elim coordinate

#print axioms
  compactParserSyntaxTraceBoundedExactFuelDirectClosedFormula_alignment
#print axioms
  compactParserSyntaxExactBoundedDirectClosedFormula_alignment

end FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectSyntax
