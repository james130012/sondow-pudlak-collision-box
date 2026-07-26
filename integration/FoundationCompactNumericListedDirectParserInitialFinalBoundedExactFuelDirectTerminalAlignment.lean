import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSourceAlignment

/-! # Terminal alignment for exact-fuel bounded parser endpoints -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectTerminalAlignment

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSyntax

private theorem substitute_sourceSubstitutionLift23
    (values : Fin 23 -> ValuationTerm) (term : ValuationTerm) :
    Rew.subst values (sourceSubstitutionLift 23 term) = term := by
  simpa only using
    (substitute_sourceSubstitutionLift (depth := 23) values term)

theorem
    compactParserInitialFinalBoundedExactFuelDirectRawTerms_substitution
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    (Rew.subst (fun index => shortBinaryNumeralTerm
        (compactParserInitialFinalBoundedDirectWitnessValues witness index))) ∘
      compactParserInitialFinalBoundedExactFuelDirectRawTerms tokenTable width
        tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount =
      compactParserInitialFinalBoundedExactFuelDirectClosedTerms tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness := by
  funext coordinate
  unfold compactParserInitialFinalBoundedExactFuelDirectRawTerms
    compactParserInitialFinalBoundedExactFuelDirectClosedTerms
  simp only [Function.comp_apply, Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · simp only [
      compactParserInitialFinalBoundedExactFuelDirectRawPublicTerms]
    exact substitute_sourceSubstitutionLift23 _ _
  · simp [compactParserInitialFinalBoundedDirectRawWitnessTerms,
      compactParserInitialFinalBoundedDirectClosedWitnessTerms,
      Rew.subst_bvar]

theorem
    compactParserInitialFinalBoundedExactFuelDirectClosedTerms_eq_exactTerms
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    compactParserInitialFinalBoundedExactFuelDirectClosedTerms tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness =
      compactUnifiedParserInitialFinalRowsExactFuelTerms tokenTable width
        tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness := by
  funext coordinate
  fin_cases coordinate <;>
    simp [
      compactParserInitialFinalBoundedExactFuelDirectClosedTerms,
      compactParserInitialFinalBoundedExactFuelDirectPublicTerms,
      compactParserInitialFinalBoundedDirectClosedWitnessTerms,
      compactParserInitialFinalBoundedDirectWitnessValues,
      compactParserInitialFinalBoundedDirectReverseIndex,
      compactUnifiedParserInitialFinalRowsExactFuelTerms,
      Matrix.vecAppend_eq_ite]

theorem
    compactUnifiedParserInitialFinalRowsExactFuelClosedFormula_eq_directClosedTerms
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    compactUnifiedParserInitialFinalRowsExactFuelClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness =
      (Rewriting.emb (ξ := Nat)
          compactUnifiedParserInitialFinalRowsDef.val) ⇜
        compactParserInitialFinalBoundedExactFuelDirectClosedTerms tokenTable
          width tokenCount stateBoundary stateCount inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount witness := by
  unfold compactUnifiedParserInitialFinalRowsExactFuelClosedFormula
  rw [
    compactParserInitialFinalBoundedExactFuelDirectClosedTerms_eq_exactTerms]

theorem compactParserInitialFinalBoundedExactFuelDirectRawTerminal_alignment
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    compactParserInitialFinalBoundedExactFuelDirectRawTerminal tokenTable width
        tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount ⇜
      (fun index => shortBinaryNumeralTerm
        (compactParserInitialFinalBoundedDirectWitnessValues witness index)) =
    compactUnifiedParserInitialFinalRowsExactFuelClosedFormula tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      witness := by
  change Rew.subst (fun index => shortBinaryNumeralTerm
      (compactParserInitialFinalBoundedDirectWitnessValues witness index)) ▹
    compactParserInitialFinalBoundedExactFuelDirectRawTerminal tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount = _
  unfold compactParserInitialFinalBoundedExactFuelDirectRawTerminal
  rw [
    FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase.rewriting_embeddedFormulaSubstitution]
  rw [
    compactParserInitialFinalBoundedExactFuelDirectRawTerms_substitution]
  exact
    (compactUnifiedParserInitialFinalRowsExactFuelClosedFormula_eq_directClosedTerms
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount witness).symm

#print axioms
  compactParserInitialFinalBoundedExactFuelDirectRawTerms_substitution
#print axioms
  compactParserInitialFinalBoundedExactFuelDirectClosedTerms_eq_exactTerms
#print axioms
  compactUnifiedParserInitialFinalRowsExactFuelClosedFormula_eq_directClosedTerms
#print axioms
  compactParserInitialFinalBoundedExactFuelDirectRawTerminal_alignment

end FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectTerminalAlignment
