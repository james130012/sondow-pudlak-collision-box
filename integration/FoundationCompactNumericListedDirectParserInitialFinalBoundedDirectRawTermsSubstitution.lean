import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax

/-! # Substitution of the split endpoint source-term vector -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectRawTermsSubstitution

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax

private theorem substitute_sourceSubstitutionLift23
    (values : Fin 23 -> ValuationTerm) (term : ValuationTerm) :
    Rew.subst values (sourceSubstitutionLift 23 term) = term := by
  simpa only using
    (substitute_sourceSubstitutionLift (depth := 23) values term)

theorem compactParserInitialFinalBoundedDirectRawTerms_substitution
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    (Rew.subst (fun index => shortBinaryNumeralTerm
        (compactParserInitialFinalBoundedDirectWitnessValues witness index))) ∘
      compactParserInitialFinalBoundedDirectRawTerms tokenTable width tokenCount
        stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
        expectedCount taskKind taskBinderArity taskRepeatCount =
      compactParserInitialFinalBoundedDirectClosedTerms tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness := by
  funext coordinate
  unfold compactParserInitialFinalBoundedDirectRawTerms
    compactParserInitialFinalBoundedDirectClosedTerms
  simp only [Function.comp_apply, Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · simp only [compactParserInitialFinalBoundedDirectRawPublicTerms]
    exact substitute_sourceSubstitutionLift23 _ _
  · simp [compactParserInitialFinalBoundedDirectRawWitnessTerms,
      compactParserInitialFinalBoundedDirectClosedWitnessTerms,
      Rew.subst_bvar]

#print axioms compactParserInitialFinalBoundedDirectRawTerms_substitution

end FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectRawTermsSubstitution
