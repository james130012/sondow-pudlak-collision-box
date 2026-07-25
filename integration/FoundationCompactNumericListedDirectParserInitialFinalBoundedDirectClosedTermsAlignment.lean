import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax

/-! # Coordinate alignment of the split endpoint term vector -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectClosedTermsAlignment

open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax

theorem compactUnifiedParserInitialFinalRowsClosedFormula_eq_directClosedTerms
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    compactUnifiedParserInitialFinalRowsClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness =
      (Rewriting.emb (ξ := Nat)
          compactUnifiedParserInitialFinalRowsDef.val) ⇜
        compactParserInitialFinalBoundedDirectClosedTerms tokenTable width
          tokenCount stateBoundary stateCount fuel inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount witness := by
  unfold compactUnifiedParserInitialFinalRowsClosedFormula
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [compactParserInitialFinalBoundedDirectClosedTerms,
      compactParserInitialFinalBoundedDirectPublicTerms,
      compactParserInitialFinalBoundedDirectClosedWitnessTerms,
      compactParserInitialFinalBoundedDirectWitnessValues,
      compactParserInitialFinalBoundedDirectReverseIndex,
      Matrix.vecAppend_eq_ite]

#print axioms
  compactUnifiedParserInitialFinalRowsClosedFormula_eq_directClosedTerms

end FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectClosedTermsAlignment
