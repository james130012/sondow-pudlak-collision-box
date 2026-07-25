import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceSyntax

/-! # Public substitution below the twenty-three endpoint binders -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceTermsSubstitution

open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceSyntax

theorem compactParserInitialFinalBoundedDirectSourceRawTerms_rewriting
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat) :
    sourceSubstitutionQpow
        (compactParserInitialFinalBoundedDirectSourceTerms tokenTable width
          tokenCount stateBoundary stateCount fuel inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount valueBound) 23 ∘
      compactParserInitialFinalBoundedDirectSourceRawTerms =
    compactParserInitialFinalBoundedDirectRawTerms tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount := by
  funext coordinate
  unfold compactParserInitialFinalBoundedDirectSourceRawTerms
    compactParserInitialFinalBoundedDirectRawTerms
  simp only [Function.comp_apply, Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · unfold compactParserInitialFinalBoundedDirectSourcePublicTerms
      compactParserInitialFinalBoundedDirectRawPublicTerms
    calc
      sourceSubstitutionQpow
          (compactParserInitialFinalBoundedDirectSourceTerms tokenTable width
            tokenCount stateBoundary stateCount fuel inputBoundary inputCount
            expectedBoundary expectedCount taskKind taskBinderArity
            taskRepeatCount valueBound) 23
          (#(⟨23 + (⟨coordinate, by omega⟩ : Fin 14).val,
            by omega⟩ : Fin 37)) =
        sourceSubstitutionLift 23
          (compactParserInitialFinalBoundedDirectSourceTerms tokenTable width
            tokenCount stateBoundary stateCount fuel inputBoundary inputCount
            expectedBoundary expectedCount taskKind taskBinderArity
            taskRepeatCount valueBound
            ⟨coordinate, by omega⟩) := by
              simpa using
                (sourceSubstitutionQpow_shiftedBVar
                  (compactParserInitialFinalBoundedDirectSourceTerms tokenTable
                    width tokenCount stateBoundary stateCount fuel
                    inputBoundary inputCount expectedBoundary expectedCount
                    taskKind taskBinderArity taskRepeatCount valueBound)
                  23 ⟨coordinate, by omega⟩)
      _ = sourceSubstitutionLift 23
          (compactParserInitialFinalBoundedDirectPublicTerms tokenTable width
            tokenCount stateBoundary stateCount fuel inputBoundary inputCount
            expectedBoundary expectedCount taskKind taskBinderArity
            taskRepeatCount ⟨coordinate, hcoordinate⟩) := by
              simp [compactParserInitialFinalBoundedDirectSourceTerms,
                Matrix.vecAppend_eq_ite, hcoordinate]
  · unfold compactParserInitialFinalBoundedDirectSourceWitnessTerms
      compactParserInitialFinalBoundedDirectRawWitnessTerms
    rw [sourceSubstitutionQpow_bvar]
    simp [sourceSubstitutionNormalizedBVarResult]

#print axioms
  compactParserInitialFinalBoundedDirectSourceRawTerms_rewriting

end FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceTermsSubstitution
