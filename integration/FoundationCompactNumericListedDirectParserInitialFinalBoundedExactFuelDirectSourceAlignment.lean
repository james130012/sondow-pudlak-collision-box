import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSyntax
import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceTerminalSubstitution
import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectOriginalSourceAlignment

/-! # Public-source alignment for exact-fuel bounded endpoints -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSourceAlignment

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectOriginalSourceAlignment
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSyntax

theorem
    compactParserInitialFinalBoundedExactFuelDirectSourceRawTerms_rewriting
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound : Nat) :
    sourceSubstitutionQpow
        (compactParserInitialFinalBoundedExactFuelDirectSourceTerms tokenTable
          width tokenCount stateBoundary stateCount inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount valueBound) 23 ∘
      compactParserInitialFinalBoundedDirectSourceRawTerms =
    compactParserInitialFinalBoundedExactFuelDirectRawTerms tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount := by
  funext coordinate
  unfold compactParserInitialFinalBoundedDirectSourceRawTerms
    compactParserInitialFinalBoundedExactFuelDirectRawTerms
  simp only [Function.comp_apply, Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · unfold compactParserInitialFinalBoundedDirectSourcePublicTerms
      compactParserInitialFinalBoundedExactFuelDirectRawPublicTerms
    calc
      sourceSubstitutionQpow
          (compactParserInitialFinalBoundedExactFuelDirectSourceTerms
            tokenTable width tokenCount stateBoundary stateCount inputBoundary
            inputCount expectedBoundary expectedCount taskKind taskBinderArity
            taskRepeatCount valueBound) 23
          (#(⟨23 + (⟨coordinate, by omega⟩ : Fin 14).val,
            by omega⟩ : Fin 37)) =
        sourceSubstitutionLift 23
          (compactParserInitialFinalBoundedExactFuelDirectSourceTerms
            tokenTable width tokenCount stateBoundary stateCount inputBoundary
            inputCount expectedBoundary expectedCount taskKind taskBinderArity
            taskRepeatCount valueBound ⟨coordinate, by omega⟩) := by
              simpa using
                (sourceSubstitutionQpow_shiftedBVar
                  (compactParserInitialFinalBoundedExactFuelDirectSourceTerms
                    tokenTable width tokenCount stateBoundary stateCount
                    inputBoundary inputCount expectedBoundary expectedCount
                    taskKind taskBinderArity taskRepeatCount valueBound)
                  23 ⟨coordinate, by omega⟩)
      _ = sourceSubstitutionLift 23
          (compactParserInitialFinalBoundedExactFuelDirectPublicTerms
            tokenTable width tokenCount stateBoundary stateCount inputBoundary
            inputCount expectedBoundary expectedCount taskKind taskBinderArity
            taskRepeatCount ⟨coordinate, hcoordinate⟩) := by
              simp [
                compactParserInitialFinalBoundedExactFuelDirectSourceTerms,
                Matrix.vecAppend_eq_ite, hcoordinate]
  · unfold compactParserInitialFinalBoundedDirectSourceWitnessTerms
      compactParserInitialFinalBoundedDirectRawWitnessTerms
    rw [sourceSubstitutionQpow_bvar]
    simp [sourceSubstitutionNormalizedBVarResult]

theorem
    compactParserInitialFinalBoundedExactFuelDirectSourceRawTerminal_rewriting
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound : Nat) :
    sourceSubstitutionQpow
        (compactParserInitialFinalBoundedExactFuelDirectSourceTerms tokenTable
          width tokenCount stateBoundary stateCount inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount valueBound) 23 ▹
      compactParserInitialFinalBoundedDirectSourceRawTerminal =
    compactParserInitialFinalBoundedExactFuelDirectRawTerminal tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount := by
  unfold compactParserInitialFinalBoundedDirectSourceRawTerminal
    compactParserInitialFinalBoundedExactFuelDirectRawTerminal
  rw [
    FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase.rewriting_embeddedFormulaSubstitution]
  rw [
    compactParserInitialFinalBoundedExactFuelDirectSourceRawTerms_rewriting]

theorem compactParserInitialFinalBoundedExactFuelDirectClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound : Nat) :
    compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 23
        (compactParserInitialFinalBoundedExactFuelDirectRawTerminal tokenTable
          width tokenCount stateBoundary stateCount inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount) := by
  unfold compactParserInitialFinalBoundedExactFuelDirectClosedFormula
    compactParserInitialFinalBoundedDirectSourceRawBody
  rw [sourceSubstitution_sourceBoundedWitnessFormula]
  rw [
    compactParserInitialFinalBoundedExactFuelDirectSourceRawTerminal_rewriting]
  have hbound :
      Rew.subst
          (compactParserInitialFinalBoundedExactFuelDirectSourceTerms
            tokenTable width tokenCount stateBoundary stateCount inputBoundary
            inputCount expectedBoundary expectedCount taskKind taskBinderArity
            taskRepeatCount valueBound)
          (#13 : ArithmeticSemiterm Nat 14) =
        shortBinaryNumeralTerm valueBound := by
    simp [Rew.subst_bvar,
      compactParserInitialFinalBoundedExactFuelDirectSourceTerms,
      Matrix.vecAppend_eq_ite]
  rw [hbound]
  rfl

theorem
    compactParserInitialFinalBoundedExactFuelDirectClosedFormula_eq_original
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound : Nat) :
    compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound =
      (Rewriting.emb (ξ := Nat) compactParserInitialFinalBoundedDef.val) ⇜
        compactParserInitialFinalBoundedExactFuelDirectSourceTerms tokenTable
          width tokenCount stateBoundary stateCount inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount valueBound := by
  unfold compactParserInitialFinalBoundedExactFuelDirectClosedFormula
  rw [compactParserInitialFinalBoundedDef_emb_eq_directSourceRawBody]

#print axioms
  compactParserInitialFinalBoundedExactFuelDirectSourceRawTerms_rewriting
#print axioms
  compactParserInitialFinalBoundedExactFuelDirectSourceRawTerminal_rewriting
#print axioms
  compactParserInitialFinalBoundedExactFuelDirectClosedFormula_alignment
#print axioms
  compactParserInitialFinalBoundedExactFuelDirectClosedFormula_eq_original

end FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSourceAlignment
