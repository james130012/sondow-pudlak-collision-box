import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax

/-! # Exact-fuel alignment of the final parser-state formula -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFinalAlignment

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserFinalFormula
open FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax

def compactParserInitialFinalFinalSourceTerms :
    Fin 16 -> ArithmeticSemiterm Nat 36 :=
  ![#0, #1, #2, #23, #24, #25, #26, #27, #28, #29, #30,
    #8, #9, #33, #34, #35]

def compactParserInitialFinalFinalClosedSourceTerms :
    Fin 16 -> ArithmeticSemiterm Empty 36 :=
  ![#0, #1, #2, #23, #24, #25, #26, #27, #28, #29, #30,
    #8, #9, #33, #34, #35]

theorem compactParserInitialFinalFinalClosedSourceTerms_embedding :
    (fun coordinate =>
      (Rew.emb : Rew ℒₒᵣ Empty 36 Nat 36)
        (compactParserInitialFinalFinalClosedSourceTerms coordinate)) =
      compactParserInitialFinalFinalSourceTerms := by
  funext coordinate
  fin_cases coordinate <;>
    simp [compactParserInitialFinalFinalClosedSourceTerms,
      compactParserInitialFinalFinalSourceTerms]

theorem compactUnifiedParserInitialFinalRowsExactFuel_final_alignment
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    Rew.subst
        (compactUnifiedParserInitialFinalRowsExactFuelTerms tokenTable width
          tokenCount stateBoundary stateCount inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount witness) ▹
      ((Rewriting.emb (ξ := Nat) compactUnifiedParserFinalStateRowsDef.val) ⇜
        compactParserInitialFinalFinalSourceTerms) =
      compactUnifiedParserFinalStateRowsClosedFormula tokenTable width
        tokenCount witness.finalCoordinates expectedBoundary expectedCount
        witness.outputStart witness.outputBoundary
        witness.outputBoundarySize := by
  unfold compactUnifiedParserFinalStateRowsClosedFormula
  rw [← TransitiveRewriting.comp_app]
  apply Rewriting.smul_ext'
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [compactParserInitialFinalFinalSourceTerms,
        compactUnifiedParserInitialFinalRowsExactFuelTerms,
        Rew.comp_app, Rew.subst_bvar,
        arithmeticZeroTerm, Semiterm.Operator.operator,
        Semiterm.Operator.numeral_zero,
        Semiterm.Operator.Zero.term_eq, Rew.func, Matrix.empty_eq]
  · intro coordinate
    rfl

theorem compactUnifiedParserInitialFinalRowsExactFuel_final_embedded_alignment
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    Rew.subst
        (compactUnifiedParserInitialFinalRowsExactFuelTerms tokenTable width
          tokenCount stateBoundary stateCount inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount witness) ▹
      Rewriting.emb (ξ := Nat)
        (compactUnifiedParserFinalStateRowsDef.val ⇜
          compactParserInitialFinalFinalClosedSourceTerms) =
      compactUnifiedParserFinalStateRowsClosedFormula tokenTable width
        tokenCount witness.finalCoordinates expectedBoundary expectedCount
        witness.outputStart witness.outputBoundary
        witness.outputBoundarySize := by
  rw [Rewriting.emb_subst_eq_subst_emb]
  rw [compactParserInitialFinalFinalClosedSourceTerms_embedding]
  exact
    compactUnifiedParserInitialFinalRowsExactFuel_final_alignment
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount witness

#print axioms
  compactUnifiedParserInitialFinalRowsExactFuel_final_alignment

#print axioms
  compactUnifiedParserInitialFinalRowsExactFuel_final_embedded_alignment

end FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFinalAlignment
