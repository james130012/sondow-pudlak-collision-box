import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax

/-! # Exact-fuel alignment of the initial parser-state formula -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelInitialAlignment

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserInitialFormula
open FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax

def compactParserInitialFinalInitialSourceTerms :
    Fin 16 -> ArithmeticSemiterm Nat 36 :=
  ![#0, #1, #2, #13, #14, #15, #16, #17, #18, #19, #20,
    #6, #7, #10, #11, #12]

def compactParserInitialFinalInitialClosedSourceTerms :
    Fin 16 -> ArithmeticSemiterm Empty 36 :=
  ![#0, #1, #2, #13, #14, #15, #16, #17, #18, #19, #20,
    #6, #7, #10, #11, #12]

theorem compactParserInitialFinalInitialClosedSourceTerms_embedding :
    (fun coordinate =>
      (Rew.emb : Rew ℒₒᵣ Empty 36 Nat 36)
        (compactParserInitialFinalInitialClosedSourceTerms coordinate)) =
      compactParserInitialFinalInitialSourceTerms := by
  funext coordinate
  fin_cases coordinate <;>
    simp [compactParserInitialFinalInitialClosedSourceTerms,
      compactParserInitialFinalInitialSourceTerms]

theorem compactUnifiedParserInitialFinalRowsExactFuel_initial_alignment
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    Rew.subst
        (compactUnifiedParserInitialFinalRowsExactFuelTerms tokenTable width
          tokenCount stateBoundary stateCount inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount witness) ▹
      ((Rewriting.emb (ξ := Nat) compactUnifiedParserInitialStateRowsDef.val) ⇜
        compactParserInitialFinalInitialSourceTerms) =
      compactUnifiedParserInitialStateRowsClosedFormula tokenTable width
        tokenCount witness.initialCoordinates inputBoundary inputCount taskKind
        taskBinderArity taskRepeatCount := by
  unfold compactUnifiedParserInitialStateRowsClosedFormula
  rw [← TransitiveRewriting.comp_app]
  apply Rewriting.smul_ext'
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [compactParserInitialFinalInitialSourceTerms,
        compactUnifiedParserInitialFinalRowsExactFuelTerms,
        Rew.comp_app, Rew.subst_bvar,
        arithmeticZeroTerm, Semiterm.Operator.operator,
        Semiterm.Operator.numeral_zero,
        Semiterm.Operator.Zero.term_eq, Rew.func, Matrix.empty_eq]
  · intro coordinate
    rfl

theorem compactUnifiedParserInitialFinalRowsExactFuel_initial_embedded_alignment
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
        (compactUnifiedParserInitialStateRowsDef.val ⇜
          compactParserInitialFinalInitialClosedSourceTerms) =
      compactUnifiedParserInitialStateRowsClosedFormula tokenTable width
        tokenCount witness.initialCoordinates inputBoundary inputCount taskKind
        taskBinderArity taskRepeatCount := by
  rw [Rewriting.emb_subst_eq_subst_emb]
  rw [compactParserInitialFinalInitialClosedSourceTerms_embedding]
  exact
    compactUnifiedParserInitialFinalRowsExactFuel_initial_alignment
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount witness

#print axioms
  compactUnifiedParserInitialFinalRowsExactFuel_initial_alignment

#print axioms
  compactUnifiedParserInitialFinalRowsExactFuel_initial_embedded_alignment

end FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelInitialAlignment
