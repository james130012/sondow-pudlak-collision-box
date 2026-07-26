import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax

/-! # Exact-fuel alignment of the initial parser-state row -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelInitialAtAlignment

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax

def compactParserInitialFinalInitialAtSourceTerms :
    Fin 16 -> ArithmeticSemiterm Nat 36 :=
  ![#0, #1, #2, #3, #4, (‘0’ : ArithmeticSemiterm Nat 36),
    #13, #14, #15, #16, #17, #18, #19, #20, #21, #22]

def compactParserInitialFinalInitialAtClosedSourceTerms :
    Fin 16 -> ArithmeticSemiterm Empty 36 :=
  ![#0, #1, #2, #3, #4, (‘0’ : ArithmeticSemiterm Empty 36),
    #13, #14, #15, #16, #17, #18, #19, #20, #21, #22]

theorem compactParserInitialFinalInitialAtClosedSourceTerms_embedding :
    (fun coordinate =>
      (Rew.emb : Rew ℒₒᵣ Empty 36 Nat 36)
        (compactParserInitialFinalInitialAtClosedSourceTerms coordinate)) =
      compactParserInitialFinalInitialAtSourceTerms := by
  funext coordinate
  fin_cases coordinate <;>
    simp [compactParserInitialFinalInitialAtClosedSourceTerms,
      compactParserInitialFinalInitialAtSourceTerms,
      arithmeticZeroTerm, Semiterm.Operator.operator,
      Semiterm.Operator.numeral_zero,
      Semiterm.Operator.Zero.term_eq, Rew.func, Matrix.empty_eq]

theorem compactUnifiedParserInitialFinalRowsExactFuel_initialAt_alignment
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    Rew.subst
        (compactUnifiedParserInitialFinalRowsExactFuelTerms tokenTable width
          tokenCount stateBoundary stateCount inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount witness) ▹
      ((Rewriting.emb (ξ := Nat) compactUnifiedParserStateAtRowsDef.val) ⇜
        compactParserInitialFinalInitialAtSourceTerms) =
      compactUnifiedParserStateAtRowsClosedFormula tokenTable width tokenCount
        stateBoundary stateCount 0 witness.initialCoordinates
        witness.initialSizeWitness := by
  unfold compactUnifiedParserStateAtRowsClosedFormula
  rw [← TransitiveRewriting.comp_app]
  apply Rewriting.smul_ext'
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [compactParserInitialFinalInitialAtSourceTerms,
        compactUnifiedParserInitialFinalRowsExactFuelTerms,
        Rew.comp_app, Rew.subst_bvar,
        arithmeticZeroTerm, Semiterm.Operator.operator,
        Semiterm.Operator.numeral_zero,
        Semiterm.Operator.Zero.term_eq, Rew.func, Matrix.empty_eq]
  · intro coordinate
    rfl

theorem compactUnifiedParserInitialFinalRowsExactFuel_initialAt_embedded_alignment
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
        (compactUnifiedParserStateAtRowsDef.val ⇜
          compactParserInitialFinalInitialAtClosedSourceTerms) =
      compactUnifiedParserStateAtRowsClosedFormula tokenTable width tokenCount
        stateBoundary stateCount 0 witness.initialCoordinates
        witness.initialSizeWitness := by
  rw [Rewriting.emb_subst_eq_subst_emb]
  rw [compactParserInitialFinalInitialAtClosedSourceTerms_embedding]
  exact
    compactUnifiedParserInitialFinalRowsExactFuel_initialAt_alignment
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount witness

#print axioms
  compactUnifiedParserInitialFinalRowsExactFuel_initialAt_alignment

#print axioms
  compactUnifiedParserInitialFinalRowsExactFuel_initialAt_embedded_alignment

end FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelInitialAtAlignment
