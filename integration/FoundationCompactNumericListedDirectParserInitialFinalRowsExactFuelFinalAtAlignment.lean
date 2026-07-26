import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax

/-! # Exact-fuel alignment of the final parser-state row -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFinalAtAlignment

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax

def compactParserInitialFinalFinalAtSourceTerms :
    Fin 16 -> ArithmeticSemiterm Nat 36 :=
  ![#0, #1, #2, #3, #4, #5, #23, #24, #25, #26, #27, #28, #29, #30,
    #31, #32]

def compactParserInitialFinalFinalAtClosedSourceTerms :
    Fin 16 -> ArithmeticSemiterm Empty 36 :=
  ![#0, #1, #2, #3, #4, #5, #23, #24, #25, #26, #27, #28, #29, #30,
    #31, #32]

theorem compactParserInitialFinalFinalAtClosedSourceTerms_embedding :
    (fun coordinate =>
      (Rew.emb : Rew ℒₒᵣ Empty 36 Nat 36)
        (compactParserInitialFinalFinalAtClosedSourceTerms coordinate)) =
      compactParserInitialFinalFinalAtSourceTerms := by
  funext coordinate
  fin_cases coordinate <;>
    simp [compactParserInitialFinalFinalAtClosedSourceTerms,
      compactParserInitialFinalFinalAtSourceTerms]

theorem compactUnifiedParserInitialFinalRowsExactFuel_finalAt_alignment
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
        compactParserInitialFinalFinalAtSourceTerms) =
      compactParserInitialFinalExactFuelFinalAtFormula tokenTable width
        tokenCount stateBoundary stateCount inputCount
        witness.finalCoordinates witness.finalSizeWitness := by
  unfold compactParserInitialFinalExactFuelFinalAtFormula
    compactUnifiedParserStateAtRowsAtValuationIndexFormula
  rw [← TransitiveRewriting.comp_app]
  apply Rewriting.smul_ext'
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [compactParserInitialFinalFinalAtSourceTerms,
        compactUnifiedParserInitialFinalRowsExactFuelTerms,
        Rew.comp_app, Rew.subst_bvar,
        arithmeticZeroTerm, Semiterm.Operator.operator,
        Semiterm.Operator.numeral_zero,
        Semiterm.Operator.Zero.term_eq, Rew.func, Matrix.empty_eq]
  · intro coordinate
    rfl

theorem compactUnifiedParserInitialFinalRowsExactFuel_finalAt_embedded_alignment
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
          compactParserInitialFinalFinalAtClosedSourceTerms) =
      compactParserInitialFinalExactFuelFinalAtFormula tokenTable width
        tokenCount stateBoundary stateCount inputCount
        witness.finalCoordinates witness.finalSizeWitness := by
  rw [Rewriting.emb_subst_eq_subst_emb]
  rw [compactParserInitialFinalFinalAtClosedSourceTerms_embedding]
  exact
    compactUnifiedParserInitialFinalRowsExactFuel_finalAt_alignment
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount witness

#print axioms
  compactUnifiedParserInitialFinalRowsExactFuel_finalAt_alignment

#print axioms
  compactUnifiedParserInitialFinalRowsExactFuel_finalAt_embedded_alignment

end FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFinalAtAlignment
