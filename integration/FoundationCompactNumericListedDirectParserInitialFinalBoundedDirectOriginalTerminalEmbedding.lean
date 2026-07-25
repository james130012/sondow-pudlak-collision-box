import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectOriginalSyntax

/-! # Embedding the empty-variable endpoint terminal into natural variables -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectOriginalTerminalEmbedding

open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectOriginalSyntax

def compactParserInitialFinalBoundedDirectExplicitSourceTerms :
    Fin 36 -> ArithmeticSemiterm Nat 37 :=
  ![(#23 : ArithmeticSemiterm Nat 37), #24, #25, #26, #27, #28,
      #29, #30, #31, #32, #33, #34, #35,
      #22, #21, #20, #19, #18, #17, #16, #15, #14, #13, #12, #11,
      #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

def compactParserInitialFinalBoundedDirectExplicitSourceRawTerminal :
    ArithmeticSemiformula Nat 37 :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserInitialFinalRowsDef.val) ⇜
    compactParserInitialFinalBoundedDirectExplicitSourceTerms

private theorem compactParserInitialFinalBoundedDirect_emb_comp_subst :
    (Rew.emb : Rew ℒₒᵣ Empty 37 Nat 37).comp
        (Rew.subst
          compactParserInitialFinalBoundedDirectEmptySourceExplicitTerms) =
      (Rew.subst
        compactParserInitialFinalBoundedDirectExplicitSourceTerms).comp
        (Rew.emb : Rew ℒₒᵣ Empty 36 Nat 36) := by
  apply Rew.ext
  · intro coordinate
    simp only [Rew.comp_app, Rew.subst_bvar]
    fin_cases coordinate <;>
      simp [compactParserInitialFinalBoundedDirectEmptySourceExplicitTerms,
        compactParserInitialFinalBoundedDirectExplicitSourceTerms]
  · intro coordinate
    exact Empty.elim coordinate

theorem
    compactParserInitialFinalBoundedDirectEmptySourceRawTerminal_embedding :
    (Rew.emb : Rew ℒₒᵣ Empty 37 Nat 37) ▹
        compactParserInitialFinalBoundedDirectEmptySourceRawTerminal =
      compactParserInitialFinalBoundedDirectExplicitSourceRawTerminal := by
  unfold compactParserInitialFinalBoundedDirectEmptySourceRawTerminal
    compactParserInitialFinalBoundedDirectExplicitSourceRawTerminal
  calc
    (Rew.emb : Rew ℒₒᵣ Empty 37 Nat 37) ▹
        (compactUnifiedParserInitialFinalRowsDef.val ⇜
          compactParserInitialFinalBoundedDirectEmptySourceExplicitTerms) =
      ((Rew.emb : Rew ℒₒᵣ Empty 37 Nat 37).comp
          (Rew.subst
            compactParserInitialFinalBoundedDirectEmptySourceExplicitTerms)) ▹
        compactUnifiedParserInitialFinalRowsDef.val := by
          rw [TransitiveRewriting.comp_app]
    _ = ((Rew.subst
          compactParserInitialFinalBoundedDirectExplicitSourceTerms).comp
            (Rew.emb : Rew ℒₒᵣ Empty 36 Nat 36)) ▹
        compactUnifiedParserInitialFinalRowsDef.val := by
          rw [compactParserInitialFinalBoundedDirect_emb_comp_subst]
    _ = (Rewriting.emb (ξ := Nat)
          compactUnifiedParserInitialFinalRowsDef.val) ⇜
        compactParserInitialFinalBoundedDirectExplicitSourceTerms := by
          rw [TransitiveRewriting.comp_app]

#print axioms
  compactParserInitialFinalBoundedDirectEmptySourceRawTerminal_embedding

end FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectOriginalTerminalEmbedding
