import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceTerminalSplitAlignment

/-! # Alignment of the public source syntax with the original bounded formula -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectOriginalSourceAlignment

open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectOriginalSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectOriginalTerminalEmbedding
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceTerminalSplitAlignment

theorem
    compactParserInitialFinalBoundedDirectEmptySourceRawTerminal_embedding :
    (Rew.emb : Rew ℒₒᵣ Empty 37 Nat 37) ▹
        compactParserInitialFinalBoundedDirectEmptySourceRawTerminal =
      compactParserInitialFinalBoundedDirectSourceRawTerminal := by
  calc
    (Rew.emb : Rew ℒₒᵣ Empty 37 Nat 37) ▹
        compactParserInitialFinalBoundedDirectEmptySourceRawTerminal =
      compactParserInitialFinalBoundedDirectExplicitSourceRawTerminal :=
        FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectOriginalTerminalEmbedding.compactParserInitialFinalBoundedDirectEmptySourceRawTerminal_embedding
    _ = compactParserInitialFinalBoundedDirectSourceRawTerminal :=
      compactParserInitialFinalBoundedDirectExplicitSourceRawTerminal_eq_split

theorem compactParserInitialFinalBoundedDef_emb_eq_directSourceRawBody :
    Rewriting.emb (ξ := Nat) compactParserInitialFinalBoundedDef.val =
      compactParserInitialFinalBoundedDirectSourceRawBody := by
  rw [compactParserInitialFinalBoundedDef_eq_directEmptySourceRawBody]
  change (Rew.emb : Rew ℒₒᵣ Empty 14 Nat 14) ▹
      compactParserInitialFinalBoundedDirectEmptySourceRawBody = _
  unfold compactParserInitialFinalBoundedDirectEmptySourceRawBody
    compactParserInitialFinalBoundedDirectSourceRawBody
  rw [rewriting_sourceBoundedWitnessFormula]
  rw [rewritingQpow_emb_eq_emb]
  rw [compactParserInitialFinalBoundedDirectEmptySourceRawTerminal_embedding]
  rfl

theorem compactParserInitialFinalBoundedDirectClosedFormula_eq_original
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat) :
    compactParserInitialFinalBoundedDirectClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound =
      (Rewriting.emb (ξ := Nat) compactParserInitialFinalBoundedDef.val) ⇜
        compactParserInitialFinalBoundedDirectSourceTerms tokenTable width
          tokenCount stateBoundary stateCount fuel inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount valueBound := by
  unfold compactParserInitialFinalBoundedDirectClosedFormula
  rw [compactParserInitialFinalBoundedDef_emb_eq_directSourceRawBody]

#print axioms
  compactParserInitialFinalBoundedDirectEmptySourceRawTerminal_embedding
#print axioms compactParserInitialFinalBoundedDef_emb_eq_directSourceRawBody
#print axioms
  compactParserInitialFinalBoundedDirectClosedFormula_eq_original

end FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectOriginalSourceAlignment
