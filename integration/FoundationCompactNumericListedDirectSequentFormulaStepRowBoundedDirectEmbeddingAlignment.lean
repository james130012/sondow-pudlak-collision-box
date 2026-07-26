import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectEmptyAlignment

/-! # Variable embedding for the bounded sequent-step row -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax

open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula

theorem compactSequentFormulaStepRowBoundedDef_emb_eq_directSourceRawBody :
    Rewriting.emb (ξ := Nat) compactSequentFormulaStepRowBoundedDef.val =
      compactSequentFormulaStepRowBoundedDirectSourceRawBody := by
  rw [compactSequentFormulaStepRowBoundedDef_eq_emptyRawBody]
  change (Rew.emb : Rew ℒₒᵣ Empty 9 Nat 9) ▹
      compactSequentFormulaStepRowBoundedDirectEmptyRawBody = _
  unfold compactSequentFormulaStepRowBoundedDirectEmptyRawBody
    compactSequentFormulaStepRowBoundedDirectSourceRawBody
  rw [rewriting_sourceBoundedWitnessFormula]
  rw [rewritingQpow_emb_eq_emb]
  rw [
    compactSequentFormulaStepRowBoundedDirectEmptyRawTerminal_embedding]
  rfl

#print axioms compactSequentFormulaStepRowBoundedDef_emb_eq_directSourceRawBody

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
