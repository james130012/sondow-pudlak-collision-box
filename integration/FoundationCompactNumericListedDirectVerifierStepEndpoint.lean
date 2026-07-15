import integration.FoundationCompactNumericListedDirectVerifierStepCompleteness

/-!
# Audited endpoint for the complete bounded verifier-step formula

This module exposes the arithmetic-complexity and constructive-completeness
claims together and re-audits the separate forward exactness theorem.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStepEndpoint

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepExactness
open FoundationCompactNumericListedDirectVerifierStepCompleteness

theorem compactNumericVerifierStepFormula_closedEndpoint :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
        compactNumericVerifierStepGraphDef.val ∧
      ∀ currentState : CompactNumericVerifierState,
        CompactNumericVerifierCanonicalStepFormula
          currentState (compactNumericVerifierStep currentState) := by
  exact ⟨compactNumericVerifierStepGraphDef_sigmaZero,
    CompactNumericVerifierCanonicalStepFormula.exists_of_public_step⟩

#print axioms compactNumericVerifierStepFormula_closedEndpoint
#print axioms CompactNumericVerifierStepGraph.realizeExactStep
#print axioms compactNumericVerifierStepGraphDef_spec

end FoundationCompactNumericListedDirectVerifierStepEndpoint
