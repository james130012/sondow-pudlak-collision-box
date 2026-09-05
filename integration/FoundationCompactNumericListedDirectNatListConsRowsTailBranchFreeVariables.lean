import integration.FoundationCompactNumericListedDirectNatListConsRowsTailBranchSourceFreeVariables
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailBranchTargetFreeVariables
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailBranchRowFreeVariables

/-! # Free-variable support of one natural-list cons tail branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailBranchFreeVariables

open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchSourceFreeVariables
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchTargetFreeVariables
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchRowFreeVariables

theorem
    compactAdditiveNatListConsRowsTailBranchTerminal_freeVariables_subset_singleton
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (compactAdditiveNatListConsRowsTailBranchTerminal tokenTable width
      tokenCount sourceBoundary targetBoundary).freeVariables ⊆ {0} := by
  unfold compactAdditiveNatListConsRowsTailBranchTerminal
  simp only [LO.FirstOrder.Semiformula.freeVariables_and]
  exact Finset.union_subset
    (consRowsTailBranchSourceLeft_freeVariables_subset_singleton sourceBoundary
      tokenCount)
    (Finset.union_subset
      (consRowsTailBranchSourceRight_freeVariables_subset_singleton
        sourceBoundary tokenCount)
      (Finset.union_subset
        (consRowsTailBranchTargetLeft_freeVariables_subset_singleton
          targetBoundary tokenCount)
        (Finset.union_subset
          (consRowsTailBranchTargetRight_freeVariables_subset_singleton
            targetBoundary tokenCount)
          (consRowsTailBranchAtomicRow_freeVariables_subset_singleton tokenTable
            width tokenCount))))

#print axioms
  compactAdditiveNatListConsRowsTailBranchTerminal_freeVariables_subset_singleton

end FoundationCompactNumericListedDirectNatListConsRowsTailBranchFreeVariables
