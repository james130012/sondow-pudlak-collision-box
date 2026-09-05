import integration.FoundationCompactNumericListedDirectNatListConsRowsTailSourceEntryClosed
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailTargetEntryClosed
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailSourceRowClosed

/-! # The five-variable cons-tail source terminal has no free variables -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailSourceTerminalClosed

open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailSourceEntryClosed
open FoundationCompactNumericListedDirectNatListConsRowsTailTargetEntryClosed
open FoundationCompactNumericListedDirectNatListConsRowsTailSourceRowClosed

theorem compactAdditiveNatListConsRowsTailSourceTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (compactAdditiveNatListConsRowsTailTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary).freeVariables = ∅ := by
  unfold compactAdditiveNatListConsRowsTailTerminal
  simp only [LO.FirstOrder.Semiformula.freeVariables_and,
    Finset.union_eq_empty]
  exact
    ⟨consRowsTailSourceTerminalSourceLeft_freeVariables_eq_empty sourceBoundary
        tokenCount,
      consRowsTailSourceTerminalSourceRight_freeVariables_eq_empty
        sourceBoundary tokenCount,
      consRowsTailSourceTerminalTargetLeft_freeVariables_eq_empty targetBoundary
        tokenCount,
      consRowsTailSourceTerminalTargetRight_freeVariables_eq_empty
        targetBoundary tokenCount,
      consRowsTailSourceTerminalAtomicRow_freeVariables_eq_empty tokenTable
        width tokenCount⟩

#print axioms
  compactAdditiveNatListConsRowsTailSourceTerminal_freeVariables_eq_empty

end FoundationCompactNumericListedDirectNatListConsRowsTailSourceTerminalClosed
