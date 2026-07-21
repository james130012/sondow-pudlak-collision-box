import integration.FoundationCompactNumericListedDirectVerifierTaskListRowBranchFromWitnessFactsExplicitHybridCertificate

/-!
# Explicit hybrid certificate from one semantic verifier task-list row

The original bounded-row proposition supplies one checked witness vector; the
cached row compiler turns that vector into the exact freed universal body.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula

/-- Direct certificate for one row from the original semantic bounded-row
proposition, with no intermediate project-level certificate assumption. -/
opaque compactNumericVerifierTaskListRowBranchExplicitHybridCertificate
    (tokenTable width tokenCount taskBoundary valueBound rowIndex : Nat)
    (hrow : CompactNumericVerifierTaskBoundedRow
      tokenTable width tokenCount taskBoundary valueBound rowIndex) :
    HybridCertificate (taskListRowsBranchValuation rowIndex)
      (Rewriting.free
        (compactNumericVerifierTaskListRowsUniversalBody
          tokenTable width tokenCount taskBoundary valueBound)) := by
  let values := taskListRowWitnessValuesOfBoundedRow
    tokenTable width tokenCount taskBoundary valueBound rowIndex hrow
  exact taskListRowBranchFromWitnessFactsExplicitHybridCertificate
    tokenTable width tokenCount taskBoundary valueBound rowIndex values
      (taskListRowWitnessValuesOfBoundedRow_spec
        tokenTable width tokenCount taskBoundary valueBound rowIndex hrow)

end FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate
