import integration.FoundationCompactNumericListedDirectVerifierTaskListRowsSourceAlignment

/-!
# Revalued verifier task-core certificate for one task-list row

The verifier-task core is closed after its concrete coordinates are installed.
This cached lemma reuses its checked certificate at the live row valuation.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables

/-- Reuse the closed task-core certificate at any valuation. -/
opaque taskListRowCoreAtBranchExplicitHybridCertificate
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness)
    (hcore : CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    HybridCertificate valuation
      (compactNumericVerifierTaskCoreClosedFormula
        tokenTable width tokenCount coordinates sizeWitness) := by
  let atZero :=
    FoundationCompactNumericListedDirectVerifierTaskCoreExplicitHybridCertificate.compactNumericVerifierTaskCoreExplicitHybridCertificate
      hcore
  exact revalueClosedHybridCertificate atZero (by
    unfold compactNumericVerifierTaskCoreClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      exact shortBinaryNumeralTerm_freeVariables_eq_empty _) valuation

end FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate
