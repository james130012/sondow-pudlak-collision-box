import integration.FoundationCompactNumericListedDirectVerifierStateCoreGraphExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierHaltedRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierFinishRowsExplicitHybridCertificate

/-!
# Direct terminal-step certificates from semantic graphs

The halted and finish branch constructors below consume only the three
semantic graph components already present in the corresponding branch of the
original verifier step relation.  All checked certificates are built inside
the module at the exact 429-coordinate environment.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierTerminalStepBranchGraphExplicitHybridCertificate

open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierStateCoreGraphExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierHaltedFormula
open FoundationCompactNumericListedDirectVerifierHaltedRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierFinishFormula
open FoundationCompactNumericListedDirectVerifierFinishRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierStepGraphExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierTerminalStepBranchExplicitHybridCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

/-- Close the current-state core in the exact 429-coordinate step
environment. -/
noncomputable def
    compactNumericVerifierCurrentStateCoreExplicitHybridCertificateOfGraph
    (values : Fin 429 -> Nat)
    (hgraph : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierCurrentStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierCurrentStateValues values))) :
    HybridCertificate
      (compactNumericVerifierCurrentStateCoreAtEnvironmentFormula values) := by
  rw [compactNumericVerifierCurrentStateCoreAtEnvironmentFormula_eq_closed]
  exact compactNumericVerifierStateCoreExplicitHybridCertificateOfGraph
    (compactNumericVerifierCurrentStateValues values) hgraph

/-- Close the next-state core in the exact 429-coordinate step
environment. -/
noncomputable def
    compactNumericVerifierNextStateCoreExplicitHybridCertificateOfGraph
    (values : Fin 429 -> Nat)
    (hgraph : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierNextStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierNextStateValues values))) :
    HybridCertificate
      (compactNumericVerifierNextStateCoreAtEnvironmentFormula values) := by
  rw [compactNumericVerifierNextStateCoreAtEnvironmentFormula_eq_closed]
  exact compactNumericVerifierStateCoreExplicitHybridCertificateOfGraph
    (compactNumericVerifierNextStateValues values) hgraph

/-- Close the complete halted branch from the three original semantic graph
components. -/
noncomputable def
    compactNumericVerifierStepHaltedBranchExplicitHybridCertificateOfGraphs
    (values : Fin 429 -> Nat)
    (hcurrent : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierCurrentStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierCurrentStateValues values)))
    (hnext : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierNextStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierNextStateValues values)))
    (hrows : CompactNumericVerifierHaltedRows
      (values 0) (values 1) (values 2) (values 3) (values 4)
      (values 15) (values 24) (values 25)) :
    HybridCertificate
      (compactNumericVerifierStepHaltedBranchAtEnvironmentFormula values) :=
  compactNumericVerifierStepHaltedBranchExplicitHybridCertificate values
    (compactNumericVerifierCurrentStateCoreExplicitHybridCertificateOfGraph
      values hcurrent)
    (compactNumericVerifierNextStateCoreExplicitHybridCertificateOfGraph
      values hnext)
    (compactNumericVerifierHaltedRowsAtEnvironmentExplicitHybridCertificateOfGraph
      values hrows)

/-- Close the complete finish branch from the three original semantic graph
components. -/
noncomputable def
    compactNumericVerifierStepFinishBranchExplicitHybridCertificateOfGraphs
    (values : Fin 429 -> Nat)
    (hcurrent : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierCurrentStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierCurrentStateValues values)))
    (hnext : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues
        (compactNumericVerifierNextStateValues values))
      (compactNumericVerifierStateSizeWitnessAtValues
        (compactNumericVerifierNextStateValues values)))
    (hrows : CompactNumericVerifierFinishRows
      (values 0) (values 1) (values 2) (values 3) (values 12)
      (values 6) (values 8) (values 10) (values 13) (values 14)
      (values 23) (values 15) (values 24) (values 33) (values 27)
      (values 29) (values 31) (values 34) (values 36) (values 38)) :
    HybridCertificate
      (compactNumericVerifierStepFinishBranchAtEnvironmentFormula values) :=
  compactNumericVerifierStepFinishBranchExplicitHybridCertificate values
    (compactNumericVerifierCurrentStateCoreExplicitHybridCertificateOfGraph
      values hcurrent)
    (compactNumericVerifierNextStateCoreExplicitHybridCertificateOfGraph
      values hnext)
    (compactNumericVerifierFinishRowsAtEnvironmentExplicitHybridCertificateOfGraph
      values hrows)

#print axioms
  compactNumericVerifierCurrentStateCoreExplicitHybridCertificateOfGraph
#print axioms
  compactNumericVerifierNextStateCoreExplicitHybridCertificateOfGraph
#print axioms
  compactNumericVerifierStepHaltedBranchExplicitHybridCertificateOfGraphs
#print axioms
  compactNumericVerifierStepFinishBranchExplicitHybridCertificateOfGraphs

end FoundationCompactNumericListedDirectVerifierTerminalStepBranchGraphExplicitHybridCertificate
