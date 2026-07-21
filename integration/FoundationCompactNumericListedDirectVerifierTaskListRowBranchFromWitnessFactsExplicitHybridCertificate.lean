import integration.FoundationCompactNumericListedDirectVerifierTaskListRowWitnessesExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierTaskListRowWitnessExtraction

/-!
# Row certificate from a checked witness vector

This bridge reads the proposition-level specification of a fourteen-entry row
vector and passes the named values and facts to the explicit witness compiler.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula

/-- Compile one checked row-witness vector to the freed universal body. -/
opaque taskListRowBranchFromWitnessFactsExplicitHybridCertificate
    (tokenTable width tokenCount taskBoundary valueBound rowIndex : Nat)
    (values : Fin 14 -> Nat)
    (hfacts : CompactNumericVerifierTaskRowWitnessFacts
      tokenTable width tokenCount taskBoundary valueBound rowIndex values) :
    HybridCertificate (taskListRowsBranchValuation rowIndex)
      (Rewriting.free
        (compactNumericVerifierTaskListRowsUniversalBody
          tokenTable width tokenCount taskBoundary valueBound)) := by
  unfold CompactNumericVerifierTaskRowWitnessFacts at hfacts
  rcases hfacts with
    ⟨hstartLe, hfinishLe, htagLe, hgammaFinishLe, hgammaCountLe,
      hgammaBoundaryLe, hfirstFinishLe, hfirstCountLe, hsecondFinishLe,
      hsecondCountLe, hwitnessFinishLe, hwitnessCountLe, hsuffixCountLe,
      hgammaBoundarySizeLe, hstartEntry, hfinishEntry, hcore⟩
  exact taskListRowWitnessesExplicitHybridCertificate
    tokenTable width tokenCount taskBoundary valueBound rowIndex
    (values 13) (values 12) (values 11) (values 10) (values 9)
    (values 8) (values 7) (values 6) (values 5) (values 4)
    (values 3) (values 2) (values 1) (values 0)
    hstartLe hfinishLe htagLe hgammaFinishLe hgammaCountLe
    hgammaBoundaryLe hfirstFinishLe hfirstCountLe hsecondFinishLe
    hsecondCountLe hwitnessFinishLe hwitnessCountLe hsuffixCountLe
    hgammaBoundarySizeLe hstartEntry hfinishEntry hcore

end FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate
