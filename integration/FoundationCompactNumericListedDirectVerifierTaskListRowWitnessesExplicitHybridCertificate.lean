import integration.FoundationCompactNumericListedDirectVerifierTaskListRowsFreeAlignment
import integration.FoundationCompactNumericListedDirectVerifierTaskListRowTerminalExplicitHybridCertificate

/-!
# Bounded-witness certificate for one verifier task-list row

The fourteen concrete row values are checked against the common bound and
installed above the already checked terminal row certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

/-- Install all fourteen bounded row witnesses and recover the freed universal
body exactly. -/
opaque taskListRowWitnessesExplicitHybridCertificate
    (tokenTable width tokenCount taskBoundary valueBound rowIndex
      start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize : Nat)
    (hstartLe : start ≤ valueBound)
    (hfinishLe : finish ≤ valueBound)
    (htagLe : tag ≤ valueBound)
    (hgammaFinishLe : gammaFinish ≤ valueBound)
    (hgammaCountLe : gammaCount ≤ valueBound)
    (hgammaBoundaryLe : gammaBoundary ≤ valueBound)
    (hfirstFinishLe : firstFinish ≤ valueBound)
    (hfirstCountLe : firstCount ≤ valueBound)
    (hsecondFinishLe : secondFinish ≤ valueBound)
    (hsecondCountLe : secondCount ≤ valueBound)
    (hwitnessFinishLe : witnessFinish ≤ valueBound)
    (hwitnessCountLe : witnessCount ≤ valueBound)
    (hsuffixCountLe : suffixCount ≤ valueBound)
    (hgammaBoundarySizeLe : gammaBoundarySize ≤ valueBound)
    (hstartEntry : CompactFixedWidthEntry
      taskBoundary tokenCount rowIndex start)
    (hfinishEntry : CompactFixedWidthEntry
      taskBoundary tokenCount (rowIndex + 1) finish)
    (hcore : CompactNumericVerifierTaskCoreGraph tokenTable width tokenCount
      (compactNumericVerifierTaskRowCoordinatesOf
        start finish tag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount
        witnessFinish witnessCount suffixCount)
      { gammaBoundarySize := gammaBoundarySize }) :
    HybridCertificate (taskListRowsBranchValuation rowIndex)
      (Rewriting.free
        (compactNumericVerifierTaskListRowsUniversalBody
          tokenTable width tokenCount taskBoundary valueBound)) := by
  let values := taskListRowWitnessValues
    start finish tag gammaFinish gammaCount gammaBoundary
    firstFinish firstCount secondFinish secondCount
    witnessFinish witnessCount suffixCount gammaBoundarySize
  let terminal := taskListRowTerminalExplicitHybridCertificate
    tokenTable width tokenCount taskBoundary rowIndex
    start finish tag gammaFinish gammaCount gammaBoundary
    firstFinish firstCount secondFinish secondCount
    witnessFinish witnessCount suffixCount gammaBoundarySize
    hstartEntry hfinishEntry hcore
  let installed : HybridCertificate (taskListRowsBranchValuation rowIndex)
      (explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm valueBound) 14
        (compactNumericVerifierTaskListRowsBranchTerminal
          tokenTable width tokenCount taskBoundary (&0 : ValuationTerm))) :=
    buildExplicitBoundedWitnessHybridCertificate
      valueBound
      (compactNumericVerifierTaskListRowsBranchTerminal
        tokenTable width tokenCount taskBoundary (&0 : ValuationTerm))
      values (by
        intro coordinate
        fin_cases coordinate
        · exact hgammaBoundarySizeLe
        · exact hsuffixCountLe
        · exact hwitnessCountLe
        · exact hwitnessFinishLe
        · exact hsecondCountLe
        · exact hsecondFinishLe
        · exact hfirstCountLe
        · exact hfirstFinishLe
        · exact hgammaBoundaryLe
        · exact hgammaCountLe
        · exact hgammaFinishLe
        · exact htagLe
        · exact hfinishLe
        · exact hstartLe) terminal
  exact .cast
    (compactNumericVerifierTaskListRowsUniversalBody_free_alignment
      tokenTable width tokenCount taskBoundary valueBound).symm installed

end FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate
