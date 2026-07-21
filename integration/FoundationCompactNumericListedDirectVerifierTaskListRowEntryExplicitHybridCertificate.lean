import integration.FoundationCompactNumericListedDirectVerifierTaskListRowsSourceAlignment

/-!
# Explicit hybrid certificates for verifier task-row endpoints

This cached layer discharges the two fixed-width table-entry certificates used
by each verifier task row.  Both certificates are built at the live row-index
valuation and retain the original fixed-width entry hypotheses verbatim.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler

/-- The fixed-width entry at the live task-row index. -/
opaque taskListRowStartEntryExplicitHybridCertificate
    (taskBoundary tokenCount rowIndex start : Nat)
    (hentry : CompactFixedWidthEntry
      taskBoundary tokenCount rowIndex start) :
    HybridCertificate (taskListRowsBranchValuation rowIndex)
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm taskBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (&0 : ValuationTerm)
        (shortBinaryNumeralTerm start)) := by
  have hindex :
      termValue (taskListRowsBranchValuation rowIndex)
        (&0 : ValuationTerm) = rowIndex := by
    rfl
  exact compactFixedWidthEntryAtValuationExplicitHybridCertificate
    (taskListRowsBranchValuation rowIndex)
    (shortBinaryNumeralTerm taskBoundary)
    (shortBinaryNumeralTerm tokenCount)
    (&0 : ValuationTerm)
    (shortBinaryNumeralTerm start) (by
      simpa only [termValue_shortBinaryNumeralTerm, hindex] using hentry)

/-- The fixed-width entry immediately after the live task-row index. -/
opaque taskListRowFinishEntryExplicitHybridCertificate
    (taskBoundary tokenCount rowIndex finish : Nat)
    (hentry : CompactFixedWidthEntry
      taskBoundary tokenCount (rowIndex + 1) finish) :
    HybridCertificate (taskListRowsBranchValuation rowIndex)
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm taskBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (‘!!(&0 : ValuationTerm) + 1’ : ValuationTerm)
        (shortBinaryNumeralTerm finish)) := by
  have hindex :
      termValue (taskListRowsBranchValuation rowIndex)
        (‘!!(&0 : ValuationTerm) + 1’ : ValuationTerm) = rowIndex + 1 := by
    change rowIndex + 1 = rowIndex + 1
    rfl
  exact compactFixedWidthEntryAtValuationExplicitHybridCertificate
    (taskListRowsBranchValuation rowIndex)
    (shortBinaryNumeralTerm taskBoundary)
    (shortBinaryNumeralTerm tokenCount)
    (‘!!(&0 : ValuationTerm) + 1’ : ValuationTerm)
    (shortBinaryNumeralTerm finish) (by
      simpa only [termValue_shortBinaryNumeralTerm, hindex] using hentry)

end FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate
