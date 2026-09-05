import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryCertificateBound
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Closedness of one closed-index endpoint entry formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 60000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryClosed

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAValuationTermCompiler

theorem endpointFixedWidthEntryAtClosedTerms_freeVariables_eq_empty
    (table width value : Nat) (indexTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables = ∅) :
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
      indexTerm (shortBinaryNumeralTerm value)).freeVariables = ∅ := by
  unfold compactFixedWidthEntryAtValuationFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  cases coordinate using Fin.cases with
  | zero => exact shortBinaryNumeralTerm_freeVariables_eq_empty table
  | succ coordinate =>
      cases coordinate using Fin.cases with
      | zero => exact shortBinaryNumeralTerm_freeVariables_eq_empty width
      | succ coordinate =>
          cases coordinate using Fin.cases with
          | zero => exact hindexClosed
          | succ coordinate =>
              cases coordinate using Fin.cases with
              | zero =>
                  exact shortBinaryNumeralTerm_freeVariables_eq_empty value
              | succ coordinate => exact Fin.elim0 coordinate

#print axioms endpointFixedWidthEntryAtClosedTerms_freeVariables_eq_empty

end FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryClosed
