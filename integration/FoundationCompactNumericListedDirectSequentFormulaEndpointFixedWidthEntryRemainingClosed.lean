import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryRemainingCertificates
import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryClosed

/-! # Closedness at the remaining three endpoint entry indices -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 90000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryRemainingClosed

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryClosed
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryRemainingCertificates

theorem sequentFormulaEndpointFixedWidthEntryOne_freeVariables_eq_empty
    (table width value : Nat) :
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
      (‘1’ : ValuationTerm) (shortBinaryNumeralTerm value)).freeVariables =
        ∅ :=
  endpointFixedWidthEntryAtClosedTerms_freeVariables_eq_empty table width value
    (‘1’ : ValuationTerm) endpointOneTerm_freeVariables_eq_empty

theorem sequentFormulaEndpointFixedWidthEntryNumeral_freeVariables_eq_empty
    (table width index value : Nat) :
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm index)
      (shortBinaryNumeralTerm value)).freeVariables = ∅ :=
  endpointFixedWidthEntryAtClosedTerms_freeVariables_eq_empty table width value
    (shortBinaryNumeralTerm index)
    (shortBinaryNumeralTerm_freeVariables_eq_empty index)

theorem sequentFormulaEndpointFixedWidthEntrySuccessor_freeVariables_eq_empty
    (table width index value : Nat) :
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
      (endpointSuccessorIndexTerm index)
      (shortBinaryNumeralTerm value)).freeVariables = ∅ :=
  endpointFixedWidthEntryAtClosedTerms_freeVariables_eq_empty table width value
    (endpointSuccessorIndexTerm index)
    (endpointSuccessorIndexTerm_freeVariables_eq_empty index)

#print axioms sequentFormulaEndpointFixedWidthEntryOne_freeVariables_eq_empty
#print axioms
  sequentFormulaEndpointFixedWidthEntryNumeral_freeVariables_eq_empty
#print axioms
  sequentFormulaEndpointFixedWidthEntrySuccessor_freeVariables_eq_empty

end FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryRemainingClosed
