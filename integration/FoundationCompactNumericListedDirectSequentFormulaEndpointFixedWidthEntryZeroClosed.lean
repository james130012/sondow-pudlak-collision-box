import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryZeroCertificate
import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryClosed

/-! # Closedness of the endpoint entry formula at index zero -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 60000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryZeroClosed

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryClosed
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryZeroCertificate

theorem sequentFormulaEndpointFixedWidthEntryZero_freeVariables_eq_empty
    (table width value : Nat) :
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
      (‘0’ : ValuationTerm) (shortBinaryNumeralTerm value)).freeVariables =
        ∅ :=
  endpointFixedWidthEntryAtClosedTerms_freeVariables_eq_empty table width value
    (‘0’ : ValuationTerm) endpointZeroTerm_freeVariables_eq_empty

#print axioms
  sequentFormulaEndpointFixedWidthEntryZero_freeVariables_eq_empty

end FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryZeroClosed
