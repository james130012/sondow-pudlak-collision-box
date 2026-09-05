import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryCertificateBound

/-! # Cached bounded endpoint entry certificate at index zero -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryZeroCertificate

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryCertificateBound

theorem endpointZeroTerm_value :
    termValue endpointEntryZeroValuation (‘0’ : ValuationTerm) = 0 := by
  exact termValue_zero endpointEntryZeroValuation ![]

theorem endpointZeroTerm_freeVariables_eq_empty :
    (‘0’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_zero,
    LO.FirstOrder.Semiterm.Operator.Zero.term_eq]

opaque sequentFormulaEndpointFixedWidthEntryZeroBoundedCertificate
    (table width value : Nat)
    (hentry : CompactFixedWidthEntry table width 0 value) :
    SequentFormulaEndpointFixedWidthEntryBoundedCertificate
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
        (‘0’ : ValuationTerm) (shortBinaryNumeralTerm value))
      (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial table width value
        (‘0’ : ValuationTerm)) := by
  exact buildSequentFormulaEndpointFixedWidthEntryBoundedCertificate table
    width 0 value (‘0’ : ValuationTerm) endpointZeroTerm_value
    endpointZeroTerm_freeVariables_eq_empty hentry

#print axioms sequentFormulaEndpointFixedWidthEntryZeroBoundedCertificate

end FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryZeroCertificate
