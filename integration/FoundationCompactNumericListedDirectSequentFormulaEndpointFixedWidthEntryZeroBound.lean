import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryZeroCertificate
import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryZeroClosed
import integration.FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

/-! # Empty-context endpoint entry bound at index zero -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryZeroBound

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryCertificateBound
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryZeroCertificate
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryZeroClosed

noncomputable def sequentFormulaEndpointFixedWidthEntryZeroBound
    (table width value : Nat)
    (hentry : CompactFixedWidthEntry table width 0 value) :
    FixedResourceEmptyContextProof
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
        (‘0’ : ValuationTerm) (shortBinaryNumeralTerm value))
      (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial table width value
        (‘0’ : ValuationTerm)) := by
  let boundedCertificate :=
    sequentFormulaEndpointFixedWidthEntryZeroBoundedCertificate table width
      value hentry
  exact fixedResourceEmptyContextProofOfClosedHybridCertificate
    boundedCertificate.certificate
    (sequentFormulaEndpointFixedWidthEntryZero_freeVariables_eq_empty table
      width value)
    (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial table width value
      (‘0’ : ValuationTerm))
    boundedCertificate.structuralPayload_le

#print axioms sequentFormulaEndpointFixedWidthEntryZeroBound

end FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryZeroBound
