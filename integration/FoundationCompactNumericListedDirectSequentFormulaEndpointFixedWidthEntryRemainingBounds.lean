import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryRemainingCertificates
import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryRemainingClosed
import integration.FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

/-! # Fixed-resource empty-context bounds for the remaining endpoint entries -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryRemainingBounds

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryCertificateBound
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryRemainingCertificates
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryRemainingClosed

noncomputable def sequentFormulaEndpointFixedWidthEntryOneBound
    (table width value : Nat)
    (hentry : CompactFixedWidthEntry table width 1 value) :
    FixedResourceEmptyContextProof
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
        (‘1’ : ValuationTerm) (shortBinaryNumeralTerm value))
      (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial table width value
        (‘1’ : ValuationTerm)) := by
  let boundedCertificate :=
    sequentFormulaEndpointFixedWidthEntryOneBoundedCertificate table width
      value hentry
  exact fixedResourceEmptyContextProofOfClosedHybridCertificate
    boundedCertificate.certificate
    (sequentFormulaEndpointFixedWidthEntryOne_freeVariables_eq_empty table
      width value)
    (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial table width value
      (‘1’ : ValuationTerm))
    boundedCertificate.structuralPayload_le

noncomputable def sequentFormulaEndpointFixedWidthEntryNumeralBound
    (table width index value : Nat)
    (hentry : CompactFixedWidthEntry table width index value) :
    FixedResourceEmptyContextProof
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm index) (shortBinaryNumeralTerm value))
      (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial table width value
        (shortBinaryNumeralTerm index)) := by
  let boundedCertificate :=
    sequentFormulaEndpointFixedWidthEntryNumeralBoundedCertificate table width
      index value hentry
  exact fixedResourceEmptyContextProofOfClosedHybridCertificate
    boundedCertificate.certificate
    (sequentFormulaEndpointFixedWidthEntryNumeral_freeVariables_eq_empty table
      width index value)
    (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial table width value
      (shortBinaryNumeralTerm index))
    boundedCertificate.structuralPayload_le

noncomputable def sequentFormulaEndpointFixedWidthEntrySuccessorBound
    (table width index value : Nat)
    (hentry : CompactFixedWidthEntry table width (index + 1) value) :
    FixedResourceEmptyContextProof
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
        (endpointSuccessorIndexTerm index) (shortBinaryNumeralTerm value))
      (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial table width value
        (endpointSuccessorIndexTerm index)) := by
  let boundedCertificate :=
    sequentFormulaEndpointFixedWidthEntrySuccessorBoundedCertificate table
      width index value hentry
  exact fixedResourceEmptyContextProofOfClosedHybridCertificate
    boundedCertificate.certificate
    (sequentFormulaEndpointFixedWidthEntrySuccessor_freeVariables_eq_empty
      table width index value)
    (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial table width value
      (endpointSuccessorIndexTerm index))
    boundedCertificate.structuralPayload_le

#print axioms sequentFormulaEndpointFixedWidthEntryOneBound
#print axioms sequentFormulaEndpointFixedWidthEntryNumeralBound
#print axioms sequentFormulaEndpointFixedWidthEntrySuccessorBound

end FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryRemainingBounds
