import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds

/-! # Fixed structural bound for one closed endpoint entry certificate -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryCertificateBound

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives

def endpointEntryZeroValuation : Nat -> Nat := fun _ => 0

def sequentFormulaEndpointFixedWidthEntryPayloadPolynomial
    (table width value : Nat) (indexTerm : ValuationTerm) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
    endpointEntryZeroValuation (shortBinaryNumeralTerm table)
    (shortBinaryNumeralTerm width) indexTerm (shortBinaryNumeralTerm value)

structure SequentFormulaEndpointFixedWidthEntryBoundedCertificate
    (formula : ValuationFormula) (resource : Nat) where
  certificate : CheckedHybridValuationBoundedFormulaCertificate
    endpointEntryZeroValuation formula
  structuralPayload_le :
    hybridFormulaStructuralPayloadBound certificate <= resource

opaque buildSequentFormulaEndpointFixedWidthEntryBoundedCertificate
    (table width index value : Nat) (indexTerm : ValuationTerm)
    (hindexValue : termValue endpointEntryZeroValuation indexTerm = index)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hentry : CompactFixedWidthEntry table width index value) :
    SequentFormulaEndpointFixedWidthEntryBoundedCertificate
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
        indexTerm (shortBinaryNumeralTerm value))
      (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial table width value
        indexTerm) := by
  let certificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      endpointEntryZeroValuation (shortBinaryNumeralTerm table)
      (shortBinaryNumeralTerm width) indexTerm
      (shortBinaryNumeralTerm value) (by
        simpa only [termValue_shortBinaryNumeralTerm, hindexValue] using hentry)
  refine { certificate := certificate, structuralPayload_le := ?_ }
  dsimp only [certificate,
    sequentFormulaEndpointFixedWidthEntryPayloadPolynomial]
  exact
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      endpointEntryZeroValuation (shortBinaryNumeralTerm table)
      (shortBinaryNumeralTerm width) indexTerm
      (shortBinaryNumeralTerm value)
      (shortBinaryNumeralTerm_freeVariables_eq_empty table)
      (shortBinaryNumeralTerm_freeVariables_eq_empty width)
      (by rw [hindexClosed]; simp)
      (shortBinaryNumeralTerm_freeVariables_eq_empty value)
      (by simpa only [termValue_shortBinaryNumeralTerm, hindexValue] using
        hentry)

noncomputable def sequentFormulaEndpointFixedWidthEntryCertificate
    (table width index value : Nat) (indexTerm : ValuationTerm)
    (hindexValue : termValue endpointEntryZeroValuation indexTerm = index)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hentry : CompactFixedWidthEntry table width index value) :=
  (buildSequentFormulaEndpointFixedWidthEntryBoundedCertificate table width
    index value indexTerm hindexValue hindexClosed hentry).certificate

theorem
    sequentFormulaEndpointFixedWidthEntryCertificate_structuralPayload_le
    (table width index value : Nat) (indexTerm : ValuationTerm)
    (hindexValue : termValue endpointEntryZeroValuation indexTerm = index)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hentry : CompactFixedWidthEntry table width index value) :
    hybridFormulaStructuralPayloadBound
        (sequentFormulaEndpointFixedWidthEntryCertificate table width index
          value indexTerm hindexValue hindexClosed hentry) <=
      sequentFormulaEndpointFixedWidthEntryPayloadPolynomial table width value
        indexTerm := by
  exact
    (buildSequentFormulaEndpointFixedWidthEntryBoundedCertificate table width
      index value indexTerm hindexValue hindexClosed hentry).structuralPayload_le

theorem sequentFormulaEndpointFixedWidthEntryCertificate_payloadLength_le
    (table width index value : Nat) (indexTerm : ValuationTerm)
    (hindexValue : termValue endpointEntryZeroValuation indexTerm = index)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hentry : CompactFixedWidthEntry table width index value) :
    (sequentFormulaEndpointFixedWidthEntryCertificate table width index value
      indexTerm hindexValue hindexClosed hentry).compile.payloadLength <=
      sequentFormulaEndpointFixedWidthEntryPayloadPolynomial table width value
        indexTerm := by
  exact
    (compile_payloadLength_le_structuralPayloadBound
      (sequentFormulaEndpointFixedWidthEntryCertificate table width index
        value indexTerm hindexValue hindexClosed hentry)).trans
      (sequentFormulaEndpointFixedWidthEntryCertificate_structuralPayload_le
        table width index value indexTerm hindexValue hindexClosed hentry)

#print axioms
  sequentFormulaEndpointFixedWidthEntryCertificate_structuralPayload_le
#print axioms
  sequentFormulaEndpointFixedWidthEntryCertificate_payloadLength_le

end FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryCertificateBound
