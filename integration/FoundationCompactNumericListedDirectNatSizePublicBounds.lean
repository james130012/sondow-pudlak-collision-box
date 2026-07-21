import integration.FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
import integration.FoundationCompactPABinaryLengthValuationContextCompilerPublicBounds
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Public structural resource for direct natural-size certificates

The direct natural-size terminal is the checked binary-length leaf specialized
to two closed short numerals.  Its resource no longer depends on an externally
supplied proof payload.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 150000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatSizePublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryLengthValuationContextCompilerBounds
open FoundationCompactPABinaryLengthValuationContextCompilerPublicBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate

private def zeroValuation : Nat -> Nat := fun _ => 0

def compactNatSizeStructuralPayloadPolynomial (size value : Nat) : Nat :=
  compileBinaryLengthAtValuationPayloadPolynomial zeroValuation
    (shortBinaryNumeralTerm size) (shortBinaryNumeralTerm value)

theorem compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
    (size value : Nat) (hsize : size = Nat.size value) :
    hybridFormulaStructuralPayloadBound
        (compactNatSizeExplicitHybridCertificateOfEq size value hsize) ≤
      compactNatSizeStructuralPayloadPolynomial size value := by
  have hsizeTerm : (shortBinaryNumeralTerm size).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hvalueTerm : (shortBinaryNumeralTerm value).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic :=
    compileBinaryLengthAtValuationPayloadResource_le_publicPolynomial
      zeroValuation (shortBinaryNumeralTerm size)
      (shortBinaryNumeralTerm value) hsizeTerm hvalueTerm
  change compileBinaryLengthAtValuationPayloadResource zeroValuation
      (shortBinaryNumeralTerm size) (shortBinaryNumeralTerm value) ≤ _
  unfold compactNatSizeStructuralPayloadPolynomial
  exact hpublic

#print axioms
  compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectNatSizePublicBounds
