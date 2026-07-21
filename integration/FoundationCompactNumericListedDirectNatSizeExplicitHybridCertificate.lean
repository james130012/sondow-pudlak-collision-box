import integration.FoundationCompactNumericListedDirectArithmeticPrimitives
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompiler
import integration.FoundationCompactPABinaryNumeralAddition
import integration.FoundationCompactPABinaryLengthValuationContextCompiler

/-!
# Explicit hybrid certificate for the direct natural-size predicate

The direct `compactNatSizeDef` formula is definitionally the native binary
length formula.  Its certificate is produced by the checked binary-length
leaf and consumes the exact size equality supplied by the graph.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryLengthValuationContextCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives

private abbrev HybridCertificate :=
  CheckedHybridValuationBoundedFormulaCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

def compactNatSizeClosedFormula (size value : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNatSizeDef.val) ⇜
    ![shortBinaryNumeralTerm size, shortBinaryNumeralTerm value]

theorem compactNatSizeClosedFormula_eq_binaryLength
    (size value : Nat) :
    compactNatSizeClosedFormula size value =
      binaryLengthAtValuationFormula
        (shortBinaryNumeralTerm size) (shortBinaryNumeralTerm value) := by
  unfold compactNatSizeClosedFormula
  unfold compactNatSizeDef
  unfold binaryLengthAtValuationFormula
  rfl

noncomputable def compactNatSizeExplicitHybridCertificateOfEq
    (size value : Nat) (hsize : size = Nat.size value) :
    HybridCertificate zeroValuation
      (compactNatSizeClosedFormula size value) := by
  rw [compactNatSizeClosedFormula_eq_binaryLength]
  exact .binaryLength zeroValuation
    (shortBinaryNumeralTerm size) (shortBinaryNumeralTerm value) (by
      simpa [termValue_shortBinaryNumeralTerm] using hsize)

#print axioms compactNatSizeClosedFormula_eq_binaryLength
#print axioms compactNatSizeExplicitHybridCertificateOfEq

end FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
