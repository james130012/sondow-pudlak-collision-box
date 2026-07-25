import integration.FoundationCompactNumericListedDirectParserEmptyPublicBounds
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

/-!
# Fixed atomic leaves for the empty parser branch

The two zero-count leaves reduce to one closed constant certificate.  The
output-area leaf is charged by the already checked completed-area polynomial
at the same three closed numeral terms.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserEmptyAtomicFixedBounds

open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

def parserEmptyClosedEqZeroFixedPayloadPolynomial : Nat :=
  parserEmptyClosedEqZeroPayloadPolynomial 0

theorem closedEqZeroCertificate_structuralPayloadBound_le_fixed
    (value : Nat) (heq : value = 0) :
    hybridFormulaStructuralPayloadBound
        (closedEqZeroCertificate value heq) <=
      parserEmptyClosedEqZeroFixedPayloadPolynomial := by
  subst value
  exact closedEqZeroCertificate_structuralPayloadBound_le_public 0 rfl

theorem outputBoundaryAreaCertificate_structuralPayloadBound_le_fixed
    (tokenCount sourceCount outputBoundary outputBoundarySize numericBound
      bitBound : Nat)
    (hbound : outputBoundarySize <= (sourceCount + 1) * tokenCount)
    (hsize : outputBoundarySize = Nat.size outputBoundary)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (houtputBoundarySize : Nat.size outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (outputBoundaryAreaCertificate tokenCount sourceCount
          outputBoundarySize hbound) <=
      completedAreaFixedPayloadPolynomial bitBound := by
  have hpublic :=
    FoundationCompactNumericListedDirectParserEmptyPublicBounds.outputBoundaryAreaCertificate_structuralPayloadBound_le_public
      tokenCount sourceCount outputBoundarySize hbound
  have hfixed :=
    completedAreaStructuralPayloadPolynomial_le_fixed tokenCount sourceCount
      outputBoundary outputBoundarySize numericBound bitBound hsize
      htokenCount hsourceCount houtputBoundarySize hnumericSize
  have hsame :
      parserEmptyOutputBoundaryAreaPayloadPolynomial tokenCount sourceCount
          outputBoundarySize <=
        completedAreaFixedPayloadPolynomial bitBound := by
    change
      completedAreaStructuralPayloadPolynomial tokenCount sourceCount
          outputBoundarySize <=
        completedAreaFixedPayloadPolynomial bitBound
    exact hfixed
  exact hpublic.trans hsame

#print axioms closedEqZeroCertificate_structuralPayloadBound_le_fixed
#print axioms outputBoundaryAreaCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectParserEmptyAtomicFixedBounds
