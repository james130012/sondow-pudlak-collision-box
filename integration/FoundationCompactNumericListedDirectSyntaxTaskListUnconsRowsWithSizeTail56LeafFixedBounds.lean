import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56Certificate
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-!
# Fixed resources for the two innermost uncons leaves
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56LeafFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsAtomicFullyFixedBounds

theorem unconsRowsNatSizeLeaf_structuralPayloadBound_le_fixed
    (tailBoundarySize tailBoundary bitBound : Nat)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactNatSizeExplicitHybridCertificateOfEq tailBoundarySize
          tailBoundary hsize) <=
      compactNatSizeFixedPayloadPolynomial bitBound :=
  (compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
    tailBoundarySize tailBoundary hsize).trans
  (compactNatSizeStructuralPayloadPolynomial_le_unconsFullyFixed
    tailBoundarySize tailBoundary bitBound hsize htailBoundarySize)

theorem unconsRowsAreaLeaf_structuralPayloadBound_le_fixed
    (tokenCount tailBoundary tailCount tailBoundarySize numericBound bitBound :
      Nat)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount)
    (htokenCount : tokenCount <= numericBound)
    (htailCount : tailCount <= numericBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (closedTailAreaLeCertificate tailBoundarySize tailCount tokenCount
          harea) <=
      parserAreaFixedPayloadPolynomial bitBound :=
  (closedTailAreaLeCertificate_structuralPayloadBound_le_public
    tailBoundarySize tailCount tokenCount harea).trans
  (compactAdditiveSyntaxTaskListUnconsRowsTailAreaPayloadPolynomial_le_fullyFixed
    tailBoundarySize tailCount tokenCount tailBoundary numericBound bitBound
    hsize htailCount htokenCount htailBoundarySize hnumericSize)

theorem unconsRowsNatSizeFormula_code_length_le_fixed
    (tailBoundarySize tailBoundary bitBound : Nat)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound) :
    (binaryFormulaCode
      (compactNatSizeClosedFormula tailBoundarySize tailBoundary)).length <=
      compactNatSizeFixedPayloadPolynomial bitBound :=
  (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
    (compactNatSizeExplicitHybridCertificateOfEq tailBoundarySize tailBoundary
      hsize)).trans
  (unconsRowsNatSizeLeaf_structuralPayloadBound_le_fixed tailBoundarySize
    tailBoundary bitBound hsize htailBoundarySize)

theorem unconsRowsAreaFormula_code_length_le_fixed
    (tokenCount tailBoundary tailCount tailBoundarySize numericBound bitBound :
      Nat)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount)
    (htokenCount : tokenCount <= numericBound)
    (htailCount : tailCount <= numericBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
        (!!(shortBinaryNumeralTerm tailCount) + 1) *
          !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula)).length <=
      parserAreaFixedPayloadPolynomial bitBound :=
  (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
    (closedTailAreaLeCertificate tailBoundarySize tailCount tokenCount
      harea)).trans
  (unconsRowsAreaLeaf_structuralPayloadBound_le_fixed tokenCount tailBoundary
    tailCount tailBoundarySize numericBound bitBound hsize harea htokenCount
    htailCount htailBoundarySize hnumericSize)

#print axioms unconsRowsNatSizeLeaf_structuralPayloadBound_le_fixed
#print axioms unconsRowsAreaLeaf_structuralPayloadBound_le_fixed
#print axioms unconsRowsNatSizeFormula_code_length_le_fixed
#print axioms unconsRowsAreaFormula_code_length_le_fixed

end FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56LeafFixedBounds
