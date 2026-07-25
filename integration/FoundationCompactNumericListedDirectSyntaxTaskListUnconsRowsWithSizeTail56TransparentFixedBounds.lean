import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56LeafFixedBounds
import integration.FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality

/-!
# Actual innermost uncons certificate below its transparent envelope
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option Elab.async false
set_option autoImplicit false

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56Certificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56LeafFixedBounds

theorem unconsRowsWithSizeTail56Certificate_structuralPayloadBound_le_transparentFixed
    (tokenCount tailBoundary tailCount tailBoundarySize numericBound bitBound :
      Nat)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount)
    (htokenCount : tokenCount <= numericBound)
    (htailCount : tailCount <= numericBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (unconsRowsWithSizeTail56Certificate tailBoundarySize tailBoundary
          tailCount tokenCount hsize harea) <=
      transparentHybridConjunctionPayloadEnvelope
        FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
        (compactNatSizeClosedFormula tailBoundarySize tailBoundary)
        (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
          (!!(shortBinaryNumeralTerm tailCount) + 1) *
            !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula)
        (compactNatSizeFixedPayloadPolynomial bitBound)
        (parserAreaFixedPayloadPolynomial bitBound) := by
  unfold unconsRowsWithSizeTail56Certificate
  rw [hybridFormulaStructuralPayloadBound_conjunction_eq_transparent]
  have hsizeResource :=
    unconsRowsNatSizeLeaf_structuralPayloadBound_le_fixed tailBoundarySize
      tailBoundary bitBound hsize htailBoundarySize
  have hareaResource :=
    unconsRowsAreaLeaf_structuralPayloadBound_le_fixed tokenCount tailBoundary
      tailCount tailBoundarySize numericBound bitBound hsize harea htokenCount
      htailCount htailBoundarySize hnumericSize
  exact transparentHybridConjunctionPayloadEnvelope_mono
    FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
    (compactNatSizeClosedFormula tailBoundarySize tailBoundary)
    (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
      (!!(shortBinaryNumeralTerm tailCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula)
    hsizeResource hareaResource
