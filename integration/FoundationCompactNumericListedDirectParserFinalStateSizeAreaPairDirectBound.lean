import integration.FoundationCompactNumericListedDirectParserFinalStateSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56FixedBounds
import integration.FoundationCompactPADirectConnectiveTransparentBounds

/-! # Fixed direct bound for the parser final size-and-area pair -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserFinalStateSizeAreaPairDirectBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserFinalStateSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56Certificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56FixedBounds

def parserFinalSizeAreaPairPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound bitBound)
    (compactNatSizeFixedPayloadPolynomial bitBound)
    (parserAreaFixedPayloadPolynomial bitBound)

noncomputable def parserFinalSizeAreaPairDirectBound
    (tokenCount outputBoundary sourceCount outputBoundarySize numericBound
      bitBound : Nat)
    (hsize : outputBoundarySize = Nat.size outputBoundary)
    (harea : outputBoundarySize <= (sourceCount + 1) * tokenCount)
    (htokenCountValue : tokenCount <= numericBound)
    (hsourceCountValue : sourceCount <= numericBound)
    (houtputBoundarySize : Nat.size outputBoundary <= bitBound)
    (hnumericBoundSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound parserFinalZeroValuation
      (parserFinalSizeFormula outputBoundarySize outputBoundary ⋏
        parserFinalAreaFormula outputBoundarySize sourceCount tokenCount)
      (parserFinalSizeAreaPairPayloadPolynomial tokenCount numericBound
        bitBound) := by
  let certificate :=
    unconsRowsWithSizeTail56Certificate outputBoundarySize outputBoundary
      sourceCount tokenCount hsize harea
  refine
    { proof := ?_
      payloadLength_le := ?_ }
  · change FoundationCompactCertifiedContextProof.CertifiedPAContextProof
      (FoundationCompactPAValuationTermCompiler.valuationContext
        (compactNatSizeClosedFormula outputBoundarySize outputBoundary ⋏
          (“!!(shortBinaryNumeralTerm outputBoundarySize) ≤
            (!!(shortBinaryNumeralTerm sourceCount) + 1) *
              !!(shortBinaryNumeralTerm tokenCount)” :
            ValuationFormula)).freeVariables (fun _ => 0))
      (compactNatSizeClosedFormula outputBoundarySize outputBoundary ⋏
        (“!!(shortBinaryNumeralTerm outputBoundarySize) ≤
          (!!(shortBinaryNumeralTerm sourceCount) + 1) *
            !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula))
    exact certificate.compile
  · exact
      (compile_payloadLength_le_structuralPayloadBound certificate).trans
      (by
        simpa only [parserFinalSizeAreaPairPayloadPolynomial] using
          (unconsRowsWithSizeTail56Certificate_structuralPayloadBound_le_fixed
            tokenCount outputBoundary sourceCount outputBoundarySize
            numericBound bitBound hsize harea htokenCountValue
            hsourceCountValue houtputBoundarySize hnumericBoundSize))

#print axioms parserFinalSizeAreaPairDirectBound

end FoundationCompactNumericListedDirectParserFinalStateSizeAreaPairDirectBound
