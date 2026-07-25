import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456Certificate
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaConsCertificateFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserGraphFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56FixedBounds
import integration.FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-! # Transparent fixed resources for the exact parser Tail456 certificate -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456TransparentFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserGraphFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56Certificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56FixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456Certificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaConsCertificateFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate

private abbrev parserFixedNumeralTerm (value : Nat) : ValuationTerm :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
    value

private theorem termValue_parserFixedNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (parserFixedNumeralTerm value) = value := by
  simp [parserFixedNumeralTerm,
    FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm,
    termValue]

def parserSyntaxFormulaUnconsTail456TransparentFixedEnvelope
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize binderArity numericBound bitBound : Nat) :
    Nat :=
  transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
    (parserSyntaxFormulaUnconsTail456ConsFormula tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount binderArity)
    (parserSyntaxFormulaUnconsTail56Formula tailBoundarySize tailBoundary
      tailCount tokenCount)
    (taskConsParserFullyFixedPayloadEnvelope numericBound bitBound)
    (hybridConjunctionGeneralPayloadEnvelope
      (FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions.unconsRowsWithSizeFormulaCodePolynomial
        tokenCount numericBound bitBound)
      (compactNatSizeFixedPayloadPolynomial bitBound)
      (parserAreaFixedPayloadPolynomial bitBound))

theorem
    parserSyntaxFormulaUnconsTail456Certificate_structuralPayloadBound_le_transparentFixed
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize binderArity numericBound bitBound : Nat)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount 1 binderArity 0)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htailCount : tailCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (parserSyntaxFormulaUnconsTail456Certificate tokenTable width tokenCount
          tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
          binderArity hcons hsize harea) <=
      parserSyntaxFormulaUnconsTail456TransparentFixedEnvelope tokenTable width
        tokenCount tailBoundary tailCount sourceBoundary sourceCount
        tailBoundarySize binderArity numericBound bitBound := by
  let consCertificate :=
    parserSyntaxFormulaConsCertificate tokenTable width tokenCount tailBoundary
      tailCount sourceBoundary sourceCount binderArity hcons
  let tailCertificate :=
    unconsRowsWithSizeTail56Certificate tailBoundarySize tailBoundary
      tailCount tokenCount hsize harea
  have hconsResource : hybridFormulaStructuralPayloadBound consCertificate <=
      taskConsParserFullyFixedPayloadEnvelope numericBound bitBound := by
    exact
      parserSyntaxFormulaConsCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount binderArity numericBound bitBound hcons hwidth htokenCount
      hsourceCount htokenTableSize hsourceBoundarySize htailBoundarySize
      hbinderSize hnumericSize
  have htailResource : hybridFormulaStructuralPayloadBound tailCertificate <=
      hybridConjunctionGeneralPayloadEnvelope
        (FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions.unconsRowsWithSizeFormulaCodePolynomial
          tokenCount numericBound bitBound)
        (compactNatSizeFixedPayloadPolynomial bitBound)
        (parserAreaFixedPayloadPolynomial bitBound) := by
    exact
      unconsRowsWithSizeTail56Certificate_structuralPayloadBound_le_fixed
      tokenCount tailBoundary tailCount tailBoundarySize numericBound bitBound
      hsize harea htokenCount htailCount htailBoundarySize hnumericSize
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        consCertificate tailCertificate) <= _
  exact transparentHybridConjunctionPayloadBound_le consCertificate
    tailCertificate _ _ hconsResource htailResource

end FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456TransparentFixedBounds
