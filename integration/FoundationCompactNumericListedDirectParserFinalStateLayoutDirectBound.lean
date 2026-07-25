import integration.FoundationCompactNumericListedDirectParserFinalStateSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
import integration.FoundationCompactPADirectConnectiveTransparentBounds

/-! # Fixed uniform direct bound for the parser final output layout -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserFinalStateLayoutDirectBound

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserFinalStateSyntaxFixedBounds
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds

noncomputable def parserFinalLayoutDirectBoundOfGraph
    (tokenTable width tokenCount outputStart sourceCount finish outputBoundary
      numericBound bitBound : Nat)
    (hlayout : CompactAdditiveStructuredListLayout tokenTable width tokenCount
      outputStart sourceCount finish outputBoundary)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hsourceCountValue : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (houtputBoundarySize : Nat.size outputBoundary <= bitBound)
    (hnumericBoundSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound parserFinalZeroValuation
      (parserFinalLayoutFormula tokenTable width tokenCount outputStart
        sourceCount finish outputBoundary)
      (compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
        numericBound bitBound) := by
  let data :=
    compactAdditiveStructuredListLayoutDataOfLayout tokenTable width tokenCount
      outputStart sourceCount finish outputBoundary hlayout
  let raw :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount outputStart sourceCount finish outputBoundary
      data.bodyStart numericBound bitBound data.bodyStart_le_tokenCount
      data.header data.boundaryFinish_le_tokenCount data.boundaryStartEntry
      data.boundaryFinishEntry data.rows htokenCountValue hsourceCountValue
      houtputBoundarySize hnumericBoundSize
  refine
    { proof := CertifiedPAContextProof.castContext (by
        rw [show
          (parserFinalLayoutFormula tokenTable width tokenCount outputStart
            sourceCount finish outputBoundary).freeVariables = ∅ by
          unfold parserFinalLayoutFormula
          exact
            compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
              tokenTable width tokenCount outputStart sourceCount finish
              outputBoundary]
        simp [valuationContext]) raw
      payloadLength_le := ?_ }
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext_payloadLength_le_fixed
      tokenTable width tokenCount outputStart sourceCount finish outputBoundary
      data.bodyStart numericBound bitBound data.bodyStart_le_tokenCount
      data.header data.boundaryFinish_le_tokenCount data.boundaryStartEntry
      data.boundaryFinishEntry data.rows hwidthValue htokenCountValue
      hsourceCountValue htokenTableSize houtputBoundarySize hnumericBoundSize

#print axioms parserFinalLayoutDirectBoundOfGraph

end FoundationCompactNumericListedDirectParserFinalStateLayoutDirectBound
