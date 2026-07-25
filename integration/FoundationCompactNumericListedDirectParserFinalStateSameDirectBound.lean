import integration.FoundationCompactNumericListedDirectParserFinalStateSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
import integration.FoundationCompactPADirectConnectiveTransparentBounds

/-! # Fixed direct bound for the parser final same-rows leaf -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserFinalStateSameDirectBound

open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserFinalStateSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds

noncomputable def parserFinalSameDirectBoundOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount outputBoundary
      numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListSameRows tokenTable width tokenCount
      sourceBoundary sourceCount outputBoundary sourceCount)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hsourceCountValue : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (houtputBoundarySize : Nat.size outputBoundary <= bitBound)
    (hnumericBoundSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound parserFinalZeroValuation
      (parserFinalSameFormula tokenTable width tokenCount sourceBoundary
        sourceCount outputBoundary)
      (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound) := by
  let certificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount sourceBoundary sourceCount outputBoundary sourceCount
      hgraph
  refine
    { proof := ?_
      payloadLength_le := ?_ }
  · change FoundationCompactCertifiedContextProof.CertifiedPAContextProof
      (FoundationCompactPAValuationTermCompiler.valuationContext
        (compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
          sourceBoundary sourceCount outputBoundary
          sourceCount).freeVariables (fun _ => 0))
      (compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount outputBoundary sourceCount)
    exact certificate.compile
  · exact
      (compile_payloadLength_le_structuralPayloadBound certificate).trans
      ((compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
        tokenTable width tokenCount sourceBoundary sourceCount outputBoundary
        sourceCount hgraph).trans
      (compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount outputBoundary
        sourceCount numericBound bitBound hgraph hwidthValue htokenCountValue
        hsourceCountValue htokenTableSize hsourceBoundarySize
        houtputBoundarySize hnumericBoundSize))

#print axioms parserFinalSameDirectBoundOfGraph

end FoundationCompactNumericListedDirectParserFinalStateSameDirectBound
