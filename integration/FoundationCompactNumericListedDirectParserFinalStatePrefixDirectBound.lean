import integration.FoundationCompactNumericListedDirectParserFinalStateSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactPADirectConnectiveTransparentBounds

/-! # Fixed direct bound for the parser final completed-status prefix -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserFinalStatePrefixDirectBound

open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserFinalStateSyntaxFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds

noncomputable def parserFinalPrefixDirectBoundOfGraph
    (tokenTable width tokenCount tasksFinish outputStart numericBound bitBound :
      Nat)
    (hgraph : CompactBinaryNatCompletedStatusPrefix tokenTable width tokenCount
      tasksFinish outputStart)
    (hwidthValue : width <= numericBound)
    (htasksFinishValue : tasksFinish <= numericBound)
    (htasksFinishSuccValue : tasksFinish + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (htasksFinishSize : Nat.size tasksFinish <= bitBound)
    (houtputStartSize : Nat.size outputStart <= bitBound)
    (htasksFinishSuccSize : Nat.size (tasksFinish + 1) <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ExplicitDirectFormulaBound parserFinalZeroValuation
      (parserFinalPrefixFormula tokenTable width tokenCount tasksFinish
        outputStart)
      (binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial numericBound
        bitBound) := by
  let certificate :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount tasksFinish outputStart hgraph
  refine
    { proof := ?_
      payloadLength_le := ?_ }
  · change FoundationCompactCertifiedContextProof.CertifiedPAContextProof
      (FoundationCompactPAValuationTermCompiler.valuationContext
        (compactBinaryNatCompletedStatusPrefixClosedFormula tokenTable width
          tokenCount tasksFinish outputStart).freeVariables (fun _ => 0))
      (compactBinaryNatCompletedStatusPrefixClosedFormula tokenTable width
        tokenCount tasksFinish outputStart)
    exact certificate.compile
  · exact
      (compile_payloadLength_le_structuralPayloadBound certificate).trans
      (compactBinaryNatCompletedStatusPrefixExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount tasksFinish outputStart numericBound
        bitBound hwidthValue htasksFinishValue htasksFinishSuccValue
        htokenTableSize hwidthSize htokenCountSize htasksFinishSize
        houtputStartSize htasksFinishSuccSize hbitPositive hgraph)

#print axioms parserFinalPrefixDirectBoundOfGraph

end FoundationCompactNumericListedDirectParserFinalStatePrefixDirectBound
