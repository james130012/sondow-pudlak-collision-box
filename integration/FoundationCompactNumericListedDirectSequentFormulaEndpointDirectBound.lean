import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointTail01Bound

/-! # Exact direct bound for the original 27-coordinate endpoint formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointDirectBound

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaEndpointAssemblyResources
open FoundationCompactNumericListedDirectSequentFormulaEndpointTail01Bound
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

opaque compactSequentFormulaEndpointDirectBoundOfGraph
    (tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
      finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates)
    (numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hinputCount : coordinates.inputCount <= numericBound)
    (hfirstCount : coordinates.firstCount <= numericBound)
    (hvalueCount : coordinates.valueCount <= numericBound)
    (hfinalCount : coordinates.finalCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hinputBoundarySize : Nat.size coordinates.inputBoundary <= bitBound)
    (hfirstBoundarySize : Nat.size coordinates.firstBoundary <= bitBound)
    (hvalueBoundarySize : Nat.size coordinates.valueBoundary <= bitBound)
    (hfinalBoundarySize : Nat.size coordinates.finalBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hgraph : CompactSequentFormulaEndpointGraph tokenTable width tokenCount
      inputStart inputFinish valueStart valueFinish finalStart finalFinish
      coordinates) :
    FixedResourceEmptyContextProof
      (compactSequentFormulaEndpointDirectClosedFormula tokenTable width
        tokenCount inputStart inputFinish valueStart valueFinish finalStart
        finalFinish coordinates)
      (endpointAssemblyTail01Resource tokenTable width tokenCount inputStart
        inputFinish valueStart valueFinish finalStart finalFinish numericBound
        bitBound coordinates) := by
  let assembled := compactSequentFormulaEndpointTail01BoundOfGraph tokenTable
    width tokenCount inputStart inputFinish valueStart valueFinish finalStart
    finalFinish coordinates numericBound bitBound hwidth htokenCount
    hinputCount hfirstCount hvalueCount hfinalCount htokenTableSize
    hinputBoundarySize hfirstBoundarySize hvalueBoundarySize
    hfinalBoundarySize hnumericSize hgraph
  have hformula :
      endpointAssemblyTail01Formula tokenTable width tokenCount inputStart
          inputFinish valueStart valueFinish finalStart finalFinish coordinates =
        compactSequentFormulaEndpointDirectClosedFormula tokenTable width
          tokenCount inputStart inputFinish valueStart valueFinish finalStart
          finalFinish coordinates :=
    (endpointAssemblyTail01Formula_eq_explicit tokenTable width tokenCount
      inputStart inputFinish valueStart valueFinish finalStart finalFinish
      coordinates).trans
      (compactSequentFormulaEndpointDirectClosedFormula_alignment tokenTable
        width tokenCount inputStart inputFinish valueStart valueFinish
        finalStart finalFinish coordinates).symm
  let proof := CertifiedPAContextProof.cast hformula assembled.proof
  refine { proof := proof, payloadLength_le := ?_ }
  dsimp only [proof]
  rw [CertifiedPAContextProof.cast_payloadLength]
  exact assembled.payloadLength_le

#print axioms compactSequentFormulaEndpointDirectBoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaEndpointDirectBound
