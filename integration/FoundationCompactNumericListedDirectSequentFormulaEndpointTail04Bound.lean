import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointTail05Bound

/-! # Exact empty-context proof for endpoint leaves 4--12 -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointTail04Bound

open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointAssemblyResources
open FoundationCompactNumericListedDirectSequentFormulaEndpointWitnessTraceLeaves
open FoundationCompactNumericListedDirectSequentFormulaEndpointTail05Bound
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

opaque compactSequentFormulaEndpointTail04BoundOfGraph
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
      (endpointAssemblyTail04Formula tokenTable width tokenCount valueStart
        valueFinish finalStart finalFinish coordinates)
      (endpointAssemblyTail04Resource tokenTable width tokenCount valueStart
        valueFinish finalStart finalFinish numericBound bitBound
        coordinates) := by
  let witnessTrace := compactSequentFormulaEndpointWitnessTraceLeavesOfGraph
    tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
    finalStart finalFinish coordinates numericBound bitBound hwidth htokenCount
    hinputCount hfirstCount hfinalCount htokenTableSize hinputBoundarySize
    hfirstBoundarySize hfinalBoundarySize hnumericSize hgraph
  let tail05 := compactSequentFormulaEndpointTail05BoundOfGraph tokenTable width
    tokenCount inputStart inputFinish valueStart valueFinish finalStart
    finalFinish coordinates numericBound bitBound hwidth htokenCount
    hinputCount hvalueCount htokenTableSize hfirstBoundarySize
    hinputBoundarySize hvalueBoundarySize hnumericSize hgraph
  exact FixedResourceEmptyContextProof.conjunction witnessTrace.trace tail05

#print axioms compactSequentFormulaEndpointTail04BoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaEndpointTail04Bound
