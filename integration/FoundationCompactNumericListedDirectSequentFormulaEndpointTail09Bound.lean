import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointAssemblyResources

/-! # Exact empty-context proof for endpoint leaves 9--12 -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointTail09Bound

open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointAssemblyResources
open FoundationCompactNumericListedDirectSequentFormulaEndpointConsLeaf
open FoundationCompactNumericListedDirectSequentFormulaEndpointValueLayoutLeaf
open FoundationCompactNumericListedDirectSequentFormulaEndpointValueSizeLeaf
open FoundationCompactNumericListedDirectSequentFormulaEndpointValueAreaLeaf
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

opaque compactSequentFormulaEndpointTail09BoundOfGraph
    (tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
      finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates)
    (numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hinputCount : coordinates.inputCount <= numericBound)
    (hvalueCount : coordinates.valueCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hfirstBoundarySize : Nat.size coordinates.firstBoundary <= bitBound)
    (hinputBoundarySize : Nat.size coordinates.inputBoundary <= bitBound)
    (hvalueBoundarySize : Nat.size coordinates.valueBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hgraph : CompactSequentFormulaEndpointGraph tokenTable width tokenCount
      inputStart inputFinish valueStart valueFinish finalStart finalFinish
      coordinates) :
    FixedResourceEmptyContextProof
      (endpointAssemblyTail09Formula tokenTable width tokenCount valueStart
        valueFinish coordinates)
      (endpointAssemblyTail09Resource tokenTable width tokenCount valueStart
        valueFinish numericBound bitBound coordinates) := by
  let cons := compactSequentFormulaEndpointConsLeafOfGraph tokenTable width
    tokenCount inputStart inputFinish valueStart valueFinish finalStart
    finalFinish coordinates numericBound bitBound hwidth htokenCount
    hinputCount hvalueCount htokenTableSize hfirstBoundarySize
    hinputBoundarySize hnumericSize hgraph
  let layout := compactSequentFormulaEndpointValueLayoutLeafOfGraph tokenTable
    width tokenCount inputStart inputFinish valueStart valueFinish finalStart
    finalFinish coordinates numericBound bitBound hwidth htokenCount
    hvalueCount htokenTableSize hvalueBoundarySize hnumericSize hgraph
  let size := compactSequentFormulaEndpointValueSizeLeafOfGraph tokenTable width
    tokenCount inputStart inputFinish valueStart valueFinish finalStart
    finalFinish coordinates bitBound hvalueBoundarySize hgraph
  let area := compactSequentFormulaEndpointValueAreaLeafOfGraph tokenTable width
    tokenCount inputStart inputFinish valueStart valueFinish finalStart
    finalFinish coordinates numericBound bitBound htokenCount hvalueCount
    hvalueBoundarySize hnumericSize hgraph
  let tail11 := FixedResourceEmptyContextProof.conjunction size area
  let tail10 := FixedResourceEmptyContextProof.conjunction layout tail11
  let tail09 := FixedResourceEmptyContextProof.conjunction cons tail10
  exact tail09

#print axioms compactSequentFormulaEndpointTail09BoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaEndpointTail09Bound
