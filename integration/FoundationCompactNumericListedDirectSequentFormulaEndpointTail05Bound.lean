import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointTail09Bound

/-! # Exact empty-context proof for endpoint leaves 5--12 -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointTail05Bound

open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointAssemblyResources
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryLeaves
open FoundationCompactNumericListedDirectSequentFormulaEndpointTail09Bound
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

opaque compactSequentFormulaEndpointTail05BoundOfGraph
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
      (endpointAssemblyTail05Formula tokenTable width tokenCount valueStart
        valueFinish finalStart finalFinish coordinates)
      (endpointAssemblyTail05Resource tokenTable width tokenCount valueStart
        valueFinish finalStart finalFinish numericBound bitBound
        coordinates) := by
  let leaves := compactSequentFormulaEndpointFixedWidthEntryLeavesOfGraph
    tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
    finalStart finalFinish coordinates hgraph
  let tail09 := compactSequentFormulaEndpointTail09BoundOfGraph tokenTable width
    tokenCount inputStart inputFinish valueStart valueFinish finalStart
    finalFinish coordinates numericBound bitBound hwidth htokenCount
    hinputCount hvalueCount htokenTableSize hfirstBoundarySize
    hinputBoundarySize hvalueBoundarySize hnumericSize hgraph
  let tail08 := FixedResourceEmptyContextProof.conjunction
    leaves.finalFinish tail09
  let tail07 := FixedResourceEmptyContextProof.conjunction
    leaves.finalStart tail08
  let tail06 := FixedResourceEmptyContextProof.conjunction
    leaves.firstFinish tail07
  let tail05 := FixedResourceEmptyContextProof.conjunction
    leaves.firstStart tail06
  exact tail05

#print axioms compactSequentFormulaEndpointTail05BoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaEndpointTail05Bound
