import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointTail04Bound

/-! # Exact empty-context proof for all twelve endpoint leaves -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointTail01Bound

open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointAssemblyResources
open FoundationCompactNumericListedDirectSequentFormulaEndpointWitnessTraceLeaves
open FoundationCompactNumericListedDirectSequentFormulaEndpointTail04Bound
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

opaque compactSequentFormulaEndpointTail01BoundOfGraph
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
      (endpointAssemblyTail01Formula tokenTable width tokenCount inputStart
        inputFinish valueStart valueFinish finalStart finalFinish coordinates)
      (endpointAssemblyTail01Resource tokenTable width tokenCount inputStart
        inputFinish valueStart valueFinish finalStart finalFinish numericBound
        bitBound coordinates) := by
  let witnessTrace := compactSequentFormulaEndpointWitnessTraceLeavesOfGraph
    tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
    finalStart finalFinish coordinates numericBound bitBound hwidth htokenCount
    hinputCount hfirstCount hfinalCount htokenTableSize hinputBoundarySize
    hfirstBoundarySize hfinalBoundarySize hnumericSize hgraph
  let tail04 := compactSequentFormulaEndpointTail04BoundOfGraph tokenTable width
    tokenCount inputStart inputFinish valueStart valueFinish finalStart
    finalFinish coordinates numericBound bitBound hwidth htokenCount
    hinputCount hfirstCount hvalueCount hfinalCount htokenTableSize
    hinputBoundarySize hfirstBoundarySize hvalueBoundarySize
    hfinalBoundarySize hnumericSize hgraph
  let tail03 := FixedResourceEmptyContextProof.conjunction
    witnessTrace.finalRows tail04
  let tail02 := FixedResourceEmptyContextProof.conjunction
    witnessTrace.firstRows tail03
  exact FixedResourceEmptyContextProof.conjunction witnessTrace.inputRows tail02

#print axioms compactSequentFormulaEndpointTail01BoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaEndpointTail01Bound
