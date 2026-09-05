import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointDirectBound

/-! # Assumption-free public resource bound for the sequent endpoint -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointDirectPublicBound

open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaEndpointAssemblyResources
open FoundationCompactNumericListedDirectSequentFormulaEndpointDirectBound
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

def compactSequentFormulaEndpointDirectNumericBound
    (width tokenCount : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) : Nat :=
  width + tokenCount + coordinates.inputCount + coordinates.firstCount +
    coordinates.valueCount + coordinates.finalCount + 1

def compactSequentFormulaEndpointDirectBitBound
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) : Nat :=
  Nat.size tokenTable + Nat.size coordinates.inputBoundary +
    Nat.size coordinates.firstBoundary +
    Nat.size coordinates.valueBoundary +
    Nat.size coordinates.finalBoundary +
    Nat.size
      (compactSequentFormulaEndpointDirectNumericBound width tokenCount
        coordinates) + 1

def compactSequentFormulaEndpointDirectPublicResource
    (tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
      finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) : Nat :=
  endpointAssemblyTail01Resource tokenTable width tokenCount inputStart
    inputFinish valueStart valueFinish finalStart finalFinish
    (compactSequentFormulaEndpointDirectNumericBound width tokenCount
      coordinates)
    (compactSequentFormulaEndpointDirectBitBound tokenTable width tokenCount
      coordinates)
    coordinates

opaque compactSequentFormulaEndpointDirectPublicBoundOfGraph
    (tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
      finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates)
    (hgraph : CompactSequentFormulaEndpointGraph tokenTable width tokenCount
      inputStart inputFinish valueStart valueFinish finalStart finalFinish
      coordinates) :
    FixedResourceEmptyContextProof
      (compactSequentFormulaEndpointDirectClosedFormula tokenTable width
        tokenCount inputStart inputFinish valueStart valueFinish finalStart
        finalFinish coordinates)
      (compactSequentFormulaEndpointDirectPublicResource tokenTable width
        tokenCount inputStart inputFinish valueStart valueFinish finalStart
        finalFinish coordinates) := by
  let numericBound := compactSequentFormulaEndpointDirectNumericBound width
    tokenCount coordinates
  let bitBound := compactSequentFormulaEndpointDirectBitBound tokenTable width
    tokenCount coordinates
  have hwidth : width <= numericBound := by
    dsimp only [numericBound,
      compactSequentFormulaEndpointDirectNumericBound]
    omega
  have htokenCount : tokenCount <= numericBound := by
    dsimp only [numericBound,
      compactSequentFormulaEndpointDirectNumericBound]
    omega
  have hinputCount : coordinates.inputCount <= numericBound := by
    dsimp only [numericBound,
      compactSequentFormulaEndpointDirectNumericBound]
    omega
  have hfirstCount : coordinates.firstCount <= numericBound := by
    dsimp only [numericBound,
      compactSequentFormulaEndpointDirectNumericBound]
    omega
  have hvalueCount : coordinates.valueCount <= numericBound := by
    dsimp only [numericBound,
      compactSequentFormulaEndpointDirectNumericBound]
    omega
  have hfinalCount : coordinates.finalCount <= numericBound := by
    dsimp only [numericBound,
      compactSequentFormulaEndpointDirectNumericBound]
    omega
  have htokenTableSize : Nat.size tokenTable <= bitBound := by
    dsimp only [bitBound, compactSequentFormulaEndpointDirectBitBound]
    omega
  have hinputBoundarySize :
      Nat.size coordinates.inputBoundary <= bitBound := by
    dsimp only [bitBound, compactSequentFormulaEndpointDirectBitBound]
    omega
  have hfirstBoundarySize :
      Nat.size coordinates.firstBoundary <= bitBound := by
    dsimp only [bitBound, compactSequentFormulaEndpointDirectBitBound]
    omega
  have hvalueBoundarySize :
      Nat.size coordinates.valueBoundary <= bitBound := by
    dsimp only [bitBound, compactSequentFormulaEndpointDirectBitBound]
    omega
  have hfinalBoundarySize :
      Nat.size coordinates.finalBoundary <= bitBound := by
    dsimp only [bitBound, compactSequentFormulaEndpointDirectBitBound]
    omega
  have hnumericSize : Nat.size numericBound <= bitBound := by
    dsimp only [numericBound, bitBound,
      compactSequentFormulaEndpointDirectBitBound]
    omega
  exact compactSequentFormulaEndpointDirectBoundOfGraph tokenTable width
    tokenCount inputStart inputFinish valueStart valueFinish finalStart
    finalFinish coordinates numericBound bitBound hwidth htokenCount
    hinputCount hfirstCount hvalueCount hfinalCount htokenTableSize
    hinputBoundarySize hfirstBoundarySize hvalueBoundarySize
    hfinalBoundarySize hnumericSize hgraph

#print axioms compactSequentFormulaEndpointDirectPublicBoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaEndpointDirectPublicBound
