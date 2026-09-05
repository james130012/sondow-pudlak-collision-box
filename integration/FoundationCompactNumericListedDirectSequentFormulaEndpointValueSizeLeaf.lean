import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointDirectSyntax
import integration.FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedChildren
import integration.FoundationCompactNumericListedDirectFixedClosedToEmptyResourceBound

/-! # The value-table size leaf of the sequent endpoint -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointValueSizeLeaf

open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedChildren
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectFixedClosedToEmptyResourceBound
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

noncomputable def compactSequentFormulaEndpointValueSizeLeafOfGraph
    (tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
      finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates)
    (bitBound : Nat)
    (hvalueBoundarySize : Nat.size coordinates.valueBoundary <= bitBound)
    (hgraph : CompactSequentFormulaEndpointGraph tokenTable width tokenCount
      inputStart inputFinish valueStart valueFinish finalStart finalFinish
      coordinates) :
    FixedResourceEmptyContextProof
      (compactNatSizeClosedFormula coordinates.valueBoundarySize
        coordinates.valueBoundary)
      (compactNatSizeFixedPayloadPolynomial bitBound) := by
  have hvalueSize := hgraph.2.2.2.2.2.2.2.2.2.2.1
  let sizeBound := compactNatListWitnessRowsSizeFixedBound
    coordinates.valueBoundarySize coordinates.valueBoundary bitBound
    hvalueSize hvalueBoundarySize
  exact
    fixedResourceEmptyContextProofOfFixedClosedDirectFormulaBound sizeBound

#print axioms compactSequentFormulaEndpointValueSizeLeafOfGraph

end FoundationCompactNumericListedDirectSequentFormulaEndpointValueSizeLeaf
