import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointDirectSyntax
import integration.FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedChildren
import integration.FoundationCompactNumericListedDirectFixedClosedToEmptyResourceBound

/-! # The value structured-list layout leaf of the sequent endpoint -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 150000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointValueLayoutLeaf

open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedChildren
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
open FoundationCompactNumericListedDirectFixedClosedToEmptyResourceBound
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

noncomputable def compactSequentFormulaEndpointValueLayoutLeafOfGraph
    (tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
      finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates)
    (numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hvalueCount : coordinates.valueCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hvalueBoundarySize : Nat.size coordinates.valueBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hgraph : CompactSequentFormulaEndpointGraph tokenTable width tokenCount
      inputStart inputFinish valueStart valueFinish finalStart finalFinish
      coordinates) :
    FixedResourceEmptyContextProof
      (compactAdditiveStructuredListLayoutClosedFormula tokenTable width
        tokenCount valueStart coordinates.valueCount valueFinish
        coordinates.valueBoundary)
      (compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
        numericBound bitBound) := by
  have hvalueLayout := hgraph.2.2.2.2.2.2.2.2.2.1
  let layoutBound := compactNatListWitnessRowsLayoutFixedBound tokenTable width
    tokenCount valueStart coordinates.valueCount valueFinish
    coordinates.valueBoundary numericBound bitBound hvalueLayout hwidth
    htokenCount hvalueCount htokenTableSize hvalueBoundarySize hnumericSize
  exact
    fixedResourceEmptyContextProofOfFixedClosedDirectFormulaBound layoutBound

#print axioms compactSequentFormulaEndpointValueLayoutLeafOfGraph

end FoundationCompactNumericListedDirectSequentFormulaEndpointValueLayoutLeaf
