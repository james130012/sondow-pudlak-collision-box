import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointDirectSyntax
import integration.FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedChildren
import integration.FoundationCompactNumericListedDirectFixedClosedToEmptyResourceBound

/-! # The value-table area leaf of the sequent endpoint -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointValueAreaLeaf

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedChildren
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectFixedClosedToEmptyResourceBound
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

noncomputable def compactSequentFormulaEndpointValueAreaLeafOfGraph
    (tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
      finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates)
    (numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (hvalueCount : coordinates.valueCount <= numericBound)
    (hvalueBoundarySize : Nat.size coordinates.valueBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hgraph : CompactSequentFormulaEndpointGraph tokenTable width tokenCount
      inputStart inputFinish valueStart valueFinish finalStart finalFinish
      coordinates) :
    FixedResourceEmptyContextProof
      (“!!(shortBinaryNumeralTerm coordinates.valueBoundarySize) ≤
        (!!(shortBinaryNumeralTerm coordinates.valueCount) + 1) *
          !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula)
      (parserAreaFixedPayloadPolynomial bitBound) := by
  have hvalueSize := hgraph.2.2.2.2.2.2.2.2.2.2.1
  have hvalueArea := hgraph.2.2.2.2.2.2.2.2.2.2.2
  let areaBound := compactNatListWitnessRowsAreaFixedBound tokenCount
    coordinates.valueCount coordinates.valueBoundary
    coordinates.valueBoundarySize numericBound bitBound hvalueSize hvalueArea
    htokenCount hvalueCount hvalueBoundarySize hnumericSize
  exact
    fixedResourceEmptyContextProofOfFixedClosedDirectFormulaBound areaBound

#print axioms compactSequentFormulaEndpointValueAreaLeafOfGraph

end FoundationCompactNumericListedDirectSequentFormulaEndpointValueAreaLeaf
