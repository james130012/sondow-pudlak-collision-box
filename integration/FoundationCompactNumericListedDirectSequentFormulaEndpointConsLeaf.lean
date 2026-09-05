import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointDirectSyntax
import integration.FoundationCompactNumericListedDirectNatListConsRowsDirectData
import integration.FoundationCompactNumericListedDirectNatListConsRowsClosedFixedDirectBound
import integration.FoundationCompactNumericListedDirectFixedClosedToEmptyResourceBound

/-! # The natural-list cons-row leaf of the sequent endpoint -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointConsLeaf

open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsDirectData
open FoundationCompactNumericListedDirectNatListConsRowsClosedFixedBound
open FoundationCompactNumericListedDirectNatListConsRowsClosedFixedDirectBound
open FoundationCompactNumericListedDirectFixedClosedToEmptyResourceBound
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

noncomputable def compactSequentFormulaEndpointConsLeafOfGraph
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
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hgraph : CompactSequentFormulaEndpointGraph tokenTable width tokenCount
      inputStart inputFinish valueStart valueFinish finalStart finalFinish
      coordinates) :
    FixedResourceEmptyContextProof
      (compactAdditiveNatListConsRowsClosedFormula tokenTable width tokenCount
        coordinates.firstBoundary coordinates.firstCount
        coordinates.inputBoundary coordinates.inputCount
        coordinates.valueCount)
      (natListConsRowsClosedFullyFixedPayloadPolynomial numericBound
        bitBound) := by
  rcases hgraph with
    ⟨_, _, _, _, _, _, _, _, hcons, _, _, _⟩
  let headData := compactAdditiveNatListConsHeadDataOfGraph tokenTable width
    tokenCount coordinates.firstBoundary coordinates.firstCount
    coordinates.inputBoundary coordinates.inputCount coordinates.valueCount
    hcons
  let tailRows : (index : Fin coordinates.firstCount) ->
      CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
        coordinates.firstBoundary coordinates.inputBoundary index :=
    fun index =>
      compactAdditiveNatListConsTailRowDataOfGraph tokenTable width tokenCount
        coordinates.firstBoundary coordinates.firstCount
        coordinates.inputBoundary coordinates.inputCount coordinates.valueCount
        index hcons index.isLt
  let consBound := compactAdditiveNatListConsRowsClosedFixedDirectBound
    tokenTable width tokenCount coordinates.firstBoundary
    coordinates.firstCount coordinates.inputBoundary coordinates.inputCount
    coordinates.valueCount numericBound bitBound hwidth htokenCount
    hinputCount hvalueCount htokenTableSize hfirstBoundarySize
    hinputBoundarySize hnumericSize hcons.1 headData tailRows
  exact
    fixedResourceEmptyContextProofOfFixedClosedDirectFormulaBound consBound

#print axioms compactSequentFormulaEndpointConsLeafOfGraph

end FoundationCompactNumericListedDirectSequentFormulaEndpointConsLeaf
