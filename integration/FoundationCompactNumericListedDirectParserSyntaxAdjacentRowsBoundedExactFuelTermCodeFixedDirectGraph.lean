import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversal
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectGraph

/-! # Exact-fuel adjacent-row graph with fixed branch resources -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectGraph

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectGraph
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectGraph
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversal

def
    compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectClosedResource
    (tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound numericBound bitBound : Nat) : Nat :=
  let exponentialFormula :=
    compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula tableWidth
      valueBound
  let universalFormula :=
    (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
      tokenCount stateBoundary stateCount valueBound).ballLT
        (compactParserSyntaxExactFuelTerm inputCount)
  compactParserSyntaxAdjacentRowsBoundedExponentialDirectResource tableWidth
      valueBound +
    compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversalResource
      tokenTable width tokenCount stateBoundary stateCount inputCount valueBound
        numericBound bitBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ exponentialFormula
      universalFormula

noncomputable def
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectClosedContext
    (tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound numericBound bitBound : Nat)
    (hgraph : CompactParserSyntaxAdjacentRowsBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount
        (compactParserSyntaxExactFuel inputCount) tableWidth valueBound)
    (hfuel : compactParserSyntaxExactFuel inputCount <= numericBound)
    (hvalueNumeric : valueBound <= numericBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    CertifiedPAContextProof ∅
      (compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputCount tableWidth
        valueBound) := by
  let exponentialProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialDirectContext
      tableWidth valueBound hgraph.1
  let universalProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount inputCount valueBound
      numericBound bitBound hgraph.2 hfuel hvalueNumeric hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hnumericSize hbitPositive
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  exact CertifiedPAContextProof.cast
    (compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount inputCount
        tableWidth valueBound).symm
    raw

theorem
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectClosedContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound numericBound bitBound : Nat)
    (hgraph : CompactParserSyntaxAdjacentRowsBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount
        (compactParserSyntaxExactFuel inputCount) tableWidth valueBound)
    (hfuel : compactParserSyntaxExactFuel inputCount <= numericBound)
    (hvalueNumeric : valueBound <= numericBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compileCompactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectClosedContext
      tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound numericBound bitBound hgraph hfuel hvalueNumeric hwidth
      hwidthBit htokenCount hstateCount htokenTableSize hstateBoundarySize
      hareaNumeric hareaBit hnumericSize hbitPositive).payloadLength <=
    compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectClosedResource
      tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound numericBound bitBound := by
  let exponentialProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialDirectContext
      tableWidth valueBound hgraph.1
  let universalProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount inputCount valueBound
      numericBound bitBound hgraph.2 hfuel hvalueNumeric hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hnumericSize hbitPositive
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  have hexponential : exponentialProof.payloadLength <=
      compactParserSyntaxAdjacentRowsBoundedExponentialDirectResource
        tableWidth valueBound :=
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialDirectContext_payloadLength_le
      tableWidth valueBound hgraph.1
  have huniversal : universalProof.payloadLength <=
      compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversalResource
        tokenTable width tokenCount stateBoundary stateCount inputCount
        valueBound numericBound bitBound :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversalContext_payloadLength_le
      tokenTable width tokenCount stateBoundary stateCount inputCount valueBound
      numericBound bitBound hgraph.2 hfuel hvalueNumeric hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hnumericSize hbitPositive
  have hraw := CertifiedPAContextProof.conjunction_payloadLength_le
    exponentialProof universalProof
  unfold
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectClosedContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change raw.payloadLength <= _
  exact hraw.trans (by
    unfold
      compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectClosedResource
    dsimp only
    omega)

#print axioms
  compileCompactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectClosedContext
#print axioms
  compileCompactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectClosedContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectGraph
