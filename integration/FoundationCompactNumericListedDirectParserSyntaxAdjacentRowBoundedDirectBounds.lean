import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedCheckedData

/-! # Direct bound for one original bounded adjacent parser row -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedDirectBounds

open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedPublicDirectCompiler
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedCheckedData

noncomputable def compactParserSyntaxAdjacentRowBoundedDirectBound
    (tokenTable width tokenCount stateBoundary stateCount index valueBound
      numericBound bitBound : Nat)
    (hbounded : CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
      stateBoundary stateCount index valueBound)
    (hvalueBound : valueBound <= numericBound)
    (hvalueBoundSize : Nat.size valueBound <= bitBound)
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
    ExplicitDirectFormulaBound
      FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate.compactParserStateAtRowsZeroValuation
      (compactParserSyntaxAdjacentRowBoundedClosedFormula tokenTable width
        tokenCount stateBoundary stateCount index valueBound)
      (compactParserSyntaxAdjacentRowBoundedPublicDirectPayloadEnvelope
        tokenTable width tokenCount stateBoundary stateCount index valueBound
        numericBound bitBound) := by
  let data := compactParserSyntaxAdjacentRowCheckedDataOfBounded tokenTable width
    tokenCount stateBoundary stateCount index valueBound hbounded
  have hcurrentAtValueBound := data.current_value_bound
  have hnextAtValueBound := data.next_value_bound
  have hwitnessAtValueBound := data.witness_value_bound
  have hcurrentValue :=
    parserStateCoordinateValueBound_mono hcurrentAtValueBound hvalueBound
  have hnextValue :=
    parserStateCoordinateValueBound_mono hnextAtValueBound hvalueBound
  have hwitnessValue :=
    parserSyntaxStepWitnessCoordinateValueBound_mono hwitnessAtValueBound
      hvalueBound
  have hcurrentSize :=
    parserStateCoordinateSizeBound_of_valueBound hcurrentAtValueBound
      hvalueBoundSize
  have hnextSize :=
    parserStateCoordinateSizeBound_of_valueBound hnextAtValueBound
      hvalueBoundSize
  have hwitnessSize :=
    parserSyntaxStepWitnessCoordinateSizeBound_of_valueBound
      hwitnessAtValueBound hvalueBoundSize
  exact compactParserSyntaxAdjacentRowBoundedPublicDirectBoundOfGraph tokenTable
    width tokenCount stateBoundary stateCount index valueBound data.row
    numericBound bitBound data.graph data.current_status data.next_status
    data.values_le hvalueBound hwidth hwidthBit htokenCount hstateCount
    hcurrentValue hnextValue htokenTableSize hstateBoundarySize hcurrentSize
    hnextSize hwitnessValue hwitnessSize hareaNumeric hareaBit hnumericSize
    hbitPositive

#print axioms compactParserSyntaxAdjacentRowBoundedDirectBound

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedDirectBounds
