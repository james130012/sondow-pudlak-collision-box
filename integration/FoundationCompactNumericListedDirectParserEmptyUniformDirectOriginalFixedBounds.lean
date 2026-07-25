import integration.FoundationCompactNumericListedDirectParserEmptyUniformDirectFixedBounds

/-! # Fixed payload bound after alignment with the original empty graph formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserEmptyUniformDirectOriginalFixedBounds

open FoundationCompactCertifiedContextProof
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectParserEmptyUniformDirectAlignment
open FoundationCompactNumericListedDirectParserEmptyUniformDirectFixedBounds

theorem
    compileCompactUnifiedParserEmptyUniformDirectOriginalContext_payloadLength_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserEmptyWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserEmptyGraphRows
      tokenTable width tokenCount current next witness)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (houtputBoundarySize :
      Nat.size witness.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compileCompactUnifiedParserEmptyUniformDirectOriginalContext tokenTable
      width tokenCount current next witness numericBound bitBound hgraph
      htokenCount
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          hcurrentValue (5 : Fin 8))
      houtputBoundarySize hnumericSize).payloadLength <=
      parserEmptyUniformDirectFixedPayloadPolynomial numericBound bitBound := by
  have hraw :=
    compileCompactUnifiedParserEmptyUniformDirectContext_payloadLength_le_fixed
      tokenTable width tokenCount current next witness numericBound bitBound
      hgraph hwidth htokenCount hcurrentValue hnextValue htokenTableSize
      hcurrentSize hnextSize houtputBoundarySize hnumericSize hbitPositive
  rw [
    compileCompactUnifiedParserEmptyUniformDirectOriginalContext_payloadLength_eq]
  exact hraw

end FoundationCompactNumericListedDirectParserEmptyUniformDirectOriginalFixedBounds
