import integration.FoundationCompactNumericListedDirectParserSyntaxTermGraphPartsFullyFixedBounds

/-! # Fully fixed bound for the complete syntax-term parser graph -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxTermGraphFullyFixedBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermAllBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermGraphCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermGraphPartsFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions

def syntaxTermGraphFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (compactUnifiedParserSyntaxTermFormulaSyntaxFixedPolynomial bitBound)
    (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
      numericBound bitBound)
    (unconsRowsWithSizeFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound)
    (syntaxTermAllBranchesFullyFixedPayloadEnvelope tokenCount numericBound
      bitBound)

theorem
    syntaxTermFullyFixedGraphCertificate_structuralPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hwitness :
      CompactUnifiedParserSyntaxTermWitnessCoordinateSizeBound witness
        bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermFullyFixedGraphCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) <=
      syntaxTermGraphFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound := by
  have hparts :=
    syntaxTermFullyFixedGraphPartsCertificate_structuralPayloadBound_le
      tokenTable width tokenCount current next binderArity numericBound bitBound
      witness hgraph hwidth htokenCount hcurrentValue hnextValue htokenTableSize
      hwidthSize htokenCountSize hcurrentSize hnextSize hbinderSize hwitness
      hnumericSize hbitPositive
  have halign :=
    syntaxTermFullyFixedGraphCertificate_structuralPayload_eq_parts tokenTable
      width tokenCount current next binderArity witness hgraph
  unfold syntaxTermGraphFullyFixedPayloadPolynomial
  calc
    hybridFormulaStructuralPayloadBound
        (syntaxTermFullyFixedGraphCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) =
      hybridFormulaStructuralPayloadBound
        (syntaxTermFullyFixedGraphPartsCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) := halign
    _ <= _ := hparts

end FoundationCompactNumericListedDirectParserSyntaxTermGraphFullyFixedBounds
