import integration.FoundationCompactNumericListedDirectParserSyntaxTermGraphRunningResourceFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermGraphTailFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermGraphFormulaFacts
import integration.FoundationCompactNumericListedDirectParserSyntaxTermGraphClosedGeneralEnvelope

/-! # Fully fixed three-part assembly of the complete syntax-term graph -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxTermGraphPartsFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermAllBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermGraphCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermGraphRunningResourceFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermGraphTailFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermGraphFormulaFacts
open FoundationCompactNumericListedDirectParserSyntaxTermGraphClosedGeneralEnvelope
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

theorem
    syntaxTermFullyFixedGraphPartsCertificate_structuralPayloadBound_le
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
        (syntaxTermFullyFixedGraphPartsCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) <=
      hybridThreeConjunctionGeneralPayloadEnvelope
        (compactUnifiedParserSyntaxTermFormulaSyntaxFixedPolynomial bitBound)
        (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
          numericBound bitBound)
        (unconsRowsWithSizeFullyFixedPayloadPolynomial tokenCount numericBound
          bitBound)
        (syntaxTermAllBranchesFullyFixedPayloadEnvelope tokenCount numericBound
          bitBound) := by
  let runningCertificate :=
    syntaxTermFullyFixedGraphRunningCertificate tokenTable width tokenCount
      current next binderArity witness hgraph
  let tailCertificate :=
    syntaxTermFullyFixedGraphTailCertificate tokenTable width tokenCount current
      next binderArity witness hgraph
  have hsize :=
    compactUnifiedParserSyntaxTermFormulaEnvironment_size_le tokenTable width
      tokenCount current next binderArity witness bitBound htokenTableSize
      hwidthSize htokenCountSize hcurrentSize hnextSize hbinderSize hwitness
  have hrunning :=
    syntaxTermFullyFixedGraphRunningCertificate_structuralPayloadBound_le
      tokenTable width tokenCount current next binderArity numericBound
      bitBound witness hgraph hwidth hcurrentValue htokenTableSize hwidthSize
      htokenCountSize hcurrentSize
  have htail :=
    syntaxTermFullyFixedGraphTailCertificate_structuralPayloadBound_le
      tokenTable width tokenCount current next binderArity numericBound
      bitBound witness hgraph hwidth htokenCount hcurrentValue hnextValue
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      hbinderSize hwitness hnumericSize hbitPositive
  have houter :=
    transparentHybridConjunctionPayloadBound_le runningCertificate
      tailCertificate _ _ hrunning htail
  have hassembly :=
    syntaxTermGraphTransparentEnvelope_le_closedGeneral tokenTable width
      tokenCount current next binderArity numericBound bitBound witness hsize
  have halign :=
    syntaxTermFullyFixedGraphPartsCertificate_structuralPayload_eq tokenTable
      width tokenCount current next binderArity witness hgraph
  have hbound := houter.trans hassembly
  calc
    hybridFormulaStructuralPayloadBound
        (syntaxTermFullyFixedGraphPartsCertificate tokenTable width tokenCount
          current next binderArity witness hgraph) =
      hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          runningCertificate tailCertificate) := halign
    _ <= _ := hbound

end FoundationCompactNumericListedDirectParserSyntaxTermGraphPartsFullyFixedBounds
