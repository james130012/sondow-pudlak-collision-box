import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphPartsCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphTailClosedGeneralBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality

/-! # Transparent fixed resources for clean syntax-formula parser parts -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphPartsTransparentFixedBounds

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphTailFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphTailClosedGeneralBounds

def cleanParserSyntaxFormulaTailFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        1)
      (shortBinaryNumeralTerm binderArity)
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        0) ⋏
    compactUnifiedParserSyntaxFormulaBranchExplicitFormula tokenTable width
      tokenCount current next binderArity witness

def cleanParserSyntaxFormulaPartsTransparentEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : Nat :=
  transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.zeroValuation
    (compactBinaryNatRunningStatusSliceClosedFormula tokenTable width tokenCount
      current.tasksFinish current.finish)
    (cleanParserSyntaxFormulaTailFormula tokenTable width tokenCount current next
      binderArity witness)
    (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial numericBound
      bitBound)
    (cleanParserSyntaxFormulaTailPayloadPolynomial tokenCount numericBound
      bitBound)

theorem
    compactUnifiedParserSyntaxFormulaCleanPartsCertificateOfGraph_structuralPayloadBound_le_transparentFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness)
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
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound)
    (hrelationAritySize : Nat.size witness.relationArity <= bitBound)
    (hrelationCodeSize : Nat.size witness.relationCode <= bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxFormulaCleanPartsCertificateOfGraph tokenTable
          width tokenCount current next binderArity witness hgraph) <=
      cleanParserSyntaxFormulaPartsTransparentEnvelope tokenTable width
        tokenCount current next binderArity numericBound bitBound witness := by
  let runningCertificate :=
    compactUnifiedParserSyntaxFormulaCleanRunningCertificateOfGraph tokenTable
      width tokenCount current next binderArity witness hgraph
  let tailCertificate :=
    compactUnifiedParserSyntaxFormulaCleanTailCertificateOfGraph tokenTable
      width tokenCount current next binderArity witness hgraph
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hstartValue : current.tasksFinish <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (3 : Fin 8)
  have hstartSize : Nat.size current.tasksFinish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (3 : Fin 8)
  have hfinishSize : Nat.size current.finish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (1 : Fin 8)
  have hrunningResource :
      hybridFormulaStructuralPayloadBound runningCertificate <=
        compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
          numericBound bitBound := by
    dsimp only [runningCertificate,
      compactUnifiedParserSyntaxFormulaCleanRunningCertificateOfGraph]
    exact
      compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount current.tasksFinish current.finish
        numericBound bitBound hwidth hstartValue htokenTableSize hwidthSize
        htokenCountSize hstartSize hfinishSize hgraph.1
  have htailResource :
      hybridFormulaStructuralPayloadBound tailCertificate <=
        cleanParserSyntaxFormulaTailPayloadPolynomial tokenCount numericBound
          bitBound := by
    exact
      compactUnifiedParserSyntaxFormulaCleanTailCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next binderArity numericBound
        bitBound witness hgraph hwidth htokenCount hcurrentValue hnextValue
        htokenTableSize hcurrentSize hnextSize htailBoundarySize
        hbinderAritySize hrelationAritySize hrelationCodeSize htagSize
        hnumericSize hbitPositive
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        runningCertificate tailCertificate) <= _
  unfold cleanParserSyntaxFormulaPartsTransparentEnvelope
  exact transparentHybridConjunctionPayloadBound_le runningCertificate
    tailCertificate _ _ hrunningResource htailResource

end FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphPartsTransparentFixedBounds
