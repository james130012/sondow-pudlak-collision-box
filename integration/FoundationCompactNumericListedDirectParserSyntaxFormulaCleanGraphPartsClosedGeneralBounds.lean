import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphPartsTransparentFixedBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-! # Closed-general fixed resources for clean syntax-formula parser parts -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphPartsClosedGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaOuterSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphTailFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphTailClosedGeneralBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphPartsTransparentFixedBounds

def cleanParserSyntaxFormulaPartsCodePolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial numericBound
      bitBound +
    cleanParserSyntaxFormulaTailPayloadPolynomial tokenCount numericBound
      bitBound +
    (binaryNatCode 4).length + 1

def cleanParserSyntaxFormulaPartsPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (cleanParserSyntaxFormulaPartsCodePolynomial tokenCount numericBound bitBound)
    (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial numericBound
      bitBound)
    (cleanParserSyntaxFormulaTailPayloadPolynomial tokenCount numericBound
      bitBound)

theorem
    compactUnifiedParserSyntaxFormulaCleanPartsCertificateOfGraph_structuralPayloadBound_le_fullyFixed
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
      cleanParserSyntaxFormulaPartsPayloadPolynomial tokenCount numericBound
        bitBound := by
  let runningCertificate :=
    compactUnifiedParserSyntaxFormulaCleanRunningCertificateOfGraph tokenTable
      width tokenCount current next binderArity witness hgraph
  let tailCertificate :=
    compactUnifiedParserSyntaxFormulaCleanTailCertificateOfGraph tokenTable
      width tokenCount current next binderArity witness hgraph
  have htransparent :=
    compactUnifiedParserSyntaxFormulaCleanPartsCertificateOfGraph_structuralPayloadBound_le_transparentFixed
      tokenTable width tokenCount current next binderArity numericBound bitBound
      witness hgraph hwidth htokenCount hcurrentValue hnextValue
      htokenTableSize hcurrentSize hnextSize htailBoundarySize
      hbinderAritySize hrelationAritySize hrelationCodeSize htagSize
      hnumericSize hbitPositive
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
  have hrunningClosed :
      (compactBinaryNatRunningStatusSliceClosedFormula tokenTable width
        tokenCount current.tasksFinish current.finish).freeVariables = ∅ := by
    simpa only [compactBinaryNatRunningStatusSliceClosedFormula] using
      fiveShortNumeralRewritingFormula_freeVariables_eq_empty
        compactBinaryNatRunningStatusSliceDef.val tokenTable width tokenCount
        current.tasksFinish current.finish
  have htailClosed :
      (cleanParserSyntaxFormulaTailFormula tokenTable width tokenCount current
        next binderArity witness).freeVariables = ∅ := by
    have huncons :=
      parserSyntaxFormulaUnconsGraphFormula_freeVariables_eq_empty tokenTable
        width tokenCount current.tasksBoundary current.tasksCount
        witness.tailBoundary witness.tailCount witness.tailBoundarySize
        binderArity
    have hbranch :=
      compactUnifiedParserSyntaxFormulaBranchExplicitFormula_freeVariables_eq_empty_fullyFixed
        tokenTable width tokenCount current next binderArity witness
    unfold cleanParserSyntaxFormulaTailFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and, huncons, hbranch]
    simp
  have hrunningCode :
      (binaryFormulaCode
        (compactBinaryNatRunningStatusSliceClosedFormula tokenTable width
          tokenCount current.tasksFinish current.finish)).length <=
        compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
          numericBound bitBound :=
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      runningCertificate).trans hrunningResource
  have htailCode :
      (binaryFormulaCode
        (cleanParserSyntaxFormulaTailFormula tokenTable width tokenCount current
          next binderArity witness)).length <=
        cleanParserSyntaxFormulaTailPayloadPolynomial tokenCount numericBound
          bitBound :=
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      tailCertificate).trans htailResource
  have hsyntaxPositive :
      1 <= cleanParserSyntaxFormulaPartsCodePolynomial tokenCount numericBound
        bitBound := by
    unfold cleanParserSyntaxFormulaPartsCodePolynomial
    omega
  have hrunningCodeGlobal :
      (binaryFormulaCode
        (compactBinaryNatRunningStatusSliceClosedFormula tokenTable width
          tokenCount current.tasksFinish current.finish)).length <=
        cleanParserSyntaxFormulaPartsCodePolynomial tokenCount numericBound
          bitBound :=
    hrunningCode.trans (by
      unfold cleanParserSyntaxFormulaPartsCodePolynomial
      omega)
  have htailCodeGlobal :
      (binaryFormulaCode
        (cleanParserSyntaxFormulaTailFormula tokenTable width tokenCount current
          next binderArity witness)).length <=
        cleanParserSyntaxFormulaPartsCodePolynomial tokenCount numericBound
          bitBound :=
    htailCode.trans (by
      unfold cleanParserSyntaxFormulaPartsCodePolynomial
      omega)
  have htotalCode :
      (binaryFormulaCode
        (compactBinaryNatRunningStatusSliceClosedFormula tokenTable width
            tokenCount current.tasksFinish current.finish ⋏
          cleanParserSyntaxFormulaTailFormula tokenTable width tokenCount
            current next binderArity witness)).length <=
        cleanParserSyntaxFormulaPartsCodePolynomial tokenCount numericBound
          bitBound := by
    simp only [binaryFormulaCode, List.length_append]
    unfold cleanParserSyntaxFormulaPartsCodePolynomial
    omega
  have henvelope :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.zeroValuation
      (compactBinaryNatRunningStatusSliceClosedFormula tokenTable width
        tokenCount current.tasksFinish current.finish)
      (cleanParserSyntaxFormulaTailFormula tokenTable width tokenCount current
        next binderArity witness)
      (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
        numericBound bitBound)
      (cleanParserSyntaxFormulaTailPayloadPolynomial tokenCount numericBound
        bitBound)
      (cleanParserSyntaxFormulaPartsCodePolynomial tokenCount numericBound
        bitBound)
      hsyntaxPositive hrunningClosed htailClosed hrunningCodeGlobal
      htailCodeGlobal htotalCode
  unfold cleanParserSyntaxFormulaPartsTransparentEnvelope at htransparent
  unfold cleanParserSyntaxFormulaPartsPayloadPolynomial
  exact Nat.le_trans htransparent henvelope

end FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphPartsClosedGeneralBounds
