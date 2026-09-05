import integration.FoundationCompactNumericListedDirectFormulaTransformInitialParserSourceCertificate
import integration.FoundationCompactPAHybridFourConjunctionClosedGeneralBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds

/-! # Fully fixed public resource for the formula-transform initial parser source -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectFormulaTransformInitialParserSourceFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridFourConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialParserSourceCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialParserTaskAtRowsFullyFixedBounds
open FoundationCompactNumericListedDirectParserInitialFormula
open FoundationCompactNumericListedDirectParserInitialStateFullyFixedBounds
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate

private def sourceZeroValuation : Nat -> Nat := fun _ => 0

def compactFormulaTransformInitialParserSourceFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridFourConjunctionGeneralPayloadEnvelope
    (compactFormulaTransformInitialParserSourceSyntaxResource bitBound)
    (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    (parserInitialTaskCountPayloadEnvelope numericBound bitBound)
    (formulaTransformInitialParserTaskFullPayloadEnvelope numericBound
      bitBound)
    (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
      numericBound bitBound)

theorem
    compactFormulaTransformInitialParserSourcePublicCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount inputBoundary inputCount binderArity
      numericBound bitBound : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (hgraph : CompactUnifiedParserInitialStateRows tokenTable width tokenCount
      coordinates.parser inputBoundary inputCount 1 binderArity 0)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hinputCountValue : inputCount <= numericBound)
    (htasksCountValue : coordinates.parserTasksCount <= numericBound)
    (htasksFinishValue : coordinates.parserTasksFinish <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size coordinates.start <= bitBound)
    (hparserFinishSize : Nat.size coordinates.parserFinish <= bitBound)
    (hparserTokensFinishSize :
      Nat.size coordinates.parserTokensFinish <= bitBound)
    (hparserTasksFinishSize :
      Nat.size coordinates.parserTasksFinish <= bitBound)
    (hparserTokensBoundarySize :
      Nat.size coordinates.parserTokensBoundary <= bitBound)
    (hparserTokensCountSize :
      Nat.size coordinates.parserTokensCount <= bitBound)
    (hparserTasksBoundarySize :
      Nat.size coordinates.parserTasksBoundary <= bitBound)
    (hparserTasksCountSize :
      Nat.size coordinates.parserTasksCount <= bitBound)
    (hinputBoundarySize : Nat.size inputBoundary <= bitBound)
    (hinputCountSize : Nat.size inputCount <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound)
    (hnumericBoundSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformInitialParserSourcePublicCertificateOfGraph
          tokenTable width tokenCount inputBoundary inputCount binderArity
          coordinates hgraph) <=
      compactFormulaTransformInitialParserSourceFullyFixedPayloadPolynomial
        numericBound bitBound := by
  rcases hgraph with ⟨hsame, htaskCount, htask, hrunning⟩
  let sameFormula := compactAdditiveNatListSameRowsClosedFormula tokenTable
    width tokenCount inputBoundary inputCount
    coordinates.parserTokensBoundary coordinates.parserTokensCount
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm coordinates.parserTasksCount) = 1”
  let taskFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount coordinates.parserTasksBoundary coordinates.parserTasksCount
      (‘0’ : ValuationTerm) (‘1’ : ValuationTerm)
      (shortBinaryNumeralTerm binderArity) (‘0’ : ValuationTerm)
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount coordinates.parserTasksFinish
      coordinates.parserFinish
  let sameCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount inputBoundary inputCount
      coordinates.parserTokensBoundary coordinates.parserTokensCount hsame
  let countCertificate :=
    parserInitialTaskCountOneCertificate coordinates.parserTasksCount
      htaskCount
  let taskCertificate :=
    formulaTransformInitialParserTaskCertificateOfGraph tokenTable width
      tokenCount coordinates.parserTasksBoundary
      coordinates.parserTasksCount binderArity htask
  let runningCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount coordinates.parserTasksFinish
      coordinates.parserFinish hrunning
  let sameResource :=
    sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound
  let countResource :=
    parserInitialTaskCountPayloadEnvelope numericBound bitBound
  let taskResource :=
    formulaTransformInitialParserTaskFullPayloadEnvelope numericBound bitBound
  let runningResource :=
    compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
      numericBound bitBound
  let syntaxResource :=
    compactFormulaTransformInitialParserSourceSyntaxResource bitBound
  have hsameResource :
      hybridFormulaStructuralPayloadBound sameCertificate <= sameResource := by
    exact
      (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
        tokenTable width tokenCount inputBoundary inputCount
        coordinates.parserTokensBoundary coordinates.parserTokensCount
        hsame).trans
      (compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_fullyFixed
        tokenTable width tokenCount inputBoundary inputCount
        coordinates.parserTokensBoundary coordinates.parserTokensCount
        numericBound bitBound hsame hwidthValue htokenCountValue
        hinputCountValue htokenTableSize hinputBoundarySize
        hparserTokensBoundarySize hnumericBoundSize)
  have hcountResource :
      hybridFormulaStructuralPayloadBound countCertificate <= countResource :=
    parserInitialTaskCountOneCertificate_structuralPayloadBound_le_fixed
      coordinates.parserTasksCount numericBound bitBound htaskCount
      hparserTasksCountSize
  have htaskResource :
      hybridFormulaStructuralPayloadBound taskCertificate <= taskResource :=
    formulaTransformInitialParserTaskCertificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount coordinates.parserTasksBoundary
      coordinates.parserTasksCount binderArity numericBound bitBound htask
      hwidthValue htokenCountValue htasksCountValue htokenTableSize hwidthSize
      htokenCountSize hparserTasksBoundarySize hparserTasksCountSize
      hbinderAritySize
  have hrunningResource :
      hybridFormulaStructuralPayloadBound runningCertificate <=
        runningResource :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount coordinates.parserTasksFinish
      coordinates.parserFinish numericBound bitBound hwidthValue
      htasksFinishValue htokenTableSize hwidthSize htokenCountSize
      hparserTasksFinishSize hparserFinishSize hrunning
  have hfullCode :
      (binaryFormulaCode
        (sameFormula ⋏
          (countFormula ⋏ (taskFormula ⋏ runningFormula)))).length <=
        syntaxResource := by
    have hcode :=
      compactFormulaTransformInitialParserSourcePublicFormula_code_length_le
        tokenTable width tokenCount inputBoundary inputCount binderArity
        bitBound coordinates htokenTableSize hwidthSize htokenCountSize
        hstartSize hparserFinishSize hparserTokensFinishSize
        hparserTasksFinishSize hparserTokensBoundarySize
        hparserTokensCountSize hparserTasksBoundarySize
        hparserTasksCountSize hinputBoundarySize hinputCountSize
        hbinderAritySize
    rw [compactFormulaTransformInitialParserSourcePublicFormula_alignment]
      at hcode
    simpa only
      [compactFormulaTransformInitialParserSourcePublicExplicitFormula,
        sameFormula, countFormula, taskFormula, runningFormula,
        syntaxResource] using hcode
  have hfullClosed :
      (sameFormula ⋏
        (countFormula ⋏ (taskFormula ⋏ runningFormula))).freeVariables = ∅ := by
    have hclosed :=
      compactFormulaTransformInitialParserSourcePublicFormula_freeVariables_eq_empty
        tokenTable width tokenCount inputBoundary inputCount binderArity
        coordinates
    rw [compactFormulaTransformInitialParserSourcePublicFormula_alignment]
      at hclosed
    simpa only
      [compactFormulaTransformInitialParserSourcePublicExplicitFormula,
        sameFormula, countFormula, taskFormula, runningFormula] using hclosed
  let taskRunningCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction taskCertificate
      runningCertificate
  have htaskRunning :
      hybridFormulaStructuralPayloadBound taskRunningCertificate <=
        transparentHybridConjunctionPayloadEnvelope sourceZeroValuation
          taskFormula runningFormula taskResource runningResource := by
    dsimp only [taskRunningCertificate]
    exact transparentHybridConjunctionPayloadBound_le taskCertificate
      runningCertificate taskResource runningResource htaskResource
      hrunningResource
  let countTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction countCertificate
      taskRunningCertificate
  have hcountTail :
      hybridFormulaStructuralPayloadBound countTailCertificate <=
        transparentHybridConjunctionPayloadEnvelope sourceZeroValuation
          countFormula (taskFormula ⋏ runningFormula) countResource
          (transparentHybridConjunctionPayloadEnvelope sourceZeroValuation
            taskFormula runningFormula taskResource runningResource) := by
    dsimp only [countTailCertificate]
    exact transparentHybridConjunctionPayloadBound_le countCertificate
      taskRunningCertificate countResource
      (transparentHybridConjunctionPayloadEnvelope sourceZeroValuation
        taskFormula runningFormula taskResource runningResource)
      hcountResource htaskRunning
  let fullCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction sameCertificate
      countTailCertificate
  have hfull :
      hybridFormulaStructuralPayloadBound fullCertificate <=
        transparentHybridConjunctionPayloadEnvelope sourceZeroValuation
          sameFormula (countFormula ⋏ (taskFormula ⋏ runningFormula))
          sameResource
          (transparentHybridConjunctionPayloadEnvelope sourceZeroValuation
            countFormula (taskFormula ⋏ runningFormula) countResource
            (transparentHybridConjunctionPayloadEnvelope sourceZeroValuation
              taskFormula runningFormula taskResource runningResource)) := by
    dsimp only [fullCertificate]
    exact transparentHybridConjunctionPayloadBound_le sameCertificate
      countTailCertificate sameResource
      (transparentHybridConjunctionPayloadEnvelope sourceZeroValuation
        countFormula (taskFormula ⋏ runningFormula) countResource
        (transparentHybridConjunctionPayloadEnvelope sourceZeroValuation
          taskFormula runningFormula taskResource runningResource))
      hsameResource hcountTail
  have hgeneral :=
    transparentHybridFourConjunctionPayloadEnvelope_le_closedGeneral
      sourceZeroValuation sameFormula countFormula taskFormula runningFormula
      sameResource countResource taskResource runningResource syntaxResource
      (by
        unfold syntaxResource
          compactFormulaTransformInitialParserSourceSyntaxResource
        omega)
      hfullClosed hfullCode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast _
        fullCertificate) <= _
  unfold compactFormulaTransformInitialParserSourceFullyFixedPayloadPolynomial
  simpa only [hybridFormulaStructuralPayloadBound, sameFormula, countFormula,
    taskFormula, runningFormula, sameCertificate, countCertificate,
    taskCertificate, runningCertificate, sameResource, countResource,
    taskResource, runningResource, syntaxResource, taskRunningCertificate,
    countTailCertificate, fullCertificate] using hfull.trans hgeneral

end FoundationCompactNumericListedDirectFormulaTransformInitialParserSourceFullyFixedBounds
