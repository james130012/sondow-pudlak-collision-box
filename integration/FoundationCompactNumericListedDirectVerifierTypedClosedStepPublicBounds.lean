import integration.FoundationCompactNumericListedDirectVerifierClosedLeafStatePublicBounds
import integration.FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierPAAxiomLeafStatePublicBounds
import integration.FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierParseSuccessCanonicalFrameCompleteness
import integration.FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
import integration.FoundationCompactNumericListedDirectVerifierCheckedStepRow
import integration.FoundationCompactListedCertificateVerifier

/-!
# A source-bounded 429-row for a typed valid closed leaf

The successful leaf transport supplies the parser, exposed-root, and output
blocks.  The closed public state constructor attaches its real canonical rule
table, including all twenty-eight closed-extra coordinates.  The typed wrapper
derives the accepted closed-rule result from the listed certificate validity
and packages the formula witness as a checked row.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTypedClosedStepPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactPAAxiomCertificate
open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectProofRootLeafFieldSemantics
open FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierParseStateFrameRows
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierParseStateCompleteness
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportGraph
open FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportPublicBounds
open FoundationCompactNumericListedDirectVerifierClosedLeafStateGraph
open FoundationCompactNumericListedDirectVerifierClosedLeafStatePublicBounds
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafStatePublicBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessCanonicalFrameCompleteness
open FoundationCompactNumericListedDirectVerifierCheckedStepRow

def compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound
    (stateBound proofWeight certificateWeight : Nat) : Nat :=
  compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight +
    compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
      proofWeight

set_option maxHeartbeats 6000000 in
theorem
    exists_compactNumericVerifierClosedStepFormulaWitness_with_publicBounds
    {stateTable stateWidth stateTokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {currentTask : CompactNumericVerifierTask}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    {nextProofTokens nextCertificateTokens : List Nat}
    {nextTasks : List CompactNumericVerifierTask}
    {nextValues : List CompactNumericChildResult}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {proofNode : CompactNumericVerifierTask}
    {certificateNode : CompactNumericCertificateNode}
    (hframePackage : CompactNumericVerifierParseSuccessCanonicalFramePackage
      stateTable stateWidth stateTokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens currentTask restTasks
      values nextProofTokens nextCertificateTokens nextTasks nextValues
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness)
    (hstateTable : Nat.size stateTable <=
      compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser
      certificateTokens = some certificateNode)
    (hproofTag : proofNode.1 = 0)
    (htransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, nextValues))) :
    let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
      stateWidth stateTokenCount
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    let blockBound :=
      compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
    exists witness : CompactNumericVerifierStepFormulaWitness
        stateTable stateWidth stateTokenCount
        currentStart currentFinish nextStart nextFinish,
      (forall coordinate : Fin 429,
          Nat.size (witness.environment coordinate) <=
            compactNumericVerifierParseSuccessStepCoordinateSizeBound
              stateWidth stateTokenCount blockBound) /\
        CompactNumericVerifierParseSuccessParserControlBounds
          witness.environment blockBound := by
  let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
    stateWidth stateTokenCount
  let proofWeight := compactAdditiveValueWeight proofTokens
  let certificateWeight := compactAdditiveValueWeight certificateTokens
  let transportBound :=
    compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  let closedExtraBound :=
    compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
      proofWeight
  let blockBound :=
    compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  rcases hframePackage with
    ⟨hcurrentPackage, hnextPackage, hhead, hframe⟩
  have hcurrentPackageSaved := hcurrentPackage
  have hnextPackageSaved := hnextPackage
  have hcurrentBounds :=
    CompactNumericVerifierStateCanonicalCorePackage.coordinateSizeBounds
      hcurrentPackageSaved
  have hnextBounds :=
    CompactNumericVerifierStateCanonicalCorePackage.coordinateSizeBounds
      hnextPackageSaved
  rcases hcurrentPackage with
    ⟨_hcurrentStart, _hcurrentFinish,
      hcurrentProof, hcurrentCertificate,
      _hcurrentTaskLayout, hcurrentTaskRows,
      _hcurrentValueLayout, hcurrentValueRows,
      hcurrentTaskCount, hcurrentValueCount,
      hcurrentTaskTableWidth, hcurrentTaskValueBound,
      hcurrentValueTableWidth, hcurrentValueValueBound,
      _hcurrentStatus, hcurrentCore⟩
  rcases hnextPackage with
    ⟨_hnextStart, _hnextFinish,
      hnextProof, hnextCertificate,
      _hnextTaskLayout, hnextTaskRows,
      _hnextValueLayout, hnextValueRows,
      hnextTaskCount, hnextValueCount,
      hnextTaskTableWidth, hnextTaskValueBound,
      hnextValueTableWidth, hnextValueValueBound,
      _hnextStatus, hnextCore⟩
  have hcurrentCoreSaved := hcurrentCore
  have hnextCoreSaved := hnextCore
  rcases hcurrentCore with
    ⟨_hcurrentProofSlice, _hcurrentCertificateSlice,
      _hcurrentTaskStructure, hcurrentTaskGraph,
      _hcurrentTaskBoundarySizeEq, _hcurrentTaskBoundarySize,
      _hcurrentValueStructure, hcurrentValueGraph,
      _hcurrentValueBoundarySizeEq, _hcurrentValueBoundarySize,
      _hcurrentOption, _hcurrentCoreStatus⟩
  rcases hnextCore with
    ⟨_hnextProofSlice, _hnextCertificateSlice,
      _hnextTaskStructure, hnextTaskGraph,
      _hnextTaskBoundarySizeEq, _hnextTaskBoundarySize,
      _hnextValueStructure, hnextValueGraph,
      _hnextValueBoundarySizeEq, _hnextValueBoundarySize,
      _hnextOption, _hnextCoreStatus⟩
  have hstateWidth : Nat.size stateWidth <= stateBound := by
    exact natSize_le_of_le
      (width_le_stateCoreCoordinateSizeBound stateWidth stateTokenCount)
  have hstateTokenCount : Nat.size stateTokenCount <= stateBound := by
    exact natSize_le_of_le
      (tokenCount_le_stateCoreCoordinateSizeBound stateWidth stateTokenCount)
  have hstateBounds :
      CompactNumericParsePayloadSuccessSeparatedTablesStateCoordinateBounds
        stateTable stateWidth stateTokenCount
        currentCoordinates.start currentCoordinates.proofFinish
        currentCoordinates.proofFinish currentCoordinates.certificateFinish
        stateBound :=
    ⟨hstateTable, hstateWidth, hstateTokenCount,
      hcurrentBounds.start, hcurrentBounds.proofFinish,
      hcurrentBounds.proofFinish, hcurrentBounds.certificateFinish⟩
  have hsourceTaskGraph : CompactNumericVerifierTaskListRowsGraph
      stateTable stateWidth stateTokenCount currentCoordinates.taskBoundary
      (currentTask :: restTasks).length
      currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound := by
    simpa only [hcurrentTaskCount] using hcurrentTaskGraph
  have htargetTaskGraphNext : CompactNumericVerifierTaskListRowsGraph
      stateTable stateWidth stateTokenCount nextCoordinates.taskBoundary
      nextTasks.length nextSizeWitness.taskTableWidth
      nextSizeWitness.taskValueBound := by
    simpa only [hnextTaskCount] using hnextTaskGraph
  have hsourceValueGraph : CompactNumericChildResultListRowsGraph
      stateTable stateWidth stateTokenCount currentCoordinates.valueBoundary
      values.length currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hcurrentValueCount] using hcurrentValueGraph
  have htargetValueGraphNext : CompactNumericChildResultListRowsGraph
      stateTable stateWidth stateTokenCount nextCoordinates.valueBoundary
      nextValues.length nextSizeWitness.valueTableWidth
      nextSizeWitness.valueValueBound := by
    simpa only [hnextValueCount] using hnextValueGraph
  have htaskTableWidth : nextSizeWitness.taskTableWidth =
      currentSizeWitness.taskTableWidth :=
    hnextTaskTableWidth.trans hcurrentTaskTableWidth.symm
  have htaskValueBound : nextSizeWitness.taskValueBound =
      currentSizeWitness.taskValueBound :=
    hnextTaskValueBound.trans hcurrentTaskValueBound.symm
  have hvalueTableWidth : nextSizeWitness.valueTableWidth =
      currentSizeWitness.valueTableWidth :=
    hnextValueTableWidth.trans hcurrentValueTableWidth.symm
  have hvalueValueBound : nextSizeWitness.valueValueBound =
      currentSizeWitness.valueValueBound :=
    hnextValueValueBound.trans hcurrentValueValueBound.symm
  have htargetTaskGraph : CompactNumericVerifierTaskListRowsGraph
      stateTable stateWidth stateTokenCount nextCoordinates.taskBoundary
      nextTasks.length currentSizeWitness.taskTableWidth
      currentSizeWitness.taskValueBound := by
    simpa only [htaskTableWidth, htaskValueBound] using htargetTaskGraphNext
  have htargetValueGraph : CompactNumericChildResultListRowsGraph
      stateTable stateWidth stateTokenCount nextCoordinates.valueBoundary
      nextValues.length currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hvalueTableWidth, hvalueValueBound] using htargetValueGraphNext
  have hsourceTaskNonempty : 1 <= (currentTask :: restTasks).length := by
    simp
  have hnextStatus : nextCoordinates.statusTag = 0 :=
    hnextPackageSaved.statusTag_eq_zero rfl
  have htransitionFull : compactNumericNodeTransition proofNode certificateNode
      ((currentTask :: restTasks).drop 1) values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, nextValues)) := by
    simpa using htransition
  have houtputCase :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode ((currentTask :: restTasks).drop 1) values
      ((nextProofTokens, nextCertificateTokens),
        (nextTasks, nextValues))).1 htransitionFull
  have hclosedOutput :
      certificateNode.1 = 0 /\
      ((proofNode.2.2.2.2.2, certificateNode.2.2),
        ((currentTask :: restTasks).drop 1,
          (proofNode.2.1,
            compactClosedRuleCheck (proofNode.2.1, proofNode.2.2.1)) ::
              values)) =
        ((nextProofTokens, nextCertificateTokens),
          (nextTasks, nextValues)) := by
    simpa [CompactNumericNodeTransitionOutputCase, hproofTag,
      compactNumericNodeFieldsSuffix] using houtputCase
  rcases hclosedOutput with ⟨_hcertificateNodeTag, houtput⟩
  have hnextProofValue : nextProofTokens = proofNode.2.2.2.2.2 := by
    have h := congrArg
      (fun output : CompactNumericRunningPayload => output.1.1) houtput
    simpa using h.symm
  have hnextCertificateValue : nextCertificateTokens = certificateNode.2.2 := by
    have h := congrArg
      (fun output : CompactNumericRunningPayload => output.1.2) houtput
    simpa using h.symm
  have htasks : nextTasks = (currentTask :: restTasks).drop 1 := by
    have h := congrArg
      (fun output : CompactNumericRunningPayload => output.2.1) houtput
    simpa using h.symm
  have hvalues : nextValues =
      (proofNode.2.1,
        compactClosedRuleCheck (proofNode.2.1, proofNode.2.2.1)) :: values := by
    have h := congrArg
      (fun output : CompactNumericRunningPayload => output.2.2) houtput
    simpa using h.symm
  rcases
      exists_compactNumericVerifierLeafParseSuccessTransportGraph_of_success_and_transition_with_publicBounds
        hcurrentProof hcurrentCertificate hstateBounds
        hnextBounds.valueValueBound hproofParser hcertificateParser
        htransitionFull rfl rfl rfl hnextProof hnextCertificate
        hcurrentTaskRows hnextTaskRows hcurrentValueRows hnextValueRows
        hsourceTaskGraph htargetTaskGraph hsourceValueGraph htargetValueGraph
        hsourceTaskNonempty htasks hvalues hnextProofValue
        hnextCertificateValue htaskTableWidth htaskValueBound
        hvalueTableWidth hvalueValueBound hnextStatus with
    ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      rootGammaFinish, rootGammaCount, rootGammaBoundary, firstFinish, firstCount,
      secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
      rootGammaBoundarySize,
      targetStart, targetFinish, targetGammaFinish, targetGammaCount,
      targetGammaBoundary, targetBool, targetGammaBoundarySize,
      htransport, hparserBounds, hrootBounds, _hleafBounds,
      _hparserPointwise, hleafPointwise⟩
  have hsuccess := htransport.1
  rcases hsuccess.1.2.2.1.sound with
    ⟨decodedProofTokens, decodedRoot, hdecodedProofLayout,
      hdecodedRootLayout, hdecodedProof, hdecodedTag⟩
  have hdecodedProofTokensEq : decodedProofTokens = proofTokens :=
    hsuccess.1.1.natListValues_eq hcurrentProof hdecodedProofLayout
  subst decodedProofTokens
  have hdecodedRootEq : decodedRoot = proofNode :=
    Option.some.inj (hdecodedProof.symm.trans hproofParser)
  subst decodedRoot
  have hproofTagCoord : proofTag = 0 := hdecodedTag.symm.trans hproofTag
  have htagMatch := hsuccess.1.2.2.2.2
  have hcertificateTagCoord : certificateTag = 0 := by
    rw [hproofTagCoord] at htagMatch
    simpa [CompactNumericNodeTransitionTagMatch] using htagMatch
  rcases CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
      hsuccess.2 with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag,
      hgammaRows, hgammaLength, hfirstLayout, _hfirstLength,
      _hsecondLayout, _hsecondLength, _hwitnessLayout, _hwitnessLength,
      _hsuffixLayout, _hsuffixLength⟩
  have hrealizedRootEq : realizedRoot = proofNode :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hsuccess.2 hdecodedRootLayout hrealizedRoot
  subst realizedRoot
  rcases compactListedProofNodeFieldsParser_tag_zero_firstFormula
      hproofParser hproofTag with ⟨parsedFormula, hparsedFormula⟩
  have hcoreSaved := hsuccess.2
  rcases hcoreSaved with
    ⟨_hrootTagCell, hgammaStructureRaw, _hgammaRowsRaw,
      hgammaSizeEqRaw, hgammaSizeRaw,
      _hfirstSlice, _hsecondSlice, _hwitnessSlice, _hsuffixSlice⟩
  have hgammaLength' : proofNode.2.1.length = rootGammaCount := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using hgammaLength
  have hgammaStructure : CompactAdditiveStructuredListLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) proofNode.2.1.length
        rootGammaFinish rootGammaBoundary := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf, hgammaLength'] using
      hgammaStructureRaw
  have hgammaSizeEq : rootGammaBoundarySize = Nat.size rootGammaBoundary := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using hgammaSizeEqRaw
  have hgammaSize :
      rootGammaBoundarySize <= (rootGammaCount + 1) * proofTokenCount := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using hgammaSizeRaw
  have hgammaBoundaryBound : Nat.size rootGammaBoundary <=
      (proofNode.2.1.length + 1) * proofTokenCount := by
    rw [hgammaLength', <- hgammaSizeEq]
    exact hgammaSize
  have hrootGammaLayout : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) rootGammaFinish proofNode.2.1 :=
    ⟨rootGammaBoundary, hgammaStructure, hgammaRows, hgammaBoundaryBound⟩
  have hrootFormulaLayout : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount rootGammaFinish firstFinish
        (compactArithmeticFormulaTokens parsedFormula) := by
    simpa [hparsedFormula, compactNumericVerifierTaskRowCoordinatesOf] using
      hfirstLayout
  have hsourceWeights :=
    compactListedProofNodeFieldsParser_closedLeaf_sourceWeights hproofParser
  rcases
      exists_compactNumericVerifierClosedLeafStateGraph_with_publicBounds_of_transport
        proofNode.2.1 parsedFormula
        (by simpa [hparsedFormula] using htransport)
        hrootGammaLayout hrootFormulaLayout
        hproofTagCoord hcertificateTagCoord hsourceWeights.1
        (by simpa [hparsedFormula] using hsourceWeights.2) with
    ⟨ruleTable, ruleWidth, ruleTokenCount,
      ruleGammaStart, ruleGammaFinish, ruleGammaBoundary,
      ruleGammaBoundarySize,
      ruleFormulaStart, ruleFormulaFinish, ruleFormulaBoundary,
      ruleFormulaBoundarySize,
      ruleNegatedStart, ruleNegatedFinish, ruleNegatedBoundary,
      ruleNegatedBoundarySize,
      ruleStateBoundary,
      ruleEmptyStart, ruleEmptyFinish, ruleEmptyBoundary,
      ruleEmptyBoundarySize,
      ruleTableWidth, ruleValueBound,
      hclosedGraph, _hcanonicalBounds, _hclosedCoordinateBounds,
      hclosedPointwise⟩
  let arguments : CompactNumericVerifierStepArguments :=
    { compactNumericVerifierStepUnusedArguments with
      taskCoordinates := taskCoordinates
      taskSizeWitness := taskSizeWitness
      proofTable := proofTable
      proofWidth := proofWidth
      proofTokenCount := proofTokenCount
      proofInputStart := proofInputStart
      proofInputFinish := proofInputFinish
      rootStart := rootStart
      rootFinish := rootFinish
      proofTag := proofTag
      proofEndpointBound := proofEndpointBound
      certificateTable := certificateTable
      certificateWidth := certificateWidth
      certificateTokenCount := certificateTokenCount
      certificateInputStart := certificateInputStart
      certificateInputFinish := certificateInputFinish
      axiomStart := axiomStart
      axiomFinish := axiomFinish
      formulaStart := formulaStart
      formulaFinish := formulaFinish
      suffixStart := suffixStart
      suffixFinish := suffixFinish
      certificateTag := certificateTag
      certificateEndpointBound := certificateEndpointBound
      rootGammaFinish := rootGammaFinish
      rootGammaCount := rootGammaCount
      rootGammaBoundary := rootGammaBoundary
      firstFinish := firstFinish
      firstCount := firstCount
      secondFinish := secondFinish
      secondCount := secondCount
      witnessFinish := witnessFinish
      witnessCount := witnessCount
      suffixCount := suffixCount
      rootGammaBoundarySize := rootGammaBoundarySize
      targetStart := targetStart
      targetFinish := targetFinish
      targetGammaFinish := targetGammaFinish
      targetGammaCount := targetGammaCount
      targetGammaBoundary := targetGammaBoundary
      targetBool := targetBool
      targetGammaBoundarySize := targetGammaBoundarySize
      resultBool := compactAdditiveBoolTag
        (compactClosedRuleCheck
          (proofNode.2.1, compactArithmeticFormulaTokens parsedFormula))
      ruleTable := ruleTable
      ruleWidth := ruleWidth
      ruleTokenCount := ruleTokenCount
      ruleProofTag := 0
      ruleCertificateTag := 0
      ruleGammaStart := ruleGammaStart
      ruleGammaFinish := ruleGammaFinish
      ruleGammaBoundary := ruleGammaBoundary
      ruleGammaCount := proofNode.2.1.length
      ruleGammaBoundarySize := ruleGammaBoundarySize
      ruleFormulaStart := ruleFormulaStart
      ruleFormulaFinish := ruleFormulaFinish
      ruleFormulaBoundary := ruleFormulaBoundary
      ruleFormulaCount := (compactArithmeticFormulaTokens parsedFormula).length
      ruleFormulaBoundarySize := ruleFormulaBoundarySize
      ruleNegatedStart := ruleNegatedStart
      ruleNegatedFinish := ruleNegatedFinish
      ruleNegatedBoundary := ruleNegatedBoundary
      ruleNegatedCount :=
        (compactArithmeticFormulaTokens (∼parsedFormula)).length
      ruleNegatedBoundarySize := ruleNegatedBoundarySize
      ruleStateBoundary := ruleStateBoundary
      ruleStateCount :=
        compactSyntaxRunFuelBound
            (compactArithmeticFormulaTokens parsedFormula) + 1
      ruleEmptyStart := ruleEmptyStart
      ruleEmptyFinish := ruleEmptyFinish
      ruleEmptyBoundary := ruleEmptyBoundary
      ruleEmptyBoundarySize := ruleEmptyBoundarySize
      ruleTableWidth := ruleTableWidth
      ruleValueBound := ruleValueBound }
  have hclosedGraphCoordinateCounts := hclosedGraph
  have hcurrentTaskCount' :
      currentCoordinates.taskCount = restTasks.length + 1 := by
    simpa only [List.length_cons, Nat.succ_eq_add_one] using
      hcurrentTaskCount
  have hnextTaskCount' :
      nextCoordinates.taskCount = nextTasks.length := by
    simpa only using hnextTaskCount
  have hcurrentValueCount' :
      currentCoordinates.valueCount = values.length := by
    simpa only using hcurrentValueCount
  have hnextValueCount' :
      nextCoordinates.valueCount = nextValues.length := by
    simpa only using hnextValueCount
  rw [← hcurrentTaskCount', ← hnextTaskCount',
    ← hcurrentValueCount', ← hnextValueCount'] at hclosedGraphCoordinateCounts
  have hparseSuccess : CompactNumericVerifierParseSuccessStateGraph
      stateTable stateWidth stateTokenCount currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize
      (compactAdditiveBoolTag
        (compactClosedRuleCheck
          (proofNode.2.1, compactArithmeticFormulaTokens parsedFormula)))
      ruleTable ruleWidth ruleTokenCount 0 0
      ruleGammaStart ruleGammaFinish ruleGammaBoundary proofNode.2.1.length
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary
        (compactArithmeticFormulaTokens parsedFormula).length
        ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary
        (compactArithmeticFormulaTokens (∼parsedFormula)).length
        ruleNegatedBoundarySize
      ruleStateBoundary
        (compactSyntaxRunFuelBound
          (compactArithmeticFormulaTokens parsedFormula) + 1)
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound
      compactNumericVerifierParseUnusedPACoordinates
      compactNumericVerifierParseUnusedTaskCoordinates
      compactNumericVerifierParseUnusedTaskCoordinates
      compactNumericVerifierParseUnusedTaskCoordinates
      compactNumericVerifierParseUnusedTaskSize
      compactNumericVerifierParseUnusedTaskSize
      compactNumericVerifierParseUnusedTaskSize :=
    ⟨hcurrentCoreSaved, hnextCoreSaved, hhead, hframe,
      Or.inr (Or.inl hclosedGraphCoordinateCounts)⟩
  have hparseGraph : CompactNumericVerifierParseStateGraph
      stateTable stateWidth stateTokenCount currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize
      (compactAdditiveBoolTag
        (compactClosedRuleCheck
          (proofNode.2.1, compactArithmeticFormulaTokens parsedFormula)))
      ruleTable ruleWidth ruleTokenCount 0 0
      ruleGammaStart ruleGammaFinish ruleGammaBoundary proofNode.2.1.length
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary
        (compactArithmeticFormulaTokens parsedFormula).length
        ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary
        (compactArithmeticFormulaTokens (∼parsedFormula)).length
        ruleNegatedBoundarySize
      ruleStateBoundary
        (compactSyntaxRunFuelBound
          (compactArithmeticFormulaTokens parsedFormula) + 1)
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound
      compactNumericVerifierParseUnusedPACoordinates
      compactNumericVerifierParseUnusedTaskCoordinates
      compactNumericVerifierParseUnusedTaskCoordinates
      compactNumericVerifierParseUnusedTaskCoordinates
      compactNumericVerifierParseUnusedTaskSize
      compactNumericVerifierParseUnusedTaskSize
      compactNumericVerifierParseUnusedTaskSize :=
    Or.inr hparseSuccess
  have hargumentsGraph : arguments.Graph
      stateTable stateWidth stateTokenCount currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness := by
    dsimp only [CompactNumericVerifierStepArguments.Graph, arguments]
    exact Or.inr (Or.inr (Or.inl hparseGraph))
  have htransportToBlock : transportBound <= blockBound := by
    dsimp only [transportBound, blockBound,
      compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound]
    omega
  have hclosedExtraToBlock : closedExtraBound <= blockBound := by
    dsimp only [closedExtraBound, blockBound,
      compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound]
    omega
  have hstateToBlock : stateBound <= blockBound := by
    dsimp only [blockBound,
      compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound,
      compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound,
      compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound,
      compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound]
    omega
  have hvalueBound : Nat.size currentSizeWitness.taskValueBound <= blockBound :=
    hcurrentBounds.taskValueBound.trans hstateToBlock
  have hparserBoundsBlock :
      CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        blockBound :=
    CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds.mono
      hparserBounds htransportToBlock
  have hrootBoundsBlock :
      CompactNumericParsePayloadSuccessExposedTaskCoordinateBounds
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize blockBound :=
    { gammaFinish := hrootBounds.gammaFinish.trans htransportToBlock
      gammaCount := hrootBounds.gammaCount.trans htransportToBlock
      gammaBoundary := hrootBounds.gammaBoundary.trans htransportToBlock
      firstFinish := hrootBounds.firstFinish.trans htransportToBlock
      firstCount := hrootBounds.firstCount.trans htransportToBlock
      secondFinish := hrootBounds.secondFinish.trans htransportToBlock
      secondCount := hrootBounds.secondCount.trans htransportToBlock
      witnessFinish := hrootBounds.witnessFinish.trans htransportToBlock
      witnessCount := hrootBounds.witnessCount.trans htransportToBlock
      suffixCount := hrootBounds.suffixCount.trans htransportToBlock
      gammaBoundarySize :=
        hrootBounds.gammaBoundarySize.trans htransportToBlock }
  have hblocks : CompactNumericVerifierParseSuccessArgumentBlockBounds
      arguments blockBound := by
    refine
      { parser := ?_
        parsedRoot := ?_
        leafOutput := ?_
        closedExtra := ?_
        pa := ?_
        nonLeaf := ?_ }
    · simpa only [arguments] using hparserBoundsBlock
    · simpa only [arguments] using hrootBoundsBlock
    · intro coordinate
      simpa [arguments, hparsedFormula] using
        (hleafPointwise coordinate).trans htransportToBlock
    · intro coordinate
      simpa only [arguments] using
        (hclosedPointwise coordinate).trans hclosedExtraToBlock
    · intro coordinate
      simpa [arguments, compactNumericVerifierStepUnusedArguments,
        compactNumericVerifierParseUnusedPACoordinates] using
        compactNumericVerifierParseUnusedPACoordinates_size_le
          blockBound coordinate
    · intro coordinate
      simpa [arguments, compactNumericVerifierStepUnusedArguments,
        compactNumericVerifierParseUnusedTaskCoordinates,
        compactNumericVerifierParseUnusedTaskSize] using
        compactNumericVerifierUnusedNonLeafEnvironment_size_le
          blockBound coordinate
  rcases
      exists_compactNumericVerifierParseSuccessStepFormulaWitness_with_publicSizeBound
        arguments hstateTable hcurrentPackageSaved hnextPackageSaved
        hargumentsGraph hhead hvalueBound hblocks with
    ⟨witness, hwitnessBounds, hparserControls⟩
  exact ⟨witness, hwitnessBounds, hparserControls⟩

#print axioms
  exists_compactNumericVerifierClosedStepFormulaWitness_with_publicBounds

set_option maxHeartbeats 6000000 in
theorem
    exists_compactNumericVerifierTypedClosedStepFormulaWitness_with_sourcePublicBounds
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.closed Gamma formula) .leaf) :
    let tree : ListedCheckedPAProofTree := .closed Gamma formula
    let structuralCertificate : StructuralValidityCertificate := .leaf
    let proofTokens := compactListedProofTokens tree ++ proofSuffix
    let certificateTokens :=
      compactStructuralCertificateTokens structuralCertificate ++
        certificateSuffix
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofSuffix, certificateSuffix),
        (restTasks, (proofNode.2.1, true) :: values)), none)
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let tokens := currentTokens ++ nextTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let stateTable := compactFixedWidthTableCode width tokens
    let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
      width tokens.length
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    let blockBound :=
      compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
    exists witness : CompactNumericVerifierStepFormulaWitness
        stateTable width tokens.length
        0 currentTokens.length currentTokens.length
        (currentTokens.length + nextTokens.length),
      (forall coordinate : Fin 429,
          Nat.size (witness.environment coordinate) <=
            compactNumericVerifierParseSuccessStepCoordinateSizeBound
              width tokens.length blockBound) /\
        CompactNumericVerifierParseSuccessParserControlBounds
          witness.environment blockBound := by
  let tree : ListedCheckedPAProofTree := .closed Gamma formula
  let structuralCertificate : StructuralValidityCertificate := .leaf
  let proofTokens := compactListedProofTokens tree ++ proofSuffix
  let certificateTokens :=
    compactStructuralCertificateTokens structuralCertificate ++
      certificateSuffix
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected structuralCertificate
      certificateSuffix
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens),
      (compactNumericParseTask :: restTasks, values)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofSuffix, certificateSuffix),
      (restTasks, (proofNode.2.1, true) :: values)), none)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let stateTable := compactFixedWidthTableCode width tokens
  let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
    width tokens.length
  let proofWeight := compactAdditiveValueWeight proofTokens
  let certificateWeight := compactAdditiveValueWeight certificateTokens
  let blockBound :=
    compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  have hpairRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState []
  have hpair :
      CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length 0 currentTokens.length currentState /\
        CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length currentTokens.length
            (currentTokens.length + nextTokens.length) nextState := by
    simpa only [stateTable, width, tokens, currentTokens, nextTokens,
      List.append_nil] using hpairRaw
  rcases hpair with ⟨hcurrentLayout, hnextLayout⟩
  rcases
      CompactNumericVerifierParseSuccessCanonicalFramePackage.exists_of_layouts
        hcurrentLayout hnextLayout (by rfl) with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, hframePackage⟩
  have hstateTable : Nat.size stateTable <= stateBound := by
    exact (compactFixedWidthTableCode_size_le width tokens).trans
      (tokenTableArea_le_stateCoreCoordinateSizeBound width tokens.length)
  have hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode := by
    simp only [proofTokens, proofNode, tree,
      compactListedProofNodeFieldsParser_canonical_append]
  have hcertificateParser :
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode := by
    simp only [certificateTokens, certificateNode, structuralCertificate,
      compactStructuralCertificateNodeParser_canonical_append]
  have hproofTag : proofNode.1 = 0 := by
    simp [proofNode, tree, compactListedProofNodeExpectedFields]
  have hcanonicalAccept : compactClosedRuleCheck
      (FoundationCompactNumericFormulaListChecks.arithmeticPropositionTokenValues
          Gamma,
        FoundationCompactNumericFormulaListChecks.arithmeticPropositionTokenValue
          formula) = true := by
    have htrace :
        (listedCertificateValidTrace (.closed Gamma formula) .leaf).1 = true :=
      (listedCertificateValidTrace_result_eq_true_iff
        (.closed Gamma formula) .leaf).2 hvalid
    exact (compactClosedRuleCheck_canonical Gamma formula).trans htrace
  have haccept : compactClosedRuleCheck
      (proofNode.2.1, proofNode.2.2.1) = true := by
    simpa [proofNode, tree, compactListedProofNodeExpectedFields] using
      hcanonicalAccept
  have htransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((proofSuffix, certificateSuffix),
          (restTasks, (proofNode.2.1, true) :: values)) := by
    simp [proofNode, certificateNode, tree, structuralCertificate,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeTransition, compactNumericNodeFieldsSuffix,
      hcanonicalAccept, haccept]
  exact
    exists_compactNumericVerifierClosedStepFormulaWitness_with_publicBounds
      hframePackage hstateTable hproofParser hcertificateParser
      hproofTag htransition

#print axioms
  exists_compactNumericVerifierTypedClosedStepFormulaWitness_with_sourcePublicBounds

set_option maxHeartbeats 6000000 in
theorem
    exists_compactNumericVerifierTypedClosedCheckedStepRow_with_sourcePublicBounds
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.closed Gamma formula) .leaf) :
    let tree : ListedCheckedPAProofTree := .closed Gamma formula
    let structuralCertificate : StructuralValidityCertificate := .leaf
    let proofTokens := compactListedProofTokens tree ++ proofSuffix
    let certificateTokens :=
      compactStructuralCertificateTokens structuralCertificate ++
        certificateSuffix
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofSuffix, certificateSuffix),
        (restTasks, (proofNode.2.1, true) :: values)), none)
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let tokens := currentTokens ++ nextTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let stateTable := compactFixedWidthTableCode width tokens
    let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
      width tokens.length
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    let blockBound :=
      compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
    let coordinateBound :=
      compactNumericVerifierParseSuccessStepCoordinateSizeBound
        width tokens.length blockBound
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = currentState /\
        row.nextState = nextState /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <= coordinateBound := by
  let tree : ListedCheckedPAProofTree := .closed Gamma formula
  let structuralCertificate : StructuralValidityCertificate := .leaf
  let proofTokens := compactListedProofTokens tree ++ proofSuffix
  let certificateTokens :=
    compactStructuralCertificateTokens structuralCertificate ++
      certificateSuffix
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens),
      (compactNumericParseTask :: restTasks, values)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofSuffix, certificateSuffix),
      (restTasks, (proofNode.2.1, true) :: values)), none)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let stateTable := compactFixedWidthTableCode width tokens
  let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
    width tokens.length
  let proofWeight := compactAdditiveValueWeight proofTokens
  let certificateWeight := compactAdditiveValueWeight certificateTokens
  let blockBound :=
    compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  let coordinateBound :=
    compactNumericVerifierParseSuccessStepCoordinateSizeBound
      width tokens.length blockBound
  rcases
      exists_compactNumericVerifierTypedClosedStepFormulaWitness_with_sourcePublicBounds
        Gamma formula proofSuffix certificateSuffix restTasks values hvalid with
    ⟨witness, hwitness, _hparserControls⟩
  have hpairRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState []
  have hpair :
      CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length 0 currentTokens.length currentState /\
        CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length currentTokens.length
            (currentTokens.length + nextTokens.length) nextState := by
    simpa only [stateTable, width, tokens, currentTokens, nextTokens,
      List.append_nil] using hpairRaw
  rcases hpair with ⟨hcurrentLayout, hnextLayout⟩
  let row : CompactNumericVerifierCheckedStepRow :=
    { environment := witness.environment
      currentState := currentState
      nextState := nextState
      currentLayout := by
        simpa only [witness.stateTable_eq, witness.stateWidth_eq,
          witness.stateTokenCount_eq, witness.currentStart_eq,
          witness.currentFinish_eq] using hcurrentLayout
      nextLayout := by
        simpa only [witness.stateTable_eq, witness.stateWidth_eq,
          witness.stateTokenCount_eq, witness.nextStart_eq,
          witness.nextFinish_eq] using hnextLayout
      formula := witness.formula }
  exact ⟨row, rfl, rfl, fun coordinate => hwitness coordinate⟩

#print axioms
  exists_compactNumericVerifierTypedClosedCheckedStepRow_with_sourcePublicBounds

end FoundationCompactNumericListedDirectVerifierTypedClosedStepPublicBounds
