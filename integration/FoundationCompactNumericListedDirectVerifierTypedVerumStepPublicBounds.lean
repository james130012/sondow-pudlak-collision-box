import integration.FoundationCompactNumericListedDirectVerifierVerumLeafStatePublicBounds
import integration.FoundationCompactNumericListedDirectVerifierPAAxiomLeafStatePublicBounds
import integration.FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierParseSuccessCanonicalFrameCompleteness
import integration.FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
import integration.FoundationCompactNumericListedDirectVerifierCheckedStepRow
import integration.FoundationCompactListedCertificateVerifier

/-!
# A source-bounded 429-row for a typed valid verum leaf

The real verum leaf state graph supplies the parser, exposed-root, and leaf
blocks.  The closed, PA, and non-leaf blocks are their canonical zero values.
The typed wrapper derives the accepted transition from
`listedCertificateValid` and packages the resulting formula witness as a
checked row.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTypedVerumStepPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
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
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
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
open FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportPublicBounds
open FoundationCompactNumericListedDirectVerifierVerumLeafStateGraph
open FoundationCompactNumericListedDirectVerifierVerumLeafStatePublicBounds
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafStatePublicBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessCanonicalFrameCompleteness
open FoundationCompactNumericListedDirectVerifierCheckedStepRow

set_option maxHeartbeats 6000000 in
theorem
    exists_compactNumericVerifierVerumStepFormulaWitness_with_publicBounds
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
    (hproofTag : proofNode.1 = 2)
    (htransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, nextValues))) :
    let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
      stateWidth stateTokenCount
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    let blockBound :=
      compactNumericVerifierVerumLeafStatePublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
    ∃ witness : CompactNumericVerifierStepFormulaWitness
        stateTable stateWidth stateTokenCount
        currentStart currentFinish nextStart nextFinish,
      (∀ coordinate : Fin 429,
          Nat.size (witness.environment coordinate) <=
            compactNumericVerifierParseSuccessStepCoordinateSizeBound
              stateWidth stateTokenCount blockBound) ∧
        CompactNumericVerifierParseSuccessParserControlBounds
          witness.environment blockBound := by
  let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
    stateWidth stateTokenCount
  let proofWeight := compactAdditiveValueWeight proofTokens
  let certificateWeight := compactAdditiveValueWeight certificateTokens
  let blockBound :=
    compactNumericVerifierVerumLeafStatePublicCoordinateSizeBound
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
  rcases
      exists_compactNumericVerifierVerumLeafStateGraph_of_success_and_transition_with_publicBounds
        hcurrentProof hcurrentCertificate hstateBounds
        hnextBounds.valueValueBound hproofParser hcertificateParser
        hproofTag htransitionFull hnextProof hnextCertificate
        hcurrentTaskRows hnextTaskRows hcurrentValueRows hnextValueRows
        hsourceTaskGraph htargetTaskGraph hsourceValueGraph htargetValueGraph
        hsourceTaskNonempty htaskTableWidth htaskValueBound
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
      hverumGraph, hparserBounds, hrootBounds, hleafBounds,
      _hparserPointwise, hleafPointwise⟩
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
        (compactVerumRuleCheck proofNode.2.1) }
  have hverumGraphCoordinateCounts := hverumGraph
  rw [← hcurrentTaskCount, ← hnextTaskCount,
    ← hcurrentValueCount, ← hnextValueCount] at hverumGraphCoordinateCounts
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
      (compactAdditiveBoolTag (compactVerumRuleCheck proofNode.2.1))
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      compactNumericVerifierParseUnusedPACoordinates
      compactNumericVerifierParseUnusedTaskCoordinates
      compactNumericVerifierParseUnusedTaskCoordinates
      compactNumericVerifierParseUnusedTaskCoordinates
      compactNumericVerifierParseUnusedTaskSize
      compactNumericVerifierParseUnusedTaskSize
      compactNumericVerifierParseUnusedTaskSize :=
    ⟨hcurrentCoreSaved, hnextCoreSaved, hhead, hframe,
      Or.inl hverumGraphCoordinateCounts⟩
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
      (compactAdditiveBoolTag (compactVerumRuleCheck proofNode.2.1))
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
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
  have hstateToBlock : stateBound <= blockBound := by
    dsimp only [blockBound,
      compactNumericVerifierVerumLeafStatePublicCoordinateSizeBound,
      compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound,
      compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound,
      compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound]
    omega
  have hvalueBound : Nat.size currentSizeWitness.taskValueBound <= blockBound :=
    hcurrentBounds.taskValueBound.trans hstateToBlock
  have hblocks : CompactNumericVerifierParseSuccessArgumentBlockBounds
      arguments blockBound := by
    refine
      { parser := ?_
        parsedRoot := ?_
        leafOutput := ?_
        closedExtra := ?_
        pa := ?_
        nonLeaf := ?_ }
    · simpa only [arguments] using hparserBounds
    · simpa only [arguments] using hrootBounds
    · simpa only [arguments] using hleafPointwise
    · intro coordinate
      simpa [arguments, compactNumericVerifierStepUnusedArguments] using
        compactNumericVerifierUnusedClosedExtraEnvironment_size_le
          blockBound coordinate
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
  exists_compactNumericVerifierVerumStepFormulaWitness_with_publicBounds

set_option maxHeartbeats 6000000 in
theorem
    exists_compactNumericVerifierTypedVerumStepFormulaWitness_with_sourcePublicBounds
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.verum Gamma) .leaf) :
    let tree : ListedCheckedPAProofTree := .verum Gamma
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
      compactNumericVerifierVerumLeafStatePublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
    ∃ witness : CompactNumericVerifierStepFormulaWitness
        stateTable width tokens.length
        0 currentTokens.length currentTokens.length
        (currentTokens.length + nextTokens.length),
      (∀ coordinate : Fin 429,
          Nat.size (witness.environment coordinate) <=
            compactNumericVerifierParseSuccessStepCoordinateSizeBound
              width tokens.length blockBound) ∧
        CompactNumericVerifierParseSuccessParserControlBounds
          witness.environment blockBound := by
  let tree : ListedCheckedPAProofTree := .verum Gamma
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
    compactNumericVerifierVerumLeafStatePublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  have hpairRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState []
  have hpair :
      CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length 0 currentTokens.length currentState ∧
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
  have hproofTag : proofNode.1 = 2 := by
    simp [proofNode, tree, compactListedProofNodeExpectedFields]
  have hcanonicalAccept : compactVerumRuleCheck
      (FoundationCompactNumericFormulaListChecks.arithmeticPropositionTokenValues
        Gamma) = true := by
    have htrace :
        (listedCertificateValidTrace (.verum Gamma) .leaf).1 = true :=
      (listedCertificateValidTrace_result_eq_true_iff
        (.verum Gamma) .leaf).2 hvalid
    exact (compactVerumRuleCheck_canonical Gamma).trans htrace
  have haccept : compactVerumRuleCheck proofNode.2.1 = true := by
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
      hcanonicalAccept]
  exact
    exists_compactNumericVerifierVerumStepFormulaWitness_with_publicBounds
      hframePackage hstateTable hproofParser hcertificateParser
      hproofTag htransition

#print axioms
  exists_compactNumericVerifierTypedVerumStepFormulaWitness_with_sourcePublicBounds

set_option maxHeartbeats 6000000 in
theorem
    exists_compactNumericVerifierTypedVerumCheckedStepRow_with_sourcePublicBounds
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.verum Gamma) .leaf) :
    let tree : ListedCheckedPAProofTree := .verum Gamma
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
      compactNumericVerifierVerumLeafStatePublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
    let coordinateBound :=
      compactNumericVerifierParseSuccessStepCoordinateSizeBound
        width tokens.length blockBound
    ∃ row : CompactNumericVerifierCheckedStepRow,
      row.currentState = currentState ∧
        row.nextState = nextState ∧
        ∀ coordinate : Fin 429,
          Nat.size (row.environment coordinate) <= coordinateBound := by
  let tree : ListedCheckedPAProofTree := .verum Gamma
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
    compactNumericVerifierVerumLeafStatePublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  let coordinateBound :=
    compactNumericVerifierParseSuccessStepCoordinateSizeBound
      width tokens.length blockBound
  rcases
      exists_compactNumericVerifierTypedVerumStepFormulaWitness_with_sourcePublicBounds
        Gamma proofSuffix certificateSuffix restTasks values hvalid with
    ⟨witness, hwitness, _hparserControls⟩
  have hpairRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState []
  have hpair :
      CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length 0 currentTokens.length currentState ∧
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
  exists_compactNumericVerifierTypedVerumCheckedStepRow_with_sourcePublicBounds

end FoundationCompactNumericListedDirectVerifierTypedVerumStepPublicBounds
