import integration.FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedLeafStateGraphPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierParseSuccessCanonicalFrameCompleteness

/-!
# A 429-coordinate public bound for an accepted PA verifier step

This is the PA branch of the canonical successful-parse row.  Its closed-rule
and non-leaf blocks are definitionally zero; the parser, parsed-root, leaf,
and PA blocks are supplied by the accepted PA-leaf graph constructor.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedStepPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactCertificateTokenMachine
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
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
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraph
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraphPublicBounds
open FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedInductionRuleWeight
open FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedLeafStateGraphPublicBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessCanonicalFrameCompleteness

set_option maxHeartbeats 6000000 in
theorem
    exists_compactNumericVerifierAcceptedPAAxiomStepFormulaWitness_with_originalPublicBounds
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
    (hproofParser : compactListedProofNodeFieldsParser proofTokens = some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser certificateTokens =
      some certificateNode)
    (hproofTag : proofNode.1 = 1)
    (htransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, nextValues)))
    (haccept : compactAxmRuleCheck
      (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1)) = true) :
    let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
      stateWidth stateTokenCount
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    exists candidate : LO.FirstOrder.ArithmeticSentence,
    exists certificate : FoundationCompactPAAxiomCertificate.PAAxiomCertificate,
      let originalWeight :=
        compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
          proofNode.2.1 candidate certificate
      let blockBound :=
        compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
          stateBound proofWeight certificateWeight originalWeight
      originalWeight <=
          compactNumericVerifierPAAxiomLeafOriginalPayloadSourceWeightBound
            proofWeight certificateWeight /\
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
      exists_compactNumericVerifierPAAxiomLeafStateGraph_of_accepted_success_and_transition_with_originalPublicBounds
        hcurrentProof hcurrentCertificate hstateBounds
        hnextBounds.valueValueBound hproofParser hcertificateParser
        hproofTag htransitionFull hnextProof hnextCertificate
        hcurrentTaskRows hnextTaskRows hcurrentValueRows hnextValueRows
        hsourceTaskGraph htargetTaskGraph hsourceValueGraph htargetValueGraph
        hsourceTaskNonempty htaskTableWidth htaskValueBound
        hvalueTableWidth hvalueValueBound hnextStatus haccept with
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
      candidate, certificate, c, hpaGraph, _hcanonical, _htypedAccept,
      hsourceOriginalWeight,
      hparserBounds, hrootBounds,
      _hparserPointwise, _hrootPointwise, hleafBounds, hpaBounds⟩
  let originalWeight :=
    compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
      proofNode.2.1 candidate certificate
  let blockBound :=
    compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight originalWeight
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
        (compactAxmRuleCheck
          (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1)))
      paCoordinates := c }
  have hpaGraphCoordinateCounts := hpaGraph
  rw [← hcurrentTaskCount, ← hnextTaskCount,
    ← hcurrentValueCount, ← hnextValueCount] at hpaGraphCoordinateCounts
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
        (compactAxmRuleCheck
          (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1))))
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      c compactNumericVerifierParseUnusedTaskCoordinates
      compactNumericVerifierParseUnusedTaskCoordinates
      compactNumericVerifierParseUnusedTaskCoordinates
      compactNumericVerifierParseUnusedTaskSize
      compactNumericVerifierParseUnusedTaskSize
      compactNumericVerifierParseUnusedTaskSize :=
    ⟨hcurrentCoreSaved, hnextCoreSaved, hhead, hframe,
      Or.inr (Or.inr (Or.inl hpaGraphCoordinateCounts))⟩
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
        (compactAxmRuleCheck
          (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1))))
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      c compactNumericVerifierParseUnusedTaskCoordinates
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
    exact
      compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound_state_le
        stateBound proofWeight certificateWeight originalWeight
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
    · simpa only [arguments] using hleafBounds
    · intro coordinate
      simpa [arguments, compactNumericVerifierStepUnusedArguments] using
        compactNumericVerifierUnusedClosedExtraEnvironment_size_le
          blockBound coordinate
    · simpa only [arguments] using hpaBounds
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
  exact ⟨candidate, certificate, hsourceOriginalWeight,
    witness, hwitnessBounds, hparserControls⟩

#print axioms
  exists_compactNumericVerifierAcceptedPAAxiomStepFormulaWitness_with_originalPublicBounds

end FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedStepPublicBounds
