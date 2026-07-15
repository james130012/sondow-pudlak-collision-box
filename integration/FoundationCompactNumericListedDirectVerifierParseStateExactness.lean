import integration.FoundationCompactNumericListedDirectVerifierParseStateFormula
import integration.FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransitionExactness
import integration.FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateGraph
import integration.FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization

/-!
# Exact semantics of the complete verifier parse-state graph

Every satisfying assignment of the bounded parse graph realizes two typed
states related by the public executable verifier step.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseStateExactness

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierStepCases
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierParseStateFrameRows
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateGraph
open FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateGraph
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
open FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization
open FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafParsedSemantics

theorem CompactNumericVerifierParseStateFrameRealization.realizeExactStep_of_parse
    {stateTable stateWidth stateTokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    (realization : CompactNumericVerifierParseStateFrameRealization
      stateTable stateWidth stateTokenCount currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness)
    (hparse : compactNumericParsePayload
      ((realization.currentProofTokens,
        realization.currentCertificateTokens),
        (realization.currentTasks.drop 1, realization.currentValues)) =
      some ((realization.nextProofTokens,
        realization.nextCertificateTokens),
        (realization.nextTasks, realization.nextValues)))
    (hnextStatusTag : nextCoordinates.statusTag = 0) :
    ∃ currentState nextState : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
        stateTable stateWidth stateTokenCount currentCoordinates.start
          currentCoordinates.finish currentState ∧
      CompactNumericVerifierStateDirectLayout
        stateTable stateWidth stateTokenCount nextCoordinates.start
          nextCoordinates.finish nextState ∧
      nextState = compactNumericVerifierStep currentState := by
  have hnextStatus : realization.nextStatus = none := by
    rcases realization.nextStatusCase with hnone | hsome
    · exact hnone.1
    · rcases hsome with ⟨result, _hstatus, htag, _hbool⟩
      omega
  let currentState : CompactNumericVerifierState :=
    (((realization.currentProofTokens,
        realization.currentCertificateTokens),
      (realization.currentTasks, realization.currentValues)), none)
  let nextState : CompactNumericVerifierState :=
    (((realization.nextProofTokens,
        realization.nextCertificateTokens),
      (realization.nextTasks, realization.nextValues)),
      realization.nextStatus)
  refine ⟨currentState, nextState,
    realization.currentLayout, realization.nextLayout, ?_⟩
  dsimp only [currentState, nextState]
  have hparseRest : compactNumericParsePayload
      ((realization.currentProofTokens,
        realization.currentCertificateTokens),
        (realization.currentRestTasks, realization.currentValues)) =
      some ((realization.nextProofTokens,
        realization.nextCertificateTokens),
        (realization.nextTasks, realization.nextValues)) := by
    rw [realization.currentRestTasks_eq]
    exact hparse
  rw [hnextStatus, realization.currentTasks_eq]
  simp [compactNumericVerifierStep, compactNumericRunningStep,
    realization.currentTaskTag, compactNumericParseState, hparseRest]

theorem CompactNumericVerifierParseStateGraph.realizeExactStep
    {stateTable stateWidth stateTokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound : Nat}
    {paCoordinates : CompactNumericVerifierPAAxiomJointLeafCoordinates}
    {firstParseCoordinates secondParseCoordinates combineCoordinates :
      CompactNumericVerifierTaskRowCoordinates}
    {firstParseSize secondParseSize combineSize :
      CompactNumericVerifierTaskSizeWitness}
    (hgraph : CompactNumericVerifierParseStateGraph
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness
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
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound paCoordinates
      firstParseCoordinates secondParseCoordinates combineCoordinates
      firstParseSize secondParseSize combineSize) :
    ∃ currentState nextState : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
        stateTable stateWidth stateTokenCount currentCoordinates.start
          currentCoordinates.finish currentState ∧
      CompactNumericVerifierStateDirectLayout
        stateTable stateWidth stateTokenCount nextCoordinates.start
          nextCoordinates.finish nextState ∧
      nextState = compactNumericVerifierStep currentState := by
  rcases hgraph with hfailure | hsuccess
  · exact hfailure.realizeExactStep
  · rcases hsuccess with ⟨hcurrent, hnext, hhead, hframe, hbranch⟩
    rcases hframe.realize hcurrent hnext hhead with ⟨realization⟩
    rcases hbranch with hverum | hclosed | hpa | hnonleaf
    · have hverumTyped := hverum
      rw [← realization.currentTasks_length,
        ← realization.nextTasks_length,
        ← realization.currentValues_length,
        ← realization.nextValues_length] at hverumTyped
      have hparseGraph := hverumTyped.1.1
      rcases hparseGraph.realize_nonleaf_fields with
        ⟨_proofInput, _proofNode, _certificateInput, _certificateNode,
          _parsedProofSuffix, parsedCertificateSuffix,
          _hproofInput, _hproofNode, _hproofParser, _hproofNodeTag,
          _hparsedProofSuffix, _hparsedProofSuffixValue,
          _hcertificateInput, hparsedCertificateSuffix,
          _hcertificateParser, _hcertificateNodeTag,
          _hcertificateSuffixNode⟩
      rcases
          FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithAllFields
            hparseGraph.2 with
        ⟨_root, _hroot, _hrootTag, hrootGamma, _hrootFirst,
          _hrootSecond, _hrootWitness, hproofSuffix⟩
      rcases hverumTyped.sound_exact
          realization.currentProofLayout realization.currentCertificateLayout
          hproofSuffix hparsedCertificateSuffix hrootGamma
          realization.nextProofLayout realization.nextCertificateLayout
          realization.currentTaskRows realization.nextTaskRows
          realization.currentValueRows realization.nextValueRows with
        ⟨proofNode, certificateNode, _htag,
          hproofParser, hcertificateParser, htransition,
          _htaskWidth, _htaskBound, _hvalueWidth, _hvalueBound,
          hnextStatusTag⟩
      have hparse : compactNumericParsePayload
          ((realization.currentProofTokens,
            realization.currentCertificateTokens),
            (realization.currentTasks.drop 1, realization.currentValues)) =
          some ((realization.nextProofTokens,
            realization.nextCertificateTokens),
            (realization.nextTasks, realization.nextValues)) :=
        (compactNumericParsePayload_eq_some_iff _ _).2
          ⟨proofNode, certificateNode, hproofParser,
            hcertificateParser, htransition⟩
      exact CompactNumericVerifierParseStateFrameRealization.realizeExactStep_of_parse
        realization hparse hnextStatusTag
    · have hclosedTyped := hclosed
      rw [← realization.currentTasks_length,
        ← realization.nextTasks_length,
        ← realization.currentValues_length,
        ← realization.nextValues_length] at hclosedTyped
      have hparseGraph := hclosedTyped.1.1
      rcases hparseGraph.realize_nonleaf_fields with
        ⟨_proofInput, _proofNode, _certificateInput, _certificateNode,
          _parsedProofSuffix, parsedCertificateSuffix,
          _hproofInput, _hproofNode, _hproofParser, _hproofNodeTag,
          _hparsedProofSuffix, _hparsedProofSuffixValue,
          _hcertificateInput, hparsedCertificateSuffix,
          _hcertificateParser, _hcertificateNodeTag,
          _hcertificateSuffixNode⟩
      rcases
          FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithAllFields
            hparseGraph.2 with
        ⟨_root, _hroot, _hrootTag, hrootGamma, hrootFormula,
          _hrootSecond, _hrootWitness, hproofSuffix⟩
      rcases hclosedTyped.sound_exact
          realization.currentProofLayout realization.currentCertificateLayout
          hproofSuffix hparsedCertificateSuffix hrootGamma hrootFormula
          realization.nextProofLayout realization.nextCertificateLayout
          realization.currentTaskRows realization.nextTaskRows
          realization.currentValueRows realization.nextValueRows with
        ⟨proofNode, certificateNode, _htag,
          hproofParser, hcertificateParser, htransition,
          _htaskWidth, _htaskBound, _hvalueWidth, _hvalueBound,
          hnextStatusTag⟩
      have hparse : compactNumericParsePayload
          ((realization.currentProofTokens,
            realization.currentCertificateTokens),
            (realization.currentTasks.drop 1, realization.currentValues)) =
          some ((realization.nextProofTokens,
            realization.nextCertificateTokens),
            (realization.nextTasks, realization.nextValues)) :=
        (compactNumericParsePayload_eq_some_iff _ _).2
          ⟨proofNode, certificateNode, hproofParser,
            hcertificateParser, htransition⟩
      exact CompactNumericVerifierParseStateFrameRealization.realizeExactStep_of_parse
        realization hparse hnextStatusTag
    · have hpaTyped := hpa
      rw [← realization.currentTasks_length,
        ← realization.nextTasks_length,
        ← realization.currentValues_length,
        ← realization.nextValues_length] at hpaTyped
      have hparseGraph := hpaTyped.1.1
      have hproofTagOne : proofTag = 1 :=
        hpaTyped.2.2.2.1.trans hpaTyped.2.1.2.2.2.2.1
      rcases
          FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithAllFields
            hparseGraph.2 with
        ⟨_root, _hroot, _hrootTag, _hrootGamma, _hrootCandidate,
          _hrootSecond, _hrootWitness, hproofSuffix⟩
      rcases
          FoundationCompactNumericListedDirectVerifierPAAxiomLeafParsedSemantics.CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph.realize_pa_leaf_fields
            hparseGraph hproofTagOne with
        ⟨_proofInput, _proofNode, parsedCandidate, _parsedCertificate,
          _certificateInput, parsedAxiomTokens, parsedCertificateSuffix,
          _hproofInput, _hproofNode, _hproofParser, _hproofNodeTag,
          hparsedGamma, hparsedCandidate, _hproofNodeCandidate,
          _hcertificateInput, hparsedAxiom, hparsedCertificateSuffix,
          _hcertificateParser, _hparsedAxiomTokens,
          _hcertificateTag⟩
      rcases hpaTyped.sound_exact
          realization.currentProofLayout realization.currentCertificateLayout
          hproofSuffix hparsedCertificateSuffix hparsedGamma hparsedCandidate
          hparsedAxiom realization.nextProofLayout
          realization.nextCertificateLayout realization.currentTaskRows
          realization.nextTaskRows realization.currentValueRows
          realization.nextValueRows with
        ⟨proofNode, certificateNode, _htag,
          hproofParser, hcertificateParser, htransition,
          _htaskWidth, _htaskBound, _hvalueWidth, _hvalueBound,
          hnextStatusTag⟩
      have hparse : compactNumericParsePayload
          ((realization.currentProofTokens,
            realization.currentCertificateTokens),
            (realization.currentTasks.drop 1, realization.currentValues)) =
          some ((realization.nextProofTokens,
            realization.nextCertificateTokens),
            (realization.nextTasks, realization.nextValues)) :=
        (compactNumericParsePayload_eq_some_iff _ _).2
          ⟨proofNode, certificateNode, hproofParser,
            hcertificateParser, htransition⟩
      exact CompactNumericVerifierParseStateFrameRealization.realizeExactStep_of_parse
        realization hparse hnextStatusTag
    · have hnonleafTyped := hnonleaf
      rw [← realization.currentTasks_length,
        ← realization.nextTasks_length,
        ← realization.currentValues_length,
        ← realization.nextValues_length] at hnonleafTyped
      have hwidths :
          nextSizeWitness.taskTableWidth = currentSizeWitness.taskTableWidth ∧
          nextSizeWitness.taskValueBound = currentSizeWitness.taskValueBound := by
        rcases hnonleafTyped with hone | htwo
        · exact ⟨hone.2.1.2.2.2.1, hone.2.1.2.2.2.2.1⟩
        · exact ⟨htwo.2.1.2.2.2.1, htwo.2.1.2.2.2.2.1⟩
      have hnextTaskGraph := realization.nextTaskGraph
      rw [hwidths.1, hwidths.2] at hnextTaskGraph
      rcases CompactNumericVerifierParseSuccessNonLeafStateGraph.sound
          stateTable stateWidth stateTokenCount
          currentCoordinates.start currentCoordinates.proofFinish
          currentCoordinates.proofFinish currentCoordinates.certificateFinish
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound
          rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
          secondFinish secondCount witnessFinish witnessCount suffixCount
          rootGammaBoundarySize
          currentCoordinates.taskBoundary nextCoordinates.taskBoundary
          currentCoordinates.valueBoundary nextCoordinates.valueBoundary
          currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
          currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
          nextSizeWitness.taskTableWidth nextSizeWitness.taskValueBound
          nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound
          nextCoordinates.start nextCoordinates.proofFinish
          nextCoordinates.certificateFinish nextCoordinates.statusTag
          firstParseCoordinates secondParseCoordinates combineCoordinates
          firstParseSize secondParseSize combineSize
          hnonleafTyped
          realization.currentProofLayout realization.currentCertificateLayout
          realization.nextProofLayout realization.nextCertificateLayout
          realization.currentTaskRows realization.nextTaskRows
          realization.currentTaskGraph hnextTaskGraph
          realization.currentValueRows realization.nextValueRows with
        ⟨proofNode, certificateNode, _htag,
          hproofParser, hcertificateParser, htransition,
          _htaskWidth, _htaskBound, _hvalueWidth, _hvalueBound,
          hnextStatusTag⟩
      have hparse : compactNumericParsePayload
          ((realization.currentProofTokens,
            realization.currentCertificateTokens),
            (realization.currentTasks.drop 1, realization.currentValues)) =
          some ((realization.nextProofTokens,
            realization.nextCertificateTokens),
            (realization.nextTasks, realization.nextValues)) :=
        (compactNumericParsePayload_eq_some_iff _ _).2
          ⟨proofNode, certificateNode, hproofParser,
            hcertificateParser, htransition⟩
      exact CompactNumericVerifierParseStateFrameRealization.realizeExactStep_of_parse
        realization hparse hnextStatusTag

#print axioms
  CompactNumericVerifierParseStateFrameRealization.realizeExactStep_of_parse
#print axioms CompactNumericVerifierParseStateGraph.realizeExactStep

end FoundationCompactNumericListedDirectVerifierParseStateExactness
