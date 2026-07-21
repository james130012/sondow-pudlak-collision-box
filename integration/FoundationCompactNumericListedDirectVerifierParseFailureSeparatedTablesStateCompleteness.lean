import integration.FoundationCompactNumericListedDirectVerifierParseFailureCanonicalFrameCompleteness
import integration.FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateGraph

/-!
# Canonical converse for a failed verifier parse step with separated tables

Typed current and next verifier states determine the state-frame coordinates.
An actual parse-payload failure independently constructs the proof and
certificate parser tables, and the two parts assemble into the complete
bounded state graph.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateCompleteness

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierParsePayloadFailureSeparatedTablesFormula
open FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesBranchRows
open FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateGraph
open FoundationCompactNumericListedDirectVerifierParseFailureCanonicalFrameCompleteness
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness

theorem exists_compactNumericVerifierParseFailureSeparatedTablesStateGraph_of_layouts
    {stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {currentTask : CompactNumericVerifierTask}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    (hcurrent : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount currentStart currentFinish
      (((proofTokens, certificateTokens),
        (currentTask :: restTasks, values)), none))
    (hnext : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextFinish
      (((proofTokens, certificateTokens), (restTasks, values)), some false))
    (hparse : compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) = none)
    (hcurrentTaskTag : currentTask.1 = 10) :
    ∃ currentCoordinates nextCoordinates :
        CompactNumericVerifierStateRowCoordinates,
    ∃ currentSizeWitness nextSizeWitness :
        CompactNumericVerifierStateSizeWitness,
    ∃ taskCoordinates : CompactNumericVerifierTaskRowCoordinates,
    ∃ taskSizeWitness : CompactNumericVerifierTaskSizeWitness,
    ∃ proofTable proofWidth proofTokenCount proofInputStart proofInputFinish,
    ∃ rootStart rootFinish proofTag proofEndpointBound,
    ∃ certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish certificateTag certificateEndpointBound,
      currentCoordinates.start = currentStart ∧
      currentCoordinates.finish = currentFinish ∧
      nextCoordinates.start = nextStart ∧
      nextCoordinates.finish = nextFinish ∧
      CompactNumericVerifierStateCanonicalCorePackage
        stateTable stateWidth stateTokenCount currentStart currentFinish
        (((proofTokens, certificateTokens),
          (currentTask :: restTasks, values)), none)
        currentCoordinates currentSizeWitness ∧
      CompactNumericVerifierStateCanonicalCorePackage
        stateTable stateWidth stateTokenCount nextStart nextFinish
        (((proofTokens, certificateTokens), (restTasks, values)), some false)
        nextCoordinates nextSizeWitness ∧
      CompactNumericVerifierParseFailureSeparatedTablesStateGraph
        stateTable stateWidth stateTokenCount
        currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness
        taskCoordinates taskSizeWitness
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound := by
  rcases
      CompactNumericVerifierParseFailureCanonicalFramePackage.exists_of_layouts
        hcurrent hnext hcurrentTaskTag with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, hframePackage⟩
  rcases hframePackage with
    ⟨hcurrentPackage, hnextPackage, hhead, hframe, hfailureRows⟩
  have hcurrentPackageSaved := hcurrentPackage
  have hnextPackageSaved := hnextPackage
  have hcurrentStartEq := hcurrentPackage.1
  have hcurrentFinishEq := hcurrentPackage.2.1
  have hnextStartEq := hnextPackage.1
  have hnextFinishEq := hnextPackage.2.1
  rcases hcurrentPackage with
    ⟨_hcurrentStart, _hcurrentFinish,
      hcurrentProof, hcurrentCertificate,
      _hcurrentTaskLayout, _hcurrentTaskRows,
      _hcurrentValueLayout, _hcurrentValueRows,
      _hcurrentTaskCount, _hcurrentValueCount,
      _hcurrentTaskTableWidth, _hcurrentTaskValueBound,
      _hcurrentValueTableWidth, _hcurrentValueValueBound,
      _hcurrentStatus, hcurrentCore⟩
  rcases hnextPackage with
    ⟨_hnextStart, _hnextFinish,
      _hnextProof, _hnextCertificate,
      _hnextTaskLayout, _hnextTaskRows,
      _hnextValueLayout, _hnextValueRows,
      _hnextTaskCount, _hnextValueCount,
      _hnextTaskTableWidth, _hnextTaskValueBound,
      _hnextValueTableWidth, _hnextValueValueBound,
      _hnextStatus, hnextCore⟩
  rcases
      exists_compactNumericParsePayloadFailureSeparatedTablesGraph_of_eq_none
        hcurrentProof hcurrentCertificate hparse with
    ⟨proofTable, proofWidth, proofTokenCount,
      proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      hpayload⟩
  refine ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness,
    taskCoordinates, taskSizeWitness,
    proofTable, proofWidth, proofTokenCount,
    proofInputStart, proofInputFinish,
    rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound, ?_⟩
  exact ⟨hcurrentStartEq, hcurrentFinishEq,
    hnextStartEq, hnextFinishEq,
    hcurrentPackageSaved, hnextPackageSaved,
    hcurrentCore, hnextCore, hhead, hframe,
    ⟨hpayload, hfailureRows⟩⟩

#print axioms
  exists_compactNumericVerifierParseFailureSeparatedTablesStateGraph_of_layouts

end FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateCompleteness
