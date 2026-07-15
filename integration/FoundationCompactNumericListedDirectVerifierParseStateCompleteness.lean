import integration.FoundationCompactNumericListedDirectVerifierParseStateFormula
import integration.FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateCompleteness
import integration.FoundationCompactNumericListedDirectVerifierParseSuccessCanonicalFrameCompleteness
import integration.FoundationCompactNumericListedDirectVerifierParseSuccessBranchCases
import integration.FoundationCompactNumericListedDirectVerifierStateCoreCompleteness

/-!
# Constructive converse for the complete verifier parse-state graph

Canonical current and next state layouts, together with the public parser
result, construct every coordinate required by the 429-column parse formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseStateCompleteness

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierStepCases
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateGraph
open FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateCompleteness
open FoundationCompactNumericListedDirectVerifierParseSuccessCanonicalFrameCompleteness
open FoundationCompactNumericListedDirectVerifierParseSuccessBranchCases
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierVerumLeafStateGraph
open FoundationCompactNumericListedDirectVerifierClosedLeafStateGraph
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraph
open FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateGraph
open FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness

def compactNumericVerifierParseUnusedTaskCoordinates :
    CompactNumericVerifierTaskRowCoordinates := by
  repeat constructor

def compactNumericVerifierParseUnusedTaskSize :
    CompactNumericVerifierTaskSizeWitness := by
  repeat constructor

def compactNumericVerifierParseUnusedPACoordinates :
    CompactNumericVerifierPAAxiomJointLeafCoordinates := by
  repeat constructor

structure CompactNumericVerifierParseStateGraphWitness
    (stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish : Nat) where
  currentCoordinates : CompactNumericVerifierStateRowCoordinates
  nextCoordinates : CompactNumericVerifierStateRowCoordinates
  currentSizeWitness : CompactNumericVerifierStateSizeWitness
  nextSizeWitness : CompactNumericVerifierStateSizeWitness
  currentStart_eq : currentCoordinates.start = currentStart
  currentFinish_eq : currentCoordinates.finish = currentFinish
  nextStart_eq : nextCoordinates.start = nextStart
  nextFinish_eq : nextCoordinates.finish = nextFinish
  taskCoordinates : CompactNumericVerifierTaskRowCoordinates
  taskSizeWitness : CompactNumericVerifierTaskSizeWitness
  proofTable : Nat
  proofWidth : Nat
  proofTokenCount : Nat
  proofInputStart : Nat
  proofInputFinish : Nat
  rootStart : Nat
  rootFinish : Nat
  proofTag : Nat
  proofEndpointBound : Nat
  certificateTable : Nat
  certificateWidth : Nat
  certificateTokenCount : Nat
  certificateInputStart : Nat
  certificateInputFinish : Nat
  axiomStart : Nat
  axiomFinish : Nat
  formulaStart : Nat
  formulaFinish : Nat
  suffixStart : Nat
  suffixFinish : Nat
  certificateTag : Nat
  certificateEndpointBound : Nat
  rootGammaFinish : Nat
  rootGammaCount : Nat
  rootGammaBoundary : Nat
  firstFinish : Nat
  firstCount : Nat
  secondFinish : Nat
  secondCount : Nat
  witnessFinish : Nat
  witnessCount : Nat
  suffixCount : Nat
  rootGammaBoundarySize : Nat
  targetStart : Nat
  targetFinish : Nat
  targetGammaFinish : Nat
  targetGammaCount : Nat
  targetGammaBoundary : Nat
  targetBool : Nat
  targetGammaBoundarySize : Nat
  resultBool : Nat
  ruleTable : Nat
  ruleWidth : Nat
  ruleTokenCount : Nat
  ruleProofTag : Nat
  ruleCertificateTag : Nat
  ruleGammaStart : Nat
  ruleGammaFinish : Nat
  ruleGammaBoundary : Nat
  ruleGammaCount : Nat
  ruleGammaBoundarySize : Nat
  ruleFormulaStart : Nat
  ruleFormulaFinish : Nat
  ruleFormulaBoundary : Nat
  ruleFormulaCount : Nat
  ruleFormulaBoundarySize : Nat
  ruleNegatedStart : Nat
  ruleNegatedFinish : Nat
  ruleNegatedBoundary : Nat
  ruleNegatedCount : Nat
  ruleNegatedBoundarySize : Nat
  ruleStateBoundary : Nat
  ruleStateCount : Nat
  ruleEmptyStart : Nat
  ruleEmptyFinish : Nat
  ruleEmptyBoundary : Nat
  ruleEmptyBoundarySize : Nat
  ruleTableWidth : Nat
  ruleValueBound : Nat
  paCoordinates : CompactNumericVerifierPAAxiomJointLeafCoordinates
  firstParseCoordinates : CompactNumericVerifierTaskRowCoordinates
  secondParseCoordinates : CompactNumericVerifierTaskRowCoordinates
  combineCoordinates : CompactNumericVerifierTaskRowCoordinates
  firstParseSize : CompactNumericVerifierTaskSizeWitness
  secondParseSize : CompactNumericVerifierTaskSizeWitness
  combineSize : CompactNumericVerifierTaskSizeWitness
  graph : CompactNumericVerifierParseStateGraph
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
    firstParseSize secondParseSize combineSize

theorem exists_compactNumericVerifierParseStateGraphWitness_of_failure
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
    Nonempty (CompactNumericVerifierParseStateGraphWitness
      stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish) := by
  rcases
      exists_compactNumericVerifierParseFailureSeparatedTablesStateGraph_of_layouts
        hcurrent hnext hparse hcurrentTaskTag with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness,
      proofTable, proofWidth, proofTokenCount,
      proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      hcurrentStartEq, hcurrentFinishEq, hnextStartEq, hnextFinishEq,
      hfailure⟩
  exact ⟨{
    currentCoordinates := currentCoordinates
    nextCoordinates := nextCoordinates
    currentSizeWitness := currentSizeWitness
    nextSizeWitness := nextSizeWitness
    currentStart_eq := hcurrentStartEq
    currentFinish_eq := hcurrentFinishEq
    nextStart_eq := hnextStartEq
    nextFinish_eq := hnextFinishEq
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
    rootGammaFinish := 0
    rootGammaCount := 0
    rootGammaBoundary := 0
    firstFinish := 0
    firstCount := 0
    secondFinish := 0
    secondCount := 0
    witnessFinish := 0
    witnessCount := 0
    suffixCount := 0
    rootGammaBoundarySize := 0
    targetStart := 0
    targetFinish := 0
    targetGammaFinish := 0
    targetGammaCount := 0
    targetGammaBoundary := 0
    targetBool := 0
    targetGammaBoundarySize := 0
    resultBool := 0
    ruleTable := 0
    ruleWidth := 0
    ruleTokenCount := 0
    ruleProofTag := 0
    ruleCertificateTag := 0
    ruleGammaStart := 0
    ruleGammaFinish := 0
    ruleGammaBoundary := 0
    ruleGammaCount := 0
    ruleGammaBoundarySize := 0
    ruleFormulaStart := 0
    ruleFormulaFinish := 0
    ruleFormulaBoundary := 0
    ruleFormulaCount := 0
    ruleFormulaBoundarySize := 0
    ruleNegatedStart := 0
    ruleNegatedFinish := 0
    ruleNegatedBoundary := 0
    ruleNegatedCount := 0
    ruleNegatedBoundarySize := 0
    ruleStateBoundary := 0
    ruleStateCount := 0
    ruleEmptyStart := 0
    ruleEmptyFinish := 0
    ruleEmptyBoundary := 0
    ruleEmptyBoundarySize := 0
    ruleTableWidth := 0
    ruleValueBound := 0
    paCoordinates := compactNumericVerifierParseUnusedPACoordinates
    firstParseCoordinates := compactNumericVerifierParseUnusedTaskCoordinates
    secondParseCoordinates := compactNumericVerifierParseUnusedTaskCoordinates
    combineCoordinates := compactNumericVerifierParseUnusedTaskCoordinates
    firstParseSize := compactNumericVerifierParseUnusedTaskSize
    secondParseSize := compactNumericVerifierParseUnusedTaskSize
    combineSize := compactNumericVerifierParseUnusedTaskSize
    graph := Or.inl hfailure }⟩

theorem exists_compactNumericVerifierParseStateGraphWitness_of_success
    {stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {currentTask : CompactNumericVerifierTask}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    {nextProofTokens nextCertificateTokens : List Nat}
    {nextTasks : List CompactNumericVerifierTask}
    {nextValues : List CompactNumericChildResult}
    (hcurrent : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount currentStart currentFinish
      (((proofTokens, certificateTokens),
        (currentTask :: restTasks, values)), none))
    (hnext : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextFinish
      (((nextProofTokens, nextCertificateTokens),
        (nextTasks, nextValues)), none))
    (hparse : compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) =
      some ((nextProofTokens, nextCertificateTokens),
        (nextTasks, nextValues)))
    (hcurrentTaskTag : currentTask.1 = 10) :
    Nonempty (CompactNumericVerifierParseStateGraphWitness
      stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish) := by
  rcases
      CompactNumericVerifierParseSuccessCanonicalFramePackage.exists_of_layouts
        hcurrent hnext hcurrentTaskTag with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, hframePackage⟩
  rcases hframePackage with
    ⟨hcurrentPackage, hnextPackage, hhead, hframe⟩
  have hcurrentPackageSaved := hcurrentPackage
  have hnextPackageSaved := hnextPackage
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
  have hsourceTaskNonempty :
      1 ≤ (currentTask :: restTasks).length := by
    simp
  have hnextStatusTag : nextCoordinates.statusTag = 0 :=
    hnextPackageSaved.statusTag_eq_zero rfl
  rcases compactNumericParsePayload_eq_some_with_grouped_tag_cases
      _ _ hparse with
    ⟨proofNode, certificateNode, hproofParser, hcertificateParser,
      htransition, htag⟩
  have htransitionFull : compactNumericNodeTransition proofNode certificateNode
      ((currentTask :: restTasks).drop 1) values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, nextValues)) := by
    simpa using htransition
  rcases htag with hclosedTag | hpaTag | hverumTag | hnonleafTag
  · rcases
        exists_compactNumericVerifierClosedLeafStateGraph_of_success_and_transition
          hcurrentProof hcurrentCertificate hproofParser hcertificateParser
          hclosedTag htransitionFull hnextProof hnextCertificate
          hcurrentTaskRows hnextTaskRows hcurrentValueRows hnextValueRows
          hsourceTaskGraph htargetTaskGraph hsourceValueGraph htargetValueGraph
          hsourceTaskNonempty htaskTableWidth htaskValueBound
          hvalueTableWidth hvalueValueBound hnextStatusTag with
      ⟨proofTable, proofWidth, proofTokenCount,
        proofInputStart, proofInputFinish,
        rootStart, rootFinish, proofTag, proofEndpointBound,
        certificateTable, certificateWidth, certificateTokenCount,
        certificateInputStart, certificateInputFinish,
        axiomStart, axiomFinish, formulaStart, formulaFinish,
        suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
        rootGammaFinish, rootGammaCount, rootGammaBoundary,
        firstFinish, firstCount, secondFinish, secondCount,
        witnessFinish, witnessCount, suffixCount, rootGammaBoundarySize,
        targetStart, targetFinish, targetGammaFinish, targetGammaCount,
        targetGammaBoundary, targetBool, targetGammaBoundarySize,
        ruleTable, ruleWidth, ruleTokenCount, ruleProofTag,
        ruleCertificateTag, ruleGammaStart, ruleGammaFinish,
        ruleGammaBoundary, ruleGammaCount, ruleGammaBoundarySize,
        ruleFormulaStart, ruleFormulaFinish, ruleFormulaBoundary,
        ruleFormulaCount, ruleFormulaBoundarySize,
        ruleNegatedStart, ruleNegatedFinish, ruleNegatedBoundary,
        ruleNegatedCount, ruleNegatedBoundarySize,
        ruleStateBoundary, ruleStateCount,
        ruleEmptyStart, ruleEmptyFinish, ruleEmptyBoundary,
        ruleEmptyBoundarySize, ruleTableWidth, ruleValueBound, hclosed⟩
    rw [← hcurrentTaskCount, ← hnextTaskCount,
      ← hcurrentValueCount, ← hnextValueCount] at hclosed
    exact ⟨{
      currentCoordinates := currentCoordinates
      nextCoordinates := nextCoordinates
      currentSizeWitness := currentSizeWitness
      nextSizeWitness := nextSizeWitness
      currentStart_eq := hcurrentPackageSaved.1
      currentFinish_eq := hcurrentPackageSaved.2.1
      nextStart_eq := hnextPackageSaved.1
      nextFinish_eq := hnextPackageSaved.2.1
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
        (compactClosedRuleCheck (proofNode.2.1, proofNode.2.2.1))
      ruleTable := ruleTable
      ruleWidth := ruleWidth
      ruleTokenCount := ruleTokenCount
      ruleProofTag := ruleProofTag
      ruleCertificateTag := ruleCertificateTag
      ruleGammaStart := ruleGammaStart
      ruleGammaFinish := ruleGammaFinish
      ruleGammaBoundary := ruleGammaBoundary
      ruleGammaCount := ruleGammaCount
      ruleGammaBoundarySize := ruleGammaBoundarySize
      ruleFormulaStart := ruleFormulaStart
      ruleFormulaFinish := ruleFormulaFinish
      ruleFormulaBoundary := ruleFormulaBoundary
      ruleFormulaCount := ruleFormulaCount
      ruleFormulaBoundarySize := ruleFormulaBoundarySize
      ruleNegatedStart := ruleNegatedStart
      ruleNegatedFinish := ruleNegatedFinish
      ruleNegatedBoundary := ruleNegatedBoundary
      ruleNegatedCount := ruleNegatedCount
      ruleNegatedBoundarySize := ruleNegatedBoundarySize
      ruleStateBoundary := ruleStateBoundary
      ruleStateCount := ruleStateCount
      ruleEmptyStart := ruleEmptyStart
      ruleEmptyFinish := ruleEmptyFinish
      ruleEmptyBoundary := ruleEmptyBoundary
      ruleEmptyBoundarySize := ruleEmptyBoundarySize
      ruleTableWidth := ruleTableWidth
      ruleValueBound := ruleValueBound
      paCoordinates := compactNumericVerifierParseUnusedPACoordinates
      firstParseCoordinates := compactNumericVerifierParseUnusedTaskCoordinates
      secondParseCoordinates := compactNumericVerifierParseUnusedTaskCoordinates
      combineCoordinates := compactNumericVerifierParseUnusedTaskCoordinates
      firstParseSize := compactNumericVerifierParseUnusedTaskSize
      secondParseSize := compactNumericVerifierParseUnusedTaskSize
      combineSize := compactNumericVerifierParseUnusedTaskSize
      graph := Or.inr ⟨hcurrentCoreSaved, hnextCoreSaved,
        hhead, hframe, Or.inr (Or.inl hclosed)⟩ }⟩
  · rcases
        exists_compactNumericVerifierPAAxiomLeafStateGraph_of_success_and_transition
          hcurrentProof hcurrentCertificate hproofParser hcertificateParser
          hpaTag htransitionFull hnextProof hnextCertificate
          hcurrentTaskRows hnextTaskRows hcurrentValueRows hnextValueRows
          hsourceTaskGraph htargetTaskGraph hsourceValueGraph htargetValueGraph
          hsourceTaskNonempty htaskTableWidth htaskValueBound
          hvalueTableWidth hvalueValueBound hnextStatusTag with
      ⟨proofTable, proofWidth, proofTokenCount,
        proofInputStart, proofInputFinish,
        rootStart, rootFinish, proofTag, proofEndpointBound,
        certificateTable, certificateWidth, certificateTokenCount,
        certificateInputStart, certificateInputFinish,
        axiomStart, axiomFinish, formulaStart, formulaFinish,
        suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
        rootGammaFinish, rootGammaCount, rootGammaBoundary,
        firstFinish, firstCount, secondFinish, secondCount,
        witnessFinish, witnessCount, suffixCount, rootGammaBoundarySize,
        targetStart, targetFinish, targetGammaFinish, targetGammaCount,
        targetGammaBoundary, targetBool, targetGammaBoundarySize,
        paCoordinates, hpa⟩
    rw [← hcurrentTaskCount, ← hnextTaskCount,
      ← hcurrentValueCount, ← hnextValueCount] at hpa
    exact ⟨{
      currentCoordinates := currentCoordinates
      nextCoordinates := nextCoordinates
      currentSizeWitness := currentSizeWitness
      nextSizeWitness := nextSizeWitness
      currentStart_eq := hcurrentPackageSaved.1
      currentFinish_eq := hcurrentPackageSaved.2.1
      nextStart_eq := hnextPackageSaved.1
      nextFinish_eq := hnextPackageSaved.2.1
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
      ruleTable := 0
      ruleWidth := 0
      ruleTokenCount := 0
      ruleProofTag := 0
      ruleCertificateTag := 0
      ruleGammaStart := 0
      ruleGammaFinish := 0
      ruleGammaBoundary := 0
      ruleGammaCount := 0
      ruleGammaBoundarySize := 0
      ruleFormulaStart := 0
      ruleFormulaFinish := 0
      ruleFormulaBoundary := 0
      ruleFormulaCount := 0
      ruleFormulaBoundarySize := 0
      ruleNegatedStart := 0
      ruleNegatedFinish := 0
      ruleNegatedBoundary := 0
      ruleNegatedCount := 0
      ruleNegatedBoundarySize := 0
      ruleStateBoundary := 0
      ruleStateCount := 0
      ruleEmptyStart := 0
      ruleEmptyFinish := 0
      ruleEmptyBoundary := 0
      ruleEmptyBoundarySize := 0
      ruleTableWidth := 0
      ruleValueBound := 0
      paCoordinates := paCoordinates
      firstParseCoordinates := compactNumericVerifierParseUnusedTaskCoordinates
      secondParseCoordinates := compactNumericVerifierParseUnusedTaskCoordinates
      combineCoordinates := compactNumericVerifierParseUnusedTaskCoordinates
      firstParseSize := compactNumericVerifierParseUnusedTaskSize
      secondParseSize := compactNumericVerifierParseUnusedTaskSize
      combineSize := compactNumericVerifierParseUnusedTaskSize
      graph := Or.inr ⟨hcurrentCoreSaved, hnextCoreSaved,
        hhead, hframe, Or.inr (Or.inr (Or.inl hpa))⟩ }⟩
  · rcases
        exists_compactNumericVerifierVerumLeafStateGraph_of_success_and_transition
          hcurrentProof hcurrentCertificate hproofParser hcertificateParser
          hverumTag htransitionFull hnextProof hnextCertificate
          hcurrentTaskRows hnextTaskRows hcurrentValueRows hnextValueRows
          hsourceTaskGraph htargetTaskGraph hsourceValueGraph htargetValueGraph
          hsourceTaskNonempty htaskTableWidth htaskValueBound
          hvalueTableWidth hvalueValueBound hnextStatusTag with
      ⟨proofTable, proofWidth, proofTokenCount,
        proofInputStart, proofInputFinish,
        rootStart, rootFinish, proofTag, proofEndpointBound,
        certificateTable, certificateWidth, certificateTokenCount,
        certificateInputStart, certificateInputFinish,
        axiomStart, axiomFinish, formulaStart, formulaFinish,
        suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
        rootGammaFinish, rootGammaCount, rootGammaBoundary,
        firstFinish, firstCount, secondFinish, secondCount,
        witnessFinish, witnessCount, suffixCount, rootGammaBoundarySize,
        targetStart, targetFinish, targetGammaFinish, targetGammaCount,
        targetGammaBoundary, targetBool, targetGammaBoundarySize, hverum⟩
    rw [← hcurrentTaskCount, ← hnextTaskCount,
      ← hcurrentValueCount, ← hnextValueCount] at hverum
    exact ⟨{
      currentCoordinates := currentCoordinates
      nextCoordinates := nextCoordinates
      currentSizeWitness := currentSizeWitness
      nextSizeWitness := nextSizeWitness
      currentStart_eq := hcurrentPackageSaved.1
      currentFinish_eq := hcurrentPackageSaved.2.1
      nextStart_eq := hnextPackageSaved.1
      nextFinish_eq := hnextPackageSaved.2.1
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
        (compactVerumRuleCheck proofNode.2.1)
      ruleTable := 0
      ruleWidth := 0
      ruleTokenCount := 0
      ruleProofTag := 0
      ruleCertificateTag := 0
      ruleGammaStart := 0
      ruleGammaFinish := 0
      ruleGammaBoundary := 0
      ruleGammaCount := 0
      ruleGammaBoundarySize := 0
      ruleFormulaStart := 0
      ruleFormulaFinish := 0
      ruleFormulaBoundary := 0
      ruleFormulaCount := 0
      ruleFormulaBoundarySize := 0
      ruleNegatedStart := 0
      ruleNegatedFinish := 0
      ruleNegatedBoundary := 0
      ruleNegatedCount := 0
      ruleNegatedBoundarySize := 0
      ruleStateBoundary := 0
      ruleStateCount := 0
      ruleEmptyStart := 0
      ruleEmptyFinish := 0
      ruleEmptyBoundary := 0
      ruleEmptyBoundarySize := 0
      ruleTableWidth := 0
      ruleValueBound := 0
      paCoordinates := compactNumericVerifierParseUnusedPACoordinates
      firstParseCoordinates := compactNumericVerifierParseUnusedTaskCoordinates
      secondParseCoordinates := compactNumericVerifierParseUnusedTaskCoordinates
      combineCoordinates := compactNumericVerifierParseUnusedTaskCoordinates
      firstParseSize := compactNumericVerifierParseUnusedTaskSize
      secondParseSize := compactNumericVerifierParseUnusedTaskSize
      combineSize := compactNumericVerifierParseUnusedTaskSize
      graph := Or.inr ⟨hcurrentCoreSaved, hnextCoreSaved,
        hhead, hframe, Or.inl hverum⟩ }⟩
  · rcases
        exists_compactNumericVerifierParseSuccessNonLeafStateGraph_of_transition
          stateTable stateWidth stateTokenCount
          currentCoordinates.start currentCoordinates.proofFinish
          currentCoordinates.proofFinish currentCoordinates.certificateFinish
          currentCoordinates.taskBoundary nextCoordinates.taskBoundary
          currentCoordinates.valueBoundary nextCoordinates.valueBoundary
          currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
          currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
          nextSizeWitness.taskTableWidth nextSizeWitness.taskValueBound
          nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound
          nextCoordinates.start nextCoordinates.proofFinish
          nextCoordinates.certificateFinish nextCoordinates.statusTag
          hcurrentProof hcurrentCertificate hproofParser hcertificateParser
          hnonleafTag htransitionFull hnextProof hnextCertificate
          hcurrentTaskRows hnextTaskRows hsourceTaskGraph htargetTaskGraph
          hcurrentValueRows hnextValueRows hsourceValueGraph htargetValueGraph
          hsourceTaskNonempty htaskTableWidth htaskValueBound
          hvalueTableWidth hvalueValueBound hnextStatusTag with
      ⟨proofTable, proofWidth, proofTokenCount,
        proofInputStart, proofInputFinish,
        rootStart, rootFinish, proofTag, proofEndpointBound,
        certificateTable, certificateWidth, certificateTokenCount,
        certificateInputStart, certificateInputFinish,
        axiomStart, axiomFinish, formulaStart, formulaFinish,
        suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
        rootGammaFinish, rootGammaCount, rootGammaBoundary,
        firstFinish, firstCount, secondFinish, secondCount,
        witnessFinish, witnessCount, suffixCount, rootGammaBoundarySize,
        firstParseCoordinates, secondParseCoordinates, combineCoordinates,
        firstParseSize, secondParseSize, combineSize, hnonleaf⟩
    rw [← hcurrentTaskCount, ← hnextTaskCount,
      ← hcurrentValueCount, ← hnextValueCount] at hnonleaf
    exact ⟨{
      currentCoordinates := currentCoordinates
      nextCoordinates := nextCoordinates
      currentSizeWitness := currentSizeWitness
      nextSizeWitness := nextSizeWitness
      currentStart_eq := hcurrentPackageSaved.1
      currentFinish_eq := hcurrentPackageSaved.2.1
      nextStart_eq := hnextPackageSaved.1
      nextFinish_eq := hnextPackageSaved.2.1
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
      targetStart := 0
      targetFinish := 0
      targetGammaFinish := 0
      targetGammaCount := 0
      targetGammaBoundary := 0
      targetBool := 0
      targetGammaBoundarySize := 0
      resultBool := 0
      ruleTable := 0
      ruleWidth := 0
      ruleTokenCount := 0
      ruleProofTag := 0
      ruleCertificateTag := 0
      ruleGammaStart := 0
      ruleGammaFinish := 0
      ruleGammaBoundary := 0
      ruleGammaCount := 0
      ruleGammaBoundarySize := 0
      ruleFormulaStart := 0
      ruleFormulaFinish := 0
      ruleFormulaBoundary := 0
      ruleFormulaCount := 0
      ruleFormulaBoundarySize := 0
      ruleNegatedStart := 0
      ruleNegatedFinish := 0
      ruleNegatedBoundary := 0
      ruleNegatedCount := 0
      ruleNegatedBoundarySize := 0
      ruleStateBoundary := 0
      ruleStateCount := 0
      ruleEmptyStart := 0
      ruleEmptyFinish := 0
      ruleEmptyBoundary := 0
      ruleEmptyBoundarySize := 0
      ruleTableWidth := 0
      ruleValueBound := 0
      paCoordinates := compactNumericVerifierParseUnusedPACoordinates
      firstParseCoordinates := firstParseCoordinates
      secondParseCoordinates := secondParseCoordinates
      combineCoordinates := combineCoordinates
      firstParseSize := firstParseSize
      secondParseSize := secondParseSize
      combineSize := combineSize
      graph := Or.inr ⟨hcurrentCoreSaved, hnextCoreSaved,
        hhead, hframe, Or.inr (Or.inr (Or.inr hnonleaf))⟩ }⟩

theorem exists_compactNumericVerifierParseStateGraphWitness_of_public_step
    {stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish : Nat}
    {currentState nextState : CompactNumericVerifierState}
    (hcurrent : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount currentStart currentFinish
      currentState)
    (hnext : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextFinish nextState)
    (hcase : CompactNumericVerifierParseStepCase currentState nextState) :
    Nonempty (CompactNumericVerifierParseStateGraphWitness
      stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish) := by
  rcases currentState with
    ⟨⟨⟨proofTokens, certificateTokens⟩, ⟨tasks, values⟩⟩, status⟩
  rcases hcase with
    ⟨currentTask, restTasks, hstatus, htasks, hcurrentTaskTag, hstep⟩
  change status = none at hstatus
  change tasks = currentTask :: restTasks at htasks
  have hcurrentTyped : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount currentStart currentFinish
      (((proofTokens, certificateTokens),
        (currentTask :: restTasks, values)), none) := by
    simpa only [hstatus, htasks] using hcurrent
  have hparseCases :=
    (compactNumericParseState_cases_iff
      ((proofTokens, certificateTokens), (restTasks, values)) nextState).2
      hstep
  rcases hparseCases with hsuccess | hfailure
  · rcases hsuccess with ⟨parsed, hparse, hnextState⟩
    rcases parsed with
      ⟨⟨nextProofTokens, nextCertificateTokens⟩,
        ⟨nextTasks, nextValues⟩⟩
    have hnextTyped : CompactNumericVerifierStateDirectLayout
        stateTable stateWidth stateTokenCount nextStart nextFinish
        (((nextProofTokens, nextCertificateTokens),
          (nextTasks, nextValues)), none) := by
      simpa only [hnextState] using hnext
    exact exists_compactNumericVerifierParseStateGraphWitness_of_success
      hcurrentTyped hnextTyped hparse hcurrentTaskTag
  · rcases hfailure with ⟨hparse, hnextState⟩
    have hnextTyped : CompactNumericVerifierStateDirectLayout
        stateTable stateWidth stateTokenCount nextStart nextFinish
        (((proofTokens, certificateTokens), (restTasks, values)), some false) := by
      simpa only [hnextState] using hnext
    exact exists_compactNumericVerifierParseStateGraphWitness_of_failure
      hcurrentTyped hnextTyped hparse hcurrentTaskTag

#print axioms
  exists_compactNumericVerifierParseStateGraphWitness_of_failure
#print axioms
  exists_compactNumericVerifierParseStateGraphWitness_of_success
#print axioms
  exists_compactNumericVerifierParseStateGraphWitness_of_public_step

end FoundationCompactNumericListedDirectVerifierParseStateCompleteness
