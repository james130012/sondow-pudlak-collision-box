import integration.FoundationCompactNumericListedDirectVerifierAcceptedTreeGlobalCoordinateBound
import integration.FoundationCompactNumericListedDirectVerifierCheckedRowExecutionSplicing
import integration.FoundationCompactNumericListedDirectVerifierCanonicalNonLeafRowsGlobalBound
import integration.FoundationCompactNumericListedPAAxiomLeafOccurrence

/-!
# Globally bounded checked rows at every accepted tree-task offset

This file joins the branch-local checked-row constructions to the actual
depth-first execution offsets of a valid listed proof tree.  The leaf lemmas
below are the base cases for the structural execution induction.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedTreeTaskRowsGlobalBound

open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsGlobalBound
open FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomGlobalBound
open FoundationCompactNumericListedDirectVerifierTypedVerumGlobalBound
open FoundationCompactNumericListedDirectVerifierTypedClosedGlobalBound
open FoundationCompactNumericListedDirectVerifierTypedNonLeafGlobalBound
open FoundationCompactNumericListedDirectVerifierAcceptedTreeGlobalCoordinateBound
open FoundationCompactNumericListedDirectVerifierCheckedRowExecutionSplicing
open FoundationCompactNumericListedDirectVerifierCanonicalNonLeafRowsGlobalBound
open FoundationCompactNumericListedPAAxiomLeafOccurrence

def compactNumericVerifierAcceptedTreeRowBound
    (rowWeight : Nat)
    (row : CompactNumericVerifierCheckedStepRow) : Prop :=
  forall coordinate : Fin 429,
    Nat.size (row.environment coordinate) <=
      compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound rowWeight

theorem compactNumericVerifierAcceptedTreeRowBound_of_closed
    {rowWeight : Nat}
    {row : CompactNumericVerifierCheckedStepRow}
    (hrow : forall coordinate : Fin 429,
      Nat.size (row.environment coordinate) <=
        compactNumericVerifierTypedClosedGlobalCoordinateSizeBound rowWeight) :
    compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
  intro coordinate
  exact (hrow coordinate).trans
    (compactNumericVerifierTypedClosedGlobal_le_acceptedTreeGlobal rowWeight)

theorem compactNumericVerifierAcceptedTreeRowBound_of_paAxiom
    {rowWeight : Nat}
    {row : CompactNumericVerifierCheckedStepRow}
    (hrow : forall coordinate : Fin 429,
      Nat.size (row.environment coordinate) <=
        compactNumericVerifierAcceptedPAAxiomGlobalCoordinateSizeBound
          rowWeight) :
    compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
  intro coordinate
  exact (hrow coordinate).trans
    (compactNumericVerifierAcceptedPAAxiomGlobal_le_acceptedTreeGlobal
      rowWeight)

theorem compactNumericVerifierAcceptedTreeRowBound_of_verum
    {rowWeight : Nat}
    {row : CompactNumericVerifierCheckedStepRow}
    (hrow : forall coordinate : Fin 429,
      Nat.size (row.environment coordinate) <=
        compactNumericVerifierTypedVerumGlobalCoordinateSizeBound rowWeight) :
    compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
  intro coordinate
  exact (hrow coordinate).trans
    (compactNumericVerifierTypedVerumGlobal_le_acceptedTreeGlobal rowWeight)

theorem compactNumericVerifierAcceptedTreeRowBound_of_nonLeaf
    {rowWeight : Nat}
    {row : CompactNumericVerifierCheckedStepRow}
    (hrow : forall coordinate : Fin 429,
      Nat.size (row.environment coordinate) <=
        compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound rowWeight) :
    compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
  intro coordinate
  exact (hrow coordinate).trans
    (compactNumericVerifierTypedNonLeafGlobal_le_acceptedTreeGlobal rowWeight)

theorem compactNumericVerifierAcceptedTreeRowBound_of_nonParse
    {rowWeight : Nat}
    {row : CompactNumericVerifierCheckedStepRow}
    (hrow : forall coordinate : Fin 429,
      Nat.size (row.environment coordinate) <=
        compactNumericVerifierNonParseGlobalCoordinateSizeBound rowWeight) :
    compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
  intro coordinate
  exact (hrow coordinate).trans
    (compactNumericVerifierNonParseGlobal_le_acceptedTreeGlobal rowWeight)

structure CompactNumericVerifierUnaryExecutionWeightBounds
    (start childStart beforeCombine finish : CompactNumericVerifierState)
    (childSteps rowWeight : Nat) : Prop where
  rootCurrent : compactNumericVerifierStateWeight start <= rowWeight
  rootNext : compactNumericVerifierStateWeight childStart <= rowWeight
  child : forall offset, offset <= childSteps ->
    compactNumericVerifierStateWeight
      (compactNumericVerifierStateAt childStart offset) <= rowWeight
  combineCurrent :
    compactNumericVerifierStateWeight beforeCombine <= rowWeight
  combineNext : compactNumericVerifierStateWeight finish <= rowWeight

theorem compactNumericVerifierUnaryExecutionWeightBounds_of_parent
    {start childStart beforeCombine finish : CompactNumericVerifierState}
    {childSteps rowWeight : Nat}
    (hrootStep : compactNumericVerifierStep start = childStart)
    (hchildExecute :
      (compactNumericVerifierStep^[childSteps]) childStart = beforeCombine)
    (hcombineStep : compactNumericVerifierStep beforeCombine = finish)
    (hparent : forall offset, offset <= 1 + childSteps + 1 ->
      compactNumericVerifierStateWeight
        (compactNumericVerifierStateAt start offset) <= rowWeight) :
    CompactNumericVerifierUnaryExecutionWeightBounds start childStart
      beforeCombine finish childSteps rowWeight := by
  have hrootIterate :
      (compactNumericVerifierStep^[1]) start = childStart := by
    simpa only [Function.iterate_one] using hrootStep
  have hthroughChild := compactNumericVerifier_iterate_trans
    hrootIterate hchildExecute
  have hcombineIterate :
      (compactNumericVerifierStep^[1]) beforeCombine = finish := by
    simpa only [Function.iterate_one] using hcombineStep
  have hall := compactNumericVerifier_iterate_trans
    hthroughChild hcombineIterate
  constructor
  · simpa only [compactNumericVerifierStateAt,
      Function.iterate_zero_apply] using hparent 0 (by omega)
  · have hnextAt : compactNumericVerifierStateAt start 1 = childStart := by
      simpa only [compactNumericVerifierStateAt] using hrootIterate
    rw [← hnextAt]
    exact hparent 1 (by omega)
  · intro offset hoffset
    exact compactNumericVerifierStateAt_weight_le_of_prefix hrootIterate
      hparent (by omega)
  · have hbeforeAt :
        compactNumericVerifierStateAt start (1 + childSteps) =
          beforeCombine := by
      simpa only [compactNumericVerifierStateAt] using hthroughChild
    rw [← hbeforeAt]
    exact hparent (1 + childSteps) (by omega)
  · have hfinishAt :
        compactNumericVerifierStateAt start (1 + childSteps + 1) =
          finish := by
      simpa only [compactNumericVerifierStateAt] using hall
    rw [← hfinishAt]
    exact hparent (1 + childSteps + 1) (by omega)

structure CompactNumericVerifierBinaryExecutionWeightBounds
    (start leftStart rightStart beforeCombine finish :
      CompactNumericVerifierState)
    (leftSteps rightSteps rowWeight : Nat) : Prop where
  rootCurrent : compactNumericVerifierStateWeight start <= rowWeight
  rootNext : compactNumericVerifierStateWeight leftStart <= rowWeight
  left : forall offset, offset <= leftSteps ->
    compactNumericVerifierStateWeight
      (compactNumericVerifierStateAt leftStart offset) <= rowWeight
  right : forall offset, offset <= rightSteps ->
    compactNumericVerifierStateWeight
      (compactNumericVerifierStateAt rightStart offset) <= rowWeight
  combineCurrent :
    compactNumericVerifierStateWeight beforeCombine <= rowWeight
  combineNext : compactNumericVerifierStateWeight finish <= rowWeight

theorem compactNumericVerifierBinaryExecutionWeightBounds_of_parent
    {start leftStart rightStart beforeCombine finish :
      CompactNumericVerifierState}
    {leftSteps rightSteps rowWeight : Nat}
    (hrootStep : compactNumericVerifierStep start = leftStart)
    (hleftExecute :
      (compactNumericVerifierStep^[leftSteps]) leftStart = rightStart)
    (hrightExecute :
      (compactNumericVerifierStep^[rightSteps]) rightStart = beforeCombine)
    (hcombineStep : compactNumericVerifierStep beforeCombine = finish)
    (hparent : forall offset,
      offset <= 1 + leftSteps + rightSteps + 1 ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt start offset) <= rowWeight) :
    CompactNumericVerifierBinaryExecutionWeightBounds start leftStart
      rightStart beforeCombine finish leftSteps rightSteps rowWeight := by
  have hrootIterate :
      (compactNumericVerifierStep^[1]) start = leftStart := by
    simpa only [Function.iterate_one] using hrootStep
  have hthroughLeft := compactNumericVerifier_iterate_trans
    hrootIterate hleftExecute
  have hthroughRight := compactNumericVerifier_iterate_trans
    hthroughLeft hrightExecute
  have hcombineIterate :
      (compactNumericVerifierStep^[1]) beforeCombine = finish := by
    simpa only [Function.iterate_one] using hcombineStep
  have hall := compactNumericVerifier_iterate_trans
    hthroughRight hcombineIterate
  constructor
  · simpa only [compactNumericVerifierStateAt,
      Function.iterate_zero_apply] using hparent 0 (by omega)
  · have hnextAt : compactNumericVerifierStateAt start 1 = leftStart := by
      simpa only [compactNumericVerifierStateAt] using hrootIterate
    rw [← hnextAt]
    exact hparent 1 (by omega)
  · intro offset hoffset
    exact compactNumericVerifierStateAt_weight_le_of_prefix hrootIterate
      hparent (by omega)
  · intro offset hoffset
    exact compactNumericVerifierStateAt_weight_le_of_prefix hthroughLeft
      hparent (by omega)
  · have hbeforeAt :
        compactNumericVerifierStateAt start
            ((1 + leftSteps) + rightSteps) = beforeCombine := by
      simpa only [compactNumericVerifierStateAt] using hthroughRight
    rw [← hbeforeAt]
    exact hparent ((1 + leftSteps) + rightSteps) (by omega)
  · have hfinishAt :
        compactNumericVerifierStateAt start
            (((1 + leftSteps) + rightSteps) + 1) = finish := by
      simpa only [compactNumericVerifierStateAt] using hall
    rw [← hfinishAt]
    exact hparent (((1 + leftSteps) + rightSteps) + 1) (by omega)

theorem exists_compactNumericVerifierAcceptedTreeRow_at_unary_offset
    {start childStart beforeCombine finish : CompactNumericVerifierState}
    {childSteps offset rowWeight : Nat}
    (hrootStep : compactNumericVerifierStep start = childStart)
    (hchildExecute :
      (compactNumericVerifierStep^[childSteps]) childStart = beforeCombine)
    (hcombineStep : compactNumericVerifierStep beforeCombine = finish)
    (hrootRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = start /\ row.nextState = childStart /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
              rowWeight)
    (hchildRows : forall childOffset, childOffset < childSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt childStart childOffset /\
          row.nextState =
            compactNumericVerifierStateAt childStart (childOffset + 1) /\
          compactNumericVerifierAcceptedTreeRowBound rowWeight row)
    (hcombineRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = beforeCombine /\ row.nextState = finish /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierNonParseGlobalCoordinateSizeBound rowWeight)
    (hoffset : offset < 1 + childSteps + 1) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt start offset /\
        row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
        compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
  apply exists_checkedStepRow_at_unary_execution_offset
    (compactNumericVerifierAcceptedTreeRowBound rowWeight) hrootStep
    hchildExecute hcombineStep
  · rcases hrootRow with ⟨row, hcurrent, hnext, hbound⟩
    exact ⟨row, hcurrent, hnext,
      compactNumericVerifierAcceptedTreeRowBound_of_nonLeaf hbound⟩
  · exact hchildRows
  · rcases hcombineRow with ⟨row, hcurrent, hnext, hbound⟩
    exact ⟨row, hcurrent, hnext,
      compactNumericVerifierAcceptedTreeRowBound_of_nonParse hbound⟩
  · exact hoffset

theorem exists_compactNumericVerifierAcceptedTreeRow_at_binary_offset
    {start leftStart rightStart beforeCombine finish :
      CompactNumericVerifierState}
    {leftSteps rightSteps offset rowWeight : Nat}
    (hrootStep : compactNumericVerifierStep start = leftStart)
    (hleftExecute :
      (compactNumericVerifierStep^[leftSteps]) leftStart = rightStart)
    (hrightExecute :
      (compactNumericVerifierStep^[rightSteps]) rightStart = beforeCombine)
    (hcombineStep : compactNumericVerifierStep beforeCombine = finish)
    (hrootRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = start /\ row.nextState = leftStart /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
              rowWeight)
    (hleftRows : forall leftOffset, leftOffset < leftSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt leftStart leftOffset /\
          row.nextState =
            compactNumericVerifierStateAt leftStart (leftOffset + 1) /\
          compactNumericVerifierAcceptedTreeRowBound rowWeight row)
    (hrightRows : forall rightOffset, rightOffset < rightSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt rightStart rightOffset /\
          row.nextState =
            compactNumericVerifierStateAt rightStart (rightOffset + 1) /\
          compactNumericVerifierAcceptedTreeRowBound rowWeight row)
    (hcombineRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = beforeCombine /\ row.nextState = finish /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierNonParseGlobalCoordinateSizeBound rowWeight)
    (hoffset : offset < 1 + leftSteps + rightSteps + 1) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt start offset /\
        row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
        compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
  apply exists_checkedStepRow_at_binary_execution_offset
    (compactNumericVerifierAcceptedTreeRowBound rowWeight) hrootStep
    hleftExecute hrightExecute hcombineStep
  · rcases hrootRow with ⟨row, hcurrent, hnext, hbound⟩
    exact ⟨row, hcurrent, hnext,
      compactNumericVerifierAcceptedTreeRowBound_of_nonLeaf hbound⟩
  · exact hleftRows
  · exact hrightRows
  · rcases hcombineRow with ⟨row, hcurrent, hnext, hbound⟩
    exact ⟨row, hcurrent, hnext,
      compactNumericVerifierAcceptedTreeRowBound_of_nonParse hbound⟩
  · exact hoffset

set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem exists_compactNumericVerifierAcceptedClosedLeafRow_at_zero
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.closed Gamma formula) .leaf)
    {rowWeight : Nat}
    (hweights : forall offset,
      offset <= compactNumericTreeTaskSteps (.closed Gamma formula) .leaf ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState (.closed Gamma formula) .leaf
              proofSuffix certificateSuffix restTasks values) offset) <=
          rowWeight) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.closed Gamma formula) .leaf
          proofSuffix certificateSuffix restTasks values) 0 /\
      row.nextState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.closed Gamma formula) .leaf
          proofSuffix certificateSuffix restTasks values) 1 /\
      compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree := .closed Gamma formula
  let certificate : StructuralValidityCertificate := .leaf
  let start := compactNumericTreeTaskStartState tree certificate
    proofSuffix certificateSuffix restTasks values
  let nextState : CompactNumericVerifierState :=
    (((proofSuffix, certificateSuffix),
      (restTasks,
        ((compactListedProofNodeExpectedFields tree proofSuffix).2.1,
          true) :: values)), none)
  have htrace : (listedCertificateValidTrace tree certificate).1 = true :=
    (listedCertificateValidTrace_result_eq_true_iff tree certificate).2 hvalid
  have hrunRaw := compactNumericClosedLeafTask_execute Gamma formula
    proofSuffix certificateSuffix restTasks values
  have hstep : compactNumericVerifierStep start = nextState := by
    simpa [tree, certificate, start, nextState,
      compactNumericTreeTaskStartState, compactNumericTreeTaskSteps,
      compactNumericTreeTaskSuccessState, compactListedProofNodeExpectedFields,
      ListedCheckedPAProofTree.conclusionList, Function.iterate_one,
      htrace] using
      hrunRaw
  have hcurrent : compactNumericVerifierStateWeight start <= rowWeight := by
    simpa [start, tree, certificate, compactNumericVerifierStateAt] using
      hweights 0 (by simp [compactNumericTreeTaskSteps])
  have hnext : compactNumericVerifierStateWeight nextState <= rowWeight := by
    rw [← hstep]
    simpa [start, tree, certificate, compactNumericVerifierStateAt,
      Function.iterate_one] using
      hweights 1 (by simp [compactNumericTreeTaskSteps])
  rcases
      exists_compactNumericVerifierTypedClosedCheckedStepRow_with_globalBound
        Gamma formula proofSuffix certificateSuffix restTasks values hvalid
        hcurrent hnext with
    ⟨row, hrowCurrent, hrowNext, hrowBound⟩
  refine ⟨row, ?_, ?_,
    compactNumericVerifierAcceptedTreeRowBound_of_closed hrowBound⟩
  · simpa [start, tree, certificate, compactNumericVerifierStateAt,
      compactNumericTreeTaskStartState] using hrowCurrent
  · have hstateAtOne :
        compactNumericVerifierStateAt start 1 = nextState := by
      simpa only [compactNumericVerifierStateAt, Function.iterate_one] using
        hstep
    exact hrowNext.trans (by
      simpa only [start, tree, certificate] using hstateAtOne.symm)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem exists_compactNumericVerifierAcceptedPAAxiomLeafRow_at_zero
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (paCertificate : PAAxiomCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.axm Gamma sentence)
      (.axiomCert paCertificate))
    {rowWeight : Nat}
    (hweights : forall offset,
      offset <= compactNumericTreeTaskSteps (.axm Gamma sentence)
          (.axiomCert paCertificate) ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState (.axm Gamma sentence)
              (.axiomCert paCertificate) proofSuffix certificateSuffix
              restTasks values) offset) <= rowWeight) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.axm Gamma sentence)
          (.axiomCert paCertificate) proofSuffix certificateSuffix restTasks
          values) 0 /\
      row.nextState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.axm Gamma sentence)
          (.axiomCert paCertificate) proofSuffix certificateSuffix restTasks
          values) 1 /\
      compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree := .axm Gamma sentence
  let certificate : StructuralValidityCertificate :=
    .axiomCert paCertificate
  let start := compactNumericTreeTaskStartState tree certificate
    proofSuffix certificateSuffix restTasks values
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected certificate certificateSuffix
  let result := compactAxmRuleCheck
    (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1))
  let nextState : CompactNumericVerifierState :=
    (((proofSuffix, certificateSuffix),
      (restTasks, (proofNode.2.1, result) :: values)), none)
  have htrace : (listedCertificateValidTrace tree certificate).1 = true :=
    (listedCertificateValidTrace_result_eq_true_iff tree certificate).2 hvalid
  have hresult : result = true := by
    simpa [result, proofNode, certificateNode, tree, certificate,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactSentenceTokens, arithmeticPropositionTokenValue] using
      (compactAxmRuleCheck_canonical Gamma sentence paCertificate).trans
        htrace
  have hrunRaw := compactNumericAxmLeafTask_execute Gamma sentence
    paCertificate proofSuffix certificateSuffix restTasks values
  have hstep : compactNumericVerifierStep start = nextState := by
    simpa [tree, certificate, start, proofNode, result, nextState,
      compactNumericTreeTaskStartState, compactNumericTreeTaskSteps,
      compactNumericTreeTaskSuccessState, compactListedProofNodeExpectedFields,
      ListedCheckedPAProofTree.conclusionList, Function.iterate_one, htrace,
      hresult] using hrunRaw
  have hcurrent : compactNumericVerifierStateWeight start <= rowWeight := by
    simpa [start, tree, certificate, compactNumericVerifierStateAt] using
      hweights 0 (by simp [compactNumericTreeTaskSteps])
  have hnext : compactNumericVerifierStateWeight nextState <= rowWeight := by
    rw [← hstep]
    simpa [start, tree, certificate, compactNumericVerifierStateAt,
      Function.iterate_one] using
      hweights 1 (by simp [compactNumericTreeTaskSteps])
  rcases
      exists_compactNumericVerifierTypedAcceptedPAAxiomCheckedStepRow_with_globalBound
        Gamma sentence paCertificate proofSuffix certificateSuffix restTasks
        values hvalid hcurrent hnext with
    ⟨row, hrowCurrent, hrowNext, hrowBound⟩
  refine ⟨row, ?_, ?_,
    compactNumericVerifierAcceptedTreeRowBound_of_paAxiom hrowBound⟩
  · simpa [start, tree, certificate, compactNumericVerifierStateAt,
      compactNumericTreeTaskStartState] using hrowCurrent
  · have hstateAtOne :
        compactNumericVerifierStateAt start 1 = nextState := by
      simpa only [compactNumericVerifierStateAt, Function.iterate_one] using
        hstep
    exact hrowNext.trans (by
      simpa only [start, tree, certificate] using hstateAtOne.symm)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem exists_compactNumericVerifierAcceptedVerumLeafRow_at_zero
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.verum Gamma) .leaf)
    {rowWeight : Nat}
    (hweights : forall offset,
      offset <= compactNumericTreeTaskSteps (.verum Gamma) .leaf ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt
            (compactNumericTreeTaskStartState (.verum Gamma) .leaf
              proofSuffix certificateSuffix restTasks values) offset) <=
          rowWeight) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.verum Gamma) .leaf proofSuffix
          certificateSuffix restTasks values) 0 /\
      row.nextState = compactNumericVerifierStateAt
        (compactNumericTreeTaskStartState (.verum Gamma) .leaf proofSuffix
          certificateSuffix restTasks values) 1 /\
      compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
  let tree : ListedCheckedPAProofTree := .verum Gamma
  let certificate : StructuralValidityCertificate := .leaf
  let start := compactNumericTreeTaskStartState tree certificate
    proofSuffix certificateSuffix restTasks values
  let nextState : CompactNumericVerifierState :=
    (((proofSuffix, certificateSuffix),
      (restTasks,
        ((compactListedProofNodeExpectedFields tree proofSuffix).2.1,
          true) :: values)), none)
  have htrace : (listedCertificateValidTrace tree certificate).1 = true :=
    (listedCertificateValidTrace_result_eq_true_iff tree certificate).2 hvalid
  have hrunRaw := compactNumericVerumLeafTask_execute Gamma proofSuffix
    certificateSuffix restTasks values
  have hstep : compactNumericVerifierStep start = nextState := by
    simpa [tree, certificate, start, nextState,
      compactNumericTreeTaskStartState, compactNumericTreeTaskSteps,
      compactNumericTreeTaskSuccessState, compactListedProofNodeExpectedFields,
      ListedCheckedPAProofTree.conclusionList, Function.iterate_one,
      htrace] using hrunRaw
  have hcurrent : compactNumericVerifierStateWeight start <= rowWeight := by
    simpa [start, tree, certificate, compactNumericVerifierStateAt] using
      hweights 0 (by simp [compactNumericTreeTaskSteps])
  have hnext : compactNumericVerifierStateWeight nextState <= rowWeight := by
    rw [← hstep]
    simpa [start, tree, certificate, compactNumericVerifierStateAt,
      Function.iterate_one] using
      hweights 1 (by simp [compactNumericTreeTaskSteps])
  rcases
      exists_compactNumericVerifierTypedVerumCheckedStepRow_with_globalBound
        Gamma proofSuffix certificateSuffix restTasks values hvalid hcurrent
        hnext with
    ⟨row, hrowCurrent, hrowNext, hrowBound⟩
  refine ⟨row, ?_, ?_,
    compactNumericVerifierAcceptedTreeRowBound_of_verum hrowBound⟩
  · simpa [start, tree, certificate, compactNumericVerifierStateAt,
      compactNumericTreeTaskStartState] using hrowCurrent
  · have hstateAtOne :
        compactNumericVerifierStateAt start 1 = nextState := by
      simpa only [compactNumericVerifierStateAt, Function.iterate_one] using
        hstep
    exact hrowNext.trans (by
      simpa only [start, tree, certificate] using hstateAtOne.symm)

#print axioms compactNumericVerifierAcceptedTreeRowBound_of_closed
#print axioms compactNumericVerifierUnaryExecutionWeightBounds_of_parent
#print axioms compactNumericVerifierBinaryExecutionWeightBounds_of_parent
#print axioms exists_compactNumericVerifierAcceptedTreeRow_at_unary_offset
#print axioms exists_compactNumericVerifierAcceptedTreeRow_at_binary_offset
#print axioms exists_compactNumericVerifierAcceptedClosedLeafRow_at_zero
#print axioms exists_compactNumericVerifierAcceptedPAAxiomLeafRow_at_zero
#print axioms exists_compactNumericVerifierAcceptedVerumLeafRow_at_zero

end FoundationCompactNumericListedDirectVerifierAcceptedTreeTaskRowsGlobalBound
