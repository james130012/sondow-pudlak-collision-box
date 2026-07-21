import integration.FoundationCompactNumericListedDirectVerifierAcceptedTreeRowStateTableControlBounds
import integration.FoundationCompactNumericListedDirectVerifierAcceptedTerminalRowsControlBounds

/-!
# Accepted terminal rows with common state-table controls

The canonical finish row and every halted tail row are lifted from their local
pair budgets to the common accepted-row budget used by tree-task rows.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedTerminalRowsStateTableControlBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectCanonicalTraceBounds
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierSimpleStepPublicBounds
open FoundationCompactNumericListedDirectVerifierCombinePublicBounds
open FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsGlobalBound
open FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsControlBounds
open FoundationCompactNumericListedDirectVerifierAcceptedTreeGlobalCoordinateBound
open FoundationCompactNumericListedDirectVerifierAcceptedTerminalRowsControlBounds
open FoundationCompactNumericListedDirectVerifierAcceptedStateTableControlBounds
open FoundationCompactNumericListedDirectVerifierAcceptedTreeRowStateTableControlBounds
open FoundationCompactNumericListedPAAxiomLeafOccurrence

theorem acceptedStateTableControlBounds_of_pairControl
    (row : CompactNumericVerifierCheckedStepRow)
    (pairWeightBound rowWeight : Nat)
    (hcontrol : CompactNumericVerifierCheckedRowControlBounds
      row pairWeightBound)
    (hpair : pairWeightBound <= 2 * rowWeight) :
    CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight := by
  have htokenBudget : 2 * rowWeight <=
      compactNumericVerifierAcceptedStateTokenCountBound rowWeight := by
    unfold compactNumericVerifierAcceptedStateTokenCountBound
      compactNumericVerifierPublicCombineTokenWeightBound
    omega
  have hwidthBudget : 4 * rowWeight <=
      compactNumericVerifierAcceptedStateWidthBound rowWeight := by
    unfold compactNumericVerifierAcceptedStateWidthBound
      compactNumericVerifierAcceptedStateTokenCountBound
      compactNumericVerifierPublicCombineTokenWeightBound
    omega
  constructor
  · exact hcontrol.stateWidth_le.trans
      ((Nat.mul_le_mul_left 2 hpair).trans (by
        have : 2 * (2 * rowWeight) = 4 * rowWeight := by omega
        simpa only [this] using hwidthBudget))
  · exact hcontrol.stateTokenCount_le.trans (hpair.trans htokenBudget)

theorem acceptedStateTableControlBounds_of_terminalControl
    (row : CompactNumericVerifierCheckedStepRow)
    (rowWeight : Nat)
    (hcontrol : CompactNumericVerifierAcceptedRowControlBounds row rowWeight) :
    CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight := by
  have htokenBudget : 2 * rowWeight <=
      compactNumericVerifierAcceptedStateTokenCountBound rowWeight := by
    unfold compactNumericVerifierAcceptedStateTokenCountBound
      compactNumericVerifierPublicCombineTokenWeightBound
    omega
  have hwidthBudget : 4 * rowWeight <=
      compactNumericVerifierAcceptedStateWidthBound rowWeight := by
    unfold compactNumericVerifierAcceptedStateWidthBound
      compactNumericVerifierAcceptedStateTokenCountBound
      compactNumericVerifierPublicCombineTokenWeightBound
    omega
  exact
    { stateWidth_le := hcontrol.stateWidth_le.trans hwidthBudget
      stateTokenCount_le := hcontrol.stateTokenCount_le.trans htokenBudget }

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem exists_canonicalAcceptedFinishCheckedStepRow_with_globalControlBound
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    let proofTokens := compactListedProofTokens tree
    let certificateTokens := compactStructuralCertificateTokens certificate
    let start := compactNumericVerifierInitialState proofTokens certificateTokens
    let taskSteps := compactNumericTreeTaskSteps tree certificate
    let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt start taskSteps /\
        row.nextState = compactNumericVerifierStateAt start (taskSteps + 1) /\
        CompactNumericVerifierAcceptedTreeControlledRowBound
          rowWeight row := by
  let proofTokens := compactListedProofTokens tree
  let certificateTokens := compactStructuralCertificateTokens certificate
  let start := compactNumericVerifierInitialState proofTokens certificateTokens
  let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
  let taskSteps := compactNumericTreeTaskSteps tree certificate
  let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
  let finalValues : List CompactNumericChildResult :=
    [(arithmeticPropositionTokenValues tree.conclusionList,
      (listedCertificateValidTrace tree certificate).1)]
  let successState := compactNumericTreeTaskSuccessState
    tree certificate [] [] [] []
  let finalState : CompactNumericVerifierState :=
    (compactNumericTreeFinalPayload tree certificate,
      some (listedCertificateValidTrace tree certificate).1)
  have hshape := compactNumericTreeCertificateShapeMatches_eq_true_of_valid
    tree certificate hvalid
  have htaskRaw := compactNumericTreeTask_execute_of_shape
    tree certificate [] [] [] [] hshape
  have htask :
      (compactNumericVerifierStep^[taskSteps]) start = successState := by
    simpa [taskSteps, start, proofTokens, certificateTokens, successState,
      compactNumericVerifierInitialState] using htaskRaw
  have hfinishStep : compactNumericVerifierStep successState = finalState := by
    simpa [successState, finalState] using
      compactNumericVerifierStep_finish_canonical tree certificate
  have hfinishIterate :
      (compactNumericVerifierStep^[1]) successState = finalState := by
    simpa only [Function.iterate_one] using hfinishStep
  have hall := compactNumericVerifier_iterate_trans htask hfinishIterate
  have hcurrentAt :
      compactNumericVerifierStateAt start taskSteps = successState := by
    simpa only [compactNumericVerifierStateAt] using htask
  have hnextAt :
      compactNumericVerifierStateAt start (taskSteps + 1) = finalState := by
    simpa only [compactNumericVerifierStateAt] using hall
  have hsuccessExplicit : successState =
      ((([], []), ([], finalValues)), none) := by
    simp [successState, finalValues, compactNumericTreeTaskSuccessState]
  have hfinishExplicit :
      compactNumericFinishState (([], []), ([], finalValues)) =
        finalState := by
    simp [finalValues, finalState, compactNumericFinishState,
      compactNumericTreeFinalPayload]
  have hfuel : fuel <=
      compactNumericVerifierPublicFuelWeightBound streamWeight := by
    simpa only [fuel, proofTokens, certificateTokens] using
      compactNumericVerifierFuelBound_le_weightBound hproof hcertificate
  have htaskFuel : taskSteps + 1 <= fuel := by
    simpa only [taskSteps, fuel, proofTokens, certificateTokens] using
      compactNumericTreeTaskSteps_add_one_le_fuel tree certificate
  have hcurrentWeight : compactNumericVerifierStateWeight
      (compactNumericVerifierStateAt start taskSteps) <= rowWeight := by
    simpa only [start, taskSteps, rowWeight, fuel, proofTokens,
      certificateTokens] using
      canonicalVerifierStateAt_weight_le_publicRowBound_of_le
        hproof hcertificate hfuel (by omega : taskSteps <= fuel)
  have hnextWeight : compactNumericVerifierStateWeight
      (compactNumericVerifierStateAt start (taskSteps + 1)) <= rowWeight := by
    simpa only [start, taskSteps, rowWeight, fuel, proofTokens,
      certificateTokens] using
      canonicalVerifierStateAt_weight_le_publicRowBound_of_le
        hproof hcertificate hfuel htaskFuel
  have hcurrentExplicitWeight : compactNumericVerifierStateWeight
      (((([], []), ([], finalValues)), none)) <= rowWeight := by
    simpa only [hcurrentAt, hsuccessExplicit] using hcurrentWeight
  have hnextExplicitWeight : compactNumericVerifierStateWeight
      (compactNumericFinishState (([], []), ([], finalValues))) <=
        rowWeight := by
    simpa only [hnextAt, hfinishExplicit] using hnextWeight
  rcases
      exists_compactNumericVerifierFinishCheckedStepRow_with_controlBounds
        [] [] finalValues with
    ⟨row, hrowCurrent, hrowNext, hcontrol, hcoordinates⟩
  let currentState : CompactNumericVerifierState :=
    ((([], []), ([], finalValues)), none)
  let nextState := compactNumericFinishState (([], []), ([], finalValues))
  have hpair : compactNumericVerifierStatePairTokenWeightBound
      (compactAdditiveValueWeight currentState)
      (compactAdditiveValueWeight nextState) <= 2 * rowWeight := by
    unfold compactNumericVerifierStatePairTokenWeightBound
    have hcurrent : compactAdditiveValueWeight currentState <= rowWeight := by
      simpa only [currentState, compactNumericVerifierStateWeight] using
        hcurrentExplicitWeight
    have hnext : compactAdditiveValueWeight nextState <= rowWeight := by
      simpa only [nextState, compactNumericVerifierStateWeight] using
        hnextExplicitWeight
    omega
  refine ⟨row,
    hrowCurrent.trans (hcurrentAt.trans hsuccessExplicit).symm,
    hrowNext.trans (hnextAt.trans hfinishExplicit.symm).symm, ?_⟩
  refine
    { coordinates := ?_
      stateTable := acceptedStateTableControlBounds_of_pairControl row _
        rowWeight hcontrol hpair
      parserControls := ?_
      combineControls := ?_ }
  · intro coordinate
    exact (hcoordinates coordinate).trans
      ((compactNumericVerifierSimpleLocalCoordinateSizeBound_le_global
        hcurrentExplicitWeight hnextExplicitWeight).trans
        ((compactNumericVerifierSimpleGlobal_le_nonParseGlobal rowWeight).trans
          (compactNumericVerifierNonParseGlobal_le_acceptedTreeGlobal rowWeight)))
  · intro _hstatus rest htasks
    have htasks' : ([] : List CompactNumericVerifierTask) =
        compactNumericParseTask :: rest := by
      simpa only [hrowCurrent, currentState] using htasks
    cases htasks'
  · intro _hstatus task rest htasks _htaskNe
    have htasks' : ([] : List CompactNumericVerifierTask) = task :: rest := by
      simpa only [hrowCurrent, currentState] using htasks
    cases htasks'

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem exists_canonicalAcceptedHaltedCheckedStepRow_with_globalControlBound
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight offset : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight)
    (hterminal : compactNumericTreeTaskSteps tree certificate + 1 <= offset)
    (hoffset : offset < compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)) :
    let proofTokens := compactListedProofTokens tree
    let certificateTokens := compactStructuralCertificateTokens certificate
    let start := compactNumericVerifierInitialState proofTokens certificateTokens
    let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt start offset /\
        row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
        CompactNumericVerifierAcceptedTreeControlledRowBound
          rowWeight row := by
  rcases exists_canonicalAcceptedHaltedCheckedStepRow_with_controlBounds
      tree certificate hvalid hproof hcertificate hterminal hoffset with
    ⟨row, hcurrent, hnext, hcontrol, hcoordinates, hstatus⟩
  refine ⟨row, hcurrent, hnext, ?_⟩
  exact
    { coordinates := hcoordinates
      stateTable := acceptedStateTableControlBounds_of_terminalControl
        row _ hcontrol
      parserControls := by
        intro hnone _restTasks _htasks
        exact (hstatus hnone).elim
      combineControls := by
        intro hnone _task _restTasks _htasks _htaskNe
        exact (hstatus hnone).elim }

#print axioms acceptedStateTableControlBounds_of_pairControl
#print axioms acceptedStateTableControlBounds_of_terminalControl
#print axioms exists_canonicalAcceptedFinishCheckedStepRow_with_globalControlBound
#print axioms exists_canonicalAcceptedHaltedCheckedStepRow_with_globalControlBound

end FoundationCompactNumericListedDirectVerifierAcceptedTerminalRowsStateTableControlBounds
