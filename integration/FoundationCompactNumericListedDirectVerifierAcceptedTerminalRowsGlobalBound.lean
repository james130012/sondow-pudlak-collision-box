import integration.FoundationCompactNumericListedDirectVerifierAcceptedTreeGlobalCoordinateBound
import integration.FoundationCompactNumericListedDirectCanonicalTraceBounds
import integration.FoundationCompactNumericListedPAAxiomLeafOccurrence

/-!
# Globally bounded terminal rows of a valid canonical verifier trace

After the depth-first tree task finishes, one real finish step produces the
final Boolean state.  All remaining fuel steps are the verifier's halted
self-loop.  This file installs those rows at their exact canonical offsets.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedTerminalRowsGlobalBound

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
open FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsGlobalBound
open FoundationCompactNumericListedDirectVerifierAcceptedTreeGlobalCoordinateBound
open FoundationCompactNumericListedPAAxiomLeafOccurrence

set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem exists_canonicalAcceptedFinishCheckedStepRow_with_globalBound
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
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound
              rowWeight := by
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
      exists_compactNumericVerifierFinishCheckedStepRow_with_globalBound
        [] [] finalValues hcurrentExplicitWeight hnextExplicitWeight with
    ⟨row, hrowCurrent, hrowNext, hcoordinates⟩
  refine ⟨row,
    hrowCurrent.trans (hcurrentAt.trans hsuccessExplicit).symm,
    hrowNext.trans (hnextAt.trans hfinishExplicit.symm).symm, ?_⟩
  intro coordinate
  exact (hcoordinates coordinate).trans
    (compactNumericVerifierNonParseGlobal_le_acceptedTreeGlobal rowWeight)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem exists_canonicalAcceptedHaltedCheckedStepRow_with_globalBound
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
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound
              rowWeight := by
  let proofTokens := compactListedProofTokens tree
  let certificateTokens := compactStructuralCertificateTokens certificate
  let start := compactNumericVerifierInitialState proofTokens certificateTokens
  let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
  let taskSteps := compactNumericTreeTaskSteps tree certificate
  let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
  let result := (listedCertificateValidTrace tree certificate).1
  let finalValues : List CompactNumericChildResult :=
    [(arithmeticPropositionTokenValues tree.conclusionList, result)]
  let successState := compactNumericTreeTaskSuccessState
    tree certificate [] [] [] []
  let finalPayload := compactNumericTreeFinalPayload tree certificate
  let finalState : CompactNumericVerifierState :=
    (finalPayload, some result)
  have hshape := compactNumericTreeCertificateShapeMatches_eq_true_of_valid
    tree certificate hvalid
  have htaskRaw := compactNumericTreeTask_execute_of_shape
    tree certificate [] [] [] [] hshape
  have htask :
      (compactNumericVerifierStep^[taskSteps]) start = successState := by
    simpa [taskSteps, start, proofTokens, certificateTokens, successState,
      compactNumericVerifierInitialState] using htaskRaw
  have hfinishStep : compactNumericVerifierStep successState = finalState := by
    simpa [successState, finalState, finalPayload, result] using
      compactNumericVerifierStep_finish_canonical tree certificate
  have hfinishIterate :
      (compactNumericVerifierStep^[1]) successState = finalState := by
    simpa only [Function.iterate_one] using hfinishStep
  have hused := compactNumericVerifier_iterate_trans htask hfinishIterate
  let extra := offset - (taskSteps + 1)
  have hoffsetSplit : offset = (taskSteps + 1) + extra := by
    dsimp only [extra]
    omega
  have hhalted := compactNumericVerifierStep_iterate_halted
    extra finalPayload result
  have hhaltedNext := compactNumericVerifierStep_iterate_halted
    (extra + 1) finalPayload result
  have htoOffset := compactNumericVerifier_iterate_trans hused hhalted
  have htoNext := compactNumericVerifier_iterate_trans hused hhaltedNext
  have hcurrentAt :
      compactNumericVerifierStateAt start offset = finalState := by
    unfold compactNumericVerifierStateAt
    rw [hoffsetSplit]
    exact htoOffset
  have hnextAt :
      compactNumericVerifierStateAt start (offset + 1) = finalState := by
    unfold compactNumericVerifierStateAt
    have hindex :
        offset + 1 = (taskSteps + 1) + (extra + 1) := by
      omega
    rw [hindex]
    exact htoNext
  have hfinalExplicit : finalState =
      ((([], []), ([], finalValues)), some result) := by
    simp [finalState, finalPayload, finalValues, result,
      compactNumericTreeFinalPayload]
  have hfuel : fuel <=
      compactNumericVerifierPublicFuelWeightBound streamWeight := by
    simpa only [fuel, proofTokens, certificateTokens] using
      compactNumericVerifierFuelBound_le_weightBound hproof hcertificate
  have hoffsetFuel : offset < fuel := by
    simpa only [fuel, proofTokens, certificateTokens] using hoffset
  have hcurrentWeight : compactNumericVerifierStateWeight
      (compactNumericVerifierStateAt start offset) <= rowWeight := by
    simpa only [start, rowWeight, fuel, proofTokens, certificateTokens] using
      canonicalVerifierStateAt_weight_le_publicRowBound_of_le
        hproof hcertificate hfuel (by omega : offset <= fuel)
  have hnextWeight : compactNumericVerifierStateWeight
      (compactNumericVerifierStateAt start (offset + 1)) <= rowWeight := by
    simpa only [start, rowWeight, fuel, proofTokens, certificateTokens] using
      canonicalVerifierStateAt_weight_le_publicRowBound_of_le
        hproof hcertificate hfuel (by omega : offset + 1 <= fuel)
  have hexplicitWeight : compactNumericVerifierStateWeight
      (((([], []), ([], finalValues)), some result)) <= rowWeight := by
    simpa only [hcurrentAt, hfinalExplicit] using hcurrentWeight
  rcases
      exists_compactNumericVerifierHaltedCheckedStepRow_with_globalBound
        [] [] [] finalValues result hexplicitWeight with
    ⟨row, hrowCurrent, hrowNext, hcoordinates⟩
  refine ⟨row,
    hrowCurrent.trans (hcurrentAt.trans hfinalExplicit).symm,
    hrowNext.trans (hnextAt.trans hfinalExplicit).symm, ?_⟩
  intro coordinate
  exact (hcoordinates coordinate).trans
    (compactNumericVerifierNonParseGlobal_le_acceptedTreeGlobal rowWeight)

#print axioms exists_canonicalAcceptedFinishCheckedStepRow_with_globalBound
#print axioms exists_canonicalAcceptedHaltedCheckedStepRow_with_globalBound

end FoundationCompactNumericListedDirectVerifierAcceptedTerminalRowsGlobalBound
