import integration.FoundationCompactNumericListedDirectVerifierAcceptedTerminalRowsGlobalBound
import integration.FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsControlBounds

/-!
# Numeric control bounds for accepted terminal rows

This strengthens the canonical halted-tail row theorem without changing its
checker semantics.  Coordinates 1 and 2 retain numeric bounds, while all 429
coordinates retain the existing binary-size bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedTerminalRowsControlBounds

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
open FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsGlobalBound
open FoundationCompactNumericListedDirectVerifierAcceptedTreeGlobalCoordinateBound
open FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsControlBounds
open FoundationCompactNumericListedPAAxiomLeafOccurrence

structure CompactNumericVerifierAcceptedRowControlBounds
    (row : CompactNumericVerifierCheckedStepRow) (rowWeight : Nat) : Prop where
  stateWidth_le : row.environment 1 <= 4 * rowWeight
  stateTokenCount_le : row.environment 2 <= 2 * rowWeight

set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem exists_canonicalAcceptedHaltedCheckedStepRow_with_controlBounds
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
        CompactNumericVerifierAcceptedRowControlBounds row rowWeight /\
        (forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound
              rowWeight) /\
        row.currentState.2 ≠ none := by
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
        offset + 1 = (taskSteps + 1) + (extra + 1) := by omega
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
  have hexplicitWeight : compactNumericVerifierStateWeight
      (((([], []), ([], finalValues)), some result)) <= rowWeight := by
    simpa only [hcurrentAt, hfinalExplicit] using hcurrentWeight
  rcases exists_compactNumericVerifierHaltedCheckedStepRow_with_controlBounds
      [] [] [] finalValues result with
    ⟨row, hrowCurrent, hrowNext, hcontrols, hcoordinates⟩
  let explicitState : CompactNumericVerifierState :=
    ((([], []), ([], finalValues)), some result)
  have hpairWeight : compactNumericVerifierStatePairTokenWeightBound
      (compactAdditiveValueWeight explicitState)
      (compactAdditiveValueWeight explicitState) <=
        2 * rowWeight := by
    have hstate : compactAdditiveValueWeight explicitState <= rowWeight := by
      simpa [compactNumericVerifierStateWeight, explicitState] using
        hexplicitWeight
    unfold compactNumericVerifierStatePairTokenWeightBound
    omega
  refine ⟨row,
    hrowCurrent.trans (hcurrentAt.trans hfinalExplicit).symm,
    hrowNext.trans (hnextAt.trans hfinalExplicit).symm, ?_, ?_, ?_⟩
  · refine
    { stateWidth_le := ?_
      stateTokenCount_le := ?_ }
    · have hpair : 2 *
          compactNumericVerifierStatePairTokenWeightBound
            (compactAdditiveValueWeight explicitState)
            (compactAdditiveValueWeight explicitState) <=
          2 * (2 * rowWeight) :=
        Nat.mul_le_mul (Nat.le_refl 2) hpairWeight
      exact hcontrols.stateWidth_le.trans (by
        have h := hpair.trans (by omega : 2 * (2 * rowWeight) <= 4 * rowWeight)
        simpa [explicitState] using h)
    · exact hcontrols.stateTokenCount_le.trans (by
        simpa [explicitState] using hpairWeight)
  · intro coordinate
    exact (hcoordinates coordinate).trans
      ((compactNumericVerifierSimpleLocalCoordinateSizeBound_le_global
          hexplicitWeight hexplicitWeight).trans
        ((compactNumericVerifierSimpleGlobal_le_nonParseGlobal rowWeight).trans
          (compactNumericVerifierNonParseGlobal_le_acceptedTreeGlobal
            rowWeight)))
  · intro hnone
    have hstatus : (some result : Option Bool) = none := by
      simpa only [hrowCurrent, explicitState] using hnone
    cases hstatus

#print axioms
  exists_canonicalAcceptedHaltedCheckedStepRow_with_controlBounds

end FoundationCompactNumericListedDirectVerifierAcceptedTerminalRowsControlBounds
