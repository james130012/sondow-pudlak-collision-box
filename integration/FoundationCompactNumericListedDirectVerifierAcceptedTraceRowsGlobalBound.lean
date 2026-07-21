import integration.FoundationCompactNumericListedDirectVerifierAcceptedTreeTaskRowsGlobalBound
import integration.FoundationCompactNumericListedDirectVerifierAcceptedTerminalRowsGlobalBound
import integration.FoundationCompactNumericListedDirectVerifierAcceptedTreeTaskRowsStructuralInduction

/-!
# Globally bounded rows throughout an accepted canonical verifier trace

The tree-task rows, the unique finish row, and every later halted self-loop
form a disjoint exhaustive partition of all offsets below the public fuel.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedTraceRowsGlobalBound

open FoundationCompactAdditiveTokenCodec
open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectCanonicalTraceBounds
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierAcceptedTreeGlobalCoordinateBound
open FoundationCompactNumericListedDirectVerifierAcceptedTreeTaskRowsGlobalBound
open FoundationCompactNumericListedDirectVerifierAcceptedTerminalRowsGlobalBound
open FoundationCompactNumericListedDirectVerifierAcceptedTreeTaskRowsStructuralInduction
open FoundationCompactNumericListedPAAxiomLeafOccurrence

set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem
    exists_canonicalAcceptedCheckedStepRow_at_offset_with_globalBound_of_taskRows
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight)
    (htaskRows : forall taskOffset,
      taskOffset < compactNumericTreeTaskSteps tree certificate ->
        exists row : CompactNumericVerifierCheckedStepRow,
          row.currentState = compactNumericVerifierStateAt
            (compactNumericVerifierInitialState
              (compactListedProofTokens tree)
              (compactStructuralCertificateTokens certificate))
            taskOffset /\
          row.nextState = compactNumericVerifierStateAt
            (compactNumericVerifierInitialState
              (compactListedProofTokens tree)
              (compactStructuralCertificateTokens certificate))
            (taskOffset + 1) /\
          compactNumericVerifierAcceptedTreeRowBound
            (compactNumericVerifierPublicRowWeightBound streamWeight) row)
    {offset : Nat}
    (hoffset : offset < compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt
        (compactNumericVerifierInitialState (compactListedProofTokens tree)
          (compactStructuralCertificateTokens certificate)) offset /\
      row.nextState = compactNumericVerifierStateAt
        (compactNumericVerifierInitialState (compactListedProofTokens tree)
          (compactStructuralCertificateTokens certificate)) (offset + 1) /\
      compactNumericVerifierAcceptedTreeRowBound
        (compactNumericVerifierPublicRowWeightBound streamWeight) row := by
  let taskSteps := compactNumericTreeTaskSteps tree certificate
  by_cases htask : offset < taskSteps
  · exact htaskRows offset htask
  · by_cases hfinish : offset = taskSteps
    · subst offset
      rcases exists_canonicalAcceptedFinishCheckedStepRow_with_globalBound
          tree certificate hvalid hproof hcertificate with
        ⟨row, hcurrent, hnext, hcoordinates⟩
      exact ⟨row, hcurrent, hnext, hcoordinates⟩
    · have hterminal : taskSteps + 1 <= offset := by omega
      rcases exists_canonicalAcceptedHaltedCheckedStepRow_with_globalBound
          tree certificate hvalid hproof hcertificate hterminal hoffset with
        ⟨row, hcurrent, hnext, hcoordinates⟩
      exact ⟨row, hcurrent, hnext, hcoordinates⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem exists_canonicalAcceptedCheckedStepRow_at_offset_with_globalBound
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight offset : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight)
    (hoffset : offset < compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)) :
    let start := compactNumericVerifierInitialState
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)
    let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt start offset /\
        row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
        compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
  let proofTokens := compactListedProofTokens tree
  let certificateTokens := compactStructuralCertificateTokens certificate
  let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
  let start := compactNumericVerifierInitialState proofTokens certificateTokens
  let taskStart := compactNumericTreeTaskStartState tree certificate
    [] [] [] []
  let taskSteps := compactNumericTreeTaskSteps tree certificate
  let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
  have hfuel : fuel <=
      compactNumericVerifierPublicFuelWeightBound streamWeight := by
    simpa only [fuel, proofTokens, certificateTokens] using
      compactNumericVerifierFuelBound_le_weightBound hproof hcertificate
  have htaskFuel : taskSteps + 1 <= fuel := by
    simpa only [taskSteps, fuel, proofTokens, certificateTokens] using
      compactNumericTreeTaskSteps_add_one_le_fuel tree certificate
  have hweights : forall taskOffset, taskOffset <= taskSteps ->
      compactNumericVerifierStateWeight
        (compactNumericVerifierStateAt taskStart taskOffset) <=
          rowWeight := by
    intro taskOffset htaskOffset
    have hcanonical :=
      canonicalVerifierStateAt_weight_le_publicRowBound_of_le
        hproof hcertificate hfuel (by omega : taskOffset <= fuel)
    simpa only [taskStart, start, rowWeight, proofTokens, certificateTokens,
      compactNumericTreeTaskStartState,
      compactNumericVerifierInitialState, List.append_nil] using hcanonical
  have htaskRows : forall taskOffset, taskOffset < taskSteps ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start taskOffset /\
          row.nextState =
            compactNumericVerifierStateAt start (taskOffset + 1) /\
          compactNumericVerifierAcceptedTreeRowBound rowWeight row := by
    intro taskOffset htaskOffset
    have hrow :=
      exists_compactNumericVerifierAcceptedTreeTaskCheckedStepRow_with_globalBound
        tree certificate [] [] [] [] hvalid hweights htaskOffset
    simpa only [taskStart, start, proofTokens, certificateTokens,
      compactNumericTreeTaskStartState,
      compactNumericVerifierInitialState, List.append_nil] using hrow
  have hrow :=
    exists_canonicalAcceptedCheckedStepRow_at_offset_with_globalBound_of_taskRows
      tree certificate hvalid hproof hcertificate htaskRows hoffset
  simpa only [start, rowWeight, proofTokens, certificateTokens] using hrow

#print axioms
  exists_canonicalAcceptedCheckedStepRow_at_offset_with_globalBound_of_taskRows
#print axioms
  exists_canonicalAcceptedCheckedStepRow_at_offset_with_globalBound

end FoundationCompactNumericListedDirectVerifierAcceptedTraceRowsGlobalBound
