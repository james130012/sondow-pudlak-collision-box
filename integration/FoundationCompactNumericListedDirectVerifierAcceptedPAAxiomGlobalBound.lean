import integration.FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomTraceRow
import integration.FoundationCompactNumericListedDirectCanonicalTraceBounds
import integration.FoundationCompactNumericListedDirectVerifierSimpleStepPublicBounds

/-!
# One global coordinate budget for every accepted PA-leaf trace row

All local parser and PA-rule envelopes are monotone in their honest source
weights.  This file raises the exact PA-leaf row from its local streams to the
single public row-weight budget of the enclosing canonical verifier trace.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomGlobalBound

open FoundationCompactAdditiveTokenCodec
open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedStateBounds
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectCanonicalTraceBounds
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
open FoundationCompactNumericListedDirectVerifierCombinePublicBounds
open FoundationCompactNumericListedDirectVerifierSimpleStepPublicBounds
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportPublicBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
open FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedInductionPublicBounds
open FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedLeafStateGraphPublicBounds
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierTypedAcceptedPAAxiomStepPublicBounds
open FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomTraceRow
open FoundationCompactNumericListedPAAxiomLeafOccurrence

theorem
    compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound_mono
    {stateLeft stateRight proofLeft proofRight certificateLeft
      certificateRight : Nat}
    (hstate : stateLeft <= stateRight)
    (hproof : proofLeft <= proofRight)
    (hcertificate : certificateLeft <= certificateRight) :
    compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound
        stateLeft proofLeft certificateLeft <=
      compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound
        stateRight proofRight certificateRight := by
  have hproofRoot :=
    FoundationCompactNumericListedDirectProofRootSuccessPublicBounds.compactProofRootSuccessPublicCoordinateSizeBound_mono
      hproof
  have hcertificateNode :=
    FoundationCompactNumericListedDirectCertificateNodeSuccessPublicBounds.compactCertificateNodeSuccessPublicCoordinateSizeBound_mono
      hcertificate
  unfold compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound
  omega

theorem
    compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound_mono
    {stateLeft stateRight proofLeft proofRight certificateLeft
      certificateRight : Nat}
    (hstate : stateLeft <= stateRight)
    (hproof : proofLeft <= proofRight)
    (hcertificate : certificateLeft <= certificateRight) :
    compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound
        stateLeft proofLeft certificateLeft <=
      compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound
        stateRight proofRight certificateRight := by
  have hbase :=
    compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound_mono
      hstate hproof hcertificate
  have harea := Nat.mul_le_mul (Nat.add_le_add_right hbase 1) hbase
  simp only [
    compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound]
  omega

theorem
    compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound_mono
    {stateLeft stateRight proofLeft proofRight certificateLeft
      certificateRight : Nat}
    (hstate : stateLeft <= stateRight)
    (hproof : proofLeft <= proofRight)
    (hcertificate : certificateLeft <= certificateRight) :
    compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound
        stateLeft proofLeft certificateLeft <=
      compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound
        stateRight proofRight certificateRight := by
  unfold compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound
  exact
    compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound_mono
      hstate hproof hcertificate

theorem compactNumericVerifierPAAxiomLeafOriginalPayloadSourceWeightBound_mono
    {proofLeft proofRight certificateLeft certificateRight : Nat}
    (hproof : proofLeft <= proofRight)
    (hcertificate : certificateLeft <= certificateRight) :
    compactNumericVerifierPAAxiomLeafOriginalPayloadSourceWeightBound
        proofLeft certificateLeft <=
      compactNumericVerifierPAAxiomLeafOriginalPayloadSourceWeightBound
        proofRight certificateRight := by
  have hnested := compactNumericNestedListWeightBound_mono hproof
  unfold compactNumericVerifierPAAxiomLeafOriginalPayloadSourceWeightBound
  omega

theorem
    compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound_mono
    {stateLeft stateRight proofLeft proofRight certificateLeft
      certificateRight originalLeft originalRight : Nat}
    (hstate : stateLeft <= stateRight)
    (hproof : proofLeft <= proofRight)
    (hcertificate : certificateLeft <= certificateRight)
    (horiginal : originalLeft <= originalRight) :
    compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
        stateLeft proofLeft certificateLeft originalLeft <=
      compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
        stateRight proofRight certificateRight originalRight := by
  have htransport :=
    compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound_mono
      hstate hproof hcertificate
  have hpa :=
    compactNumericVerifierPAAxiomAcceptedPublicCoordinateSizeBound_mono
      horiginal
  unfold
    compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
  omega

theorem compactNumericVerifierParseSuccessStepCoordinateSizeBound_mono
    {widthLeft widthRight tokenLeft tokenRight blockLeft blockRight : Nat}
    (hwidth : widthLeft <= widthRight)
    (htoken : tokenLeft <= tokenRight)
    (hblock : blockLeft <= blockRight) :
    compactNumericVerifierParseSuccessStepCoordinateSizeBound
        widthLeft tokenLeft blockLeft <=
      compactNumericVerifierParseSuccessStepCoordinateSizeBound
        widthRight tokenRight blockRight := by
  have hstate :=
    compactNumericVerifierStateCoreCoordinateSizeBound_mono hwidth htoken
  unfold compactNumericVerifierParseSuccessStepCoordinateSizeBound
  omega

def compactNumericVerifierAcceptedPAAxiomGlobalCoordinateSizeBound
    (rowWeight : Nat) : Nat :=
  let pairWeight :=
    compactNumericVerifierStatePairTokenWeightBound rowWeight rowWeight
  let widthBound := 2 * pairWeight
  let stateBound :=
    compactNumericVerifierStateCoreCoordinateSizeBound widthBound pairWeight
  let originalWeightBound :=
    compactNumericVerifierPAAxiomLeafOriginalPayloadSourceWeightBound
      rowWeight rowWeight
  let blockBound :=
    compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
      stateBound rowWeight rowWeight originalWeightBound
  compactNumericVerifierParseSuccessStepCoordinateSizeBound
    widthBound pairWeight blockBound

theorem
    compactNumericVerifierAcceptedPAAxiomStepSourceCoordinateSizeBound_le_global
    {currentState nextState : CompactNumericVerifierState}
    {rowWeight : Nat}
    (hcurrent : compactNumericVerifierStateWeight currentState <= rowWeight)
    (hnext : compactNumericVerifierStateWeight nextState <= rowWeight) :
    compactNumericVerifierAcceptedPAAxiomStepSourceCoordinateSizeBound
        currentState nextState <=
      compactNumericVerifierAcceptedPAAxiomGlobalCoordinateSizeBound
        rowWeight := by
  have hcurrent' : compactAdditiveValueWeight currentState <= rowWeight := by
    simpa [compactNumericVerifierStateWeight] using hcurrent
  have hnext' : compactAdditiveValueWeight nextState <= rowWeight := by
    simpa [compactNumericVerifierStateWeight] using hnext
  have hpair := compactNumericVerifierStatePairTokenWeightBound_mono
    hcurrent' hnext'
  have htoken :=
    (compactNumericVerifierStatePairTokens_length_le
      currentState nextState).trans hpair
  have hwidth :=
    (compactNumericVerifierStatePairWidth_le
      currentState nextState).trans (Nat.mul_le_mul_left 2 hpair)
  have hproofState :
      compactAdditiveValueWeight currentState.1.1.1 <=
        compactNumericVerifierStateWeight currentState := by
    rw [compactNumericVerifierStateWeight_eq_components]
    unfold compactNumericVerifierStateComponentWeight
    omega
  have hcertificateState :
      compactAdditiveValueWeight currentState.1.1.2 <=
        compactNumericVerifierStateWeight currentState := by
    rw [compactNumericVerifierStateWeight_eq_components]
    unfold compactNumericVerifierStateComponentWeight
    omega
  have hproof := hproofState.trans hcurrent
  have hcertificate := hcertificateState.trans hcurrent
  have hstate :=
    compactNumericVerifierStateCoreCoordinateSizeBound_mono hwidth htoken
  have horiginal :=
    compactNumericVerifierPAAxiomLeafOriginalPayloadSourceWeightBound_mono
      hproof hcertificate
  have hblock :=
    compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound_mono
      hstate hproof hcertificate horiginal
  have hstep :=
    compactNumericVerifierParseSuccessStepCoordinateSizeBound_mono
      hwidth htoken hblock
  simpa only [
    compactNumericVerifierAcceptedPAAxiomStepSourceCoordinateSizeBound,
    compactNumericVerifierAcceptedPAAxiomGlobalCoordinateSizeBound] using hstep

set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem
    exists_compactNumericVerifierTypedAcceptedPAAxiomCheckedStepRow_with_globalBound
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (paCertificate : PAAxiomCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid
      (.axm Gamma sentence) (.axiomCert paCertificate))
    {rowWeight : Nat} :
    let tree : ListedCheckedPAProofTree := .axm Gamma sentence
    let structuralCertificate : StructuralValidityCertificate :=
      .axiomCert paCertificate
    let proofTokens := compactListedProofTokens tree ++ proofSuffix
    let certificateTokens :=
      compactStructuralCertificateTokens structuralCertificate ++
        certificateSuffix
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let certificateNode :=
      compactStructuralCertificateNodeExpected structuralCertificate
        certificateSuffix
    let result := compactAxmRuleCheck
      (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1))
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofSuffix, certificateSuffix),
        (restTasks, (proofNode.2.1, result) :: values)), none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <=
              compactNumericVerifierAcceptedPAAxiomGlobalCoordinateSizeBound
                rowWeight := by
  dsimp only
  intro hcurrent hnext
  rcases
      exists_compactNumericVerifierTypedAcceptedPAAxiomCheckedStepRow_with_sourcePublicBounds
        Gamma sentence paCertificate proofSuffix certificateSuffix
        restTasks values hvalid with
    ⟨row, hrowCurrent, hrowNext, hcoordinates⟩
  refine ⟨row, hrowCurrent, hrowNext, ?_⟩
  have hsource : forall coordinate : Fin 429,
      Nat.size (row.environment coordinate) <=
        compactNumericVerifierAcceptedPAAxiomStepSourceCoordinateSizeBound
          row.currentState row.nextState := by
    intro coordinate
    simpa only [hrowCurrent, hrowNext,
      compactNumericVerifierAcceptedPAAxiomStepSourceCoordinateSizeBound] using
      hcoordinates coordinate
  intro coordinate
  exact (hsource coordinate).trans
    (compactNumericVerifierAcceptedPAAxiomStepSourceCoordinateSizeBound_le_global
      (by simpa only [hrowCurrent] using hcurrent)
      (by simpa only [hrowNext] using hnext))

set_option maxHeartbeats 6000000 in
theorem
    ListedPAAxiomLeafAt.exists_checkedStepRow_at_canonical_offset_with_globalBound
    {tree : ListedCheckedPAProofTree}
    {certificate : StructuralValidityCertificate}
    {offset : Nat}
    {Gamma : List LO.FirstOrder.ArithmeticProposition}
    {sentence : LO.FirstOrder.ArithmeticSentence}
    {paCertificate : PAAxiomCertificate}
    {streamWeight : Nat}
    (occurrence : ListedPAAxiomLeafAt tree certificate offset
      Gamma sentence paCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    let proofTokens := compactListedProofTokens tree
    let certificateTokens := compactStructuralCertificateTokens certificate
    let start := compactNumericVerifierInitialState proofTokens certificateTokens
    let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt start offset /\
        row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierAcceptedPAAxiomGlobalCoordinateSizeBound
              rowWeight := by
  let proofTokens := compactListedProofTokens tree
  let certificateTokens := compactStructuralCertificateTokens certificate
  let start := compactNumericVerifierInitialState proofTokens certificateTokens
  let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
  let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
  rcases
      FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomTraceRow.ListedPAAxiomLeafAt.exists_checkedStepRow_at_canonical_offset_with_sourceBound
        occurrence hvalid with
    ⟨proofSuffix, certificateSuffix, restTasks, values, row,
      _hleafAt, hrowCurrent, hrowNext, hlocalPackage⟩
  dsimp only at hlocalPackage
  rcases hlocalPackage with
    ⟨_hcurrentExplicit, _hnextExplicit, _hcoordinates, hsource⟩
  have hfuel : fuel <=
      compactNumericVerifierPublicFuelWeightBound streamWeight :=
    compactNumericVerifierFuelBound_le_weightBound hproof hcertificate
  have htaskFuel :
      compactNumericTreeTaskSteps tree certificate + 1 <= fuel := by
    simpa only [fuel, proofTokens, certificateTokens] using
      compactNumericTreeTaskSteps_add_one_le_fuel tree certificate
  have hoffset := occurrence.offset_lt_taskSteps
  have hcurrentIndex : offset <= fuel := by omega
  have hnextIndex : offset + 1 <= fuel := by omega
  have hcurrentWeight :
      compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt start offset) <= rowWeight := by
    simpa only [start, rowWeight, fuel, proofTokens, certificateTokens] using
      canonicalVerifierStateAt_weight_le_publicRowBound_of_le
        hproof hcertificate hfuel hcurrentIndex
  have hnextWeight :
      compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt start (offset + 1)) <= rowWeight := by
    simpa only [start, rowWeight, fuel, proofTokens, certificateTokens] using
      canonicalVerifierStateAt_weight_le_publicRowBound_of_le
        hproof hcertificate hfuel hnextIndex
  have hrowCurrentWeight :
      compactNumericVerifierStateWeight row.currentState <= rowWeight := by
    simpa only [hrowCurrent] using hcurrentWeight
  have hrowNextWeight :
      compactNumericVerifierStateWeight row.nextState <= rowWeight := by
    simpa only [hrowNext] using hnextWeight
  have hraise :=
    compactNumericVerifierAcceptedPAAxiomStepSourceCoordinateSizeBound_le_global
      hrowCurrentWeight hrowNextWeight
  refine ⟨row, hrowCurrent, hrowNext, ?_⟩
  intro coordinate
  exact (hsource coordinate).trans hraise

#print axioms
  compactNumericVerifierAcceptedPAAxiomStepSourceCoordinateSizeBound_le_global
#print axioms
  exists_compactNumericVerifierTypedAcceptedPAAxiomCheckedStepRow_with_globalBound
#print axioms
  ListedPAAxiomLeafAt.exists_checkedStepRow_at_canonical_offset_with_globalBound

end FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomGlobalBound
