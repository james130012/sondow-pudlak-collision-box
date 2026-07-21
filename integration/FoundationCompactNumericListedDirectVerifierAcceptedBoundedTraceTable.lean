import integration.FoundationCompactNumericListedDirectVerifierBoundedTraceExactness
import integration.FoundationCompactNumericListedVerifierRunExactness

/-!
# An explicit bounded accepted-trace table for every valid canonical proof
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedBoundedTraceTable

open FoundationCompactAdditiveTokenCodec
open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierAcceptedTraceFormula
open FoundationCompactNumericListedDirectVerifierAcceptedTreeGlobalCoordinateBound
open FoundationCompactNumericListedDirectVerifierAcceptedTreeTaskRowsGlobalBound
open FoundationCompactNumericListedDirectVerifierAcceptedTraceRowsGlobalBound
open FoundationCompactNumericListedDirectVerifierBoundedTraceSelection
open FoundationCompactNumericListedDirectVerifierBoundedTraceExactness

def compactNumericVerifierAcceptedCoordinateSizeBound
    (streamWeight : Nat) : Nat :=
  compactNumericVerifierAcceptedTreeGlobalCoordinateSizeBound
    (compactNumericVerifierPublicRowWeightBound streamWeight)

theorem compactNumericVerifierAcceptedBoundedRowExists
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
    let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
    let start := compactNumericVerifierInitialState proofTokens certificateTokens
    forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState =
            compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <=
              compactNumericVerifierAcceptedCoordinateSizeBound
                streamWeight := by
  dsimp only
  intro offset hoffset
  rcases exists_canonicalAcceptedCheckedStepRow_at_offset_with_globalBound
      tree certificate hvalid hproof hcertificate hoffset with
    ⟨row, hcurrent, hnext, hbound⟩
  refine ⟨row, hcurrent, hnext, ?_⟩
  exact hbound

noncomputable def compactNumericVerifierAcceptedBoundedStepFormulaRows
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (streamWeight : Nat)
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    List CompactNumericVerifierStepFormulaRow :=
  let proofTokens := compactListedProofTokens tree
  let certificateTokens := compactStructuralCertificateTokens certificate
  let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
  let start := compactNumericVerifierInitialState proofTokens certificateTokens
  compactNumericVerifierBoundedStepFormulaRows fuel start
    (compactNumericVerifierAcceptedCoordinateSizeBound streamWeight)
    (compactNumericVerifierAcceptedBoundedRowExists tree certificate hvalid
      hproof hcertificate)

noncomputable def compactNumericVerifierAcceptedBoundedTraceWidth
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (streamWeight : Nat)
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) : Nat :=
  compactNumericVerifierStepFormulaDynamicWidth
    (compactNumericVerifierAcceptedBoundedStepFormulaRows tree certificate
      hvalid streamWeight hproof hcertificate)

noncomputable def compactNumericVerifierAcceptedBoundedTraceTable
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (streamWeight : Nat)
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) : Nat :=
  compactNumericVerifierStepWitnessTableCode
    (compactNumericVerifierAcceptedBoundedTraceWidth tree certificate hvalid
      streamWeight hproof hcertificate)
    (compactNumericVerifierAcceptedBoundedStepFormulaRows tree certificate
      hvalid streamWeight hproof hcertificate)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem compactNumericVerifierAcceptedBoundedTraceTable_complete
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight)
    (hproofSource : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount proofStart proofFinish
        (compactListedProofTokens tree))
    (hcertificateSource : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish
        (compactStructuralCertificateTokens certificate)) :
    CompactNumericVerifierAcceptedTraceTable
      (compactNumericVerifierAcceptedBoundedTraceWidth tree certificate hvalid
        streamWeight hproof hcertificate)
      (compactNumericVerifierAcceptedBoundedTraceTable tree certificate hvalid
        streamWeight hproof hcertificate)
      (2 ^ compactNumericVerifierAcceptedBoundedTraceWidth tree certificate
        hvalid streamWeight hproof hcertificate)
      (compactNumericVerifierFuelBound (compactListedProofTokens tree)
        (compactStructuralCertificateTokens certificate))
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish := by
  let proofTokens := compactListedProofTokens tree
  let certificateTokens := compactStructuralCertificateTokens certificate
  let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
  let start := compactNumericVerifierInitialState proofTokens certificateTokens
  let coordinateBound :=
    compactNumericVerifierAcceptedCoordinateSizeBound streamWeight
  let hrows := compactNumericVerifierAcceptedBoundedRowExists tree certificate
    hvalid hproof hcertificate
  have hfuel : 0 < fuel := by
    simp [fuel, compactNumericVerifierFuelBound]
  have hrun := compactNumericVerifierRun_canonical_of_valid tree certificate
    hvalid
  have haccepted :
      (compactNumericVerifierStateAt start fuel).2 = some true := by
    have hstatus := congrArg Prod.snd hrun
    simpa only [start, fuel, proofTokens, certificateTokens,
      compactNumericVerifierRun, compactNumericVerifierStateAt] using hstatus
  have htrace := acceptedTraceTable_complete_boundedRows coordinateBound hrows
    hfuel hproofSource hcertificateSource haccepted
  simpa only [proofTokens, certificateTokens, fuel, start, coordinateBound,
    hrows, compactNumericVerifierAcceptedBoundedTraceWidth,
    compactNumericVerifierAcceptedBoundedTraceTable,
    compactNumericVerifierAcceptedBoundedStepFormulaRows] using htrace

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem compactNumericVerifierAcceptedBoundedTraceTable_size_le
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    let fuel := compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)
    let coordinateBound :=
      compactNumericVerifierAcceptedCoordinateSizeBound streamWeight
    let width := compactNumericVerifierAcceptedBoundedTraceWidth tree
      certificate hvalid streamWeight hproof hcertificate
    let table := compactNumericVerifierAcceptedBoundedTraceTable tree
      certificate hvalid streamWeight hproof hcertificate
    width <=
        fuel *
          (compactNumericVerifierStepWitnessColumnCount * coordinateBound) /\
      Nat.size table <=
        fuel * compactNumericVerifierStepWitnessColumnCount *
          (fuel *
            (compactNumericVerifierStepWitnessColumnCount *
              coordinateBound)) /\
      Nat.size (2 ^ width) <=
        fuel *
          (compactNumericVerifierStepWitnessColumnCount * coordinateBound) +
            1 := by
  let proofTokens := compactListedProofTokens tree
  let certificateTokens := compactStructuralCertificateTokens certificate
  let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
  let start := compactNumericVerifierInitialState proofTokens certificateTokens
  let coordinateBound :=
    compactNumericVerifierAcceptedCoordinateSizeBound streamWeight
  let hrows := compactNumericVerifierAcceptedBoundedRowExists tree certificate
    hvalid hproof hcertificate
  have hbound := compactNumericVerifierBoundedTraceCoordinates_size_le fuel
    start coordinateBound hrows
  simpa only [proofTokens, certificateTokens, fuel, start, coordinateBound,
    hrows, compactNumericVerifierAcceptedBoundedTraceWidth,
    compactNumericVerifierAcceptedBoundedTraceTable,
    compactNumericVerifierAcceptedBoundedStepFormulaRows] using hbound

#print axioms compactNumericVerifierAcceptedBoundedRowExists
#print axioms compactNumericVerifierAcceptedBoundedTraceTable_complete
#print axioms compactNumericVerifierAcceptedBoundedTraceTable_size_le

end FoundationCompactNumericListedDirectVerifierAcceptedBoundedTraceTable
