import integration.FoundationCompactNumericListedPAAxiomLeafOccurrence
import integration.FoundationCompactNumericListedDirectVerifierTypedAcceptedPAAxiomStepPublicBounds

/-!
# Source-bounded PA rows at exact canonical trace offsets

A typed valid PA leaf occurrence is first located in the real depth-first
verifier execution.  Its local 429-column witness is then installed at that
exact canonical step, with a budget computed only from the two actual states.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomTraceRow

open FoundationCompactAdditiveTokenCodec
open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
open FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedLeafStateGraphPublicBounds
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierTypedAcceptedPAAxiomStepPublicBounds
open FoundationCompactNumericListedPAAxiomLeafOccurrence

def compactNumericVerifierAcceptedPAAxiomStepSourceCoordinateSizeBound
    (currentState nextState : CompactNumericVerifierState) : Nat :=
  let tokens :=
    compactAdditiveEncode currentState ++ compactAdditiveEncode nextState
  let width := (compactBinaryNatPayloadBits tokens).length
  let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
    width tokens.length
  let proofWeight :=
    compactAdditiveValueWeight currentState.1.1.1
  let certificateWeight :=
    compactAdditiveValueWeight currentState.1.1.2
  let originalWeightBound :=
    compactNumericVerifierPAAxiomLeafOriginalPayloadSourceWeightBound
      proofWeight certificateWeight
  let blockBound :=
    compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight originalWeightBound
  compactNumericVerifierParseSuccessStepCoordinateSizeBound
    width tokens.length blockBound

set_option maxHeartbeats 6000000 in
theorem
    ListedPAAxiomLeafAt.exists_checkedStepRow_at_canonical_offset_with_sourceBound
    {tree : ListedCheckedPAProofTree}
    {certificate : StructuralValidityCertificate}
    {offset : Nat}
    {Gamma : List LO.FirstOrder.ArithmeticProposition}
    {sentence : LO.FirstOrder.ArithmeticSentence}
    {paCertificate : PAAxiomCertificate}
    (occurrence : ListedPAAxiomLeafAt tree certificate offset
      Gamma sentence paCertificate)
    (hvalid : listedCertificateValid tree certificate) :
    let start := compactNumericVerifierInitialState
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)
    exists (proofSuffix certificateSuffix : List Nat)
        (restTasks : List CompactNumericVerifierTask)
        (values : List CompactNumericChildResult)
        (row : CompactNumericVerifierCheckedStepRow),
      compactNumericVerifierStateAt start offset =
          compactNumericTreeTaskStartState (.axm Gamma sentence)
            (.axiomCert paCertificate) proofSuffix certificateSuffix
            restTasks values /\
        row.currentState = compactNumericVerifierStateAt start offset /\
        row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
        (let leafTree : ListedCheckedPAProofTree := .axm Gamma sentence
         let leafCertificate : StructuralValidityCertificate :=
           .axiomCert paCertificate
         let proofTokens := compactListedProofTokens leafTree ++ proofSuffix
         let certificateTokens :=
           compactStructuralCertificateTokens leafCertificate ++
             certificateSuffix
         let proofNode :=
           compactListedProofNodeExpectedFields leafTree proofSuffix
         let certificateNode :=
           compactStructuralCertificateNodeExpected leafCertificate
             certificateSuffix
         let result := compactAxmRuleCheck
           (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1))
         let currentState : CompactNumericVerifierState :=
           (((proofTokens, certificateTokens),
             (compactNumericParseTask :: restTasks, values)), none)
         let nextState : CompactNumericVerifierState :=
           (((proofSuffix, certificateSuffix),
             (restTasks, (proofNode.2.1, result) :: values)), none)
         let currentTokens := compactAdditiveEncode currentState
         let nextTokens := compactAdditiveEncode nextState
         let tokens := currentTokens ++ nextTokens
         let width := (compactBinaryNatPayloadBits tokens).length
         let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
           width tokens.length
         let proofWeight := compactAdditiveValueWeight proofTokens
         let certificateWeight :=
           compactAdditiveValueWeight certificateTokens
         let originalWeightBound :=
           compactNumericVerifierPAAxiomLeafOriginalPayloadSourceWeightBound
             proofWeight certificateWeight
         let blockBound :=
           compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
             stateBound proofWeight certificateWeight originalWeightBound
         let coordinateBound :=
           compactNumericVerifierParseSuccessStepCoordinateSizeBound
             width tokens.length blockBound
         row.currentState = currentState /\
           row.nextState = nextState /\
           (forall coordinate : Fin 429,
             Nat.size (row.environment coordinate) <= coordinateBound) /\
           forall coordinate : Fin 429,
             Nat.size (row.environment coordinate) <=
               compactNumericVerifierAcceptedPAAxiomStepSourceCoordinateSizeBound
                 row.currentState row.nextState) := by
  let start := compactNumericVerifierInitialState
    (compactListedProofTokens tree)
    (compactStructuralCertificateTokens certificate)
  rcases occurrence.exists_stateAt_eq_leafStart hvalid [] [] [] [] with
    ⟨proofSuffix, certificateSuffix, restTasks, values, hleaf⟩
  have hleafAt :
      compactNumericVerifierStateAt start offset =
        compactNumericTreeTaskStartState (.axm Gamma sentence)
          (.axiomCert paCertificate) proofSuffix certificateSuffix
          restTasks values := by
    simpa [start, compactNumericVerifierInitialState,
      compactNumericTreeTaskStartState] using hleaf
  have hlocalValid := occurrence.localValid hvalid
  rcases
      exists_compactNumericVerifierTypedAcceptedPAAxiomCheckedStepRow_with_sourcePublicBounds
        Gamma sentence paCertificate proofSuffix certificateSuffix
        restTasks values hlocalValid with
    ⟨row, hrowCurrent, hrowNext, hcoordinates⟩
  have hcurrent :
      row.currentState = compactNumericVerifierStateAt start offset :=
    hrowCurrent.trans hleafAt.symm
  have hnext :
      row.nextState = compactNumericVerifierStateAt start (offset + 1) := by
    rw [row.exact_step, hcurrent]
    simp [compactNumericVerifierStateAt, Function.iterate_succ_apply']
  refine ⟨proofSuffix, certificateSuffix, restTasks, values, row,
    hleafAt, hcurrent, hnext, ?_⟩
  refine ⟨hrowCurrent, hrowNext, hcoordinates, ?_⟩
  intro coordinate
  simpa only [hrowCurrent, hrowNext,
    compactNumericVerifierAcceptedPAAxiomStepSourceCoordinateSizeBound] using
    hcoordinates coordinate

#print axioms
  ListedPAAxiomLeafAt.exists_checkedStepRow_at_canonical_offset_with_sourceBound

end FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomTraceRow
