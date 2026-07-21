import integration.FoundationCompactNumericListedDirectVerifierTypedNonLeafStepPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomGlobalBound

/-!
# One global coordinate budget for successful non-leaf parse rows

The one-child and two-child schedules share the conservative two-parse public
envelope.  This file proves that envelope monotone and raises every concrete
node-transition output case to the enclosing canonical trace's row budget.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTypedNonLeafGlobalBound

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
open FoundationCompactNumericListedDirectVerifierCombinePublicBounds
open FoundationCompactNumericListedDirectVerifierSimpleStepPublicBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
open FoundationCompactNumericListedDirectVerifierTwoParseSuccessNonLeafStatePublicBounds
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierTypedNonLeafStepPublicBounds
open FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomGlobalBound

theorem
    compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound_mono
    {stateLeft stateRight proofLeft proofRight certificateLeft
      certificateRight : Nat}
    (hstate : stateLeft <= stateRight)
    (hproof : proofLeft <= proofRight)
    (hcertificate : certificateLeft <= certificateRight) :
    compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound
        stateLeft proofLeft certificateLeft <=
      compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound
        stateRight proofRight certificateRight := by
  have hexposed :=
    compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound_mono
      hstate hproof hcertificate
  unfold compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound
    compactNumericVerifierTwoParseSuccessNonLeafStatePublicCoordinateSizeBound
  exact max_le_max hexposed hstate

def compactNumericVerifierTypedNonLeafStepSourceCoordinateSizeBound
    (currentState nextState : CompactNumericVerifierState) : Nat :=
  let tokens :=
    compactAdditiveEncode currentState ++ compactAdditiveEncode nextState
  let width := (compactBinaryNatPayloadBits tokens).length
  let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
    width tokens.length
  let proofWeight := compactAdditiveValueWeight currentState.1.1.1
  let certificateWeight := compactAdditiveValueWeight currentState.1.1.2
  let blockBound :=
    compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  compactNumericVerifierParseSuccessStepCoordinateSizeBound
    width tokens.length blockBound

def compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
    (rowWeight : Nat) : Nat :=
  let pairWeight :=
    compactNumericVerifierStatePairTokenWeightBound rowWeight rowWeight
  let widthBound := 2 * pairWeight
  let stateBound :=
    compactNumericVerifierStateCoreCoordinateSizeBound widthBound pairWeight
  let blockBound :=
    compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound
      stateBound rowWeight rowWeight
  compactNumericVerifierParseSuccessStepCoordinateSizeBound
    widthBound pairWeight blockBound

theorem
    compactNumericVerifierTypedNonLeafStepSourceCoordinateSizeBound_le_global
    {currentState nextState : CompactNumericVerifierState}
    {rowWeight : Nat}
    (hcurrent : compactNumericVerifierStateWeight currentState <= rowWeight)
    (hnext : compactNumericVerifierStateWeight nextState <= rowWeight) :
    compactNumericVerifierTypedNonLeafStepSourceCoordinateSizeBound
        currentState nextState <=
      compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
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
  have hblock :=
    compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound_mono
      hstate hproof hcertificate
  have hstep :=
    compactNumericVerifierParseSuccessStepCoordinateSizeBound_mono
      hwidth htoken hblock
  simpa only [
    compactNumericVerifierTypedNonLeafStepSourceCoordinateSizeBound,
    compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound] using hstep

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_globalBound
    (proofTokens certificateTokens nextProofTokens nextCertificateTokens :
      List Nat)
    (restTasks nextTasks : List CompactNumericVerifierTask)
    (values nextValues : List CompactNumericChildResult)
    (proofNode : CompactNumericVerifierTask)
    (certificateNode : CompactNumericCertificateNode)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser
      certificateTokens = some certificateNode)
    (hproofTag : proofNode.1 = 3 \/ proofNode.1 = 4 \/ proofNode.1 = 5 \/
      proofNode.1 = 6 \/ proofNode.1 = 7 \/ proofNode.1 = 8 \/
      proofNode.1 = 9)
    (houtputCase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens), (nextTasks, nextValues)))
    {rowWeight : Nat} :
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((nextProofTokens, nextCertificateTokens),
        (nextTasks, nextValues)), none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <=
              compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
                rowWeight := by
  dsimp only
  intro hcurrent hnext
  rcases
      exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_sourcePublicBounds
        proofTokens certificateTokens nextProofTokens nextCertificateTokens
        restTasks nextTasks values nextValues proofNode certificateNode
        hproofParser hcertificateParser hproofTag houtputCase with
    ⟨row, hrowCurrent, hrowNext, hcoordinates⟩
  refine ⟨row, hrowCurrent, hrowNext, ?_⟩
  have hsource : forall coordinate : Fin 429,
      Nat.size (row.environment coordinate) <=
        compactNumericVerifierTypedNonLeafStepSourceCoordinateSizeBound
          row.currentState row.nextState := by
    intro coordinate
    simpa only [hrowCurrent, hrowNext,
      compactNumericVerifierTypedNonLeafStepSourceCoordinateSizeBound] using
      hcoordinates coordinate
  intro coordinate
  exact (hsource coordinate).trans
    (compactNumericVerifierTypedNonLeafStepSourceCoordinateSizeBound_le_global
      (by simpa only [hrowCurrent] using hcurrent)
      (by simpa only [hrowNext] using hnext))

#print axioms
  compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound_mono
#print axioms
  compactNumericVerifierTypedNonLeafStepSourceCoordinateSizeBound_le_global
#print axioms
  exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_globalBound

end FoundationCompactNumericListedDirectVerifierTypedNonLeafGlobalBound
