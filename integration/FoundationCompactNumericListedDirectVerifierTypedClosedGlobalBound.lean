import integration.FoundationCompactNumericListedDirectVerifierTypedClosedStepPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomGlobalBound

/-!
# One global coordinate budget for a valid closed-leaf row

The parser, leaf transport, and all twenty-eight closed-rule coordinates are
raised from their actual source weights to the enclosing canonical trace's
single public row-weight budget.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTypedClosedGlobalBound

open FoundationCompactAdditiveTokenCodec
open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
open FoundationCompactNumericListedDirectVerifierCombinePublicBounds
open FoundationCompactNumericListedDirectVerifierSimpleStepPublicBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
open FoundationCompactNumericListedDirectVerifierClosedLeafStatePublicBounds
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierTypedClosedStepPublicBounds
open FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomGlobalBound

theorem compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound_mono
    {stateLeft stateRight proofLeft proofRight certificateLeft
      certificateRight : Nat}
    (hstate : stateLeft <= stateRight)
    (hproof : proofLeft <= proofRight)
    (hcertificate : certificateLeft <= certificateRight) :
    compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound
        stateLeft proofLeft certificateLeft <=
      compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound
        stateRight proofRight certificateRight := by
  have htransport :=
    compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound_mono
      hstate hproof hcertificate
  have hclosed :=
    compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound_mono
      hproof
  unfold compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound
  omega

def compactNumericVerifierTypedClosedStepSourceCoordinateSizeBound
    (currentState nextState : CompactNumericVerifierState) : Nat :=
  let tokens :=
    compactAdditiveEncode currentState ++ compactAdditiveEncode nextState
  let width := (compactBinaryNatPayloadBits tokens).length
  let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
    width tokens.length
  let proofWeight := compactAdditiveValueWeight currentState.1.1.1
  let certificateWeight := compactAdditiveValueWeight currentState.1.1.2
  let blockBound :=
    compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  compactNumericVerifierParseSuccessStepCoordinateSizeBound
    width tokens.length blockBound

def compactNumericVerifierTypedClosedGlobalCoordinateSizeBound
    (rowWeight : Nat) : Nat :=
  let pairWeight :=
    compactNumericVerifierStatePairTokenWeightBound rowWeight rowWeight
  let widthBound := 2 * pairWeight
  let stateBound :=
    compactNumericVerifierStateCoreCoordinateSizeBound widthBound pairWeight
  let blockBound :=
    compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound
      stateBound rowWeight rowWeight
  compactNumericVerifierParseSuccessStepCoordinateSizeBound
    widthBound pairWeight blockBound

theorem
    compactNumericVerifierTypedClosedStepSourceCoordinateSizeBound_le_global
    {currentState nextState : CompactNumericVerifierState}
    {rowWeight : Nat}
    (hcurrent : compactNumericVerifierStateWeight currentState <= rowWeight)
    (hnext : compactNumericVerifierStateWeight nextState <= rowWeight) :
    compactNumericVerifierTypedClosedStepSourceCoordinateSizeBound
        currentState nextState <=
      compactNumericVerifierTypedClosedGlobalCoordinateSizeBound rowWeight := by
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
    compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound_mono
      hstate hproof hcertificate
  have hstep :=
    compactNumericVerifierParseSuccessStepCoordinateSizeBound_mono
      hwidth htoken hblock
  simpa only [
    compactNumericVerifierTypedClosedStepSourceCoordinateSizeBound,
    compactNumericVerifierTypedClosedGlobalCoordinateSizeBound] using hstep

set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem
    exists_compactNumericVerifierTypedClosedCheckedStepRow_with_globalBound
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.closed Gamma formula) .leaf)
    {rowWeight : Nat} :
    let tree : ListedCheckedPAProofTree := .closed Gamma formula
    let structuralCertificate : StructuralValidityCertificate := .leaf
    let proofTokens := compactListedProofTokens tree ++ proofSuffix
    let certificateTokens :=
      compactStructuralCertificateTokens structuralCertificate ++
        certificateSuffix
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofSuffix, certificateSuffix),
        (restTasks, (proofNode.2.1, true) :: values)), none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <=
              compactNumericVerifierTypedClosedGlobalCoordinateSizeBound
                rowWeight := by
  dsimp only
  intro hcurrent hnext
  rcases
      exists_compactNumericVerifierTypedClosedCheckedStepRow_with_sourcePublicBounds
        Gamma formula proofSuffix certificateSuffix restTasks values hvalid with
    ⟨row, hrowCurrent, hrowNext, hcoordinates⟩
  refine ⟨row, hrowCurrent, hrowNext, ?_⟩
  have hsource : forall coordinate : Fin 429,
      Nat.size (row.environment coordinate) <=
        compactNumericVerifierTypedClosedStepSourceCoordinateSizeBound
          row.currentState row.nextState := by
    intro coordinate
    simpa only [hrowCurrent, hrowNext,
      compactNumericVerifierTypedClosedStepSourceCoordinateSizeBound] using
      hcoordinates coordinate
  intro coordinate
  exact (hsource coordinate).trans
    (compactNumericVerifierTypedClosedStepSourceCoordinateSizeBound_le_global
      (by simpa only [hrowCurrent] using hcurrent)
      (by simpa only [hrowNext] using hnext))

#print axioms
  compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound_mono
#print axioms
  compactNumericVerifierTypedClosedStepSourceCoordinateSizeBound_le_global
#print axioms
  exists_compactNumericVerifierTypedClosedCheckedStepRow_with_globalBound

end FoundationCompactNumericListedDirectVerifierTypedClosedGlobalBound
