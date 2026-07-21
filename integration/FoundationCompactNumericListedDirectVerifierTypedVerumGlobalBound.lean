import integration.FoundationCompactNumericListedDirectVerifierTypedVerumStepPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomGlobalBound

/-!
# One global coordinate budget for a valid verum-leaf row

The typed verum constructor is first bounded by its two actual endpoint
states.  Monotonicity then raises that source bound to the public row-weight
budget of the enclosing canonical trace.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTypedVerumGlobalBound

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
open FoundationCompactNumericListedDirectVerifierVerumLeafStatePublicBounds
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierTypedVerumStepPublicBounds
open FoundationCompactNumericListedDirectVerifierAcceptedPAAxiomGlobalBound

def compactNumericVerifierTypedVerumStepSourceCoordinateSizeBound
    (currentState nextState : CompactNumericVerifierState) : Nat :=
  let tokens :=
    compactAdditiveEncode currentState ++ compactAdditiveEncode nextState
  let width := (compactBinaryNatPayloadBits tokens).length
  let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
    width tokens.length
  let proofWeight := compactAdditiveValueWeight currentState.1.1.1
  let certificateWeight := compactAdditiveValueWeight currentState.1.1.2
  let blockBound :=
    compactNumericVerifierVerumLeafStatePublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  compactNumericVerifierParseSuccessStepCoordinateSizeBound
    width tokens.length blockBound

def compactNumericVerifierTypedVerumGlobalCoordinateSizeBound
    (rowWeight : Nat) : Nat :=
  let pairWeight :=
    compactNumericVerifierStatePairTokenWeightBound rowWeight rowWeight
  let widthBound := 2 * pairWeight
  let stateBound :=
    compactNumericVerifierStateCoreCoordinateSizeBound widthBound pairWeight
  let blockBound :=
    compactNumericVerifierVerumLeafStatePublicCoordinateSizeBound
      stateBound rowWeight rowWeight
  compactNumericVerifierParseSuccessStepCoordinateSizeBound
    widthBound pairWeight blockBound

theorem
    compactNumericVerifierTypedVerumStepSourceCoordinateSizeBound_le_global
    {currentState nextState : CompactNumericVerifierState}
    {rowWeight : Nat}
    (hcurrent : compactNumericVerifierStateWeight currentState <= rowWeight)
    (hnext : compactNumericVerifierStateWeight nextState <= rowWeight) :
    compactNumericVerifierTypedVerumStepSourceCoordinateSizeBound
        currentState nextState <=
      compactNumericVerifierTypedVerumGlobalCoordinateSizeBound rowWeight := by
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
    compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound_mono
      hstate hproof hcertificate
  have hstep :=
    compactNumericVerifierParseSuccessStepCoordinateSizeBound_mono
      hwidth htoken hblock
  simpa only [
    compactNumericVerifierTypedVerumStepSourceCoordinateSizeBound,
    compactNumericVerifierTypedVerumGlobalCoordinateSizeBound,
    compactNumericVerifierVerumLeafStatePublicCoordinateSizeBound] using hstep

set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem
    exists_compactNumericVerifierTypedVerumCheckedStepRow_with_globalBound
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.verum Gamma) .leaf)
    {rowWeight : Nat}
    (hcurrent : compactNumericVerifierStateWeight
      (((compactListedProofTokens (.verum Gamma) ++ proofSuffix,
          compactStructuralCertificateTokens (.leaf) ++ certificateSuffix),
        (compactNumericParseTask :: restTasks, values)), none) <= rowWeight)
    (hnext : compactNumericVerifierStateWeight
      (((proofSuffix, certificateSuffix),
        (restTasks,
          ((compactListedProofNodeExpectedFields
            (.verum Gamma) proofSuffix).2.1, true) :: values)), none) <=
        rowWeight) :
    let tree : ListedCheckedPAProofTree := .verum Gamma
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
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = currentState /\
        row.nextState = nextState /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierTypedVerumGlobalCoordinateSizeBound
              rowWeight := by
  dsimp only
  rcases
      exists_compactNumericVerifierTypedVerumCheckedStepRow_with_sourcePublicBounds
        Gamma proofSuffix certificateSuffix restTasks values hvalid with
    ⟨row, hrowCurrent, hrowNext, hcoordinates⟩
  refine ⟨row, hrowCurrent, hrowNext, ?_⟩
  have hsource : forall coordinate : Fin 429,
      Nat.size (row.environment coordinate) <=
        compactNumericVerifierTypedVerumStepSourceCoordinateSizeBound
          row.currentState row.nextState := by
    intro coordinate
    simpa only [hrowCurrent, hrowNext,
      compactNumericVerifierTypedVerumStepSourceCoordinateSizeBound] using
      hcoordinates coordinate
  intro coordinate
  exact (hsource coordinate).trans
    (compactNumericVerifierTypedVerumStepSourceCoordinateSizeBound_le_global
      (by simpa only [hrowCurrent] using hcurrent)
      (by simpa only [hrowNext] using hnext))

#print axioms
  compactNumericVerifierTypedVerumStepSourceCoordinateSizeBound_le_global
#print axioms
  exists_compactNumericVerifierTypedVerumCheckedStepRow_with_globalBound

end FoundationCompactNumericListedDirectVerifierTypedVerumGlobalBound
