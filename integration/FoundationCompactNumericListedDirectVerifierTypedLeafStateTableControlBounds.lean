import integration.FoundationCompactNumericListedDirectVerifierAcceptedStateTableControlBounds
import integration.FoundationCompactNumericListedDirectVerifierTypedClosedStepPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierTypedVerumStepPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierTypedAcceptedPAAxiomStepPublicBounds

/-!
# Numeric state-table controls for typed accepted leaf rows

The accepted closed, verum, and PA-axiom leaf constructors all use the exact
canonical table `encode current ++ encode next`.  This module retains numeric
loop controls from those same row witnesses.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTypedLeafStateTableControlBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierTypedClosedStepPublicBounds
open FoundationCompactNumericListedDirectVerifierTypedVerumStepPublicBounds
open FoundationCompactNumericListedDirectVerifierVerumLeafStatePublicBounds
open FoundationCompactNumericListedDirectVerifierTypedAcceptedPAAxiomStepPublicBounds
open FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedLeafStateGraphPublicBounds
open FoundationCompactNumericListedDirectVerifierAcceptedStateTableControlBounds

set_option maxRecDepth 4000 in
set_option maxHeartbeats 7000000 in
theorem
    exists_compactNumericVerifierTypedClosedCheckedStepRow_with_controlBounds
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
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let tokens := currentTokens ++ nextTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
      width tokens.length
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    let blockBound :=
      compactNumericVerifierClosedLeafStatePublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
    let coordinateBound :=
      compactNumericVerifierParseSuccessStepCoordinateSizeBound
        width tokens.length blockBound
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight /\
          (forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound) /\
          CompactNumericVerifierParseSuccessParserControlBounds
            row.environment blockBound := by
  dsimp only
  intro hcurrent hnext
  rcases
      exists_compactNumericVerifierTypedClosedStepFormulaWitness_with_sourcePublicBounds
        Gamma formula proofSuffix certificateSuffix restTasks values hvalid with
    ⟨witness, hwitness, hparserControls⟩
  exact
    exists_checkedStepRow_of_canonicalStatePairFormulaWitness_with_controls_and_property
      _ _ rowWeight _
      (fun environment =>
        CompactNumericVerifierParseSuccessParserControlBounds environment _)
      (by simpa only [compactNumericVerifierStateWeight] using hcurrent)
      (by simpa only [compactNumericVerifierStateWeight] using hnext)
      witness hwitness hparserControls

set_option maxRecDepth 4000 in
set_option maxHeartbeats 7000000 in
theorem
    exists_compactNumericVerifierTypedVerumCheckedStepRow_with_controlBounds
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid (.verum Gamma) .leaf)
    {rowWeight : Nat} :
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
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let tokens := currentTokens ++ nextTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
      width tokens.length
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    let blockBound :=
      compactNumericVerifierVerumLeafStatePublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
    let coordinateBound :=
      compactNumericVerifierParseSuccessStepCoordinateSizeBound
        width tokens.length blockBound
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight /\
          (forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound) /\
          CompactNumericVerifierParseSuccessParserControlBounds
            row.environment blockBound := by
  dsimp only
  intro hcurrent hnext
  rcases
      exists_compactNumericVerifierTypedVerumStepFormulaWitness_with_sourcePublicBounds
        Gamma proofSuffix certificateSuffix restTasks values hvalid with
    ⟨witness, hwitness, hparserControls⟩
  exact
    exists_checkedStepRow_of_canonicalStatePairFormulaWitness_with_controls_and_property
      _ _ rowWeight _
      (fun environment =>
        CompactNumericVerifierParseSuccessParserControlBounds environment _)
      (by simpa only [compactNumericVerifierStateWeight] using hcurrent)
      (by simpa only [compactNumericVerifierStateWeight] using hnext)
      witness hwitness hparserControls

set_option maxRecDepth 4000 in
set_option maxHeartbeats 7000000 in
theorem
    exists_compactNumericVerifierTypedAcceptedPAAxiomCheckedStepRow_with_controlBounds
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
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let tokens := currentTokens ++ nextTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
      width tokens.length
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    let originalWeightBound :=
      compactNumericVerifierPAAxiomLeafOriginalPayloadSourceWeightBound
        proofWeight certificateWeight
    let blockBound :=
      compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
        stateBound proofWeight certificateWeight originalWeightBound
    let coordinateBound :=
      compactNumericVerifierParseSuccessStepCoordinateSizeBound
        width tokens.length blockBound
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight /\
          (forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound) /\
          CompactNumericVerifierParseSuccessParserControlBounds
            row.environment blockBound := by
  dsimp only
  intro hcurrent hnext
  rcases
      exists_compactNumericVerifierTypedAcceptedPAAxiomStepFormulaWitness_with_sourcePublicBounds
        Gamma sentence paCertificate proofSuffix certificateSuffix
          restTasks values hvalid with
    ⟨witness, hwitness, hparserControls⟩
  exact
    exists_checkedStepRow_of_canonicalStatePairFormulaWitness_with_controls_and_property
      _ _ rowWeight _
      (fun environment =>
        CompactNumericVerifierParseSuccessParserControlBounds environment _)
      (by simpa only [compactNumericVerifierStateWeight] using hcurrent)
      (by simpa only [compactNumericVerifierStateWeight] using hnext)
      witness hwitness hparserControls

#print axioms
  exists_compactNumericVerifierTypedClosedCheckedStepRow_with_controlBounds
#print axioms
  exists_compactNumericVerifierTypedVerumCheckedStepRow_with_controlBounds
#print axioms
  exists_compactNumericVerifierTypedAcceptedPAAxiomCheckedStepRow_with_controlBounds

end FoundationCompactNumericListedDirectVerifierTypedLeafStateTableControlBounds
