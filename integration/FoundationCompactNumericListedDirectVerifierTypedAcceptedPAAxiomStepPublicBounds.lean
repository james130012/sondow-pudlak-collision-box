import integration.FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedStepPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
import integration.FoundationCompactNumericListedDirectVerifierCheckedStepRow
import integration.FoundationCompactListedCertificateVerifier

/-!
# A source-bounded 429-row for a typed valid PA leaf

The local axiom-check acceptance is derived from the real typed certificate
validity.  The public coordinate budget depends only on the canonical state
table and the two current source streams; no local witness bound is exposed.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTypedAcceptedPAAxiomStepPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectVerifierParseSuccessCanonicalFrameCompleteness
open FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
open FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedInductionRuleWeight
open FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedLeafStateGraphPublicBounds
open FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedStepPublicBounds
open FoundationCompactNumericListedDirectVerifierCheckedStepRow

set_option maxHeartbeats 6000000 in
theorem
    exists_compactNumericVerifierTypedAcceptedPAAxiomStepFormulaWitness_with_sourcePublicBounds
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (paCertificate : PAAxiomCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid
      (.axm Gamma sentence) (.axiomCert paCertificate)) :
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
    let stateTable := compactFixedWidthTableCode width tokens
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
    exists witness : CompactNumericVerifierStepFormulaWitness
        stateTable width tokens.length
        0 currentTokens.length currentTokens.length
        (currentTokens.length + nextTokens.length),
      (forall coordinate : Fin 429,
          Nat.size (witness.environment coordinate) <=
            compactNumericVerifierParseSuccessStepCoordinateSizeBound
              width tokens.length blockBound) /\
        CompactNumericVerifierParseSuccessParserControlBounds
          witness.environment blockBound := by
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
  let stateTable := compactFixedWidthTableCode width tokens
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
  have hpairRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState []
  have hpair :
      CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length 0 currentTokens.length currentState /\
        CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length currentTokens.length
            (currentTokens.length + nextTokens.length) nextState := by
    simpa only [stateTable, width, tokens, currentTokens, nextTokens,
      List.append_nil] using hpairRaw
  rcases hpair with ⟨hcurrentLayout, hnextLayout⟩
  rcases
      CompactNumericVerifierParseSuccessCanonicalFramePackage.exists_of_layouts
        hcurrentLayout hnextLayout (by rfl) with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, hframePackage⟩
  have hstateTable : Nat.size stateTable <= stateBound := by
    exact (compactFixedWidthTableCode_size_le width tokens).trans
      (tokenTableArea_le_stateCoreCoordinateSizeBound width tokens.length)
  have hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode := by
    simp only [proofTokens, proofNode, tree,
      compactListedProofNodeFieldsParser_canonical_append]
  have hcertificateParser :
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode := by
    simp only [certificateTokens, certificateNode, structuralCertificate,
      compactStructuralCertificateNodeParser_canonical_append]
  have hproofTag : proofNode.1 = 1 := by
    simp [proofNode, tree, compactListedProofNodeExpectedFields]
  have haccept : compactAxmRuleCheck
      (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1)) = true := by
    have htrace :
        (listedCertificateValidTrace (.axm Gamma sentence)
          (.axiomCert paCertificate)).1 = true :=
      (listedCertificateValidTrace_result_eq_true_iff
        (.axm Gamma sentence) (.axiomCert paCertificate)).2 hvalid
    simpa [proofNode, certificateNode, tree, structuralCertificate,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactSentenceTokens, arithmeticPropositionTokenValue] using
      (compactAxmRuleCheck_canonical Gamma sentence paCertificate).trans htrace
  have htransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((proofSuffix, certificateSuffix),
          (restTasks, (proofNode.2.1, result) :: values)) := by
    simp [proofNode, certificateNode, tree, structuralCertificate, result,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeTransition, compactNumericNodeFieldsSuffix]
  rcases
      exists_compactNumericVerifierAcceptedPAAxiomStepFormulaWitness_with_originalPublicBounds
        hframePackage hstateTable hproofParser hcertificateParser
        hproofTag htransition haccept with
    ⟨candidate, certificate, hsourceWeight, witness, hwitness,
      hparserControls⟩
  let originalWeight :=
    compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
      proofNode.2.1 candidate certificate
  let originalBlockBound :=
    compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight originalWeight
  have hblock : originalBlockBound <= blockBound := by
    dsimp only [originalBlockBound, blockBound, originalWeight,
      originalWeightBound]
    exact
      compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound_mono_original
        stateBound proofWeight certificateWeight hsourceWeight
  have hstepBound :
      compactNumericVerifierParseSuccessStepCoordinateSizeBound
          width tokens.length originalBlockBound <=
        compactNumericVerifierParseSuccessStepCoordinateSizeBound
          width tokens.length blockBound := by
    unfold compactNumericVerifierParseSuccessStepCoordinateSizeBound
    omega
  exact ⟨witness, fun coordinate => (hwitness coordinate).trans hstepBound,
    hparserControls.mono hblock⟩

#print axioms
  exists_compactNumericVerifierTypedAcceptedPAAxiomStepFormulaWitness_with_sourcePublicBounds

set_option maxHeartbeats 6000000 in
theorem
    exists_compactNumericVerifierTypedAcceptedPAAxiomCheckedStepRow_with_sourcePublicBounds
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (paCertificate : PAAxiomCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (hvalid : listedCertificateValid
      (.axm Gamma sentence) (.axiomCert paCertificate)) :
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
    let stateTable := compactFixedWidthTableCode width tokens
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
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = currentState /\
        row.nextState = nextState /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <= coordinateBound := by
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
  let stateTable := compactFixedWidthTableCode width tokens
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
  rcases
      exists_compactNumericVerifierTypedAcceptedPAAxiomStepFormulaWitness_with_sourcePublicBounds
        Gamma sentence paCertificate proofSuffix certificateSuffix
        restTasks values hvalid with
    ⟨witness, hwitness, _hparserControls⟩
  have hpairRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState []
  have hpair :
      CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length 0 currentTokens.length currentState /\
        CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length currentTokens.length
            (currentTokens.length + nextTokens.length) nextState := by
    simpa only [stateTable, width, tokens, currentTokens, nextTokens,
      List.append_nil] using hpairRaw
  rcases hpair with ⟨hcurrentLayout, hnextLayout⟩
  let row : CompactNumericVerifierCheckedStepRow :=
    { environment := witness.environment
      currentState := currentState
      nextState := nextState
      currentLayout := by
        simpa only [witness.stateTable_eq, witness.stateWidth_eq,
          witness.stateTokenCount_eq, witness.currentStart_eq,
          witness.currentFinish_eq] using hcurrentLayout
      nextLayout := by
        simpa only [witness.stateTable_eq, witness.stateWidth_eq,
          witness.stateTokenCount_eq, witness.nextStart_eq,
          witness.nextFinish_eq] using hnextLayout
      formula := witness.formula }
  exact ⟨row, rfl, rfl, fun coordinate => hwitness coordinate⟩

#print axioms
  exists_compactNumericVerifierTypedAcceptedPAAxiomCheckedStepRow_with_sourcePublicBounds

end FoundationCompactNumericListedDirectVerifierTypedAcceptedPAAxiomStepPublicBounds
