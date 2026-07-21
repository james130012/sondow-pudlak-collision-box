import integration.FoundationCompactNumericListedDirectProofPredicate
import integration.FoundationCompactNumericListedDirectVerifierAcceptedControlledTraceTable

/-!
# A quantitatively bounded direct proof witness

Public acceptance supplies the same canonical non-trace coordinates as the
direct predicate, but uses the explicitly bounded accepted trace table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBoundedProofWitness

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactAdditiveTokenCodec
open FoundationCompactListedPackedBitTokenSynchronization
open FoundationCompactListedVerifierArithmeticInput
open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedPublicVerifier
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectInputTableau
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierAcceptedTraceFormula
open FoundationCompactNumericListedDirectVerifierAcceptedTraceExactness
open FoundationCompactNumericListedDirectVerifierAcceptedTraceInputTableau
open FoundationCompactNumericListedDirectVerifierAcceptedTraceInputSplit
open FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrix
open FoundationCompactNumericListedDirectVerifierAcceptedConclusionRow
open FoundationCompactNumericListedDirectVerifierAcceptedBoundedTraceTable
open FoundationCompactNumericListedDirectVerifierAcceptedStateTableControlBounds
open FoundationCompactNumericListedDirectVerifierAcceptedControlledTraceTable
open FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
open FoundationCompactNumericListedDirectVerifierStepStateListCountControlBounds
open FoundationCompactNumericListedDirectVerifierCombineActiveCountBounds
open FoundationCompactNumericListedDirectProofPredicate

structure CompactListedPADirectBoundedWitness
    (bound formulaCode : Nat) where
  witness : CompactListedPADirectWitness bound formulaCode
  tree : ListedCheckedPAProofTree
  certificate : StructuralValidityCertificate
  formula : LO.FirstOrder.ArithmeticProposition
  valid : listedCertificateValid tree certificate
  conclusion_eq : tree.conclusionList.toFinset = {formula}
  proofTokens : List Nat
  certificateTokens : List Nat
  formulaTokens : List Nat
  proofTokens_eq : proofTokens = compactListedProofTokens tree
  certificateTokens_eq : certificateTokens =
    compactStructuralCertificateTokens certificate
  formulaTokens_eq : formulaTokens = compactArithmeticFormulaTokens formula
  streamWeight : Nat
  streamWeight_eq : streamWeight =
    compactNumericDecodedTokenListWeightBound bound
  proofWeight : compactAdditiveValueWeight proofTokens <= streamWeight
  certificateWeight :
    compactAdditiveValueWeight certificateTokens <= streamWeight
  proofCode_eq : witness.proofCode =
    compactAdditivePackedCode (proofTokens ++ certificateTokens)
  formulaCode_eq : formulaCode = compactAdditivePackedCode formulaTokens
  inputTokenCount_eq : witness.inputTokenCount =
    (proofTokens ++ certificateTokens).length
  inputWidth_eq : witness.inputWidth =
    (compactBinaryNatPayloadBits
      (proofTokens ++ certificateTokens)).length
  inputTable_eq : witness.inputTable =
    compactFixedWidthTableCode witness.inputWidth
      (proofTokens ++ certificateTokens)
  inputOffsetTable_eq : witness.inputOffsetTable =
    compactFixedWidthTableCode witness.inputWidth
      (compactBinaryNatTokenOffsets (proofTokens ++ certificateTokens))
  sourceTokenCount_eq : witness.sourceTokenCount =
    (compactAdditiveEncode proofTokens ++
      compactAdditiveEncode certificateTokens).length
  sourceWidth_eq : witness.sourceWidth =
    (compactBinaryNatPayloadBits
      (compactAdditiveEncode proofTokens ++
        compactAdditiveEncode certificateTokens)).length
  sourceTable_eq : witness.sourceTable =
    compactFixedWidthTableCode witness.sourceWidth
      (compactAdditiveEncode proofTokens ++
        compactAdditiveEncode certificateTokens)
  proofStart_eq : witness.proofStart = 0
  proofFinish_eq : witness.proofFinish =
    (compactAdditiveEncode proofTokens).length
  certificateStart_eq : witness.certificateStart =
    (compactAdditiveEncode proofTokens).length
  certificateFinish_eq : witness.certificateFinish =
    (compactAdditiveEncode proofTokens ++
      compactAdditiveEncode certificateTokens).length
  split_eq : witness.split = proofTokens.length
  traceWidth_eq : witness.traceWidth =
    compactNumericVerifierAcceptedControlledTraceWidth tree certificate valid
      streamWeight (by simpa [proofTokens_eq] using proofWeight)
      (by simpa [certificateTokens_eq] using certificateWeight)
  traceTable_eq : witness.traceTable =
    compactNumericVerifierAcceptedControlledTraceTable tree certificate valid
      streamWeight (by simpa [proofTokens_eq] using proofWeight)
      (by simpa [certificateTokens_eq] using certificateWeight)
  traceValueBound_eq : witness.traceValueBound = 2 ^ witness.traceWidth
  formulaTokenCount_eq : witness.formulaTokenCount = formulaTokens.length
  formulaWidth_eq : witness.formulaWidth =
    (compactBinaryNatPayloadBits formulaTokens).length
  formulaTable_eq : witness.formulaTable =
    compactFixedWidthTableCode witness.formulaWidth formulaTokens
  formulaOffsetTable_eq : witness.formulaOffsetTable =
    compactFixedWidthTableCode witness.formulaWidth
      (compactBinaryNatTokenOffsets formulaTokens)
  traceCoordinates_size_le :
    let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
    let coordinateBound :=
      compactNumericVerifierAcceptedCoordinateSizeBound streamWeight
    witness.traceWidth <=
        fuel *
          (compactNumericVerifierStepWitnessColumnCount * coordinateBound) /\
      Nat.size witness.traceTable <=
        fuel * compactNumericVerifierStepWitnessColumnCount *
          (fuel *
            (compactNumericVerifierStepWitnessColumnCount *
              coordinateBound)) /\
      Nat.size witness.traceValueBound <=
        fuel *
          (compactNumericVerifierStepWitnessColumnCount * coordinateBound) +
            1
  traceEnvironment_controlBounds :
    let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
    let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
    forall rowIndex, rowIndex < fuel ->
      let environment :=
        compactNumericVerifierStepWitnessTableFormulaEnvironment
          witness.traceWidth witness.traceTable rowIndex
      environment 1 <=
          compactNumericVerifierAcceptedStateWidthBound rowWeight /\
        environment 2 <=
          compactNumericVerifierAcceptedStateTokenCountBound rowWeight
  traceEnvironment_stateListCountBounds :
    let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
    let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
    forall rowIndex, rowIndex < fuel ->
      let environment :=
        compactNumericVerifierStepWitnessTableFormulaEnvironment
          witness.traceWidth witness.traceTable rowIndex
      CompactNumericVerifierStepStateListCountBounds environment
        (compactNumericVerifierAcceptedStateTokenCountBound rowWeight)
  traceEnvironment_parserControlBounds :
    let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
    let start := compactNumericVerifierInitialState proofTokens certificateTokens
    forall rowIndex, rowIndex < fuel ->
      let environment :=
        compactNumericVerifierStepWitnessTableFormulaEnvironment
          witness.traceWidth witness.traceTable rowIndex
      (compactNumericVerifierStateAt start rowIndex).2 = none ->
        forall restTasks,
          (compactNumericVerifierStateAt start rowIndex).1.2.1 =
              compactNumericParseTask :: restTasks ->
            CompactNumericVerifierParseSuccessParserControlBounds
              environment
                (compactNumericVerifierAcceptedCoordinateSizeBound streamWeight)
  traceEnvironment_combineControlBounds :
    let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
    let start := compactNumericVerifierInitialState proofTokens certificateTokens
    forall rowIndex, rowIndex < fuel ->
      let environment :=
        compactNumericVerifierStepWitnessTableFormulaEnvironment
          witness.traceWidth witness.traceTable rowIndex
      (compactNumericVerifierStateAt start rowIndex).2 = none ->
        forall task restTasks,
          (compactNumericVerifierStateAt start rowIndex).1.2.1 =
              task :: restTasks ->
          task.1 ≠ 10 ->
            CompactNumericVerifierCombineEnvironmentCountControls
              environment
  traceFinalEnvironment_controlBounds :
    let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
    let lastRow := fuel - 1
    let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
    let environment :=
      compactNumericVerifierStepWitnessTableFormulaEnvironment
        witness.traceWidth witness.traceTable lastRow
    environment 1 <= 4 * rowWeight /\
      environment 2 <= 2 * rowWeight

set_option maxRecDepth 5000 in
set_option maxHeartbeats 12000000 in
theorem directBoundedWitness_nonempty_of_public
    {bound proofCode formulaCode : Nat}
    (hbound : packedPayloadLength proofCode <= bound)
    (haccept :
      compactNumericListedPublicVerifier proofCode formulaCode = true) :
    Nonempty (CompactListedPADirectBoundedWitness bound formulaCode) := by
  rcases (compactNumericListedPublicVerifier_eq_true_iff
      proofCode formulaCode).mp haccept with
    ⟨tree, certificate, formula, hproofDecode,
      hvalid, hconclusion, hformulaCode⟩
  let proofTokens := compactListedProofTokens tree
  let certificateTokens := compactStructuralCertificateTokens certificate
  let inputTokens := proofTokens ++ certificateTokens
  let inputWidth := (compactBinaryNatPayloadBits inputTokens).length
  let inputTable := compactFixedWidthTableCode inputWidth inputTokens
  let inputOffsetTable := compactFixedWidthTableCode inputWidth
    (compactBinaryNatTokenOffsets inputTokens)
  have hproofStream :
      compactPackedTokenStream proofCode = some inputTokens := by
    have hraw := (compactPackedTokenStream_eq_proofTokens_iff
      proofCode tree certificate).mpr hproofDecode
    simpa [inputTokens, proofTokens, certificateTokens,
      compactListedCertifiedTokens] using hraw
  rcases compactPackedTokenStream_to_canonical_tableau hproofStream with
    ⟨normalizedProofCode, _normalizedTable, _normalizedOffsetTable,
      hnormalizedCode, hnormalizedSize, _hnormalizedTableau⟩
  have hnormalizedBound :
      packedPayloadLength normalizedProofCode <= bound := by
    unfold packedPayloadLength at hbound ⊢
    omega
  have hinput : CompactCanonicalPackedTokenStreamTableauAtWidth
      normalizedProofCode inputTokens.length inputTable inputOffsetTable
        inputWidth := by
    rw [hnormalizedCode]
    exact compactCanonicalPackedTokenStreamTableauAtWidth_canonical inputTokens

  let proofEncoded := compactAdditiveEncode proofTokens
  let certificateEncoded := compactAdditiveEncode certificateTokens
  let sourceTokens := proofEncoded ++ certificateEncoded
  let sourceWidth := (compactBinaryNatPayloadBits sourceTokens).length
  let sourceTable := compactFixedWidthTableCode sourceWidth sourceTokens
  have hsplit : CompactNumericVerifierAcceptedTraceInputSplit
      inputTable inputWidth inputTokens.length
      sourceTable sourceWidth sourceTokens.length
      0 proofEncoded.length proofEncoded.length sourceTokens.length
      proofTokens.length := by
    exact compactNumericVerifierAcceptedTraceInputSplit_canonical
      proofTokens certificateTokens
  have hproofLayout : CompactAdditiveNatListDirectLayout
      sourceTable sourceWidth sourceTokens.length
      0 proofEncoded.length proofTokens := by
    have hsourceTokens :
        [] ++ compactAdditiveEncode proofTokens ++ certificateEncoded =
          sourceTokens := by
      simp [sourceTokens, proofEncoded]
    have hraw := compactAdditiveNatListDirectLayout_canonical
      [] proofTokens certificateEncoded
    dsimp only at hraw
    rw [hsourceTokens] at hraw
    have hfinish : ([] : List Nat).length +
        (compactAdditiveEncode proofTokens).length = proofEncoded.length := by
      simp [proofEncoded]
    rw [hfinish] at hraw
    exact hraw
  have hcertificateLayout : CompactAdditiveNatListDirectLayout
      sourceTable sourceWidth sourceTokens.length
      proofEncoded.length sourceTokens.length certificateTokens := by
    have hsourceTokens :
        proofEncoded ++ compactAdditiveEncode certificateTokens ++ [] =
          sourceTokens := by
      simp [sourceTokens, certificateEncoded]
    have hraw := compactAdditiveNatListDirectLayout_canonical
      proofEncoded certificateTokens []
    dsimp only at hraw
    rw [hsourceTokens] at hraw
    have hfinish : proofEncoded.length +
        (compactAdditiveEncode certificateTokens).length =
          sourceTokens.length := by
      simp [sourceTokens, certificateEncoded]
    rw [hfinish] at hraw
    exact hraw

  have hinputWidthBound : inputWidth <= bound := by
    rw [← hinput.packedPayloadLength_eq]
    exact hnormalizedBound
  let streamWeight := compactNumericDecodedTokenListWeightBound bound
  have hinputWeight : compactAdditiveValueWeight inputTokens <=
      streamWeight := by
    rcases (compactPackedTokenStream_success_iff
      proofCode inputTokens).mp hproofStream with
      ⟨payload, hpayload, hdecode⟩
    have hraw :=
      compactAdditiveValueWeight_natList_le_of_tokensDecode hdecode
    have hpack := (packedPayloadBits_eq_some_iff
      proofCode payload).mp hpayload
    have hpayloadLength : payload.length <= bound := by
      have hlength : packedPayloadLength proofCode = payload.length := by
        unfold packedPayloadLength
        rw [← hpack, size_packBinaryString]
        omega
      rw [← hlength]
      exact hbound
    exact hraw.trans
      (compactNumericDecodedTokenListWeightBound_mono hpayloadLength)
  have hproofWeight : compactAdditiveValueWeight proofTokens <=
      streamWeight := by
    exact (compactAdditiveValueWeight_infix_le
      (List.prefix_append proofTokens certificateTokens).isInfix).trans
        hinputWeight
  have hcertificateWeight :
      compactAdditiveValueWeight certificateTokens <= streamWeight := by
    exact (compactAdditiveValueWeight_suffix_le
      (show certificateTokens <:+ inputTokens from
        ⟨proofTokens, rfl⟩)).trans hinputWeight
  let traceWidth :=
    compactNumericVerifierAcceptedControlledTraceWidth tree certificate hvalid
      streamWeight hproofWeight hcertificateWeight
  let traceTable :=
    compactNumericVerifierAcceptedControlledTraceTable tree certificate hvalid
      streamWeight hproofWeight hcertificateWeight
  have htrace : CompactNumericVerifierAcceptedTraceTable
      traceWidth traceTable (2 ^ traceWidth)
      (compactNumericVerifierFuelBound proofTokens certificateTokens)
      sourceTable sourceWidth sourceTokens.length
      0 proofEncoded.length
      sourceTable sourceWidth sourceTokens.length
      proofEncoded.length sourceTokens.length := by
    simpa only [traceWidth, traceTable, proofTokens, certificateTokens] using
      compactNumericVerifierAcceptedControlledTraceTable_complete
        tree certificate hvalid hproofWeight hcertificateWeight
        hproofLayout hcertificateLayout
  have hpayloadMatrix : CompactNumericVerifierAcceptedPayloadMatrix
      normalizedProofCode inputTokens.length inputTable inputOffsetTable
        inputWidth sourceTable sourceWidth sourceTokens.length
        0 proofEncoded.length proofEncoded.length sourceTokens.length
        proofTokens.length traceWidth traceTable (2 ^ traceWidth) := by
    refine ⟨hinput, hsplit, ?_⟩
    simpa [compactNumericVerifierFuelBound, inputTokens] using htrace

  let formulaTokens := compactArithmeticFormulaTokens formula
  let formulaWidth := (compactBinaryNatPayloadBits formulaTokens).length
  let formulaTable := compactFixedWidthTableCode formulaWidth formulaTokens
  let formulaOffsetTable := compactFixedWidthTableCode formulaWidth
    (compactBinaryNatTokenOffsets formulaTokens)
  have hformulaCodeCanonical :
      formulaCode = compactAdditivePackedCode formulaTokens := by
    rw [← hformulaCode]
    exact compactFormulaCode_eq_additivePackedCode formula
  have hformulaTableau : CompactCanonicalPackedTokenStreamTableauAtWidth
      formulaCode formulaTokens.length formulaTable formulaOffsetTable
        formulaWidth := by
    rw [hformulaCodeCanonical]
    exact compactCanonicalPackedTokenStreamTableauAtWidth_canonical
      formulaTokens

  rcases acceptedTraceTable_exact_finalLayout
      htrace hproofLayout hcertificateLayout with
    ⟨hstep, hstateLayout⟩
  have hlastRow :
      compactNumericVerifierFuelBound proofTokens certificateTokens - 1 =
        compactNumericVerifierDirectLastRow inputTokens.length := by
    simp [compactNumericVerifierFuelBound,
      compactNumericVerifierDirectLastRow, inputTokens]
  rw [hlastRow] at hstep hstateLayout
  have hstateAt :
      compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          (compactNumericVerifierFuelBound proofTokens certificateTokens) =
        (compactNumericTreeFinalPayload tree certificate, some true) := by
    have hrun := compactNumericVerifierRun_canonical_of_valid
      tree certificate hvalid
    simpa [compactNumericVerifierStateAt, compactNumericVerifierRun,
      proofTokens, certificateTokens] using hrun
  rw [hstateAt] at hstateLayout
  have hvaluesLength :
      ((compactNumericTreeFinalPayload tree certificate, some true) :
        CompactNumericVerifierState).1.2.2.length = 1 := by
    simp [compactNumericTreeFinalPayload]
  have hvalidTrace :
      (listedCertificateValidTrace tree certificate).1 = true :=
    (listedCertificateValidTrace_result_eq_true_iff tree certificate).2 hvalid
  have hchildTrue :
      (((compactNumericTreeFinalPayload tree certificate, some true) :
        CompactNumericVerifierState).1.2.2.getI 0).2 = true := by
    simp [compactNumericTreeFinalPayload, hvalidTrace]
  have htokenSet :
      (arithmeticPropositionTokenValues tree.conclusionList).toFinset =
        (arithmeticPropositionTokenValues [formula]).toFinset :=
    (arithmeticPropositionTokenValues_toFinset_eq_iff
      tree.conclusionList [formula]).2 hconclusion
  have hformulaSet :
      (((compactNumericTreeFinalPayload tree certificate, some true) :
        CompactNumericVerifierState).1.2.2.getI 0).1.toFinset =
          {formulaTokens} := by
    simpa [compactNumericTreeFinalPayload, formulaTokens,
      arithmeticPropositionTokenValues, arithmeticPropositionTokenValue]
      using htokenSet
  have hformulaEntries : forall index, index < formulaTokens.length ->
      CompactFixedWidthEntry formulaTable formulaWidth
        index (formulaTokens.getI index) := by
    intro index hindex
    apply compactFixedWidthTableCode_entry formulaWidth formulaTokens
      index hindex
    intro value hvalue
    exact compactBinaryNatToken_size_le_payloadLength
      formulaTokens value hvalue
  have hconclusionRow : CompactNumericVerifierAcceptedConclusionRow
      traceWidth traceTable (2 ^ traceWidth)
      (compactNumericVerifierDirectLastRow inputTokens.length)
      formulaTable formulaWidth formulaTokens.length := by
    exact CompactNumericVerifierAcceptedConclusionRow.of_formulaSet
      rfl hstep hstateLayout hvaluesLength hchildTrue hformulaSet
      rfl hformulaEntries
  let witness : CompactListedPADirectWitness bound formulaCode :=
    ⟨normalizedProofCode,
      inputTokens.length, inputTable, inputOffsetTable, inputWidth,
      sourceTable, sourceWidth, sourceTokens.length,
      0, proofEncoded.length, proofEncoded.length, sourceTokens.length,
      proofTokens.length, traceWidth, traceTable, 2 ^ traceWidth,
      formulaTokens.length, formulaTable, formulaOffsetTable, formulaWidth,
      ⟨hinputWidthBound, hpayloadMatrix, hformulaTableau,
        hconclusionRow⟩⟩
  have htraceSize :=
    compactNumericVerifierAcceptedControlledTraceTable_size_le
      tree certificate hvalid hproofWeight hcertificateWeight
  have htraceControl :=
    compactNumericVerifierAcceptedControlledTraceFinalEnvironment_controlBounds
      tree certificate hvalid hproofWeight hcertificateWeight
  have htraceControls :
      forall rowIndex,
        rowIndex < compactNumericVerifierFuelBound proofTokens certificateTokens ->
          let environment :=
            compactNumericVerifierStepWitnessTableFormulaEnvironment
              traceWidth traceTable rowIndex
          environment 1 <= compactNumericVerifierAcceptedStateWidthBound
              (compactNumericVerifierPublicRowWeightBound streamWeight) /\
            environment 2 <= compactNumericVerifierAcceptedStateTokenCountBound
              (compactNumericVerifierPublicRowWeightBound streamWeight) := by
    intro rowIndex hrowIndex
    simpa only [traceWidth, traceTable, proofTokens, certificateTokens] using
      compactNumericVerifierAcceptedControlledTraceEnvironment_controlBounds
        tree certificate hvalid hproofWeight hcertificateWeight hrowIndex
  have htraceListCounts :
      forall rowIndex,
        rowIndex < compactNumericVerifierFuelBound proofTokens certificateTokens ->
          let environment :=
            compactNumericVerifierStepWitnessTableFormulaEnvironment
              traceWidth traceTable rowIndex
          CompactNumericVerifierStepStateListCountBounds environment
            (compactNumericVerifierAcceptedStateTokenCountBound
              (compactNumericVerifierPublicRowWeightBound streamWeight)) := by
    intro rowIndex hrowIndex
    simpa only [traceWidth, traceTable, proofTokens, certificateTokens] using
      compactNumericVerifierAcceptedControlledTraceEnvironment_stateListCountBounds
        tree certificate hvalid hproofWeight hcertificateWeight hrowIndex
  have htraceParserControls :
      forall rowIndex,
        rowIndex < compactNumericVerifierFuelBound proofTokens certificateTokens ->
          let environment :=
            compactNumericVerifierStepWitnessTableFormulaEnvironment
              traceWidth traceTable rowIndex
          (compactNumericVerifierStateAt
              (compactNumericVerifierInitialState proofTokens certificateTokens)
              rowIndex).2 = none ->
            forall restTasks,
              (compactNumericVerifierStateAt
                  (compactNumericVerifierInitialState proofTokens
                    certificateTokens) rowIndex).1.2.1 =
                    compactNumericParseTask :: restTasks ->
                CompactNumericVerifierParseSuccessParserControlBounds
                  environment
                    (compactNumericVerifierAcceptedCoordinateSizeBound
                      streamWeight) := by
    intro rowIndex hrowIndex
    simpa only [traceWidth, traceTable, proofTokens, certificateTokens] using
      compactNumericVerifierAcceptedControlledTraceEnvironment_parserControlBounds
        tree certificate hvalid hproofWeight hcertificateWeight hrowIndex
  have htraceCombineControls :
      forall rowIndex,
        rowIndex < compactNumericVerifierFuelBound proofTokens certificateTokens ->
          let environment :=
            compactNumericVerifierStepWitnessTableFormulaEnvironment
              traceWidth traceTable rowIndex
          (compactNumericVerifierStateAt
              (compactNumericVerifierInitialState proofTokens certificateTokens)
              rowIndex).2 = none ->
            forall task restTasks,
              (compactNumericVerifierStateAt
                  (compactNumericVerifierInitialState proofTokens
                    certificateTokens) rowIndex).1.2.1 = task :: restTasks ->
              task.1 ≠ 10 ->
                CompactNumericVerifierCombineEnvironmentCountControls
                  environment := by
    intro rowIndex hrowIndex
    simpa only [traceWidth, traceTable, proofTokens, certificateTokens] using
      compactNumericVerifierAcceptedControlledTraceEnvironment_combineControlBounds
        tree certificate hvalid hproofWeight hcertificateWeight hrowIndex
  refine ⟨
    { witness := witness
      tree := tree
      certificate := certificate
      formula := formula
      valid := hvalid
      conclusion_eq := hconclusion
      proofTokens := proofTokens
      certificateTokens := certificateTokens
      formulaTokens := formulaTokens
      proofTokens_eq := rfl
      certificateTokens_eq := rfl
      formulaTokens_eq := rfl
      streamWeight := streamWeight
      streamWeight_eq := rfl
      proofWeight := hproofWeight
      certificateWeight := hcertificateWeight
      proofCode_eq := ?_
      formulaCode_eq := ?_
      inputTokenCount_eq := ?_
      inputWidth_eq := ?_
      inputTable_eq := ?_
      inputOffsetTable_eq := ?_
      sourceTokenCount_eq := ?_
      sourceWidth_eq := ?_
      sourceTable_eq := ?_
      proofStart_eq := ?_
      proofFinish_eq := ?_
      certificateStart_eq := ?_
      certificateFinish_eq := ?_
      split_eq := ?_
      traceWidth_eq := ?_
      traceTable_eq := ?_
      traceValueBound_eq := ?_
      formulaTokenCount_eq := ?_
      formulaWidth_eq := ?_
      formulaTable_eq := ?_
      formulaOffsetTable_eq := ?_
      traceCoordinates_size_le := ?_
      traceEnvironment_controlBounds := ?_
      traceEnvironment_stateListCountBounds := ?_
      traceEnvironment_parserControlBounds := ?_
      traceEnvironment_combineControlBounds := ?_
      traceFinalEnvironment_controlBounds := ?_ }⟩
  · simpa only [witness, inputTokens] using hnormalizedCode
  · simpa only [formulaTokens] using hformulaCodeCanonical
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simpa only [witness, traceWidth, traceTable, proofTokens,
      certificateTokens] using htraceSize
  · simpa only [witness, traceWidth, traceTable, proofTokens,
      certificateTokens] using htraceControls
  · simpa only [witness, traceWidth, traceTable, proofTokens,
      certificateTokens] using htraceListCounts
  · simpa only [witness, traceWidth, traceTable, proofTokens,
      certificateTokens] using htraceParserControls
  · simpa only [witness, traceWidth, traceTable, proofTokens,
      certificateTokens] using htraceCombineControls
  · simpa only [witness, traceWidth, traceTable, proofTokens,
      certificateTokens] using htraceControl

#print axioms directBoundedWitness_nonempty_of_public

end FoundationCompactNumericListedDirectBoundedProofWitness
