import integration.FoundationCompactNumericListedDirectBoundedWitnessBounds

/-!
# Numeric quantifier profile for the direct proof predicate

This module separates numeric bounds for universal-control coordinates from
binary-size bounds for packed values.  In particular, `traceValueBound` is
recorded only by its exact exponential identity and its binary size; it is not
claimed to be polynomial as a numeric value.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectQuantifierProfile

open FoundationCompactAdditiveTokenCodec
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTraceNatListSlices
open FoundationCompactNumericListedDirectProofPredicate
open FoundationCompactNumericListedDirectBoundedProofWitness
open FoundationCompactNumericListedDirectWitnessBounds
open FoundationCompactNumericListedDirectBoundedWitnessBounds
open FoundationCompactNumericListedDirectVerifierAcceptedBoundedTraceTable
open FoundationCompactNumericListedDirectVerifierAcceptedControlledTraceSelection
open FoundationCompactNumericListedDirectVerifierAcceptedStateTableControlBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierStepStateListCountControlBounds
open FoundationCompactNumericListedDirectVerifierCombineActiveCountBounds

def directPredicateAcceptedFuel (inputTokenCount : Nat) : Nat :=
  4 * (inputTokenCount + 1) + 8

def directPredicateAcceptedFuelBound (bound : Nat) : Nat :=
  4 * (bound + 1) + 8

def directPredicateConclusionRow (inputTokenCount : Nat) : Nat :=
  4 * (inputTokenCount + 1) + 7

def directPredicateConclusionRowBound (bound : Nat) : Nat :=
  4 * (bound + 1) + 7

def directPredicateConclusionStateWidthLimit (bound : Nat) : Nat :=
  4 * compactNumericVerifierPublicRowWeightBound
    (directBoundedWitnessStreamWeight bound)

def directPredicateConclusionStateTokenCountLimit (bound : Nat) : Nat :=
  2 * compactNumericVerifierPublicRowWeightBound
    (directBoundedWitnessStreamWeight bound)

def directPredicateTraceStateWidthLimit (bound : Nat) : Nat :=
  compactNumericVerifierAcceptedStateWidthBound
    (compactNumericVerifierPublicRowWeightBound
      (directBoundedWitnessStreamWeight bound))

def directPredicateTraceStateTokenCountLimit (bound : Nat) : Nat :=
  compactNumericVerifierAcceptedStateTokenCountBound
    (compactNumericVerifierPublicRowWeightBound
      (directBoundedWitnessStreamWeight bound))

/-- Numeric bounds for every outer coordinate that controls a finite loop in
the fixed direct-predicate matrix.  Packed table values are deliberately absent
from the numeric part of this profile. -/
structure DirectPredicateOuterQuantifierProfile
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) : Prop where
  inputTokenCount_le : bounded.witness.inputTokenCount <= bound
  inputWidth_le : bounded.witness.inputWidth <= bound
  proofCode_size_le : Nat.size bounded.witness.proofCode <= bound + 1
  sourceTokenCount_le : bounded.witness.sourceTokenCount <= bound + 2
  sourceWidth_le : bounded.witness.sourceWidth <= 5 * bound + 4
  proofFinish_le : bounded.witness.proofFinish <= bound + 2
  certificateStart_le : bounded.witness.certificateStart <= bound + 2
  certificateFinish_le : bounded.witness.certificateFinish <= bound + 2
  split_le : bounded.witness.split <= bound
  formulaTokenCount_le : bounded.witness.formulaTokenCount <= Nat.size formulaCode
  formulaWidth_le : bounded.witness.formulaWidth <= Nat.size formulaCode
  traceWidth_le : bounded.witness.traceWidth <=
    directBoundedWitnessTraceWidthLimit bound
  acceptedFuel_le : directPredicateAcceptedFuel bounded.witness.inputTokenCount <=
    directPredicateAcceptedFuelBound bound
  conclusionRow_le : directPredicateConclusionRow bounded.witness.inputTokenCount <=
    directPredicateConclusionRowBound bound
  traceValueBound_eq : bounded.witness.traceValueBound =
    2 ^ bounded.witness.traceWidth
  traceValueBound_size_le : Nat.size bounded.witness.traceValueBound <=
    directBoundedWitnessTraceValueLimit bound

theorem directBoundedWitness_traceWidth_le
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    bounded.witness.traceWidth <= directBoundedWitnessTraceWidthLimit bound := by
  have hraw := bounded.traceCoordinates_size_le
  have hfuel : compactNumericVerifierFuelBound bounded.proofTokens
      bounded.certificateTokens <=
      compactNumericVerifierPublicFuelWeightBound bounded.streamWeight :=
    compactNumericVerifierFuelBound_le_weightBound
      bounded.proofWeight bounded.certificateWeight
  have hscale :
      compactNumericVerifierFuelBound bounded.proofTokens
          bounded.certificateTokens *
            (compactNumericVerifierStepWitnessColumnCount *
              compactNumericVerifierAcceptedCoordinateSizeBound
                bounded.streamWeight) <=
        compactNumericVerifierPublicFuelWeightBound bounded.streamWeight *
            (compactNumericVerifierStepWitnessColumnCount *
              compactNumericVerifierAcceptedCoordinateSizeBound
                bounded.streamWeight) :=
    Nat.mul_le_mul_right _ hfuel
  exact hraw.1.trans (by
    simpa [directBoundedWitnessTraceWidthLimit,
      directBoundedWitnessFuelLimit, directBoundedWitnessCoordinateLimit,
      directBoundedWitnessStreamWeight, bounded.streamWeight_eq] using hscale)

theorem directBoundedWitness_outerQuantifierProfile
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    DirectPredicateOuterQuantifierProfile bounded := by
  have hinputWidth : bounded.witness.inputWidth <= bound :=
    directWitnessInputWidth_le_bound bounded.witness
  have hinputCount : bounded.witness.inputTokenCount <= bound := by
    have hcount := compactBinaryNatToken_count_le_payloadLength
      (bounded.proofTokens ++ bounded.certificateTokens)
    rw [← bounded.inputTokenCount_eq, ← bounded.inputWidth_eq] at hcount
    exact hcount.trans hinputWidth
  have hproofCodeSize : Nat.size bounded.witness.proofCode <= bound + 1 := by
    calc
      Nat.size bounded.witness.proofCode =
          Nat.size (compactAdditivePackedCode
            (bounded.proofTokens ++ bounded.certificateTokens)) := by
        exact congrArg Nat.size bounded.proofCode_eq
      _ = compactAdditiveTokenBitLength
            (bounded.proofTokens ++ bounded.certificateTokens) + 1 :=
        compactAdditivePackedCode_size _
      _ = (compactBinaryNatPayloadBits
            (bounded.proofTokens ++ bounded.certificateTokens)).length + 1 := by
        rw [compactBinaryNatPayloadBits_length_eq_tokenBitLength]
      _ = bounded.witness.inputWidth + 1 := by rw [bounded.inputWidth_eq]
      _ <= bound + 1 := Nat.add_le_add_right hinputWidth 1
  have hproofLength : bounded.proofTokens.length <= bound := by
    calc
      bounded.proofTokens.length <=
          (bounded.proofTokens ++ bounded.certificateTokens).length := by simp
      _ = bounded.witness.inputTokenCount := bounded.inputTokenCount_eq.symm
      _ <= bound := hinputCount
  have hcertificateLength : bounded.certificateTokens.length <= bound := by
    calc
      bounded.certificateTokens.length <=
          (bounded.proofTokens ++ bounded.certificateTokens).length := by simp
      _ = bounded.witness.inputTokenCount := bounded.inputTokenCount_eq.symm
      _ <= bound := hinputCount
  have hsourceCount : bounded.witness.sourceTokenCount <= bound + 2 := by
    rw [bounded.sourceTokenCount_eq, List.length_append,
      compactAdditiveEncode_natList_length,
      compactAdditiveEncode_natList_length]
    have hinputLength :
        bounded.proofTokens.length + bounded.certificateTokens.length <= bound := by
      calc
        bounded.proofTokens.length + bounded.certificateTokens.length =
            (bounded.proofTokens ++ bounded.certificateTokens).length := by simp
        _ = bounded.witness.inputTokenCount := bounded.inputTokenCount_eq.symm
        _ <= bound := hinputCount
    omega
  have hsourceWidth : bounded.witness.sourceWidth <= 5 * bound + 4 := by
    rw [bounded.sourceWidth_eq,
      compactBinaryNatPayloadBits_additiveNatLists_length,
      ← bounded.inputWidth_eq]
    have hproofSize := nat_size_le_self bounded.proofTokens.length
    have hcertificateSize := nat_size_le_self bounded.certificateTokens.length
    omega
  have hformulaCodeSize :
      Nat.size formulaCode = bounded.witness.formulaWidth + 1 := by
    calc
      Nat.size formulaCode =
          Nat.size (compactAdditivePackedCode bounded.formulaTokens) := by
        exact congrArg Nat.size bounded.formulaCode_eq
      _ = compactAdditiveTokenBitLength bounded.formulaTokens + 1 :=
        compactAdditivePackedCode_size bounded.formulaTokens
      _ = (compactBinaryNatPayloadBits bounded.formulaTokens).length + 1 := by
        rw [compactBinaryNatPayloadBits_length_eq_tokenBitLength]
      _ = bounded.witness.formulaWidth + 1 := by rw [bounded.formulaWidth_eq]
  have hformulaWidth : bounded.witness.formulaWidth <= Nat.size formulaCode := by
    omega
  have hformulaCount :
      bounded.witness.formulaTokenCount <= Nat.size formulaCode := by
    rw [bounded.formulaTokenCount_eq]
    have hcount := compactBinaryNatToken_count_le_payloadLength
      bounded.formulaTokens
    rw [← bounded.formulaWidth_eq] at hcount
    exact hcount.trans hformulaWidth
  have hproofFinish : bounded.witness.proofFinish <= bound + 2 := by
    rw [bounded.proofFinish_eq]
    calc
      (compactAdditiveEncode bounded.proofTokens).length <=
          (compactAdditiveEncode bounded.proofTokens ++
            compactAdditiveEncode bounded.certificateTokens).length := by simp
      _ = bounded.witness.sourceTokenCount := bounded.sourceTokenCount_eq.symm
      _ <= bound + 2 := hsourceCount
  have hcertificateStart : bounded.witness.certificateStart <= bound + 2 := by
    rw [bounded.certificateStart_eq, ← bounded.proofFinish_eq]
    exact hproofFinish
  have hcertificateFinish : bounded.witness.certificateFinish <= bound + 2 := by
    rw [bounded.certificateFinish_eq, ← bounded.sourceTokenCount_eq]
    exact hsourceCount
  have hsplit : bounded.witness.split <= bound := by
    rw [bounded.split_eq]
    exact hproofLength
  have htraceSize := directBoundedWitness_trace_sizeBounds bounded
  refine
    { inputTokenCount_le := hinputCount
      inputWidth_le := hinputWidth
      proofCode_size_le := hproofCodeSize
      sourceTokenCount_le := hsourceCount
      sourceWidth_le := hsourceWidth
      proofFinish_le := hproofFinish
      certificateStart_le := hcertificateStart
      certificateFinish_le := hcertificateFinish
      split_le := hsplit
      formulaTokenCount_le := hformulaCount
      formulaWidth_le := hformulaWidth
      traceWidth_le := directBoundedWitness_traceWidth_le bounded
      acceptedFuel_le := ?_
      conclusionRow_le := ?_
      traceValueBound_eq := bounded.traceValueBound_eq
      traceValueBound_size_le := htraceSize.traceValueBound }
  · unfold directPredicateAcceptedFuel directPredicateAcceptedFuelBound
    omega
  · unfold directPredicateConclusionRow directPredicateConclusionRowBound
    omega

/-- Numeric controls internal to the two canonical token tableaux and the two
input-split comparisons.  The packed table codes themselves are not loop
bounds; only token counts, token/offset bit lengths, and comparison widths are
recorded here. -/
structure DirectPredicateStreamQuantifierProfile
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) : Prop where
  proofTokenCount_le : bounded.proofTokens.length <= bound
  certificateTokenCount_le : bounded.certificateTokens.length <= bound
  inputToken_size_le : forall token,
    token ∈ bounded.proofTokens ++ bounded.certificateTokens ->
      Nat.size token <= bound
  inputOffset_size_le : forall offset,
    offset ∈ compactBinaryNatTokenOffsets
        (bounded.proofTokens ++ bounded.certificateTokens) ->
      Nat.size offset <= bound
  formulaToken_size_le : forall token, token ∈ bounded.formulaTokens ->
    Nat.size token <= Nat.size formulaCode
  formulaOffset_size_le : forall offset,
    offset ∈ compactBinaryNatTokenOffsets bounded.formulaTokens ->
      Nat.size offset <= Nat.size formulaCode
  inputSplit_bitWidth_le :
    bounded.witness.inputWidth + bounded.witness.sourceWidth <= 6 * bound + 4

theorem directBoundedWitness_streamQuantifierProfile
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    DirectPredicateStreamQuantifierProfile bounded := by
  have houter := directBoundedWitness_outerQuantifierProfile bounded
  have hproofLength : bounded.proofTokens.length <= bound := by
    calc
      bounded.proofTokens.length <=
          (bounded.proofTokens ++ bounded.certificateTokens).length := by simp
      _ = bounded.witness.inputTokenCount := bounded.inputTokenCount_eq.symm
      _ <= bound := houter.inputTokenCount_le
  have hcertificateLength : bounded.certificateTokens.length <= bound := by
    calc
      bounded.certificateTokens.length <=
          (bounded.proofTokens ++ bounded.certificateTokens).length := by simp
      _ = bounded.witness.inputTokenCount := bounded.inputTokenCount_eq.symm
      _ <= bound := houter.inputTokenCount_le
  refine
    { proofTokenCount_le := hproofLength
      certificateTokenCount_le := hcertificateLength
      inputToken_size_le := ?_
      inputOffset_size_le := ?_
      formulaToken_size_le := ?_
      formulaOffset_size_le := ?_
      inputSplit_bitWidth_le := ?_ }
  · intro token htoken
    have hsize := compactBinaryNatToken_size_le_payloadLength
      (bounded.proofTokens ++ bounded.certificateTokens) token htoken
    rw [← bounded.inputWidth_eq] at hsize
    exact hsize.trans houter.inputWidth_le
  · intro offset hoffset
    have hsize := compactBinaryNatTokenOffsets_size_le_payloadLength
      (bounded.proofTokens ++ bounded.certificateTokens) offset hoffset
    rw [← bounded.inputWidth_eq] at hsize
    exact hsize.trans houter.inputWidth_le
  · intro token htoken
    have hsize := compactBinaryNatToken_size_le_payloadLength
      bounded.formulaTokens token htoken
    rw [← bounded.formulaWidth_eq] at hsize
    exact hsize.trans houter.formulaWidth_le
  · intro offset hoffset
    have hsize := compactBinaryNatTokenOffsets_size_le_payloadLength
      bounded.formulaTokens offset hoffset
    rw [← bounded.formulaWidth_eq] at hsize
    exact hsize.trans houter.formulaWidth_le
  · have hsum := Nat.add_le_add houter.inputWidth_le houter.sourceWidth_le
    omega

/-- Numeric controls for the actual accepted conclusion row selected by the
bounded witness.  These are value bounds for loop controls, not merely bounds
on their binary encodings. -/
structure DirectPredicateConclusionQuantifierProfile
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) : Prop where
  stateWidth_le :
    let fuel := compactNumericVerifierFuelBound bounded.proofTokens
      bounded.certificateTokens
    let environment :=
      compactNumericVerifierStepWitnessTableFormulaEnvironment
        bounded.witness.traceWidth bounded.witness.traceTable (fuel - 1)
    environment 1 <= directPredicateConclusionStateWidthLimit bound
  stateTokenCount_le :
    let fuel := compactNumericVerifierFuelBound bounded.proofTokens
      bounded.certificateTokens
    let environment :=
      compactNumericVerifierStepWitnessTableFormulaEnvironment
        bounded.witness.traceWidth bounded.witness.traceTable (fuel - 1)
    environment 2 <= directPredicateConclusionStateTokenCountLimit bound
  formulaWidth_le : bounded.witness.formulaWidth <= Nat.size formulaCode
  formulaTokenCount_le :
    bounded.witness.formulaTokenCount <= Nat.size formulaCode
  stateFormulaWidth_le :
    let fuel := compactNumericVerifierFuelBound bounded.proofTokens
      bounded.certificateTokens
    let environment :=
      compactNumericVerifierStepWitnessTableFormulaEnvironment
        bounded.witness.traceWidth bounded.witness.traceTable (fuel - 1)
    environment 1 + bounded.witness.formulaWidth <=
      directPredicateConclusionStateWidthLimit bound + Nat.size formulaCode

theorem directBoundedWitness_conclusionQuantifierProfile
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    DirectPredicateConclusionQuantifierProfile bounded := by
  have houter := directBoundedWitness_outerQuantifierProfile bounded
  have hcontrols := bounded.traceFinalEnvironment_controlBounds
  refine
    { stateWidth_le := ?_
      stateTokenCount_le := ?_
      formulaWidth_le := houter.formulaWidth_le
      formulaTokenCount_le := houter.formulaTokenCount_le
      stateFormulaWidth_le := ?_ }
  · simpa only [directPredicateConclusionStateWidthLimit,
      directBoundedWitnessStreamWeight, bounded.streamWeight_eq] using
        hcontrols.1
  · simpa only [directPredicateConclusionStateTokenCountLimit,
      directBoundedWitnessStreamWeight, bounded.streamWeight_eq] using
        hcontrols.2
  · exact Nat.add_le_add
      (by
        simpa only [directPredicateConclusionStateWidthLimit,
          directBoundedWitnessStreamWeight, bounded.streamWeight_eq] using
            hcontrols.1)
      houter.formulaWidth_le

theorem directBoundedWitness_fuel_eq
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    compactNumericVerifierFuelBound bounded.proofTokens
        bounded.certificateTokens =
      directPredicateAcceptedFuel bounded.witness.inputTokenCount := by
  unfold compactNumericVerifierFuelBound directPredicateAcceptedFuel
  rw [bounded.inputTokenCount_eq, List.length_append]

/-- Every row used by the packed trace is tied to the same canonical verifier
execution, and every one of its 429 coordinates has a public binary-size bound.
This controls table-entry bit loops without claiming that arbitrary packed
coordinate values are polynomial as natural numbers. -/
theorem directBoundedWitness_canonicalRows
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    let fuel := compactNumericVerifierFuelBound bounded.proofTokens
      bounded.certificateTokens
    let start := compactNumericVerifierInitialState bounded.proofTokens
      bounded.certificateTokens
    forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <=
              directBoundedWitnessCoordinateLimit bound := by
  have hproof : compactAdditiveValueWeight
      (compactListedProofTokens bounded.tree) <= bounded.streamWeight := by
    rw [← bounded.proofTokens_eq]
    exact bounded.proofWeight
  have hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens bounded.certificate) <=
        bounded.streamWeight := by
    rw [← bounded.certificateTokens_eq]
    exact bounded.certificateWeight
  have hrows := compactNumericVerifierAcceptedBoundedRowExists
    bounded.tree bounded.certificate bounded.valid hproof hcertificate
  rw [← bounded.proofTokens_eq, ← bounded.certificateTokens_eq] at hrows
  simpa [directBoundedWitnessCoordinateLimit,
    directBoundedWitnessStreamWeight, bounded.streamWeight_eq] using hrows

theorem directBoundedWitness_traceEnvironment_controlBounds
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    let fuel := compactNumericVerifierFuelBound bounded.proofTokens
      bounded.certificateTokens
    forall rowIndex, rowIndex < fuel ->
      let environment :=
        compactNumericVerifierStepWitnessTableFormulaEnvironment
          bounded.witness.traceWidth bounded.witness.traceTable rowIndex
      environment 1 <= directPredicateTraceStateWidthLimit bound /\
        environment 2 <=
          directPredicateTraceStateTokenCountLimit bound := by
  dsimp only
  intro rowIndex hrowIndex
  have hcontrols := bounded.traceEnvironment_controlBounds rowIndex hrowIndex
  simpa only [directPredicateTraceStateWidthLimit,
    directPredicateTraceStateTokenCountLimit,
    directBoundedWitnessStreamWeight, bounded.streamWeight_eq] using hcontrols

theorem directBoundedWitness_traceEnvironment_stateListCountBounds
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    let fuel := compactNumericVerifierFuelBound bounded.proofTokens
      bounded.certificateTokens
    forall rowIndex, rowIndex < fuel ->
      let environment :=
        compactNumericVerifierStepWitnessTableFormulaEnvironment
          bounded.witness.traceWidth bounded.witness.traceTable rowIndex
      CompactNumericVerifierStepStateListCountBounds environment
        (directPredicateTraceStateTokenCountLimit bound) := by
  dsimp only
  intro rowIndex hrowIndex
  have hcounts :=
    bounded.traceEnvironment_stateListCountBounds rowIndex hrowIndex
  simpa only [directPredicateTraceStateTokenCountLimit,
    directBoundedWitnessStreamWeight, bounded.streamWeight_eq] using hcounts

/-- The four parser loop controls are numerically bounded on precisely those
canonical rows whose active task is the parse task. -/
theorem directBoundedWitness_traceEnvironment_parserControlBounds
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    let fuel := compactNumericVerifierFuelBound bounded.proofTokens
      bounded.certificateTokens
    let start := compactNumericVerifierInitialState bounded.proofTokens
      bounded.certificateTokens
    forall rowIndex, rowIndex < fuel ->
      let environment :=
        compactNumericVerifierStepWitnessTableFormulaEnvironment
          bounded.witness.traceWidth bounded.witness.traceTable rowIndex
      (compactNumericVerifierStateAt start rowIndex).2 = none ->
        forall restTasks,
          (compactNumericVerifierStateAt start rowIndex).1.2.1 =
              compactNumericParseTask :: restTasks ->
            CompactNumericVerifierParseSuccessParserControlBounds
              environment (directBoundedWitnessCoordinateLimit bound) := by
  dsimp only
  intro rowIndex hrowIndex
  have hcontrols :=
    bounded.traceEnvironment_parserControlBounds rowIndex hrowIndex
  simpa only [directBoundedWitnessCoordinateLimit,
    directBoundedWitnessStreamWeight, bounded.streamWeight_eq] using hcontrols

/-- Active combine branches retain their task counts, rule-list counts, and
quadratic formula-transform state-count controls on the public witness. -/
theorem directBoundedWitness_traceEnvironment_combineControlBounds
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    let fuel := compactNumericVerifierFuelBound bounded.proofTokens
      bounded.certificateTokens
    let start := compactNumericVerifierInitialState bounded.proofTokens
      bounded.certificateTokens
    forall rowIndex, rowIndex < fuel ->
      let environment :=
        compactNumericVerifierStepWitnessTableFormulaEnvironment
          bounded.witness.traceWidth bounded.witness.traceTable rowIndex
      (compactNumericVerifierStateAt start rowIndex).2 = none ->
        forall task restTasks,
          (compactNumericVerifierStateAt start rowIndex).1.2.1 =
              task :: restTasks ->
          task.1 ≠ 10 ->
            CompactNumericVerifierCombineEnvironmentCountControls
              environment := by
  dsimp only
  intro rowIndex hrowIndex hstatus task restTasks htask htaskNe
  exact bounded.traceEnvironment_combineControlBounds
    rowIndex hrowIndex hstatus task restTasks htask htaskNe

structure DirectPredicateTraceOuterQuantifierProfile
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) : Prop where
  fuel_eq : compactNumericVerifierFuelBound bounded.proofTokens
      bounded.certificateTokens =
    directPredicateAcceptedFuel bounded.witness.inputTokenCount
  fuel_le : compactNumericVerifierFuelBound bounded.proofTokens
      bounded.certificateTokens <= directPredicateAcceptedFuelBound bound
  traceWidth_le : bounded.witness.traceWidth <=
    directBoundedWitnessTraceWidthLimit bound
  canonicalRows :
    let fuel := compactNumericVerifierFuelBound bounded.proofTokens
      bounded.certificateTokens
    let start := compactNumericVerifierInitialState bounded.proofTokens
      bounded.certificateTokens
    forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <=
              directBoundedWitnessCoordinateLimit bound
  traceEnvironmentControls :
    let fuel := compactNumericVerifierFuelBound bounded.proofTokens
      bounded.certificateTokens
    forall rowIndex, rowIndex < fuel ->
      let environment :=
        compactNumericVerifierStepWitnessTableFormulaEnvironment
          bounded.witness.traceWidth bounded.witness.traceTable rowIndex
      environment 1 <= directPredicateTraceStateWidthLimit bound /\
        environment 2 <=
          directPredicateTraceStateTokenCountLimit bound
  stateListCountBounds :
    let fuel := compactNumericVerifierFuelBound bounded.proofTokens
      bounded.certificateTokens
    forall rowIndex, rowIndex < fuel ->
      let environment :=
        compactNumericVerifierStepWitnessTableFormulaEnvironment
          bounded.witness.traceWidth bounded.witness.traceTable rowIndex
      CompactNumericVerifierStepStateListCountBounds environment
        (directPredicateTraceStateTokenCountLimit bound)
  parserControlBounds :
    let fuel := compactNumericVerifierFuelBound bounded.proofTokens
      bounded.certificateTokens
    let start := compactNumericVerifierInitialState bounded.proofTokens
      bounded.certificateTokens
    forall rowIndex, rowIndex < fuel ->
      let environment :=
        compactNumericVerifierStepWitnessTableFormulaEnvironment
          bounded.witness.traceWidth bounded.witness.traceTable rowIndex
      (compactNumericVerifierStateAt start rowIndex).2 = none ->
        forall restTasks,
          (compactNumericVerifierStateAt start rowIndex).1.2.1 =
              compactNumericParseTask :: restTasks ->
            CompactNumericVerifierParseSuccessParserControlBounds
              environment (directBoundedWitnessCoordinateLimit bound)
  combineControlBounds :
    let fuel := compactNumericVerifierFuelBound bounded.proofTokens
      bounded.certificateTokens
    let start := compactNumericVerifierInitialState bounded.proofTokens
      bounded.certificateTokens
    forall rowIndex, rowIndex < fuel ->
      let environment :=
        compactNumericVerifierStepWitnessTableFormulaEnvironment
          bounded.witness.traceWidth bounded.witness.traceTable rowIndex
      (compactNumericVerifierStateAt start rowIndex).2 = none ->
        forall task restTasks,
          (compactNumericVerifierStateAt start rowIndex).1.2.1 =
              task :: restTasks ->
          task.1 ≠ 10 ->
            CompactNumericVerifierCombineEnvironmentCountControls
              environment

theorem directBoundedWitness_traceOuterQuantifierProfile
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    DirectPredicateTraceOuterQuantifierProfile bounded := by
  have houter := directBoundedWitness_outerQuantifierProfile bounded
  refine
    { fuel_eq := directBoundedWitness_fuel_eq bounded
      fuel_le := ?_
      traceWidth_le := houter.traceWidth_le
      canonicalRows := directBoundedWitness_canonicalRows bounded
      traceEnvironmentControls :=
        directBoundedWitness_traceEnvironment_controlBounds bounded
      stateListCountBounds :=
        directBoundedWitness_traceEnvironment_stateListCountBounds bounded
      parserControlBounds :=
        directBoundedWitness_traceEnvironment_parserControlBounds bounded
      combineControlBounds :=
        directBoundedWitness_traceEnvironment_combineControlBounds bounded }
  rw [directBoundedWitness_fuel_eq bounded]
  exact houter.acceptedFuel_le

#print axioms directBoundedWitness_traceWidth_le
#print axioms directBoundedWitness_outerQuantifierProfile
#print axioms directBoundedWitness_streamQuantifierProfile
#print axioms directBoundedWitness_conclusionQuantifierProfile
#print axioms directBoundedWitness_canonicalRows
#print axioms directBoundedWitness_traceEnvironment_controlBounds
#print axioms directBoundedWitness_traceEnvironment_stateListCountBounds
#print axioms directBoundedWitness_traceEnvironment_parserControlBounds
#print axioms directBoundedWitness_traceEnvironment_combineControlBounds
#print axioms directBoundedWitness_traceOuterQuantifierProfile

end FoundationCompactNumericListedDirectQuantifierProfile
