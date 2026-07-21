import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceInputTableau
import integration.FoundationCompactNumericListedDirectVerifierInitialEnvironmentFormula

/-!
# Exact split between a public token stream and verifier-state list bodies

The public proof code decodes to the raw concatenation of proof tokens and
certificate tokens.  The verifier state stores each list with one additive
list header.  This bounded graph compares the raw prefix and suffix with the
two list bodies, deliberately skipping those two internal headers.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedTraceInputSplit

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectVerifierInitialEnvironmentFormula
open FoundationCompactNumericListedDirectVerifierAcceptedTraceInputTableau

def CompactNumericVerifierAcceptedTraceInputSplit
    (inputTable inputWidth inputTokenCount
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split : Nat) :
    Prop :=
  split <= inputTokenCount /\
    CompactFixedWidthCrossTableSlicesEq
      inputTable inputWidth inputTokenCount 0 split
      sourceTable sourceWidth sourceTokenCount (proofStart + 1) proofFinish /\
    CompactFixedWidthCrossTableSlicesEq
      inputTable inputWidth inputTokenCount split inputTokenCount
      sourceTable sourceWidth sourceTokenCount
        (certificateStart + 1) certificateFinish

def compactNumericVerifierAcceptedTraceInputSplitDef :
    HierarchySymbol.sigmaZero.Semisentence 11 := .mkSigma
  “inputTable inputWidth inputTokenCount
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split.
    split ≤ inputTokenCount ∧
    !(compactFixedWidthCrossTableSlicesEqDef)
      inputTable inputWidth inputTokenCount 0 split
      sourceTable sourceWidth sourceTokenCount (proofStart + 1) proofFinish ∧
    !(compactFixedWidthCrossTableSlicesEqDef)
      inputTable inputWidth inputTokenCount split inputTokenCount
      sourceTable sourceWidth sourceTokenCount
        (certificateStart + 1) certificateFinish”

@[simp] theorem compactNumericVerifierAcceptedTraceInputSplitDef_spec
    (inputTable inputWidth inputTokenCount
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split : Nat) :
    compactNumericVerifierAcceptedTraceInputSplitDef.val.Evalb
        ![inputTable, inputWidth, inputTokenCount,
          sourceTable, sourceWidth, sourceTokenCount,
          proofStart, proofFinish, certificateStart, certificateFinish,
          split] ↔
      CompactNumericVerifierAcceptedTraceInputSplit
        inputTable inputWidth inputTokenCount
        sourceTable sourceWidth sourceTokenCount
        proofStart proofFinish certificateStart certificateFinish split := by
  let env : Fin 11 -> Nat :=
    ![inputTable, inputWidth, inputTokenCount,
      sourceTable, sourceWidth, sourceTokenCount,
      proofStart, proofFinish, certificateStart, certificateFinish, split]
  change compactNumericVerifierAcceptedTraceInputSplitDef.val.Evalb env ↔ _
  have hproofEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 11), #1, #2, (↑(0 : Nat)), #10,
          #3, #4, #5, ‘#6 + 1’, #7]) =
        ![inputTable, inputWidth, inputTokenCount, 0, split,
          sourceTable, sourceWidth, sourceTokenCount,
          proofStart + 1, proofFinish] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  have hcertificateEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 11), #1, #2, #10, #2,
          #3, #4, #5, ‘#8 + 1’, #9]) =
        ![inputTable, inputWidth, inputTokenCount, split, inputTokenCount,
          sourceTable, sourceWidth, sourceTokenCount,
          certificateStart + 1, certificateFinish] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  simp [compactNumericVerifierAcceptedTraceInputSplitDef,
    CompactNumericVerifierAcceptedTraceInputSplit,
    Semiformula.eval_substs, hproofEnv, hcertificateEnv, env]

theorem compactNumericVerifierAcceptedTraceInputSplitDef_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactNumericVerifierAcceptedTraceInputSplitDef.val :=
  compactNumericVerifierAcceptedTraceInputSplitDef.sigma_prop

private theorem crossTable_entryValue_eq
    {sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish
      offset sourceValue targetValue : Nat}
    (heq : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish)
    (hoffset : offset < sourceFinish - sourceStart)
    (hsource : CompactFixedWidthEntry sourceTable sourceWidth
      (sourceStart + offset) sourceValue)
    (htarget : CompactFixedWidthEntry targetTable targetWidth
      (targetStart + offset) targetValue) :
    sourceValue = targetValue :=
  heq.entryValue_eq_at_offset hoffset hsource htarget

theorem CompactNumericVerifierAcceptedTraceInputSplit.decodedTokens_eq
    {code inputTable inputWidth inputTokenCount inputOffsetTable
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split : Nat}
    {proofTokens certificateTokens : List Nat}
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateFinish : Nat}
    (_hinput : CompactCanonicalPackedTokenStreamTableauAtWidth
      code inputTokenCount inputTable inputOffsetTable inputWidth)
    (hsplit : CompactNumericVerifierAcceptedTraceInputSplit
      inputTable inputWidth inputTokenCount
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split)
    (hproofSource : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount proofStart proofFinish
      stateTable stateWidth stateTokenCount stateProofStart stateProofFinish)
    (hcertificateSource : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount
        certificateStart certificateFinish
      stateTable stateWidth stateTokenCount
        stateProofFinish stateCertificateFinish)
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
      stateProofFinish stateCertificateFinish certificateTokens) :
    compactCanonicalPackedTokenStreamTableauAtWidthTokens
        inputTokenCount inputTable inputWidth =
      proofTokens ++ certificateTokens := by
  let inputTokens :=
    compactCanonicalPackedTokenStreamTableauAtWidthTokens
      inputTokenCount inputTable inputWidth
  rcases hsplit with ⟨hsplitBound, hproofRaw, hcertificateRaw⟩
  have hproofFinishInternal :=
    CompactAdditiveNatListDirectLayout.finish_eq hproofLayout
  have hcertificateFinishInternal :=
    CompactAdditiveNatListDirectLayout.finish_eq hcertificateLayout
  rcases hproofSource with
    ⟨proofEncodedCount, _hproofSourceCount, _hproofTargetCount,
      hproofSourceFinish, hproofTargetFinish,
      _hproofSourceBound, _hproofTargetBound, hproofSourceBits⟩
  let hproofSource' : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount proofStart proofFinish
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish :=
    ⟨proofEncodedCount, _hproofSourceCount, _hproofTargetCount,
      hproofSourceFinish, hproofTargetFinish,
      _hproofSourceBound, _hproofTargetBound, hproofSourceBits⟩
  rcases hcertificateSource with
    ⟨certificateEncodedCount, _hcertificateSourceCount,
      _hcertificateTargetCount,
      hcertificateSourceFinish, hcertificateTargetFinish,
      _hcertificateSourceBound, _hcertificateTargetBound,
      hcertificateSourceBits⟩
  let hcertificateSource' : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount
        certificateStart certificateFinish
      stateTable stateWidth stateTokenCount
        stateProofFinish stateCertificateFinish :=
    ⟨certificateEncodedCount, _hcertificateSourceCount,
      _hcertificateTargetCount,
      hcertificateSourceFinish, hcertificateTargetFinish,
      _hcertificateSourceBound, _hcertificateTargetBound,
      hcertificateSourceBits⟩
  rcases hproofRaw with
    ⟨proofRawCount, _hproofRawSourceCount, _hproofRawTargetCount,
      hproofRawFinish, hproofRawTargetFinish,
      _hproofRawSourceBound, _hproofRawTargetBound, hproofRawBits⟩
  let hproofRaw' : CompactFixedWidthCrossTableSlicesEq
      inputTable inputWidth inputTokenCount 0 split
      sourceTable sourceWidth sourceTokenCount
        (proofStart + 1) proofFinish :=
    ⟨proofRawCount, _hproofRawSourceCount, _hproofRawTargetCount,
      hproofRawFinish, hproofRawTargetFinish,
      _hproofRawSourceBound, _hproofRawTargetBound, hproofRawBits⟩
  rcases hcertificateRaw with
    ⟨certificateRawCount, _hcertificateRawSourceCount,
      _hcertificateRawTargetCount,
      hcertificateRawFinish, hcertificateRawTargetFinish,
      _hcertificateRawSourceBound, _hcertificateRawTargetBound,
      hcertificateRawBits⟩
  let hcertificateRaw' : CompactFixedWidthCrossTableSlicesEq
      inputTable inputWidth inputTokenCount split inputTokenCount
      sourceTable sourceWidth sourceTokenCount
        (certificateStart + 1) certificateFinish :=
    ⟨certificateRawCount, _hcertificateRawSourceCount,
      _hcertificateRawTargetCount,
      hcertificateRawFinish, hcertificateRawTargetFinish,
      _hcertificateRawSourceBound, _hcertificateRawTargetBound,
      hcertificateRawBits⟩
  have hproofLength : proofTokens.length = split := by omega
  have hcertificateLength :
      certificateTokens.length = inputTokenCount - split := by omega
  have hproofRawCountEq : proofRawCount = split := by omega
  have hproofEncodedCountEq :
      proofEncodedCount = 1 + proofTokens.length := by omega
  have hcertificateRawCountEq :
      certificateRawCount = inputTokenCount - split := by omega
  have hcertificateEncodedCountEq :
      certificateEncodedCount = 1 + certificateTokens.length := by omega
  have htotalLength :
      (proofTokens ++ certificateTokens).length = inputTokenCount := by
    simp only [List.length_append]
    omega
  have hinputLength : inputTokens.length = inputTokenCount := by
    simp [inputTokens]
  apply List.ext_getElem
  · exact hinputLength.trans htotalLength.symm
  · intro index hinputIndex htargetIndex
    have hindexCount : index < inputTokenCount := by
      simpa [hinputLength] using hinputIndex
    by_cases hproofIndex : index < split
    · have hproofListIndex : index < proofTokens.length := by omega
      have hinputIndex' : index < inputTokens.length := by
        simpa [inputTokens] using hinputIndex
      have hinputEntry : CompactFixedWidthEntry inputTable inputWidth index
          (inputTokens.getI index) := by
        simpa [inputTokens] using
          compactCanonicalPackedTokenStreamTableauAtWidth_entry
            inputTokenCount inputTable inputWidth index hindexCount
      let sourceValue := compactFixedWidthTableValue sourceTable sourceWidth
        (proofStart + 1 + index)
      have hsourceEntry : CompactFixedWidthEntry sourceTable sourceWidth
          (proofStart + 1 + index) sourceValue := by
        exact compactFixedWidthTableValue_entry _ _ _
      have hinternalEntry :=
        CompactAdditiveNatListDirectLayout.valueEntry
          hproofLayout index hproofListIndex
      have hrawEq : inputTokens.getI index = sourceValue := by
        apply crossTable_entryValue_eq (offset := index) hproofRaw' (by
          rw [show split - 0 = proofRawCount by omega, hproofRawCountEq]
          exact hproofIndex)
        · simpa using hinputEntry
        · simpa [Nat.add_assoc] using hsourceEntry
      have hinternalEq : sourceValue = proofTokens.getI index := by
        apply crossTable_entryValue_eq (offset := 1 + index) hproofSource' (by
          rw [show proofFinish - proofStart = proofEncodedCount by omega,
            hproofEncodedCountEq]
          omega)
        · simpa [Nat.add_assoc] using hsourceEntry
        · simpa [Nat.add_assoc] using hinternalEntry
      rw [List.getI_eq_getElem _ hinputIndex'] at hrawEq
      rw [List.getI_eq_getElem proofTokens hproofListIndex] at hinternalEq
      rw [List.getElem_append_left hproofListIndex]
      exact hrawEq.trans hinternalEq
    · have hcertificateIndex : index - split < certificateTokens.length := by
        omega
      have hinputIndex' : index < inputTokens.length := by
        simpa [inputTokens] using hinputIndex
      have hsplitIndex : split + (index - split) = index := by omega
      have hinputEntry : CompactFixedWidthEntry inputTable inputWidth index
          (inputTokens.getI index) := by
        simpa [inputTokens] using
          compactCanonicalPackedTokenStreamTableauAtWidth_entry
            inputTokenCount inputTable inputWidth index hindexCount
      let sourceValue := compactFixedWidthTableValue sourceTable sourceWidth
        (certificateStart + 1 + (index - split))
      have hsourceEntry : CompactFixedWidthEntry sourceTable sourceWidth
          (certificateStart + 1 + (index - split)) sourceValue := by
        exact compactFixedWidthTableValue_entry _ _ _
      have hinternalEntry :=
        CompactAdditiveNatListDirectLayout.valueEntry
          hcertificateLayout (index - split) hcertificateIndex
      have hrawEq : inputTokens.getI index = sourceValue := by
        apply crossTable_entryValue_eq (offset := index - split)
          hcertificateRaw' (by
            simpa only [← hcertificateLength] using hcertificateIndex)
        · simpa [hsplitIndex] using hinputEntry
        · simpa [Nat.add_assoc] using hsourceEntry
      have hinternalEq : sourceValue =
          certificateTokens.getI (index - split) := by
        apply crossTable_entryValue_eq (offset := 1 + (index - split))
          hcertificateSource' (by
            rw [show certificateFinish - certificateStart =
                certificateEncodedCount by omega,
              hcertificateEncodedCountEq]
            omega)
        · simpa [Nat.add_assoc] using hsourceEntry
        · simpa [Nat.add_assoc] using hinternalEntry
      rw [List.getI_eq_getElem _ hinputIndex'] at hrawEq
      rw [List.getI_eq_getElem certificateTokens hcertificateIndex]
        at hinternalEq
      have hproofLength' : proofTokens.length = split := hproofLength
      rw [List.getElem_append_right (by omega)]
      simpa [hproofLength'] using hrawEq.trans hinternalEq

theorem compactNumericVerifierAcceptedTraceInputSplit_canonical
    (proofTokens certificateTokens : List Nat) :
    let inputTokens := proofTokens ++ certificateTokens
    let inputWidth := (compactBinaryNatPayloadBits inputTokens).length
    let proofEncoded := compactAdditiveEncode proofTokens
    let certificateEncoded := compactAdditiveEncode certificateTokens
    let sourceTokens := proofEncoded ++ certificateEncoded
    let sourceWidth := (compactBinaryNatPayloadBits sourceTokens).length
    CompactNumericVerifierAcceptedTraceInputSplit
      (compactFixedWidthTableCode inputWidth inputTokens)
      inputWidth inputTokens.length
      (compactFixedWidthTableCode sourceWidth sourceTokens)
      sourceWidth sourceTokens.length
      0 proofEncoded.length
      proofEncoded.length sourceTokens.length proofTokens.length := by
  let inputTokens := proofTokens ++ certificateTokens
  let inputWidth := (compactBinaryNatPayloadBits inputTokens).length
  let proofEncoded := compactAdditiveEncode proofTokens
  let certificateEncoded := compactAdditiveEncode certificateTokens
  let sourceTokens := proofEncoded ++ certificateEncoded
  let sourceWidth := (compactBinaryNatPayloadBits sourceTokens).length
  have hinputSizes : ∀ value ∈ inputTokens, Nat.size value ≤ inputWidth := by
    intro value hvalue
    exact compactBinaryNatToken_size_le_payloadLength
      inputTokens value hvalue
  have hsourceSizes : ∀ value ∈ sourceTokens,
      Nat.size value ≤ sourceWidth := by
    intro value hvalue
    exact compactBinaryNatToken_size_le_payloadLength
      sourceTokens value hvalue
  have hproofLayout : CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode sourceWidth sourceTokens)
      sourceWidth sourceTokens.length 0 proofEncoded.length proofTokens := by
    have hsourceTokens :
        [] ++ compactAdditiveEncode proofTokens ++ certificateEncoded =
          sourceTokens := by
      simp [sourceTokens, proofEncoded]
    have hraw := compactAdditiveNatListDirectLayout_canonical
      [] proofTokens certificateEncoded
    dsimp only at hraw
    rw [hsourceTokens] at hraw
    have hfinish : ([] : List Nat).length +
        (compactAdditiveEncode proofTokens).length =
        proofEncoded.length := by simp [proofEncoded]
    rw [hfinish] at hraw
    exact hraw
  have hcertificateLayout : CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode sourceWidth sourceTokens)
      sourceWidth sourceTokens.length proofEncoded.length
        sourceTokens.length certificateTokens := by
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
  have hproofFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hproofLayout
  have hcertificateFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hcertificateLayout
  have hproofRaw : CompactFixedWidthCrossTableSlicesEq
      (compactFixedWidthTableCode inputWidth inputTokens)
        inputWidth inputTokens.length 0 proofTokens.length
      (compactFixedWidthTableCode sourceWidth sourceTokens)
        sourceWidth sourceTokens.length 1 proofEncoded.length := by
    apply CompactFixedWidthCrossTableSlicesEq.of_entry_values
        (values := proofTokens)
    · simp
    · omega
    · simp [inputTokens]
    · simp [sourceTokens]
    · intro index hindex
      have hentry := compactFixedWidthTableCode_entry
        inputWidth inputTokens index (by simp [inputTokens]; omega)
        hinputSizes
      have hvalue : inputTokens.getI index = proofTokens.getI index := by
        change (proofTokens ++ certificateTokens).getI index = _
        rw [List.getI_append _ _ _ hindex]
      simpa only [Nat.zero_add, hvalue] using hentry
    · intro index hindex
      simpa only [Nat.zero_add, Nat.add_assoc] using
        (CompactAdditiveNatListDirectLayout.valueEntry
          hproofLayout index hindex)
  have hcertificateRaw : CompactFixedWidthCrossTableSlicesEq
      (compactFixedWidthTableCode inputWidth inputTokens)
        inputWidth inputTokens.length proofTokens.length inputTokens.length
      (compactFixedWidthTableCode sourceWidth sourceTokens)
        sourceWidth sourceTokens.length
        (proofEncoded.length + 1) sourceTokens.length := by
    apply CompactFixedWidthCrossTableSlicesEq.of_entry_values
        (values := certificateTokens)
    · simp [inputTokens]
    · omega
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · intro index hindex
      have hrawIndex : proofTokens.length + index < inputTokens.length := by
        simp [inputTokens]
        omega
      have hentry := compactFixedWidthTableCode_entry
        inputWidth inputTokens (proofTokens.length + index)
        hrawIndex hinputSizes
      have hvalue : inputTokens.getI (proofTokens.length + index) =
          certificateTokens.getI index := by
        have happend := List.getI_append_right proofTokens certificateTokens
          (proofTokens.length + index) (by omega)
        simpa using happend
      simpa only [Nat.add_assoc, hvalue] using hentry
    · intro index hindex
      simpa only [Nat.add_assoc] using
        (CompactAdditiveNatListDirectLayout.valueEntry
          hcertificateLayout index hindex)
  exact ⟨by simp, hproofRaw, hcertificateRaw⟩

#print axioms compactNumericVerifierAcceptedTraceInputSplitDef_spec
#print axioms compactNumericVerifierAcceptedTraceInputSplitDef_sigmaZero
#print axioms CompactNumericVerifierAcceptedTraceInputSplit.decodedTokens_eq
#print axioms compactNumericVerifierAcceptedTraceInputSplit_canonical

end FoundationCompactNumericListedDirectVerifierAcceptedTraceInputSplit
