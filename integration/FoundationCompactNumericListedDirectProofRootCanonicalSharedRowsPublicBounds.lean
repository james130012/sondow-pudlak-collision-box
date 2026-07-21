import integration.FoundationCompactNumericListedDirectProofRootCanonicalSharedRows

/-!
# Public bounds for canonical proof-root shared rows

The canonical proof-root table already contains every input, decoded field,
sequent suffix, and nested parser trace needed by all successful root-parser
branches.  The original constructor intentionally returned only the layouts.
This module repeats the same concrete table construction while retaining the
table-code bound and every outer boundary-table size certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootCanonicalSharedRowsPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectSequentFormulaCanonicalLayouts

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNumericNodeFieldsAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

def compactProofRootCanonicalSharedDataWeight
    (input : List Nat) (root : CompactNumericProofRoot) (body : List Nat)
    (sequentSuffixes : List (List Nat))
    (sequentParserTraces : List CompactFormulaTokenParserDirectTrace)
    (intermediateSuffixes : List (List Nat))
    (extraParserTraces : List (List CompactUnifiedParserState)) : Nat :=
  compactAdditiveValueWeight input +
    compactAdditiveValueWeight root +
    compactAdditiveValueWeight body +
    compactAdditiveValueWeight sequentSuffixes +
    compactAdditiveValueWeight sequentParserTraces +
    compactAdditiveValueWeight intermediateSuffixes +
    compactAdditiveValueWeight extraParserTraces

def compactProofRootCanonicalSharedCoordinateSizeBound
    (dataWeight : Nat) : Nat :=
  dataWeight * (2 * dataWeight) +
    2 * dataWeight + dataWeight + 8

structure CompactProofRootCanonicalSharedTablePublicBounds
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish bound : Nat) : Prop where
  tokenTable : Nat.size tokenTable <= bound
  width_size : Nat.size width <= bound
  width_value : width <= bound
  tokenCount_size : Nat.size tokenCount <= bound
  tokenCount_value : tokenCount <= bound
  inputStart : Nat.size inputStart <= bound
  inputFinish : Nat.size inputFinish <= bound
  rootStart : Nat.size rootStart <= bound
  rootFinish : Nat.size rootFinish <= bound
  bodyStart : Nat.size bodyStart <= bound
  bodyFinish : Nat.size bodyFinish <= bound

structure CompactProofRootCanonicalSharedRowsPackage
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish
      sequentSuffixBoundary intermediateSuffixBoundary : Nat)
    (input : List Nat) (root : CompactNumericProofRoot) (body : List Nat)
    (sequentSuffixes : List (List Nat))
    (sequentParserTraces : List CompactFormulaTokenParserDirectTrace)
    (intermediateSuffixes : List (List Nat))
    (extraParserTraces : List (List CompactUnifiedParserState)) : Prop where
  inputLayout :
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input
  rootLayout :
    CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount rootStart rootFinish root
  bodyLayout :
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount bodyStart bodyFinish body
  sequentSuffixRows :
    CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        sequentSuffixBoundary sequentSuffixes
  sequentSuffixBoundary_size_le :
    Nat.size sequentSuffixBoundary <=
      (sequentSuffixes.length + 1) * tokenCount
  sequentParserRows :
    ∀ index < sequentParserTraces.length,
      ∃ parserStateBoundary,
        CompactUnifiedParserStateListRowLayouts
            tokenTable width tokenCount parserStateBoundary
              (sequentParserTraces.getI index) ∧
          Nat.size parserStateBoundary <=
            ((sequentParserTraces.getI index).length + 1) * tokenCount
  intermediateSuffixRows :
    CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        intermediateSuffixBoundary intermediateSuffixes
  intermediateSuffixBoundary_size_le :
    Nat.size intermediateSuffixBoundary <=
      (intermediateSuffixes.length + 1) * tokenCount
  extraParserRows :
    ∀ index < extraParserTraces.length,
      ∃ parserStateBoundary,
        CompactUnifiedParserStateListRowLayouts
            tokenTable width tokenCount parserStateBoundary
              (extraParserTraces.getI index) ∧
          Nat.size parserStateBoundary <=
            ((extraParserTraces.getI index).length + 1) * tokenCount

private theorem compactAdditiveTokenList_length_le_weight
    (tokens : List Nat) :
    tokens.length <= compactAdditiveTokenWeight tokens := by
  induction tokens with
  | nil => simp
  | cons token tokens ih =>
      simp only [List.length_cons, compactAdditiveTokenWeight_cons]
      omega

theorem exists_compactProofRootCanonicalSharedRows_with_publicBounds
    (input : List Nat) (root : CompactNumericProofRoot) (body : List Nat)
    (sequentSuffixes : List (List Nat))
    (sequentParserTraces : List CompactFormulaTokenParserDirectTrace)
    (intermediateSuffixes : List (List Nat))
    (extraParserTraces : List (List CompactUnifiedParserState)) :
    let dataWeight :=
      compactProofRootCanonicalSharedDataWeight input root body
        sequentSuffixes sequentParserTraces intermediateSuffixes
        extraParserTraces
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ sequentSuffixBoundary intermediateSuffixBoundary,
      CompactProofRootCanonicalSharedRowsPackage
          tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish
          sequentSuffixBoundary intermediateSuffixBoundary
          input root body sequentSuffixes sequentParserTraces
          intermediateSuffixes extraParserTraces ∧
        CompactProofRootCanonicalSharedTablePublicBounds
          tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish
          (compactProofRootCanonicalSharedCoordinateSizeBound dataWeight) := by
  let dataWeight :=
    compactProofRootCanonicalSharedDataWeight input root body
      sequentSuffixes sequentParserTraces intermediateSuffixes
      extraParserTraces
  let inputTokens := compactAdditiveEncode input
  let rootTokens := compactAdditiveEncode root
  let bodyTokens := compactAdditiveEncode body
  let sequentSuffixTokens := compactAdditiveEncode sequentSuffixes
  let sequentParserTokens := compactAdditiveEncode sequentParserTraces
  let intermediateSuffixTokens := compactAdditiveEncode intermediateSuffixes
  let extraParserTokens := compactAdditiveEncode extraParserTraces
  let tokens := inputTokens ++ rootTokens ++ bodyTokens ++
    sequentSuffixTokens ++ sequentParserTokens ++
    intermediateSuffixTokens ++ extraParserTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have htokenWeight :
      compactAdditiveTokenWeight tokens = dataWeight := by
    simp only [tokens, compactAdditiveTokenWeight_append,
      inputTokens, rootTokens, bodyTokens, sequentSuffixTokens,
      sequentParserTokens, intermediateSuffixTokens, extraParserTokens]
    rfl
  have htokenCount : tokens.length <= dataWeight := by
    rw [← htokenWeight]
    exact compactAdditiveTokenList_length_le_weight tokens
  have hwidth : width <= 2 * dataWeight := by
    change compactAdditiveTokenBitLength tokens <= _
    rw [compactAdditiveTokenBitLength_eq_two_mul_weight, htokenWeight]
  have htable :
      Nat.size tokenTable <= dataWeight * (2 * dataWeight) := by
    exact (compactFixedWidthTableCode_size_le width tokens).trans
      (Nat.mul_le_mul htokenCount hwidth)
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical
    [] input (rootTokens ++ bodyTokens ++ sequentSuffixTokens ++
      sequentParserTokens ++ intermediateSuffixTokens ++ extraParserTokens)
  dsimp only at hinputRaw
  have hinputTokenEq : [] ++ compactAdditiveEncode input ++
      (rootTokens ++ bodyTokens ++ sequentSuffixTokens ++
        sequentParserTokens ++ intermediateSuffixTokens ++
        extraParserTokens) = tokens := by
    simp [inputTokens, tokens, List.append_assoc]
  rw [hinputTokenEq] at hinputRaw
  have hrootRaw := compactNumericVerifierTaskDirectLayout_canonical
    inputTokens root (bodyTokens ++ sequentSuffixTokens ++
      sequentParserTokens ++ intermediateSuffixTokens ++ extraParserTokens)
  dsimp only at hrootRaw
  have hrootTokenEq : inputTokens ++ compactAdditiveEncode root ++
      (bodyTokens ++ sequentSuffixTokens ++ sequentParserTokens ++
        intermediateSuffixTokens ++ extraParserTokens) = tokens := by
    simp [rootTokens, tokens, List.append_assoc]
  rw [hrootTokenEq] at hrootRaw
  have hbodyRaw := compactAdditiveNatListDirectLayout_canonical
    (inputTokens ++ rootTokens) body
      (sequentSuffixTokens ++ sequentParserTokens ++
        intermediateSuffixTokens ++ extraParserTokens)
  dsimp only at hbodyRaw
  have hbodyTokenEq : (inputTokens ++ rootTokens) ++
      compactAdditiveEncode body ++
      (sequentSuffixTokens ++ sequentParserTokens ++
        intermediateSuffixTokens ++ extraParserTokens) = tokens := by
    simp [bodyTokens, tokens, List.append_assoc]
  rw [hbodyTokenEq] at hbodyRaw
  have hsequentSuffixRaw := compactAdditiveNatListListDirectLayout_canonical
    (inputTokens ++ rootTokens ++ bodyTokens) sequentSuffixes
      (sequentParserTokens ++ intermediateSuffixTokens ++ extraParserTokens)
  dsimp only at hsequentSuffixRaw
  have hsequentSuffixTokenEq :
      (inputTokens ++ rootTokens ++ bodyTokens) ++
        compactAdditiveEncode sequentSuffixes ++
        (sequentParserTokens ++ intermediateSuffixTokens ++
          extraParserTokens) = tokens := by
    simp [sequentSuffixTokens, tokens, List.append_assoc]
  rw [hsequentSuffixTokenEq] at hsequentSuffixRaw
  rcases hsequentSuffixRaw with
    ⟨sequentSuffixBoundary, _hsequentSuffixStructure,
      hsequentSuffixRows, hsequentSuffixSize⟩
  have hsequentParserRaw := compactAdditiveStructuredListElementLayouts_canonical
    CompactUnifiedParserStateListDirectLayout
    compactUnifiedParserStateListDirectLayout_canonical
    (inputTokens ++ rootTokens ++ bodyTokens ++ sequentSuffixTokens)
      sequentParserTraces (intermediateSuffixTokens ++ extraParserTokens)
  dsimp only at hsequentParserRaw
  have hsequentParserTokenEq :
      (inputTokens ++ rootTokens ++ bodyTokens ++ sequentSuffixTokens) ++
        compactAdditiveEncode sequentParserTraces ++
        (intermediateSuffixTokens ++ extraParserTokens) = tokens := by
    simp [sequentParserTokens, tokens, List.append_assoc]
  rw [hsequentParserTokenEq] at hsequentParserRaw
  have hsequentParserRows := hsequentParserRaw.2.1
  have hintermediateRaw := compactAdditiveNatListListDirectLayout_canonical
    (inputTokens ++ rootTokens ++ bodyTokens ++ sequentSuffixTokens ++
      sequentParserTokens) intermediateSuffixes extraParserTokens
  dsimp only at hintermediateRaw
  have hintermediateTokenEq :
      (inputTokens ++ rootTokens ++ bodyTokens ++ sequentSuffixTokens ++
        sequentParserTokens) ++ compactAdditiveEncode intermediateSuffixes ++
        extraParserTokens = tokens := by
    simp [intermediateSuffixTokens, tokens, List.append_assoc]
  rw [hintermediateTokenEq] at hintermediateRaw
  rcases hintermediateRaw with
    ⟨intermediateSuffixBoundary, _hintermediateStructure,
      hintermediateRows, hintermediateSize⟩
  have hextraParserRaw := compactAdditiveStructuredListElementLayouts_canonical
    CompactUnifiedParserStateListDirectLayout
    compactUnifiedParserStateListDirectLayout_canonical
    (inputTokens ++ rootTokens ++ bodyTokens ++ sequentSuffixTokens ++
      sequentParserTokens ++ intermediateSuffixTokens)
      extraParserTraces []
  dsimp only at hextraParserRaw
  have hextraParserTokenEq :
      (inputTokens ++ rootTokens ++ bodyTokens ++ sequentSuffixTokens ++
        sequentParserTokens ++ intermediateSuffixTokens) ++
        compactAdditiveEncode extraParserTraces ++ [] = tokens := by
    simp [extraParserTokens, tokens, List.append_assoc]
  rw [hextraParserTokenEq] at hextraParserRaw
  have hextraParserRows := hextraParserRaw.2.1
  let coordinateBound :=
    compactProofRootCanonicalSharedCoordinateSizeBound dataWeight
  have hposition
      {position : Nat} (hposition : position <= tokens.length) :
      Nat.size position <= coordinateBound := by
    exact (natSize_le_of_le (hposition.trans htokenCount)).trans (by
      unfold coordinateBound
        compactProofRootCanonicalSharedCoordinateSizeBound
      omega)
  have htablePublic : Nat.size tokenTable <= coordinateBound :=
    htable.trans (by
      unfold coordinateBound
        compactProofRootCanonicalSharedCoordinateSizeBound
      omega)
  have hwidthPublic : Nat.size width <= coordinateBound :=
    (natSize_le_of_le hwidth).trans (by
      unfold coordinateBound
        compactProofRootCanonicalSharedCoordinateSizeBound
      omega)
  have htokenCountPublic : Nat.size tokens.length <= coordinateBound :=
    (natSize_le_of_le htokenCount).trans (by
      unfold coordinateBound
        compactProofRootCanonicalSharedCoordinateSizeBound
      omega)
  have hwidthValuePublic : width <= coordinateBound :=
    hwidth.trans (by
      unfold coordinateBound
        compactProofRootCanonicalSharedCoordinateSizeBound
      omega)
  have htokenCountValuePublic : tokens.length <= coordinateBound :=
    htokenCount.trans (by
      unfold coordinateBound
        compactProofRootCanonicalSharedCoordinateSizeBound
      omega)
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    inputTokens.length, inputTokens.length + rootTokens.length,
    inputTokens.length + rootTokens.length,
    inputTokens.length + rootTokens.length + bodyTokens.length,
    sequentSuffixBoundary, intermediateSuffixBoundary, ?_, ?_⟩
  · refine
      { inputLayout := ?_
        rootLayout := ?_
        bodyLayout := ?_
        sequentSuffixRows := ?_
        sequentSuffixBoundary_size_le := ?_
        sequentParserRows := ?_
        intermediateSuffixRows := ?_
        intermediateSuffixBoundary_size_le := ?_
        extraParserRows := ?_ }
    · simpa only [tokenTable, width, inputTokens,
        List.length_nil, Nat.zero_add] using hinputRaw
    · simpa only [tokenTable, width, List.length_append] using hrootRaw
    · simpa only [tokenTable, width, List.length_append] using hbodyRaw
    · simpa only [tokenTable, width] using hsequentSuffixRows
    · simpa only [List.length_append] using hsequentSuffixSize
    · intro index hindex
      rcases hsequentParserRows index hindex with
        ⟨left, _hleftBound, right, _hrightBound,
          _hleftEntry, _hrightEntry, htraceLayout⟩
      rcases htraceLayout with
        ⟨parserStateBoundary, _htraceStructure,
          hparserStateRows, hparserStateSize⟩
      exact ⟨parserStateBoundary, by
        simpa only [tokenTable, width] using hparserStateRows, by
        simpa only [List.length_append] using hparserStateSize⟩
    · simpa only [tokenTable, width] using hintermediateRows
    · simpa only [List.length_append] using hintermediateSize
    · intro index hindex
      rcases hextraParserRows index hindex with
        ⟨left, _hleftBound, right, _hrightBound,
          _hleftEntry, _hrightEntry, htraceLayout⟩
      rcases htraceLayout with
        ⟨parserStateBoundary, _htraceStructure,
          hparserStateRows, hparserStateSize⟩
      exact ⟨parserStateBoundary, by
        simpa only [tokenTable, width] using hparserStateRows, by
        simpa only [List.length_append] using hparserStateSize⟩
  · exact
      { tokenTable := htablePublic
        width_size := hwidthPublic
        width_value := hwidthValuePublic
        tokenCount_size := htokenCountPublic
        tokenCount_value := htokenCountValuePublic
        inputStart := by
          simp [compactProofRootCanonicalSharedCoordinateSizeBound]
        inputFinish := hposition (by simp [tokens])
        rootStart := hposition (by simp [tokens])
        rootFinish := hposition (by
          simp only [tokens, List.length_append]
          omega)
        bodyStart := hposition (by
          simp only [tokens, List.length_append]
          omega)
        bodyFinish := hposition (by
          simp only [tokens, List.length_append]
          omega) }

#print axioms
  exists_compactProofRootCanonicalSharedRows_with_publicBounds

end FoundationCompactNumericListedDirectProofRootCanonicalSharedRowsPublicBounds
