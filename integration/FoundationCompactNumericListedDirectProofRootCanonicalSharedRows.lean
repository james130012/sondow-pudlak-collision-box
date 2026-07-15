import integration.FoundationCompactNumericListedDirectProofRootSequentOnlyEndpoint

/-!
# Canonical shared rows for every proof-root parser branch

The full input, decoded root, sequent body, sequent-parser traces, optional
intermediate suffixes, and additional formula/term-parser traces are encoded in
one fixed-width token table.  Later branch graphs use these rows without
introducing independent existential tables.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootCanonicalSharedRows

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
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

/-- A single canonical table containing every typed object needed by any
successful proof-root parser branch. -/
theorem exists_compactProofRootCanonicalSharedRows
    (input : List Nat) (root : CompactNumericProofRoot) (body : List Nat)
    (sequentSuffixes : List (List Nat))
    (sequentParserTraces : List CompactFormulaTokenParserDirectTrace)
    (intermediateSuffixes : List (List Nat))
    (extraParserTraces : List (List CompactUnifiedParserState)) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ sequentSuffixBoundary intermediateSuffixBoundary,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactNumericVerifierTaskDirectLayout
        tokenTable width tokenCount rootStart rootFinish root ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount bodyStart bodyFinish body ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          sequentSuffixBoundary sequentSuffixes ∧
      (∀ index < sequentParserTraces.length,
        ∃ parserStateBoundary,
          CompactUnifiedParserStateListRowLayouts
            tokenTable width tokenCount parserStateBoundary
              (sequentParserTraces.getI index)) ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          intermediateSuffixBoundary intermediateSuffixes ∧
      (∀ index < extraParserTraces.length,
        ∃ parserStateBoundary,
          CompactUnifiedParserStateListRowLayouts
            tokenTable width tokenCount parserStateBoundary
              (extraParserTraces.getI index)) := by
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
      hsequentSuffixRows, _hsequentSuffixSize⟩
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
      hintermediateRows, _hintermediateSize⟩
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
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    inputTokens.length, inputTokens.length + rootTokens.length,
    inputTokens.length + rootTokens.length,
    inputTokens.length + rootTokens.length + bodyTokens.length,
    sequentSuffixBoundary, intermediateSuffixBoundary,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [tokenTable, width, inputTokens,
      List.length_nil, Nat.zero_add] using hinputRaw
  · simpa only [tokenTable, width, List.length_append] using hrootRaw
  · simpa only [tokenTable, width, List.length_append] using hbodyRaw
  · simpa only [tokenTable, width] using hsequentSuffixRows
  · intro index hindex
    rcases hsequentParserRows index hindex with
      ⟨left, _hleftBound, right, _hrightBound,
        _hleftEntry, _hrightEntry, htraceLayout⟩
    rcases htraceLayout with
      ⟨parserStateBoundary, _htraceStructure,
        hparserStateRows, _hparserStateSize⟩
    exact ⟨parserStateBoundary, by
      simpa only [tokenTable, width] using hparserStateRows⟩
  · simpa only [tokenTable, width] using hintermediateRows
  · intro index hindex
    rcases hextraParserRows index hindex with
      ⟨left, _hleftBound, right, _hrightBound,
        _hleftEntry, _hrightEntry, htraceLayout⟩
    rcases htraceLayout with
      ⟨parserStateBoundary, _htraceStructure,
        hparserStateRows, _hparserStateSize⟩
    exact ⟨parserStateBoundary, by
      simpa only [tokenTable, width] using hparserStateRows⟩

#print axioms exists_compactProofRootCanonicalSharedRows

end FoundationCompactNumericListedDirectProofRootCanonicalSharedRows
