import integration.FoundationCompactNumericListedDirectSequentFormulaTraceCompleteness

/-!
# Canonical shared layouts for a sequent formula trace

The suffix rows, parsed formula-value rows, and every formula-parser state
trace are placed in one canonical additive token table.  This closes the
coordinate-sharing part of the reverse sequent-trace construction.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSequentFormulaCanonicalLayouts

open FoundationCompactAdditiveTokenCodec
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectParserStateListLayout

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

/-- The complete direct layout of one list of parser states, packaged so it
can itself be used as an element relation in an outer structured list. -/
def CompactUnifiedParserStateListDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (states : List CompactUnifiedParserState) : Prop :=
  ∃ boundaryTable,
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start states.length finish boundaryTable ∧
    CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount boundaryTable states ∧
    Nat.size boundaryTable ≤ (states.length + 1) * tokenCount

theorem compactUnifiedParserStateListDirectLayout_canonical
    (frontTokens : List Nat) (states : List CompactUnifiedParserState)
    (backTokens : List Nat) :
    let stateTokens := compactAdditiveEncode states
    let tokens := frontTokens ++ stateTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + stateTokens.length
    CompactUnifiedParserStateListDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish states := by
  rcases
      FoundationCompactNumericListedDirectParserStateListLayout.compactUnifiedParserStateListDirectLayout_canonical
        frontTokens states backTokens with
    ⟨hlayout, hrows, hsize⟩
  exact ⟨_, hlayout, hrows, hsize⟩

/-- Canonical common table for all three typed data families used by the
sequent formula-list trace. -/
theorem exists_compactSequentFormulaCanonicalSharedLayouts
    (suffixes values : List (List Nat))
    (parserTraces : List CompactFormulaTokenParserDirectTrace) :
    ∃ tokenTable width tokenCount suffixBoundary valueBoundary,
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          suffixBoundary suffixes ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          valueBoundary values ∧
      (∀ index < parserTraces.length,
        ∃ parserStateBoundary,
          CompactUnifiedParserStateListRowLayouts
            tokenTable width tokenCount parserStateBoundary
              (parserTraces.getI index)) := by
  let suffixTokens := compactAdditiveEncode suffixes
  let valueTokens := compactAdditiveEncode values
  let parserTokens := compactAdditiveEncode parserTraces
  let tokens := suffixTokens ++ valueTokens ++ parserTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have hsuffixRaw := compactAdditiveNatListListDirectLayout_canonical
    [] suffixes (valueTokens ++ parserTokens)
  dsimp only at hsuffixRaw
  have hsuffixTokens :
      [] ++ compactAdditiveEncode suffixes ++
          (valueTokens ++ parserTokens) = tokens := by
    simp [suffixTokens, tokens]
  rw [hsuffixTokens] at hsuffixRaw
  rcases hsuffixRaw with ⟨suffixBoundary, _hsuffixLayout,
    hsuffixRows, _hsuffixSize⟩
  have hvalueRaw := compactAdditiveNatListListDirectLayout_canonical
    suffixTokens values parserTokens
  dsimp only at hvalueRaw
  have hvalueTokens :
      suffixTokens ++ compactAdditiveEncode values ++ parserTokens =
        tokens := by
    simp [valueTokens, tokens]
  rw [hvalueTokens] at hvalueRaw
  rcases hvalueRaw with ⟨valueBoundary, _hvalueLayout,
    hvalueRows, _hvalueSize⟩
  have hparserRaw := compactAdditiveStructuredListElementLayouts_canonical
    CompactUnifiedParserStateListDirectLayout
    compactUnifiedParserStateListDirectLayout_canonical
    (suffixTokens ++ valueTokens) parserTraces []
  dsimp only at hparserRaw
  have hparserTokens :
      (suffixTokens ++ valueTokens) ++
          compactAdditiveEncode parserTraces ++ [] = tokens := by
    simp [parserTokens, tokens, List.append_assoc]
  rw [hparserTokens] at hparserRaw
  have hparserRows := hparserRaw.2.1
  refine ⟨tokenTable, width, tokens.length,
    suffixBoundary, valueBoundary, ?_, ?_, ?_⟩
  · simpa only [tokenTable, width] using hsuffixRows
  · simpa only [tokenTable, width] using hvalueRows
  intro index hindex
  rcases hparserRows index hindex with
    ⟨left, _hleftBound, right, _hrightBound,
      _hleftEntry, _hrightEntry, htraceLayout⟩
  rcases htraceLayout with
    ⟨parserStateBoundary, _htraceStructure,
      hparserStateRows, _hparserStateSize⟩
  exact ⟨parserStateBoundary, by
    simpa only [tokenTable, width] using hparserStateRows⟩

/-- Canonical common table including the public count-prefixed input.  The
returned coordinates are exactly those needed by the endpoint graph. -/
theorem exists_compactSequentFormulaCanonicalEndpointLayouts
    (input : List Nat)
    (suffixes values : List (List Nat))
    (parserTraces : List CompactFormulaTokenParserDirectTrace) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ suffixBoundary valueStart valueFinish valueBoundary,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          suffixBoundary suffixes ∧
      CompactAdditiveStructuredListLayout
        tokenTable width tokenCount valueStart values.length valueFinish
          valueBoundary ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          valueBoundary values ∧
      Nat.size valueBoundary ≤ (values.length + 1) * tokenCount ∧
      (∀ index < parserTraces.length,
        ∃ parserStateBoundary,
          CompactUnifiedParserStateListRowLayouts
            tokenTable width tokenCount parserStateBoundary
              (parserTraces.getI index)) := by
  let inputTokens := compactAdditiveEncode input
  let suffixTokens := compactAdditiveEncode suffixes
  let valueTokens := compactAdditiveEncode values
  let parserTokens := compactAdditiveEncode parserTraces
  let tokens := inputTokens ++ suffixTokens ++ valueTokens ++ parserTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical
    [] input (suffixTokens ++ valueTokens ++ parserTokens)
  dsimp only at hinputRaw
  have hinputTokens :
      [] ++ compactAdditiveEncode input ++
          (suffixTokens ++ valueTokens ++ parserTokens) = tokens := by
    simp [inputTokens, tokens]
  rw [hinputTokens] at hinputRaw
  have hsuffixRaw := compactAdditiveNatListListDirectLayout_canonical
    inputTokens suffixes (valueTokens ++ parserTokens)
  dsimp only at hsuffixRaw
  have hsuffixTokens :
      inputTokens ++ compactAdditiveEncode suffixes ++
          (valueTokens ++ parserTokens) = tokens := by
    simp [suffixTokens, tokens]
  rw [hsuffixTokens] at hsuffixRaw
  rcases hsuffixRaw with
    ⟨suffixBoundary, _hsuffixStructure, hsuffixRows, _hsuffixSize⟩
  have hvalueRaw := compactAdditiveNatListListDirectLayout_canonical
    (inputTokens ++ suffixTokens) values parserTokens
  dsimp only at hvalueRaw
  have hvalueTokens :
      (inputTokens ++ suffixTokens) ++ compactAdditiveEncode values ++
          parserTokens = tokens := by
    simp [valueTokens, tokens, List.append_assoc]
  rw [hvalueTokens] at hvalueRaw
  rcases hvalueRaw with
    ⟨valueBoundary, hvalueStructure, hvalueRows, hvalueSize⟩
  have hparserRaw := compactAdditiveStructuredListElementLayouts_canonical
    CompactUnifiedParserStateListDirectLayout
    compactUnifiedParserStateListDirectLayout_canonical
    (inputTokens ++ suffixTokens ++ valueTokens) parserTraces []
  dsimp only at hparserRaw
  have hparserTokens :
      (inputTokens ++ suffixTokens ++ valueTokens) ++
          compactAdditiveEncode parserTraces ++ [] = tokens := by
    simp [parserTokens, tokens, List.append_assoc]
  rw [hparserTokens] at hparserRaw
  have hparserRows := hparserRaw.2.1
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    suffixBoundary, inputTokens.length + suffixTokens.length,
    inputTokens.length + suffixTokens.length + valueTokens.length,
    valueBoundary, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [tokenTable, width, inputTokens,
      List.length_nil, Nat.zero_add] using hinputRaw
  · simpa only [tokenTable, width] using hsuffixRows
  · simpa only [tokenTable, width, List.length_append]
      using hvalueStructure
  · simpa only [tokenTable, width] using hvalueRows
  · simpa only using hvalueSize
  · intro index hindex
    rcases hparserRows index hindex with
      ⟨left, _hleftBound, right, _hrightBound,
        _hleftEntry, _hrightEntry, htraceLayout⟩
    rcases htraceLayout with
      ⟨parserStateBoundary, _htraceStructure,
        hparserStateRows, _hparserStateSize⟩
    exact ⟨parserStateBoundary, by
      simpa only [tokenTable, width] using hparserStateRows⟩

#print axioms compactUnifiedParserStateListDirectLayout_canonical
#print axioms exists_compactSequentFormulaCanonicalSharedLayouts
#print axioms exists_compactSequentFormulaCanonicalEndpointLayouts

end FoundationCompactNumericListedDirectSequentFormulaCanonicalLayouts
