import integration.FoundationCompactNumericListedDirectCanonicalFormulaTableInternalBounds
import integration.FoundationCompactNumericListedDirectWitnessBounds

/-!
# Canonical row witnesses for the formula-token tableau

Every bounded token-row existential is assigned its concrete list-derived
token, current offset, and next offset.  The theorem records both the semantic
row relations and the public size bounds needed by the quantitative compiler.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCanonicalFormulaTableRowWitnesses

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectCanonicalFormulaTableInternalBounds
open FoundationCompactNumericListedDirectWitnessBounds

/-- The three canonical row witnesses satisfy the exact handwritten row and
have sizes controlled by the same public formula code. -/
theorem compactNumericListedDirectCanonicalFormulaTable_rowWitnesses
    (formulaTokens : List Nat) (formulaCode index : Nat)
    (hcode : formulaCode = compactAdditivePackedCode formulaTokens)
    (hindex : index < formulaTokens.length) :
    let width := (compactBinaryNatPayloadBits formulaTokens).length
    let sentinel := 2 ^ width
    let tokenTable := compactFixedWidthTableCode width formulaTokens
    let offsetTable := compactFixedWidthTableCode width
      (compactBinaryNatTokenOffsets formulaTokens)
    let token := formulaTokens.getI index
    let offset := (compactBinaryNatTokenOffsets formulaTokens).getI index
    let next :=
      (compactBinaryNatTokenOffsets formulaTokens).getI (index + 1)
    token <= sentinel /\
      offset <= sentinel /\
      next <= sentinel /\
      Nat.size token <= Nat.size formulaCode /\
      Nat.size offset <= Nat.size formulaCode /\
      Nat.size next <= Nat.size formulaCode /\
      CompactFixedWidthEntry tokenTable width index token /\
      CompactFixedWidthEntry offsetTable width index offset /\
      CompactFixedWidthEntry offsetTable width (index + 1) next /\
      CompactBinaryNatTokenSegment
        (compactBinaryNatPayloadValue formulaTokens) offset token next := by
  let width := (compactBinaryNatPayloadBits formulaTokens).length
  let sentinel := 2 ^ width
  let tokenTable := compactFixedWidthTableCode width formulaTokens
  let offsets := compactBinaryNatTokenOffsets formulaTokens
  let offsetTable := compactFixedWidthTableCode width offsets
  let token := formulaTokens.getI index
  let offset := offsets.getI index
  let next := offsets.getI (index + 1)
  have hpublic :=
    compactNumericListedDirectCanonicalFormulaTable_internalBounds
      formulaTokens formulaCode hcode
  have hwidthPublic : width <= Nat.size formulaCode := by
    have hwidthSize : width + 1 = Nat.size formulaCode := hpublic.2.2.2.1
    omega
  have htokenMem : token ∈ formulaTokens := by
    dsimp only [token]
    rw [List.getI_eq_getElem _ hindex]
    exact List.getElem_mem hindex
  have hcurrentIndex : index < offsets.length := by
    dsimp only [offsets]
    rw [compactBinaryNatTokenOffsets_length]
    omega
  have hnextIndex : index + 1 < offsets.length := by
    dsimp only [offsets]
    rw [compactBinaryNatTokenOffsets_length]
    omega
  have hoffsetMem : offset ∈ offsets := by
    dsimp only [offset]
    rw [List.getI_eq_getElem _ hcurrentIndex]
    exact List.getElem_mem hcurrentIndex
  have hnextMem : next ∈ offsets := by
    dsimp only [next]
    rw [List.getI_eq_getElem _ hnextIndex]
    exact List.getElem_mem hnextIndex
  have htokenWidth : Nat.size token <= width :=
    compactBinaryNatToken_size_le_payloadLength
      formulaTokens token htokenMem
  have hoffsetWidth : offset <= width := by
    exact compactBinaryNatTokenOffsets_mem_le_payloadLength
      formulaTokens offset (by simpa only [offsets] using hoffsetMem)
  have hnextWidth : next <= width := by
    exact compactBinaryNatTokenOffsets_mem_le_payloadLength
      formulaTokens next (by simpa only [offsets] using hnextMem)
  have htokenSentinel : token <= sentinel := by
    exact Nat.le_of_lt (Nat.size_le.mp htokenWidth)
  have hoffsetSentinel : offset <= sentinel := by
    exact (hoffsetWidth.trans_lt width.lt_two_pow_self).le
  have hnextSentinel : next <= sentinel := by
    exact (hnextWidth.trans_lt width.lt_two_pow_self).le
  have htokenPublic : Nat.size token <= Nat.size formulaCode :=
    htokenWidth.trans hwidthPublic
  have hoffsetPublic : Nat.size offset <= Nat.size formulaCode :=
    (nat_size_le_self offset).trans (hoffsetWidth.trans hwidthPublic)
  have hnextPublic : Nat.size next <= Nat.size formulaCode :=
    (nat_size_le_self next).trans (hnextWidth.trans hwidthPublic)
  have htokenSizes : forall value, value ∈ formulaTokens ->
      Nat.size value <= width := by
    intro value hvalue
    exact compactBinaryNatToken_size_le_payloadLength
      formulaTokens value hvalue
  have hoffsetSizes : forall value, value ∈ offsets ->
      Nat.size value <= width := by
    intro value hvalue
    exact compactBinaryNatTokenOffsets_size_le_payloadLength
      formulaTokens value (by simpa only [offsets] using hvalue)
  have htokenEntry : CompactFixedWidthEntry tokenTable width index token := by
    exact compactFixedWidthTableCode_entry width formulaTokens index hindex
      htokenSizes
  have hoffsetEntry :
      CompactFixedWidthEntry offsetTable width index offset := by
    exact compactFixedWidthTableCode_entry width offsets index hcurrentIndex
      hoffsetSizes
  have hnextEntry :
      CompactFixedWidthEntry offsetTable width (index + 1) next := by
    exact compactFixedWidthTableCode_entry width offsets (index + 1)
      hnextIndex hoffsetSizes
  have hsegment : CompactBinaryNatTokenSegment
      (compactBinaryNatPayloadValue formulaTokens) offset token next := by
    simpa only [token, offset, next, offsets] using
      compactBinaryNatPayloadValue_segment formulaTokens index hindex
  exact ⟨htokenSentinel, hoffsetSentinel, hnextSentinel,
    htokenPublic, hoffsetPublic, hnextPublic, htokenEntry,
    hoffsetEntry, hnextEntry, hsegment⟩

#print axioms
  compactNumericListedDirectCanonicalFormulaTable_rowWitnesses

end FoundationCompactNumericListedDirectCanonicalFormulaTableRowWitnesses
