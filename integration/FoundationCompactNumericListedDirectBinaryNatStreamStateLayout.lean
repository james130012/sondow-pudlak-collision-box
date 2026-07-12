import integration.FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
import integration.FoundationCompactBinaryNatStreamMachine

/-!
# Complete direct layout of one binary-natural stream state

A state is `List Bool × (List Nat × Option (Option (List Nat)))`.  Its two
product splits, two list tableaux, and nested status layout are aligned to one
exact state interval in the common trace token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStreamStateLayout

open FoundationCompactAdditiveTokenCodec
open FoundationCompactBinaryNatStreamMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectTraceComponentTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectStructuredListCanonical
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout

def CompactBinaryNatStreamStateDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (state : BinaryNatStreamState) : Prop :=
  ∃ bitsFinish decodedFinish bitsBoundaryTable decodedBoundaryTable,
    CompactAdditiveProductSplit tokenCount start bitsFinish finish ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start state.1.length bitsFinish
      bitsBoundaryTable ∧
    CompactAdditiveProductSplit tokenCount bitsFinish decodedFinish finish ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount bitsFinish state.2.1.length decodedFinish
      decodedBoundaryTable ∧
    CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount decodedFinish finish state.2.2 ∧
    Nat.size bitsBoundaryTable ≤ (state.1.length + 1) * tokenCount ∧
    Nat.size decodedBoundaryTable ≤
      (state.2.1.length + 1) * tokenCount

theorem compactBinaryNatStreamStateDirectLayout_canonical
    (frontTokens : List Nat) (state : BinaryNatStreamState)
    (backTokens : List Nat) :
    let stateTokens := compactAdditiveEncode state
    let tokens := frontTokens ++ stateTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + stateTokens.length
    CompactBinaryNatStreamStateDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish state := by
  let bits := state.1
  let decoded := state.2.1
  let status := state.2.2
  let rest := (decoded, status)
  let stateTokens := compactAdditiveEncode state
  let tokens := frontTokens ++ stateTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let start := frontTokens.length
  let bitsFinish := start + (compactAdditiveEncode bits).length
  let decodedFinish := bitsFinish + (compactAdditiveEncode decoded).length
  let finish := start + stateTokens.length
  let afterBits := frontTokens ++ compactAdditiveEncode bits
  let afterDecoded := afterBits ++ compactAdditiveEncode decoded
  have hrestTokens : compactAdditiveEncode rest =
      compactAdditiveEncode decoded ++ compactAdditiveEncode status := by
    simp [rest]
  have hstateTokens : stateTokens =
      compactAdditiveEncode bits ++ compactAdditiveEncode decoded ++
        compactAdditiveEncode status := by
    change compactAdditiveEncode state = _
    rw [show state = (bits, rest) by rfl]
    rw [compactAdditiveEncode_prod, hrestTokens]
    simp [List.append_assoc]
  have hfinish : finish = decodedFinish +
      (compactAdditiveEncode status).length := by
    dsimp only [finish, decodedFinish, bitsFinish]
    rw [hstateTokens]
    simp only [List.length_append]
    omega
  have hcommonTokens : tokens =
      frontTokens ++ compactAdditiveEncode bits ++
        compactAdditiveEncode decoded ++ compactAdditiveEncode status ++
          backTokens := by
    rw [show tokens = frontTokens ++ stateTokens ++ backTokens by rfl]
    rw [hstateTokens]
    simp [List.append_assoc]
  have hbitsFull :
      frontTokens ++ compactAdditiveEncode bits ++
          (compactAdditiveEncode decoded ++
            compactAdditiveEncode status ++ backTokens) = tokens := by
    simpa [List.append_assoc] using hcommonTokens.symm
  have hdecodedFull :
      afterBits ++ compactAdditiveEncode decoded ++
          (compactAdditiveEncode status ++ backTokens) = tokens := by
    simpa [afterBits, List.append_assoc] using hcommonTokens.symm
  have hstatusFull :
      afterDecoded ++ compactAdditiveEncode status ++ backTokens = tokens := by
    simpa [afterDecoded, afterBits, List.append_assoc] using
      hcommonTokens.symm
  have houterFull :
      frontTokens ++ compactAdditiveEncode (bits, rest) ++ backTokens =
        tokens := by
    rw [compactAdditiveEncode_prod, hrestTokens]
    simpa [List.append_assoc] using hcommonTokens.symm
  have hinnerFull :
      afterBits ++ compactAdditiveEncode (decoded, status) ++ backTokens =
        tokens := by
    rw [compactAdditiveEncode_prod]
    simpa [afterBits, List.append_assoc] using hcommonTokens.symm
  have houterRaw := compactAdditiveProductSplit_canonical
    frontTokens bits rest backTokens
  have hinnerRaw := compactAdditiveProductSplit_canonical
    afterBits decoded status backTokens
  rcases compactAdditiveStructuredListLayout_canonical
      frontTokens bits
        (compactAdditiveEncode decoded ++
          compactAdditiveEncode status ++ backTokens) with
    ⟨bitsBoundaryTable, hbitsLayout, hbitsSize⟩
  rcases compactAdditiveStructuredListLayout_canonical
      afterBits decoded (compactAdditiveEncode status ++ backTokens) with
    ⟨decodedBoundaryTable, hdecodedLayout, hdecodedSize⟩
  have hstatusRaw := compactBinaryNatStreamStatusDirectLayout_canonical
    afterDecoded status backTokens
  dsimp only at houterRaw hinnerRaw hstatusRaw
  rw [houterFull] at houterRaw
  rw [hinnerFull] at hinnerRaw
  rw [hbitsFull] at hbitsLayout hbitsSize
  rw [hdecodedFull] at hdecodedLayout hdecodedSize
  rw [hstatusFull] at hstatusRaw
  have hafterBits : afterBits.length = bitsFinish := by
    dsimp only [afterBits, bitsFinish, start]
    simp only [List.length_append]
  have hafterDecoded : afterDecoded.length = decodedFinish := by
    dsimp only [afterDecoded, afterBits, decodedFinish, bitsFinish, start]
    simp only [List.length_append]
  have hbitsLayout' : CompactAdditiveStructuredListLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start bits.length bitsFinish
      bitsBoundaryTable := by
    have hstart : frontTokens.length = start := rfl
    simpa only [width, hstart, hafterBits] using hbitsLayout
  have hdecodedLayout' : CompactAdditiveStructuredListLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length bitsFinish decoded.length decodedFinish
      decodedBoundaryTable := by
    simpa only [width, hafterBits, hafterDecoded] using hdecodedLayout
  have hstatus' : CompactBinaryNatStreamStatusDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length decodedFinish finish status := by
    have hstatusFinish : decodedFinish +
        (compactAdditiveEncode status).length = finish := by
      exact hfinish.symm
    simpa only [width, hafterDecoded, hstatusFinish] using hstatusRaw
  have houterFinish : start + (compactAdditiveEncode bits).length +
      (compactAdditiveEncode rest).length = finish := by
    rw [hrestTokens]
    dsimp only [finish]
    rw [hstateTokens]
    simp only [List.length_append]
    omega
  have houter : CompactAdditiveProductSplit
      tokens.length start bitsFinish finish := by
    simpa only [start, bitsFinish, houterFinish] using houterRaw
  have hinnerFinish : bitsFinish +
      (compactAdditiveEncode decoded).length +
        (compactAdditiveEncode status).length = finish := by
    exact hfinish.symm
  have hinner : CompactAdditiveProductSplit
      tokens.length bitsFinish decodedFinish finish := by
    simpa only [hafterBits, hafterDecoded,
      hinnerFinish] using hinnerRaw
  have hbitsSize' : Nat.size bitsBoundaryTable ≤
      (bits.length + 1) * tokens.length := hbitsSize
  have hdecodedSize' : Nat.size decodedBoundaryTable ≤
      (decoded.length + 1) * tokens.length := hdecodedSize
  exact ⟨bitsFinish, decodedFinish, bitsBoundaryTable,
    decodedBoundaryTable, houter, hbitsLayout', hinner,
    hdecodedLayout', hstatus', hbitsSize', hdecodedSize'⟩

#print axioms compactBinaryNatStreamStateDirectLayout_canonical

end FoundationCompactNumericListedDirectBinaryNatStreamStateLayout
