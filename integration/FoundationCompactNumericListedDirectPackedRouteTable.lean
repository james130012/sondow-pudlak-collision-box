import integration.FoundationCompactNumericListedDirectNatListWitnessRows
import integration.FoundationCompactNumericListedDirectFormulaTransformStateLayout
import integration.FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute

/-!
# Canonical shared table for direct route witnesses

A route may place many natural-number lists and formula-transform state lists
in one fixed-width token table.  These lemmas recover the canonical slot and
row layouts for any selected chunk without rebuilding prefix arithmetic in
every route constructor.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectPackedRouteTable

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

def compactPackedChunkPrefix (chunks : List (List Nat)) (index : Nat) :
    List Nat :=
  (chunks.take index).flatten

def compactPackedChunkSuffix (chunks : List (List Nat)) (index : Nat) :
    List Nat :=
  (chunks.drop (index + 1)).flatten

theorem compactPackedChunkPrefix_append_getElem_append_suffix
    (chunks : List (List Nat)) (index : Nat)
    (hindex : index < chunks.length) :
    compactPackedChunkPrefix chunks index ++ chunks[index] ++
        compactPackedChunkSuffix chunks index = chunks.flatten := by
  have hsplit : chunks.take index ++ [chunks[index]] ++
      chunks.drop (index + 1) = chunks := by
    calc
      chunks.take index ++ [chunks[index]] ++ chunks.drop (index + 1) =
          chunks.take (index + 1) ++ chunks.drop (index + 1) := by
            rw [List.take_append_getElem hindex]
      _ = chunks := List.take_append_drop (index + 1) chunks
  have hflatten := congrArg List.flatten hsplit
  simpa only [compactPackedChunkPrefix, compactPackedChunkSuffix,
    List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc] using hflatten

def compactPackedNatListSlot
    (chunks : List (List Nat)) (index : Nat) (values : List Nat) :
    CompactNatListRowSlot :=
  let tokens := chunks.flatten
  let start := (compactPackedChunkPrefix chunks index).length
  let finish := start + (compactAdditiveEncode values).length
  let boundary := compactAdditiveStructuredListElementBoundaryTable
    tokens.length (start + 1) values
  { start := start
    finish := finish
    boundary := boundary
    count := values.length
    boundarySize := Nat.size boundary }

def CompactPackedNatListSlotCanonical
    (tokenTable width tokenCount : Nat)
    (slot : CompactNatListRowSlot) (values : List Nat) : Prop :=
  slot.count = values.length /\
    CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      slot.start slot.count slot.finish slot.boundary slot.boundarySize /\
    CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      slot.start slot.finish values /\
    CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        slot.boundary values

theorem CompactPackedNatListSlotCanonical.rows
    {tokenTable width tokenCount : Nat}
    {slot : CompactNatListRowSlot} {values : List Nat}
    (hslot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount slot values) :
    CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      slot.start values.length slot.finish slot.boundary slot.boundarySize := by
  simpa only [hslot.1] using hslot.2.1

theorem CompactPackedNatListSlotCanonical.layout
    {tokenTable width tokenCount : Nat}
    {slot : CompactNatListRowSlot} {values : List Nat}
    (hslot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount slot values) :
    CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      slot.start slot.finish values :=
  hslot.2.2.1

theorem CompactPackedNatListSlotCanonical.elements
    {tokenTable width tokenCount : Nat}
    {slot : CompactNatListRowSlot} {values : List Nat}
    (hslot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount slot values) :
    CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        slot.boundary values :=
  hslot.2.2.2

theorem compactPackedNatListSlot_canonical
    (chunks : List (List Nat)) (index : Nat) (values : List Nat)
    (hindex : index < chunks.length)
    (hchunk : chunks[index] = compactAdditiveEncode values) :
    let tokens := chunks.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    let slot := compactPackedNatListSlot chunks index values
    CompactPackedNatListSlotCanonical
      tokenTable width tokens.length slot values := by
  let front := compactPackedChunkPrefix chunks index
  let back := compactPackedChunkSuffix chunks index
  have htokens : front ++ compactAdditiveEncode values ++ back =
      chunks.flatten := by
    rw [← hchunk]
    exact compactPackedChunkPrefix_append_getElem_append_suffix
      chunks index hindex
  have hraw := compactAdditiveNatListElementLayouts_canonical
    front values back
  dsimp only at hraw
  rw [htokens] at hraw
  rcases hraw with ⟨hstructure, helements, hsize⟩
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  let slot := compactPackedNatListSlot chunks index values
  have hstructure' : CompactAdditiveStructuredListLayout
      tokenTable width tokens.length slot.start values.length slot.finish
        slot.boundary := by
    simpa [tokenTable, width, tokens, slot, compactPackedNatListSlot,
      front] using hstructure
  have helements' : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokens.length
        slot.boundary values := by
    simpa [tokenTable, width, tokens, slot, compactPackedNatListSlot,
      front] using helements
  have hsize' : Nat.size slot.boundary <=
      (values.length + 1) * tokens.length := by
    simpa [tokens, slot, compactPackedNatListSlot, front] using hsize
  have hwitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length slot.start slot.count slot.finish
        slot.boundary slot.boundarySize := by
    refine ⟨?_, ?_, rfl, ?_⟩
    · simpa [slot, compactPackedNatListSlot] using hstructure'
    · exact
        FoundationCompactNumericListedDirectNatListBoundaryRigidity.CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
          helements'
    · simpa [slot, compactPackedNatListSlot] using hsize'
  have hlayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length slot.start slot.finish values := by
    exact ⟨slot.boundary, hstructure', helements', hsize'⟩
  exact ⟨rfl, hwitness, hlayout, helements'⟩

def compactPackedFormulaTransformStateBoundary
    (chunks : List (List Nat)) (index : Nat)
    (states : List CompactFormulaTransformState) : Nat :=
  let tokens := chunks.flatten
  let start := (compactPackedChunkPrefix chunks index).length
  compactFormulaTransformStateBoundaryTable
    tokens.length (start + 1) states

theorem compactPackedFormulaTransformStateRows_canonical
    (chunks : List (List Nat)) (index : Nat)
    (states : List CompactFormulaTransformState)
    (hindex : index < chunks.length)
    (hchunk : chunks[index] = compactAdditiveEncode states) :
    let tokens := chunks.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    let boundary := compactPackedFormulaTransformStateBoundary
      chunks index states
    CompactFormulaTransformStateListRowLayouts
      tokenTable width tokens.length boundary states := by
  let front := compactPackedChunkPrefix chunks index
  let back := compactPackedChunkSuffix chunks index
  have htokens : front ++ compactAdditiveEncode states ++ back =
      chunks.flatten := by
    rw [← hchunk]
    exact compactPackedChunkPrefix_append_getElem_append_suffix
      chunks index hindex
  have hraw := compactFormulaTransformStateListDirectLayout_canonical
    front states back
  dsimp only at hraw
  rw [htokens] at hraw
  exact hraw.2.1

theorem compactPackedFormulaTransformStateRows_canonical_with_size
    (chunks : List (List Nat)) (index : Nat)
    (states : List CompactFormulaTransformState)
    (hindex : index < chunks.length)
    (hchunk : chunks[index] = compactAdditiveEncode states) :
    let tokens := chunks.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    let boundary := compactPackedFormulaTransformStateBoundary
      chunks index states
    CompactFormulaTransformStateListRowLayouts
        tokenTable width tokens.length boundary states ∧
      Nat.size boundary ≤ (states.length + 1) * tokens.length := by
  let front := compactPackedChunkPrefix chunks index
  let back := compactPackedChunkSuffix chunks index
  have htokens : front ++ compactAdditiveEncode states ++ back =
      chunks.flatten := by
    rw [← hchunk]
    exact compactPackedChunkPrefix_append_getElem_append_suffix
      chunks index hindex
  have hraw := compactFormulaTransformStateListDirectLayout_canonical
    front states back
  dsimp only at hraw
  rw [htokens] at hraw
  exact hraw.2

theorem compactPackedNatListListLayout_canonical
    (chunks : List (List Nat)) (index : Nat)
    (values : List (List Nat))
    (hindex : index < chunks.length)
    (hchunk : chunks[index] = compactAdditiveEncode values) :
    let tokens := chunks.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    let start := (compactPackedChunkPrefix chunks index).length
    let finish := start + (compactAdditiveEncode values).length
    CompactAdditiveNatListListDirectLayout
      tokenTable width tokens.length start finish values := by
  let front := compactPackedChunkPrefix chunks index
  let back := compactPackedChunkSuffix chunks index
  have htokens : front ++ compactAdditiveEncode values ++ back =
      chunks.flatten := by
    rw [← hchunk]
    exact compactPackedChunkPrefix_append_getElem_append_suffix
      chunks index hindex
  have hraw := compactAdditiveNatListListDirectLayout_canonical
    front values back
  dsimp only at hraw
  rw [htokens] at hraw
  simpa [front] using hraw

#print axioms compactPackedChunkPrefix_append_getElem_append_suffix
#print axioms compactPackedNatListSlot_canonical
#print axioms compactPackedFormulaTransformStateRows_canonical
#print axioms compactPackedFormulaTransformStateRows_canonical_with_size
#print axioms compactPackedNatListListLayout_canonical

end FoundationCompactNumericListedDirectPackedRouteTable
