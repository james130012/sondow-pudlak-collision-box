import integration.FoundationCompactNumericListedDirectTracePackedStreamSplits

/-!
# Canonical direct tableaux for structured additive lists

Every concrete additive list begins with its count token and then concatenates
nonempty element encodings.  This module constructs the shifted element
boundary table and proves an explicit polynomial table-size bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectStructuredListCanonical

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectTraceComponentTableau
open FoundationCompactNumericListedDirectTraceNatListSlices
open FoundationCompactNumericListedDirectAdditiveTypeLayouts

def compactAdditiveShiftedBoundaries
    (base : Nat) (components : List (List Nat)) : List Nat :=
  (compactAdditiveComponentBoundaries components).map
    (fun cursor => base + cursor)

@[simp] theorem compactAdditiveShiftedBoundaries_length
    (base : Nat) (components : List (List Nat)) :
    (compactAdditiveShiftedBoundaries base components).length =
      components.length + 1 := by
  simp [compactAdditiveShiftedBoundaries]

theorem compactAdditiveShiftedBoundaries_getI
    (base : Nat) (components : List (List Nat)) (index : Nat)
    (hindex : index < (compactAdditiveComponentBoundaries components).length) :
    (compactAdditiveShiftedBoundaries base components).getI index =
      base + (compactAdditiveComponentBoundaries components).getI index := by
  rw [compactAdditiveShiftedBoundaries]
  rw [List.getI_eq_getElem _ (by simpa using hindex)]
  rw [List.getI_eq_getElem _ hindex]
  simp

@[simp] theorem compactAdditiveShiftedBoundaries_getI_zero
    (base : Nat) (components : List (List Nat)) :
    (compactAdditiveShiftedBoundaries base components).getI 0 = base := by
  rw [compactAdditiveShiftedBoundaries_getI base components 0 (by simp)]
  simp

theorem compactAdditiveShiftedBoundaries_final
    (base : Nat) (components : List (List Nat)) :
    (compactAdditiveShiftedBoundaries base components).getI
        components.length =
      base + components.flatten.length := by
  rw [compactAdditiveShiftedBoundaries_getI
    base components components.length (by simp)]
  rw [compactAdditiveComponentBoundaries_final]

theorem compactAdditiveShiftedBoundaries_strict
    (base : Nat) (components : List (List Nat))
    (hne : ∀ component ∈ components, component ≠ [])
    (index : Nat) (hindex : index < components.length) :
    (compactAdditiveShiftedBoundaries base components).getI index <
      (compactAdditiveShiftedBoundaries base components).getI (index + 1) := by
  rw [compactAdditiveShiftedBoundaries_getI
    base components index (by simp; omega)]
  rw [compactAdditiveShiftedBoundaries_getI
    base components (index + 1) (by simp; omega)]
  exact Nat.add_lt_add_left
    (compactAdditiveComponentBoundaries_strict
      components hne index hindex) base

theorem compactAdditiveShiftedBoundaries_bounded
    (base tokenCount : Nat) (components : List (List Nat))
    (hfinish : base + components.flatten.length ≤ tokenCount) :
    ∀ cursor ∈ compactAdditiveShiftedBoundaries base components,
      cursor ≤ tokenCount := by
  intro cursor hcursor
  rcases List.mem_map.mp hcursor with
    ⟨rawCursor, hrawCursor, rfl⟩
  have hrawBound := compactAdditiveComponentBoundaries_bounded
    components rawCursor hrawCursor
  omega

theorem compactAdditiveShiftedBoundaryTable
    (base tokenCount : Nat) (components : List (List Nat))
    (hne : ∀ component ∈ components, component ≠ [])
    (hfinish : base + components.flatten.length ≤ tokenCount) :
    CompactAdditiveBoundaryTable tokenCount components.length base
      (base + components.flatten.length)
      (compactFixedWidthTableCode tokenCount
        (compactAdditiveShiftedBoundaries base components)) := by
  apply compactAdditiveBoundaryTable_of_rows
  · simp
  · exact compactAdditiveShiftedBoundaries_getI_zero base components
  · exact compactAdditiveShiftedBoundaries_final base components
  · exact compactAdditiveShiftedBoundaries_bounded
      base tokenCount components hfinish
  · exact compactAdditiveShiftedBoundaries_strict base components hne

theorem compactAdditiveShiftedBoundaryTable_size_le
    (base tokenCount : Nat) (components : List (List Nat)) :
    Nat.size (compactFixedWidthTableCode tokenCount
        (compactAdditiveShiftedBoundaries base components)) ≤
      (components.length + 1) * tokenCount := by
  simpa using compactFixedWidthTableCode_size_le tokenCount
    (compactAdditiveShiftedBoundaries base components)

theorem compactAdditiveElementComponents_flatten
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (values : List α) :
    (values.map compactAdditiveEncode).flatten =
      values.flatMap compactAdditiveEncode := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [ih]

theorem compactAdditiveListEncode_eq_header_components
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (values : List α) :
    compactAdditiveEncode values =
      values.length :: (values.map compactAdditiveEncode).flatten := by
  rw [compactAdditiveEncode_list]
  rw [compactAdditiveElementComponents_flatten]

theorem compactAdditiveElementCount_le_flattenLength
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    [CompactAdditiveNonemptyCodec α] (values : List α) :
    values.length ≤ (values.map compactAdditiveEncode).flatten.length := by
  induction values with
  | nil => simp
  | cons value values ih =>
      have hvalue : 0 < (compactAdditiveEncode value).length :=
        List.length_pos_iff.mpr (compactAdditiveEncode_ne_nil value)
      simp only [List.length_cons, List.map_cons, List.flatten_cons,
        List.length_append]
      omega

/-- A structured list embedded between arbitrary front and back token streams
has a canonical direct layout and a polynomial-size element-boundary table. -/
theorem compactAdditiveStructuredListLayout_canonical
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    [CompactAdditiveNonemptyCodec α]
    (frontTokens : List Nat) (values : List α) (backTokens : List Nat) :
    let listTokens := compactAdditiveEncode values
    let tokens := frontTokens ++ listTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + listTokens.length
    ∃ elementBoundaryTable,
      CompactAdditiveStructuredListLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length start values.length finish
        elementBoundaryTable ∧
      Nat.size elementBoundaryTable ≤
        (values.length + 1) * tokens.length := by
  let elementComponents := values.map compactAdditiveEncode
  let listTokens := compactAdditiveEncode values
  let tokens := frontTokens ++ listTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let start := frontTokens.length
  let bodyStart := start + 1
  let finish := start + listTokens.length
  let elementBoundaryTable := compactFixedWidthTableCode tokens.length
    (compactAdditiveShiftedBoundaries bodyStart elementComponents)
  have hlistTokens : listTokens =
      values.length :: elementComponents.flatten := by
    exact compactAdditiveListEncode_eq_header_components values
  have hwidth : ∀ token ∈ tokens, Nat.size token ≤ width := by
    intro token htoken
    exact compactBinaryNatToken_size_le_payloadLength tokens token htoken
  have hstartLt : start < tokens.length := by
    rw [show tokens = frontTokens ++ listTokens ++ backTokens by rfl]
    rw [hlistTokens]
    simp [start]
  have htokenAt : tokens.getI start = values.length := by
    rw [show tokens = frontTokens ++ listTokens ++ backTokens by rfl]
    rw [hlistTokens]
    rw [List.append_assoc]
    rw [List.getI_append_right
      frontTokens (values.length :: elementComponents.flatten ++ backTokens)
      frontTokens.length (by rfl)]
    simp
  have hcellRaw := compactAdditiveTokenCell_canonical
    tokens width start hstartLt hwidth
  have hcell : CompactAdditiveTokenCell
      (compactFixedWidthTableCode width tokens)
      width tokens.length start values.length bodyStart := by
    simpa [bodyStart, htokenAt] using hcellRaw
  have hcountBound : bodyStart + values.length ≤ tokens.length := by
    have hcount : values.length ≤ elementComponents.flatten.length := by
      simpa [elementComponents] using
        compactAdditiveElementCount_le_flattenLength values
    rw [show tokens = frontTokens ++ listTokens ++ backTokens by rfl]
    rw [hlistTokens]
    simp only [List.length_append, List.length_cons]
    dsimp only [bodyStart, start]
    omega
  have hheader : CompactAdditiveListHeader
      (compactFixedWidthTableCode width tokens)
      width tokens.length start values.length bodyStart :=
    ⟨hcell, hcountBound⟩
  have hfinishEq : finish =
      bodyStart + elementComponents.flatten.length := by
    dsimp only [finish]
    rw [hlistTokens]
    simp [bodyStart, start]
    omega
  have hfinishBound :
      bodyStart + elementComponents.flatten.length ≤ tokens.length := by
    rw [← hfinishEq]
    rw [show tokens = frontTokens ++ listTokens ++ backTokens by rfl]
    simp [finish, start]
  have helementsNonempty :
      ∀ component ∈ elementComponents, component ≠ [] := by
    intro component hcomponent
    rcases List.mem_map.mp hcomponent with ⟨value, _, rfl⟩
    exact compactAdditiveEncode_ne_nil value
  have hboundaries : CompactAdditiveBoundaryTable
      tokens.length values.length bodyStart finish
      elementBoundaryTable := by
    rw [hfinishEq]
    simpa [elementComponents, elementBoundaryTable] using
      compactAdditiveShiftedBoundaryTable
        bodyStart tokens.length elementComponents
          helementsNonempty hfinishBound
  refine ⟨elementBoundaryTable,
    FoundationCompactNumericListedDirectAdditiveTypeLayouts.CompactAdditiveListHeader.structuredLayout
      hheader hboundaries, ?_⟩
  change Nat.size elementBoundaryTable ≤
    (values.length + 1) * tokens.length
  simpa [elementBoundaryTable, elementComponents] using
    compactAdditiveShiftedBoundaryTable_size_le
      bodyStart tokens.length elementComponents

#print axioms compactAdditiveShiftedBoundaries_getI
#print axioms compactAdditiveShiftedBoundaries_strict
#print axioms compactAdditiveShiftedBoundaries_bounded
#print axioms compactAdditiveShiftedBoundaryTable
#print axioms compactAdditiveShiftedBoundaryTable_size_le
#print axioms compactAdditiveListEncode_eq_header_components
#print axioms compactAdditiveElementCount_le_flattenLength
#print axioms compactAdditiveStructuredListLayout_canonical

end FoundationCompactNumericListedDirectStructuredListCanonical
