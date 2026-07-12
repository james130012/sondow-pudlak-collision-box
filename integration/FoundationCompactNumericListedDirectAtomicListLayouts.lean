import integration.FoundationCompactNumericListedDirectAdditiveTypeCanonical

/-!
# Canonical direct row layouts for atomic additive lists

A single generic construction ties every row of a structured-list boundary
table to its real typed element.  It is instantiated for Boolean bit lists and
natural-number token lists, the two atomic lists inside a stream state.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectAtomicListLayouts

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectTraceComponentTableau
open FoundationCompactNumericListedDirectTraceNatListSlices
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectStructuredListCanonical
open FoundationCompactNumericListedDirectAdditiveTypeCanonical

/-- A boundary table reads two exact cursors for every typed list element and
the supplied direct element relation holds on that interval. -/
def CompactAdditiveStructuredListElementRowLayouts
    {α : Type*} [Inhabited α]
    (ElementLayout : Nat → Nat → Nat → Nat → Nat → α → Prop)
    (tokenTable width tokenCount boundaryTable : Nat)
    (values : List α) : Prop :=
  ∀ index < values.length,
    ∃ left, left ≤ tokenCount ∧
    ∃ right, right ≤ tokenCount ∧
      CompactFixedWidthEntry boundaryTable tokenCount index left ∧
      CompactFixedWidthEntry boundaryTable tokenCount (index + 1) right ∧
      ElementLayout tokenTable width tokenCount left right
        (values.getI index)

def compactAdditiveStructuredListElementComponents
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (values : List α) : List (List Nat) :=
  values.map compactAdditiveEncode

def compactAdditiveStructuredListElementBoundaryRows
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (bodyStart : Nat) (values : List α) : List Nat :=
  compactAdditiveShiftedBoundaries bodyStart
    (compactAdditiveStructuredListElementComponents values)

def compactAdditiveStructuredListElementBoundaryTable
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (tokenCount bodyStart : Nat) (values : List α) : Nat :=
  compactFixedWidthTableCode tokenCount
    (compactAdditiveStructuredListElementBoundaryRows bodyStart values)

@[simp] theorem compactAdditiveStructuredListElementComponents_length
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    (values : List α) :
    (compactAdditiveStructuredListElementComponents values).length =
      values.length := by
  simp [compactAdditiveStructuredListElementComponents]

theorem compactAdditiveStructuredListElementComponents_getI
    {α : Type*} [Inhabited α]
    [Primcodable α] [CompactAdditiveTokenCodec α]
    (values : List α) (index : Nat) (hindex : index < values.length) :
    (compactAdditiveStructuredListElementComponents values).getI index =
      compactAdditiveEncode (values.getI index) := by
  rw [compactAdditiveStructuredListElementComponents]
  rw [List.getI_eq_getElem _ (by simpa using hindex)]
  rw [List.getI_eq_getElem _ hindex]
  simp

/-- Generic exact structured-list construction.  The element constructor is
required on arbitrary surrounding token streams, so every row can be moved
into one common public token table without an encoding conversion. -/
theorem compactAdditiveStructuredListElementLayouts_canonical
    {α : Type*} [Inhabited α]
    [Primcodable α] [CompactAdditiveTokenCodec α]
    [CompactAdditiveNonemptyCodec α]
    (ElementLayout : Nat → Nat → Nat → Nat → Nat → α → Prop)
    (elementCanonical :
      ∀ (frontTokens : List Nat) (value : α) (backTokens : List Nat),
        let elementTokens := compactAdditiveEncode value
        let tokens := frontTokens ++ elementTokens ++ backTokens
        let width := (compactBinaryNatPayloadBits tokens).length
        let start := frontTokens.length
        let finish := start + elementTokens.length
        ElementLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length start finish value)
    (frontTokens : List Nat) (values : List α) (backTokens : List Nat) :
    let listTokens := compactAdditiveEncode values
    let tokens := frontTokens ++ listTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let bodyStart := start + 1
    let finish := start + listTokens.length
    let boundaryTable :=
      compactAdditiveStructuredListElementBoundaryTable
        tokens.length bodyStart values
    CompactAdditiveStructuredListLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length start values.length finish boundaryTable ∧
      CompactAdditiveStructuredListElementRowLayouts
        ElementLayout (compactFixedWidthTableCode width tokens)
        width tokens.length boundaryTable values ∧
      Nat.size boundaryTable ≤ (values.length + 1) * tokens.length := by
  let elementComponents :=
    compactAdditiveStructuredListElementComponents values
  let listTokens := compactAdditiveEncode values
  let tokens := frontTokens ++ listTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let start := frontTokens.length
  let bodyStart := start + 1
  let finish := start + listTokens.length
  let boundaryRows :=
    compactAdditiveStructuredListElementBoundaryRows bodyStart values
  let boundaryTable :=
    compactAdditiveStructuredListElementBoundaryTable
      tokens.length bodyStart values
  have helementComponents : elementComponents =
      values.map compactAdditiveEncode := rfl
  have hlistTokens : listTokens =
      values.length :: elementComponents.flatten := by
    change compactAdditiveEncode values =
      values.length :: (values.map compactAdditiveEncode).flatten
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
    rw [hlistTokens, List.append_assoc]
    rw [List.getI_append_right frontTokens
      (values.length :: elementComponents.flatten ++ backTokens)
      frontTokens.length (by rfl)]
    simp
  have hcellRaw := compactAdditiveTokenCell_canonical
    tokens width start hstartLt hwidth
  have hcell : CompactAdditiveTokenCell
      (compactFixedWidthTableCode width tokens)
      width tokens.length start values.length bodyStart := by
    simpa [bodyStart, htokenAt] using hcellRaw
  have hcount : values.length ≤ elementComponents.flatten.length := by
    change values.length ≤
      (values.map compactAdditiveEncode).flatten.length
    exact compactAdditiveElementCount_le_flattenLength values
  have hcountBound : bodyStart + values.length ≤ tokens.length := by
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
    rw [helementComponents] at hcomponent
    rcases List.mem_map.mp hcomponent with ⟨value, _, rfl⟩
    exact compactAdditiveEncode_ne_nil value
  have hboundaries : CompactAdditiveBoundaryTable
      tokens.length values.length bodyStart finish boundaryTable := by
    rw [hfinishEq]
    simpa [boundaryTable,
      compactAdditiveStructuredListElementBoundaryTable,
      boundaryRows, compactAdditiveStructuredListElementBoundaryRows,
      elementComponents] using
      compactAdditiveShiftedBoundaryTable
        bodyStart tokens.length elementComponents
          helementsNonempty hfinishBound
  have hlayout : CompactAdditiveStructuredListLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start values.length finish boundaryTable :=
    CompactAdditiveListHeader.structuredLayout hheader hboundaries
  have hrowsBounded : ∀ cursor ∈ boundaryRows,
      cursor ≤ tokens.length := by
    simpa [boundaryRows,
      compactAdditiveStructuredListElementBoundaryRows,
      elementComponents] using
      compactAdditiveShiftedBoundaries_bounded
        bodyStart tokens.length elementComponents hfinishBound
  have hrowEntryBound : ∀ cursor ∈ boundaryRows,
      Nat.size cursor ≤ tokens.length := by
    intro cursor hcursor
    exact natSize_le_of_le (hrowsBounded cursor hcursor)
  have hrows : CompactAdditiveStructuredListElementRowLayouts
      ElementLayout (compactFixedWidthTableCode width tokens)
      width tokens.length boundaryTable values := by
    intro index hindex
    let value := values.getI index
    let componentFront := (elementComponents.take index).flatten
    let componentBack :=
      (elementComponents.drop (index + 1)).flatten
    let rowFront := frontTokens ++ [values.length] ++ componentFront
    let rowBack := componentBack ++ backTokens
    let left := boundaryRows.getI index
    let right := boundaryRows.getI (index + 1)
    have hcomponentIndex : elementComponents.getI index =
        compactAdditiveEncode value := by
      simpa [elementComponents, value] using
        compactAdditiveStructuredListElementComponents_getI
          values index hindex
    have hcomponentIndexBound : index < elementComponents.length := by
      simpa [elementComponents] using hindex
    have hsplit := List.flatten_split_at
      elementComponents index hcomponentIndexBound
    have hrowTokens :
        rowFront ++ compactAdditiveEncode value ++ rowBack = tokens := by
      rw [show tokens = frontTokens ++ listTokens ++ backTokens by rfl]
      rw [hlistTokens]
      rw [hsplit, hcomponentIndex]
      simp [rowFront, rowBack, componentFront, componentBack,
        List.append_assoc]
    have hcomponentBoundary :
        (compactAdditiveComponentBoundaries elementComponents).getI index =
          componentFront.length := by
      simpa [componentFront] using
        compactAdditiveComponentBoundaries_getI_eq_take
          elementComponents index (Nat.le_of_lt hcomponentIndexBound)
    have hrowFrontLength : rowFront.length =
        bodyStart + componentFront.length := by
      dsimp only [rowFront, bodyStart, start]
      simp only [List.length_append, List.length_singleton]
    have hleft : left = rowFront.length := by
      have hindexBoundary : index <
          (compactAdditiveComponentBoundaries elementComponents).length := by
        simp only [compactAdditiveComponentBoundaries_length]
        omega
      rw [show left = boundaryRows.getI index by rfl]
      rw [show boundaryRows = compactAdditiveShiftedBoundaries
          bodyStart elementComponents by
        rfl]
      rw [compactAdditiveShiftedBoundaries_getI
        bodyStart elementComponents index hindexBoundary]
      rw [hcomponentBoundary]
      exact hrowFrontLength.symm
    have hnextBoundary := compactAdditiveComponentBoundaries_getI_next
      elementComponents index hcomponentIndexBound
    have hright : right = rowFront.length +
        (compactAdditiveEncode value).length := by
      rw [show right = boundaryRows.getI (index + 1) by rfl]
      rw [show boundaryRows = compactAdditiveShiftedBoundaries
          bodyStart elementComponents by
        rfl]
      rw [compactAdditiveShiftedBoundaries_getI
        bodyStart elementComponents (index + 1) (by
          simp only [compactAdditiveComponentBoundaries_length]
          omega)]
      rw [hnextBoundary, hcomponentIndex, hcomponentBoundary]
      rw [hrowFrontLength]
      omega
    have hleftIndex : index < boundaryRows.length := by
      dsimp only [boundaryRows,
        compactAdditiveStructuredListElementBoundaryRows]
      simp only [compactAdditiveShiftedBoundaries_length,
        compactAdditiveStructuredListElementComponents_length]
      omega
    have hrightIndex : index + 1 < boundaryRows.length := by
      dsimp only [boundaryRows,
        compactAdditiveStructuredListElementBoundaryRows]
      simp only [compactAdditiveShiftedBoundaries_length,
        compactAdditiveStructuredListElementComponents_length]
      omega
    have hleftBound : left ≤ tokens.length := by
      apply hrowsBounded
      rw [show left = boundaryRows.getI index by rfl]
      rw [List.getI_eq_getElem _ hleftIndex]
      exact List.getElem_mem hleftIndex
    have hrightBound : right ≤ tokens.length := by
      apply hrowsBounded
      rw [show right = boundaryRows.getI (index + 1) by rfl]
      rw [List.getI_eq_getElem _ hrightIndex]
      exact List.getElem_mem hrightIndex
    have hleftEntry : CompactFixedWidthEntry
        boundaryTable tokens.length index left := by
      simpa [boundaryTable,
        compactAdditiveStructuredListElementBoundaryTable,
        boundaryRows] using
        compactFixedWidthTableCode_entry tokens.length boundaryRows index
          hleftIndex hrowEntryBound
    have hrightEntry : CompactFixedWidthEntry
        boundaryTable tokens.length (index + 1) right := by
      simpa [boundaryTable,
        compactAdditiveStructuredListElementBoundaryTable,
        boundaryRows] using
        compactFixedWidthTableCode_entry tokens.length boundaryRows
          (index + 1) hrightIndex hrowEntryBound
    have helementRaw := elementCanonical rowFront value rowBack
    dsimp only at helementRaw
    rw [hrowTokens] at helementRaw
    have helementLayout : ElementLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length left right value := by
      simpa only [width, hleft, hright] using helementRaw
    exact ⟨left, hleftBound, right, hrightBound,
      hleftEntry, hrightEntry, helementLayout⟩
  have htableSize : Nat.size boundaryTable ≤
      (values.length + 1) * tokens.length := by
    simpa [boundaryTable,
      compactAdditiveStructuredListElementBoundaryTable,
      boundaryRows, compactAdditiveStructuredListElementBoundaryRows,
      elementComponents] using
      compactAdditiveShiftedBoundaryTable_size_le
        bodyStart tokens.length elementComponents
  exact ⟨hlayout, hrows, htableSize⟩

def CompactAdditiveBoolValueDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (value : Bool) : Prop :=
  CompactAdditiveBoolSlice tokenTable width tokenCount start
    (compactAdditiveBoolTag value) finish

theorem compactAdditiveBoolValueDirectLayout_canonical
    (frontTokens : List Nat) (value : Bool) (backTokens : List Nat) :
    let elementTokens := compactAdditiveEncode value
    let tokens := frontTokens ++ elementTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + elementTokens.length
    CompactAdditiveBoolValueDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish value := by
  have hcanonical := compactAdditiveBoolSlice_canonical
    frontTokens value backTokens
  dsimp only at hcanonical ⊢
  simpa [CompactAdditiveBoolValueDirectLayout] using hcanonical

def CompactAdditiveNatValueDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (value : Nat) : Prop :=
  CompactAdditiveTokenCell
    tokenTable width tokenCount start value finish

theorem compactAdditiveNatValueDirectLayout_canonical
    (frontTokens : List Nat) (value : Nat) (backTokens : List Nat) :
    let elementTokens := compactAdditiveEncode value
    let tokens := frontTokens ++ elementTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + elementTokens.length
    CompactAdditiveNatValueDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish value := by
  let elementTokens := compactAdditiveEncode value
  let tokens := frontTokens ++ elementTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let start := frontTokens.length
  let finish := start + elementTokens.length
  have helementTokens : elementTokens = [value] := by simp [elementTokens]
  have hwidth : ∀ token ∈ tokens, Nat.size token ≤ width := by
    intro token htoken
    exact compactBinaryNatToken_size_le_payloadLength tokens token htoken
  have hstartLt : start < tokens.length := by
    rw [show tokens = frontTokens ++ elementTokens ++ backTokens by rfl]
    rw [helementTokens]
    simp [start]
  have htokenAt : tokens.getI start = value := by
    rw [show tokens = frontTokens ++ elementTokens ++ backTokens by rfl]
    rw [helementTokens, List.append_assoc]
    rw [List.getI_append_right frontTokens ([value] ++ backTokens)
      frontTokens.length (by rfl)]
    simp
  have hcellRaw := compactAdditiveTokenCell_canonical
    tokens width start hstartLt hwidth
  have hcell : CompactAdditiveTokenCell
      (compactFixedWidthTableCode width tokens)
      width tokens.length start value (start + 1) := by
    simpa only [htokenAt] using hcellRaw
  have hfinish : finish = start + 1 := by
    simp [finish, helementTokens]
  change CompactAdditiveTokenCell
    (compactFixedWidthTableCode width tokens)
    width tokens.length start value finish
  rw [hfinish]
  exact hcell

theorem compactAdditiveBoolListElementLayouts_canonical
    (frontTokens : List Nat) (values : List Bool) (backTokens : List Nat) :
    let listTokens := compactAdditiveEncode values
    let tokens := frontTokens ++ listTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let bodyStart := start + 1
    let finish := start + listTokens.length
    let boundaryTable :=
      compactAdditiveStructuredListElementBoundaryTable
        tokens.length bodyStart values
    CompactAdditiveStructuredListLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length start values.length finish boundaryTable ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveBoolValueDirectLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length boundaryTable values ∧
      Nat.size boundaryTable ≤ (values.length + 1) * tokens.length := by
  exact compactAdditiveStructuredListElementLayouts_canonical
    CompactAdditiveBoolValueDirectLayout
    compactAdditiveBoolValueDirectLayout_canonical
    frontTokens values backTokens

theorem compactAdditiveNatListElementLayouts_canonical
    (frontTokens : List Nat) (values : List Nat) (backTokens : List Nat) :
    let listTokens := compactAdditiveEncode values
    let tokens := frontTokens ++ listTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let bodyStart := start + 1
    let finish := start + listTokens.length
    let boundaryTable :=
      compactAdditiveStructuredListElementBoundaryTable
        tokens.length bodyStart values
    CompactAdditiveStructuredListLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length start values.length finish boundaryTable ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatValueDirectLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length boundaryTable values ∧
      Nat.size boundaryTable ≤ (values.length + 1) * tokens.length := by
  exact compactAdditiveStructuredListElementLayouts_canonical
    CompactAdditiveNatValueDirectLayout
    compactAdditiveNatValueDirectLayout_canonical
    frontTokens values backTokens

#print axioms compactAdditiveStructuredListElementComponents_getI
#print axioms compactAdditiveStructuredListElementLayouts_canonical
#print axioms compactAdditiveBoolValueDirectLayout_canonical
#print axioms compactAdditiveNatValueDirectLayout_canonical
#print axioms compactAdditiveBoolListElementLayouts_canonical
#print axioms compactAdditiveNatListElementLayouts_canonical

end FoundationCompactNumericListedDirectAtomicListLayouts
