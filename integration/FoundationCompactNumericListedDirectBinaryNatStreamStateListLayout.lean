import integration.FoundationCompactNumericListedDirectBinaryNatStreamStateLayout

/-!
# Direct row layouts for lists of binary-natural stream states

The structured-list boundary table is strengthened row by row: its entries at
`i` and `i + 1` delimit the actual additive encoding of `states.getI i`, and
that exact interval carries the complete direct state layout.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStreamStateListLayout

open FoundationCompactAdditiveTokenCodec
open FoundationCompactBinaryNatStreamMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectTraceComponentTableau
open FoundationCompactNumericListedDirectTraceNatListSlices
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectStructuredListCanonical
open FoundationCompactNumericListedDirectBinaryNatStreamStateLayout

/-- Every row of a state-list boundary table is tied to the corresponding
typed state and carries that state's complete direct layout. -/
def CompactBinaryNatStreamStateListRowLayouts
    (tokenTable width tokenCount boundaryTable : Nat)
    (states : List BinaryNatStreamState) : Prop :=
  ∀ index < states.length,
    ∃ left, left ≤ tokenCount ∧
    ∃ right, right ≤ tokenCount ∧
      CompactFixedWidthEntry boundaryTable tokenCount index left ∧
      CompactFixedWidthEntry boundaryTable tokenCount (index + 1) right ∧
      CompactBinaryNatStreamStateDirectLayout
        tokenTable width tokenCount left right (states.getI index)

def compactBinaryNatStreamStateElementComponents
    (states : List BinaryNatStreamState) : List (List Nat) :=
  states.map compactAdditiveEncode

def compactBinaryNatStreamStateBoundaryRows
    (bodyStart : Nat) (states : List BinaryNatStreamState) : List Nat :=
  compactAdditiveShiftedBoundaries bodyStart
    (compactBinaryNatStreamStateElementComponents states)

def compactBinaryNatStreamStateBoundaryTable
    (tokenCount bodyStart : Nat) (states : List BinaryNatStreamState) : Nat :=
  compactFixedWidthTableCode tokenCount
    (compactBinaryNatStreamStateBoundaryRows bodyStart states)

@[simp] theorem compactBinaryNatStreamStateElementComponents_length
    (states : List BinaryNatStreamState) :
    (compactBinaryNatStreamStateElementComponents states).length =
      states.length := by
  simp [compactBinaryNatStreamStateElementComponents]

theorem compactBinaryNatStreamStateElementComponents_getI
    (states : List BinaryNatStreamState) (index : Nat)
    (hindex : index < states.length) :
    (compactBinaryNatStreamStateElementComponents states).getI index =
      compactAdditiveEncode (states.getI index) := by
  rw [compactBinaryNatStreamStateElementComponents]
  rw [List.getI_eq_getElem _ (by simpa using hindex)]
  rw [List.getI_eq_getElem _ hindex]
  simp

/-- A real additive encoding of a state list has one canonical boundary table
that simultaneously satisfies the structured-list formula and all exact row
state layouts. -/
theorem compactBinaryNatStreamStateListDirectLayout_canonical
    (frontTokens : List Nat) (states : List BinaryNatStreamState)
    (backTokens : List Nat) :
    let listTokens := compactAdditiveEncode states
    let tokens := frontTokens ++ listTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let bodyStart := start + 1
    let finish := start + listTokens.length
    let boundaryTable :=
      compactBinaryNatStreamStateBoundaryTable
        tokens.length bodyStart states
    CompactAdditiveStructuredListLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length start states.length finish boundaryTable ∧
      CompactBinaryNatStreamStateListRowLayouts
        (compactFixedWidthTableCode width tokens)
        width tokens.length boundaryTable states ∧
      Nat.size boundaryTable ≤ (states.length + 1) * tokens.length := by
  let elementComponents :=
    compactBinaryNatStreamStateElementComponents states
  let listTokens := compactAdditiveEncode states
  let tokens := frontTokens ++ listTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let start := frontTokens.length
  let bodyStart := start + 1
  let finish := start + listTokens.length
  let boundaryRows :=
    compactBinaryNatStreamStateBoundaryRows bodyStart states
  let boundaryTable :=
    compactBinaryNatStreamStateBoundaryTable
      tokens.length bodyStart states
  have helementComponents : elementComponents =
      states.map compactAdditiveEncode := rfl
  have hlistTokens : listTokens =
      states.length :: elementComponents.flatten := by
    change compactAdditiveEncode states =
      states.length :: (states.map compactAdditiveEncode).flatten
    exact compactAdditiveListEncode_eq_header_components states
  have hwidth : ∀ token ∈ tokens, Nat.size token ≤ width := by
    intro token htoken
    exact compactBinaryNatToken_size_le_payloadLength tokens token htoken
  have hstartLt : start < tokens.length := by
    rw [show tokens = frontTokens ++ listTokens ++ backTokens by rfl]
    rw [hlistTokens]
    simp [start]
  have htokenAt : tokens.getI start = states.length := by
    rw [show tokens = frontTokens ++ listTokens ++ backTokens by rfl]
    rw [hlistTokens, List.append_assoc]
    rw [List.getI_append_right frontTokens
      (states.length :: elementComponents.flatten ++ backTokens)
      frontTokens.length (by rfl)]
    simp
  have hcellRaw := compactAdditiveTokenCell_canonical
    tokens width start hstartLt hwidth
  have hcell : CompactAdditiveTokenCell
      (compactFixedWidthTableCode width tokens)
      width tokens.length start states.length bodyStart := by
    simpa [bodyStart, htokenAt] using hcellRaw
  have hcount : states.length ≤ elementComponents.flatten.length := by
    change states.length ≤
      (states.map compactAdditiveEncode).flatten.length
    exact compactAdditiveElementCount_le_flattenLength states
  have hcountBound : bodyStart + states.length ≤ tokens.length := by
    rw [show tokens = frontTokens ++ listTokens ++ backTokens by rfl]
    rw [hlistTokens]
    simp only [List.length_append, List.length_cons]
    dsimp only [bodyStart, start]
    omega
  have hheader : CompactAdditiveListHeader
      (compactFixedWidthTableCode width tokens)
      width tokens.length start states.length bodyStart :=
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
    rcases List.mem_map.mp hcomponent with ⟨state, _, rfl⟩
    exact compactAdditiveEncode_ne_nil state
  have hboundaries : CompactAdditiveBoundaryTable
      tokens.length states.length bodyStart finish boundaryTable := by
    rw [hfinishEq]
    simpa [boundaryTable, compactBinaryNatStreamStateBoundaryTable,
      boundaryRows, compactBinaryNatStreamStateBoundaryRows,
      elementComponents] using
      compactAdditiveShiftedBoundaryTable
        bodyStart tokens.length elementComponents
          helementsNonempty hfinishBound
  have hlayout : CompactAdditiveStructuredListLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start states.length finish boundaryTable :=
    FoundationCompactNumericListedDirectAdditiveTypeLayouts.CompactAdditiveListHeader.structuredLayout
      hheader hboundaries
  have hrowsBounded : ∀ cursor ∈ boundaryRows,
      cursor ≤ tokens.length := by
    simpa [boundaryRows, compactBinaryNatStreamStateBoundaryRows,
      elementComponents] using
      compactAdditiveShiftedBoundaries_bounded
        bodyStart tokens.length elementComponents hfinishBound
  have hrowEntryBound : ∀ cursor ∈ boundaryRows,
      Nat.size cursor ≤ tokens.length := by
    intro cursor hcursor
    exact natSize_le_of_le (hrowsBounded cursor hcursor)
  have hrows : CompactBinaryNatStreamStateListRowLayouts
      (compactFixedWidthTableCode width tokens)
      width tokens.length boundaryTable states := by
    intro index hindex
    let state := states.getI index
    let componentFront := (elementComponents.take index).flatten
    let componentBack :=
      (elementComponents.drop (index + 1)).flatten
    let rowFront := frontTokens ++ [states.length] ++ componentFront
    let rowBack := componentBack ++ backTokens
    let left := boundaryRows.getI index
    let right := boundaryRows.getI (index + 1)
    have hcomponentIndex : elementComponents.getI index =
        compactAdditiveEncode state := by
      simpa [elementComponents, state] using
        compactBinaryNatStreamStateElementComponents_getI
          states index hindex
    have hcomponentIndexBound : index < elementComponents.length := by
      simpa [elementComponents] using hindex
    have hsplit := List.flatten_split_at
      elementComponents index hcomponentIndexBound
    have hrowTokens :
        rowFront ++ compactAdditiveEncode state ++ rowBack = tokens := by
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
        (compactAdditiveEncode state).length := by
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
        compactBinaryNatStreamStateBoundaryRows]
      simp only [compactAdditiveShiftedBoundaries_length,
        compactBinaryNatStreamStateElementComponents_length]
      omega
    have hrightIndex : index + 1 < boundaryRows.length := by
      dsimp only [boundaryRows,
        compactBinaryNatStreamStateBoundaryRows]
      simp only [compactAdditiveShiftedBoundaries_length,
        compactBinaryNatStreamStateElementComponents_length]
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
      simpa [boundaryTable, compactBinaryNatStreamStateBoundaryTable,
        boundaryRows] using
        compactFixedWidthTableCode_entry tokens.length boundaryRows index
          hleftIndex hrowEntryBound
    have hrightEntry : CompactFixedWidthEntry
        boundaryTable tokens.length (index + 1) right := by
      simpa [boundaryTable, compactBinaryNatStreamStateBoundaryTable,
        boundaryRows] using
        compactFixedWidthTableCode_entry tokens.length boundaryRows
          (index + 1) hrightIndex hrowEntryBound
    have hstateRaw :=
      compactBinaryNatStreamStateDirectLayout_canonical
        rowFront state rowBack
    dsimp only at hstateRaw
    rw [hrowTokens] at hstateRaw
    have hstateLayout : CompactBinaryNatStreamStateDirectLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length left right state := by
      simpa only [width, hleft, hright] using hstateRaw
    exact ⟨left, hleftBound, right, hrightBound,
      hleftEntry, hrightEntry, hstateLayout⟩
  have htableSize : Nat.size boundaryTable ≤
      (states.length + 1) * tokens.length := by
    simpa [boundaryTable, compactBinaryNatStreamStateBoundaryTable,
      boundaryRows, compactBinaryNatStreamStateBoundaryRows,
      elementComponents] using
      compactAdditiveShiftedBoundaryTable_size_le
        bodyStart tokens.length elementComponents
  exact ⟨hlayout, hrows, htableSize⟩

#print axioms compactBinaryNatStreamStateElementComponents_getI
#print axioms compactBinaryNatStreamStateListDirectLayout_canonical

end FoundationCompactNumericListedDirectBinaryNatStreamStateListLayout
