import integration.FoundationCompactNumericListedDirectInputTableau

/-!
# Direct cursor graphs for the additive trace codec

The complete trace is a flat stream of natural-number tokens.  These bounded
relations expose one token, a list header, an exact `List Nat` slice, and a
strict table of component boundaries without invoking the typed decoder.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectAdditiveCodecGraph

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTokenStreamInverse

/-- One additive-code token at `cursor`, with the exact successor cursor. -/
def CompactAdditiveTokenCell
    (tokenTable width tokenCount cursor value next : Nat) : Prop :=
  cursor < tokenCount ∧
    next = cursor + 1 ∧
    CompactFixedWidthEntry tokenTable width cursor value

def compactAdditiveTokenCellDef : 𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount cursor value next.
    cursor < tokenCount ∧
    next = cursor + 1 ∧
    !(compactFixedWidthEntryDef) tokenTable width cursor value”

@[simp] theorem compactAdditiveTokenCellDef_spec
    (tokenTable width tokenCount cursor value next : Nat) :
    compactAdditiveTokenCellDef.val.Evalb
        ![tokenTable, width, tokenCount, cursor, value, next] ↔
      CompactAdditiveTokenCell
        tokenTable width tokenCount cursor value next := by
  simp [compactAdditiveTokenCellDef, CompactAdditiveTokenCell]

theorem compactAdditiveTokenCellDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveTokenCellDef.val := by
  simp [compactAdditiveTokenCellDef]

theorem CompactAdditiveTokenCell.value_eq_tableValue
    {tokenTable width tokenCount cursor value next : Nat}
    (hcell : CompactAdditiveTokenCell
      tokenTable width tokenCount cursor value next) :
    value = compactFixedWidthTableValue tokenTable width cursor :=
  FoundationCompactNumericListedDirectTokenStreamInverse.CompactFixedWidthEntry.value_eq_tableValue
    hcell.2.2

theorem compactAdditiveTokenCell_canonical
    (tokens : List Nat) (width cursor : Nat)
    (hcursor : cursor < tokens.length)
    (hwidth : ∀ token ∈ tokens, Nat.size token ≤ width) :
    CompactAdditiveTokenCell
      (compactFixedWidthTableCode width tokens)
      width tokens.length cursor (tokens.getI cursor) (cursor + 1) := by
  exact ⟨hcursor, rfl,
    compactFixedWidthTableCode_entry
      width tokens cursor hcursor hwidth⟩

/-- The first token of an additive list is its element count.  Every encoded
element is nonempty in the concrete codec, so the count is bounded by the
remaining token interval. -/
def CompactAdditiveListHeader
    (tokenTable width tokenCount start count bodyStart : Nat) : Prop :=
  CompactAdditiveTokenCell
      tokenTable width tokenCount start count bodyStart ∧
    bodyStart + count ≤ tokenCount

def compactAdditiveListHeaderDef : 𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount start count bodyStart.
    !(compactAdditiveTokenCellDef)
      tokenTable width tokenCount start count bodyStart ∧
    bodyStart + count ≤ tokenCount”

@[simp] theorem compactAdditiveListHeaderDef_spec
    (tokenTable width tokenCount start count bodyStart : Nat) :
    compactAdditiveListHeaderDef.val.Evalb
        ![tokenTable, width, tokenCount, start, count, bodyStart] ↔
      CompactAdditiveListHeader
        tokenTable width tokenCount start count bodyStart := by
  simp [compactAdditiveListHeaderDef, compactAdditiveTokenCellDef,
    CompactAdditiveListHeader, CompactAdditiveTokenCell]

theorem compactAdditiveListHeaderDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveListHeaderDef.val := by
  simp [compactAdditiveListHeaderDef]

/-- A `List Nat` occupies exactly one header token and then one token per
element; no auxiliary decoding witness is needed. -/
def CompactAdditiveNatListSlice
    (tokenTable width tokenCount start count finish : Nat) : Prop :=
  ∃ bodyStart, bodyStart ≤ tokenCount ∧
    CompactAdditiveListHeader
      tokenTable width tokenCount start count bodyStart ∧
    finish = bodyStart + count

def compactAdditiveNatListSliceDef : 𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount start count finish.
    ∃ bodyStart <⁺ tokenCount,
      !(compactAdditiveListHeaderDef)
        tokenTable width tokenCount start count bodyStart ∧
      finish = bodyStart + count”

@[simp] theorem compactAdditiveNatListSliceDef_spec
    (tokenTable width tokenCount start count finish : Nat) :
    compactAdditiveNatListSliceDef.val.Evalb
        ![tokenTable, width, tokenCount, start, count, finish] ↔
      CompactAdditiveNatListSlice
        tokenTable width tokenCount start count finish := by
  simp [compactAdditiveNatListSliceDef, compactAdditiveListHeaderDef,
    compactAdditiveTokenCellDef, CompactAdditiveNatListSlice,
    CompactAdditiveListHeader, CompactAdditiveTokenCell]

theorem compactAdditiveNatListSliceDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveNatListSliceDef.val := by
  simp [compactAdditiveNatListSliceDef]

theorem CompactAdditiveListHeader.natListSlice
    {tokenTable width tokenCount start count bodyStart : Nat}
    (hheader : CompactAdditiveListHeader
      tokenTable width tokenCount start count bodyStart) :
    CompactAdditiveNatListSlice
      tokenTable width tokenCount start count (bodyStart + count) := by
  refine ⟨bodyStart, ?_, hheader, rfl⟩
  exact (Nat.le_add_right bodyStart count).trans hheader.2

/-- A flat table stores the cursor before and after every nonempty component.
This is the common layout for products and lists of structured values. -/
def CompactAdditiveBoundaryTable
    (tokenCount partCount start finish boundaryTable : Nat) : Prop :=
  start ≤ tokenCount ∧
    finish ≤ tokenCount ∧
    CompactFixedWidthEntry boundaryTable tokenCount 0 start ∧
    CompactFixedWidthEntry boundaryTable tokenCount partCount finish ∧
    ∀ index < partCount,
      ∃ left, left ≤ tokenCount ∧
      ∃ right, right ≤ tokenCount ∧
        CompactFixedWidthEntry boundaryTable tokenCount index left ∧
        CompactFixedWidthEntry boundaryTable tokenCount (index + 1) right ∧
        left < right

def compactAdditiveBoundaryTableDef : 𝚺₀.Semisentence 5 := .mkSigma
  “tokenCount partCount start finish boundaryTable.
    start ≤ tokenCount ∧
    finish ≤ tokenCount ∧
    !(compactFixedWidthEntryDef) boundaryTable tokenCount 0 start ∧
    !(compactFixedWidthEntryDef) boundaryTable tokenCount partCount finish ∧
    ∀ index < partCount,
      ∃ left <⁺ tokenCount,
      ∃ right <⁺ tokenCount,
        !(compactFixedWidthEntryDef) boundaryTable tokenCount index left ∧
        !(compactFixedWidthEntryDef)
          boundaryTable tokenCount (index + 1) right ∧
        left < right”

@[simp] theorem compactAdditiveBoundaryTableDef_spec
    (tokenCount partCount start finish boundaryTable : Nat) :
    compactAdditiveBoundaryTableDef.val.Evalb
        ![tokenCount, partCount, start, finish, boundaryTable] ↔
      CompactAdditiveBoundaryTable
        tokenCount partCount start finish boundaryTable := by
  simp [compactAdditiveBoundaryTableDef, CompactAdditiveBoundaryTable,
    FoundationCompactNumericListedDirectTokenStreamTableau.foundationNatLE_iff_standard]

theorem compactAdditiveBoundaryTableDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveBoundaryTableDef.val := by
  simp [compactAdditiveBoundaryTableDef]

theorem natSize_le_of_le
    {value bound : Nat} (hvalue : value ≤ bound) :
    Nat.size value ≤ bound := by
  rw [Nat.size_le]
  exact hvalue.trans_lt bound.lt_two_pow_self

/-- Any explicitly supplied strictly increasing boundary list has a canonical
row-major table with the exact direct arithmetic semantics. -/
theorem compactAdditiveBoundaryTable_of_rows
    (tokenCount partCount start finish : Nat)
    (boundaries : List Nat)
    (hlength : boundaries.length = partCount + 1)
    (hstart : boundaries.getI 0 = start)
    (hfinish : boundaries.getI partCount = finish)
    (hbounded : ∀ cursor ∈ boundaries, cursor ≤ tokenCount)
    (hstrict : ∀ index < partCount,
      boundaries.getI index < boundaries.getI (index + 1)) :
    CompactAdditiveBoundaryTable tokenCount partCount start finish
      (compactFixedWidthTableCode tokenCount boundaries) := by
  have hentryBound : ∀ cursor ∈ boundaries,
      Nat.size cursor ≤ tokenCount := by
    intro cursor hcursor
    exact natSize_le_of_le (hbounded cursor hcursor)
  have hzeroIndex : 0 < boundaries.length := by omega
  have hfinalIndex : partCount < boundaries.length := by omega
  have hstartBound : start ≤ tokenCount := by
    rw [← hstart]
    apply hbounded
    rw [List.getI_eq_getElem _ hzeroIndex]
    exact List.getElem_mem hzeroIndex
  have hfinishBound : finish ≤ tokenCount := by
    rw [← hfinish]
    apply hbounded
    rw [List.getI_eq_getElem _ hfinalIndex]
    exact List.getElem_mem hfinalIndex
  refine ⟨hstartBound, hfinishBound, ?_, ?_, ?_⟩
  · simpa [hstart] using compactFixedWidthTableCode_entry
      tokenCount boundaries 0 hzeroIndex hentryBound
  · simpa [hfinish] using compactFixedWidthTableCode_entry
      tokenCount boundaries partCount hfinalIndex hentryBound
  · intro index hindex
    have hleftIndex : index < boundaries.length := by omega
    have hrightIndex : index + 1 < boundaries.length := by omega
    have hleftBound : boundaries.getI index ≤ tokenCount := by
      apply hbounded
      rw [List.getI_eq_getElem _ hleftIndex]
      exact List.getElem_mem hleftIndex
    have hrightBound : boundaries.getI (index + 1) ≤ tokenCount := by
      apply hbounded
      rw [List.getI_eq_getElem _ hrightIndex]
      exact List.getElem_mem hrightIndex
    refine ⟨boundaries.getI index, hleftBound,
      boundaries.getI (index + 1), hrightBound, ?_, ?_, hstrict index hindex⟩
    · exact compactFixedWidthTableCode_entry
        tokenCount boundaries index hleftIndex hentryBound
    · exact compactFixedWidthTableCode_entry
        tokenCount boundaries (index + 1) hrightIndex hentryBound

theorem compactAdditiveBoundaryTable_code_size_le
    (tokenCount : Nat) (boundaries : List Nat) :
    Nat.size (compactFixedWidthTableCode tokenCount boundaries) ≤
      boundaries.length * tokenCount :=
  compactFixedWidthTableCode_size_le tokenCount boundaries

#print axioms compactAdditiveTokenCellDef_spec
#print axioms compactAdditiveTokenCellDef_sigmaZero
#print axioms CompactAdditiveTokenCell.value_eq_tableValue
#print axioms compactAdditiveTokenCell_canonical
#print axioms compactAdditiveListHeaderDef_spec
#print axioms compactAdditiveListHeaderDef_sigmaZero
#print axioms compactAdditiveNatListSliceDef_spec
#print axioms compactAdditiveNatListSliceDef_sigmaZero
#print axioms CompactAdditiveListHeader.natListSlice
#print axioms compactAdditiveBoundaryTableDef_spec
#print axioms compactAdditiveBoundaryTableDef_sigmaZero
#print axioms compactAdditiveBoundaryTable_of_rows
#print axioms compactAdditiveBoundaryTable_code_size_le

end FoundationCompactNumericListedDirectAdditiveCodecGraph
