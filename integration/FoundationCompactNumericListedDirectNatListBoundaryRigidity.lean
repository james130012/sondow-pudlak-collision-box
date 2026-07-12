import integration.FoundationCompactNumericListedDirectAtomicListLayouts

/-!
# Rigidity of one-token natural-list boundary tables

If every list row occupies exactly one token, the shared boundary table is
forced: row `i` starts at `bodyStart + i`, and the list finishes at
`bodyStart + count`.  This excludes alternative boundary witnesses.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListBoundaryRigidity

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts

def CompactAdditiveUnitBoundaryRows
    (tokenCount count boundaryTable : Nat) : Prop :=
  ∀ index < count,
    ∃ left, left ≤ tokenCount ∧
    ∃ right, right ≤ tokenCount ∧
      CompactFixedWidthEntry boundaryTable tokenCount index left ∧
      CompactFixedWidthEntry boundaryTable tokenCount (index + 1) right ∧
      right = left + 1

theorem CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
    {tokenTable width tokenCount boundaryTable : Nat}
    {values : List Nat}
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      boundaryTable values) :
    CompactAdditiveUnitBoundaryRows
      tokenCount values.length boundaryTable := by
  intro index hindex
  rcases hrows index hindex with
    ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, hlayout⟩
  exact ⟨left, hleft, right, hright,
    hleftEntry, hrightEntry, hlayout.2.1⟩

theorem CompactAdditiveBoundaryTable.entry_eq_bodyStart_add
    {tokenCount count bodyStart finish boundaryTable : Nat}
    (hboundary : CompactAdditiveBoundaryTable
      tokenCount count bodyStart finish boundaryTable)
    (hunit : CompactAdditiveUnitBoundaryRows
      tokenCount count boundaryTable)
    (index : Nat) (hindex : index ≤ count) :
    CompactFixedWidthEntry boundaryTable tokenCount index
      (bodyStart + index) := by
  induction index with
  | zero =>
      simpa using hboundary.2.2.1
  | succ index ih =>
      have hindexLt : index < count := by omega
      have hprevious := ih (by omega)
      rcases hunit index hindexLt with
        ⟨left, _hleft, right, _hright,
          hleftEntry, hrightEntry, hnext⟩
      have hleftEq : left = bodyStart + index :=
        (CompactFixedWidthEntry.value_eq_tableValue hleftEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue hprevious).symm
      subst left
      subst right
      simpa [Nat.add_assoc] using hrightEntry

theorem CompactAdditiveStructuredListLayout.entry_eq_start_add
    {tokenTable width tokenCount start count finish boundaryTable : Nat}
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable)
    (hunit : CompactAdditiveUnitBoundaryRows
      tokenCount count boundaryTable)
    (index : Nat) (hindex : index ≤ count) :
    CompactFixedWidthEntry boundaryTable tokenCount index
      (start + 1 + index) := by
  rcases hlayout with ⟨bodyStart, _hbodyStart, hheader, hboundary⟩
  have hbodyStart : bodyStart = start + 1 := hheader.1.2.1
  rw [← hbodyStart]
  exact CompactAdditiveBoundaryTable.entry_eq_bodyStart_add
    hboundary hunit index hindex

theorem CompactAdditiveStructuredListLayout.finish_eq_start_add_count
    {tokenTable width tokenCount start count finish boundaryTable : Nat}
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable)
    (hunit : CompactAdditiveUnitBoundaryRows
      tokenCount count boundaryTable) :
    finish = start + 1 + count := by
  have hcanonical :=
    CompactAdditiveStructuredListLayout.entry_eq_start_add
      hlayout hunit count (by rfl)
  rcases hlayout with ⟨_bodyStart, _hbodyStart, _hheader, hboundary⟩
  exact (CompactFixedWidthEntry.value_eq_tableValue
    hboundary.2.2.2.1).trans
      (CompactFixedWidthEntry.value_eq_tableValue hcanonical).symm

theorem CompactAdditiveStructuredListElementRowLayouts.natRows_on_unitBoundary
    {tokenTable width tokenCount start finish
      actualBoundary targetBoundary : Nat}
    {values : List Nat}
    (hactualLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start values.length finish actualBoundary)
    (hactualRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        actualBoundary values)
    (htargetLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start values.length finish targetBoundary)
    (htargetUnit : CompactAdditiveUnitBoundaryRows
      tokenCount values.length targetBoundary) :
    CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        targetBoundary values := by
  have hactualUnit : CompactAdditiveUnitBoundaryRows
      tokenCount values.length actualBoundary :=
    CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
      hactualRows
  intro index hindex
  rcases hactualRows index hindex with
    ⟨actualLeft, _hactualLeft, actualRight, _hactualRight,
      hactualLeftEntry, hactualRightEntry, hactualValue⟩
  rcases htargetUnit index hindex with
    ⟨targetLeft, htargetLeft, targetRight, htargetRight,
      htargetLeftEntry, htargetRightEntry, _htargetNext⟩
  have hactualLeftCanonical :=
    CompactAdditiveStructuredListLayout.entry_eq_start_add
      hactualLayout hactualUnit index (by omega)
  have hactualRightCanonical :=
    CompactAdditiveStructuredListLayout.entry_eq_start_add
      hactualLayout hactualUnit (index + 1) (by omega)
  have htargetLeftCanonical :=
    CompactAdditiveStructuredListLayout.entry_eq_start_add
      htargetLayout htargetUnit index (by omega)
  have htargetRightCanonical :=
    CompactAdditiveStructuredListLayout.entry_eq_start_add
      htargetLayout htargetUnit (index + 1) (by omega)
  have hactualLeftCursor : actualLeft = start + 1 + index :=
    (CompactFixedWidthEntry.value_eq_tableValue
      hactualLeftEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          hactualLeftCanonical).symm
  have hactualRightCursor :
      actualRight = start + 1 + (index + 1) :=
    (CompactFixedWidthEntry.value_eq_tableValue
      hactualRightEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          hactualRightCanonical).symm
  have htargetLeftCursor : targetLeft = start + 1 + index :=
    (CompactFixedWidthEntry.value_eq_tableValue
      htargetLeftEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          htargetLeftCanonical).symm
  have htargetRightCursor :
      targetRight = start + 1 + (index + 1) :=
    (CompactFixedWidthEntry.value_eq_tableValue
      htargetRightEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          htargetRightCanonical).symm
  have hleft : targetLeft = actualLeft := by omega
  have hright : targetRight = actualRight := by omega
  refine ⟨targetLeft, htargetLeft, targetRight, htargetRight,
    htargetLeftEntry, htargetRightEntry, ?_⟩
  rw [hleft, hright]
  exact hactualValue

#print axioms CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
#print axioms CompactAdditiveBoundaryTable.entry_eq_bodyStart_add
#print axioms CompactAdditiveStructuredListLayout.entry_eq_start_add
#print axioms CompactAdditiveStructuredListLayout.finish_eq_start_add_count
#print axioms CompactAdditiveStructuredListElementRowLayouts.natRows_on_unitBoundary

end FoundationCompactNumericListedDirectNatListBoundaryRigidity
