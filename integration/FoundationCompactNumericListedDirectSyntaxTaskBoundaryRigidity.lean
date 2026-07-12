import integration.FoundationCompactNumericListedDirectSyntaxTaskRowRealization

/-!
# Rigidity of three-token syntax-task boundary tables

Every task row occupies exactly three tokens.  Hence row `i` begins at
`bodyStart + 3 * i`, and any second valid boundary table over the same list
interval carries the same typed task rows.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSyntaxTaskBoundaryRigidity

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization

theorem CompactAdditiveBoundaryTable.entry_eq_bodyStart_add_three_mul
    {tokenCount count bodyStart finish boundaryTable : Nat}
    (hboundary : CompactAdditiveBoundaryTable
      tokenCount count bodyStart finish boundaryTable)
    (htriple : CompactAdditiveTripleBoundaryRows
      tokenCount count boundaryTable)
    (index : Nat) (hindex : index ≤ count) :
    CompactFixedWidthEntry boundaryTable tokenCount index
      (bodyStart + 3 * index) := by
  induction index with
  | zero => simpa using hboundary.2.2.1
  | succ index ih =>
      have hindexLt : index < count := by omega
      have hprevious := ih (by omega)
      rcases htriple index hindexLt with
        ⟨left, _hleft, right, _hright,
          hleftEntry, hrightEntry, hnext⟩
      have hleftEq : left = bodyStart + 3 * index :=
        (CompactFixedWidthEntry.value_eq_tableValue hleftEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue hprevious).symm
      subst left
      subst right
      convert hrightEntry using 1 <;> omega

theorem CompactAdditiveStructuredListLayout.taskEntry_eq_start_add_three_mul
    {tokenTable width tokenCount start count finish boundaryTable : Nat}
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable)
    (htriple : CompactAdditiveTripleBoundaryRows
      tokenCount count boundaryTable)
    (index : Nat) (hindex : index ≤ count) :
    CompactFixedWidthEntry boundaryTable tokenCount index
      (start + 1 + 3 * index) := by
  rcases hlayout with ⟨bodyStart, _hbodyStart, hheader, hboundary⟩
  have hbodyStart : bodyStart = start + 1 := hheader.1.2.1
  rw [← hbodyStart]
  exact CompactAdditiveBoundaryTable.entry_eq_bodyStart_add_three_mul
    hboundary htriple index hindex

theorem CompactAdditiveStructuredListLayout.taskFinish_eq_start_add_count
    {tokenTable width tokenCount start count finish boundaryTable : Nat}
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable)
    (htriple : CompactAdditiveTripleBoundaryRows
      tokenCount count boundaryTable) :
    finish = start + 1 + 3 * count := by
  have hcanonical :=
    CompactAdditiveStructuredListLayout.taskEntry_eq_start_add_three_mul
      hlayout htriple count (by rfl)
  rcases hlayout with ⟨_bodyStart, _hbodyStart, _hheader, hboundary⟩
  exact (CompactFixedWidthEntry.value_eq_tableValue
    hboundary.2.2.2.1).trans
      (CompactFixedWidthEntry.value_eq_tableValue hcanonical).symm

theorem CompactAdditiveStructuredListElementRowLayouts.taskRows_on_tripleBoundary
    {tokenTable width tokenCount start finish
      actualBoundary targetBoundary : Nat}
    {tasks : List CompactSyntaxTask}
    (hactualLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start tasks.length finish actualBoundary)
    (hactualRows : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        actualBoundary tasks)
    (htargetLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start tasks.length finish targetBoundary)
    (htargetTriple : CompactAdditiveTripleBoundaryRows
      tokenCount tasks.length targetBoundary) :
    CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        targetBoundary tasks := by
  have hactualTriple : CompactAdditiveTripleBoundaryRows
      tokenCount tasks.length actualBoundary :=
    CompactAdditiveStructuredListElementRowLayouts.tripleBoundaryRows
      hactualRows
  intro index hindex
  rcases hactualRows index hindex with
    ⟨actualLeft, _hactualLeft, actualRight, _hactualRight,
      hactualLeftEntry, hactualRightEntry, hactualTask⟩
  rcases htargetTriple index hindex with
    ⟨targetLeft, htargetLeft, targetRight, htargetRight,
      htargetLeftEntry, htargetRightEntry, _htargetNext⟩
  have hactualLeftCanonical :=
    CompactAdditiveStructuredListLayout.taskEntry_eq_start_add_three_mul
      hactualLayout hactualTriple index (by omega)
  have hactualRightCanonical :=
    CompactAdditiveStructuredListLayout.taskEntry_eq_start_add_three_mul
      hactualLayout hactualTriple (index + 1) (by omega)
  have htargetLeftCanonical :=
    CompactAdditiveStructuredListLayout.taskEntry_eq_start_add_three_mul
      htargetLayout htargetTriple index (by omega)
  have htargetRightCanonical :=
    CompactAdditiveStructuredListLayout.taskEntry_eq_start_add_three_mul
      htargetLayout htargetTriple (index + 1) (by omega)
  have hactualLeftCursor : actualLeft = start + 1 + 3 * index :=
    (CompactFixedWidthEntry.value_eq_tableValue hactualLeftEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualLeftCanonical).symm
  have hactualRightCursor : actualRight = start + 1 + 3 * (index + 1) :=
    (CompactFixedWidthEntry.value_eq_tableValue hactualRightEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualRightCanonical).symm
  have htargetLeftCursor : targetLeft = start + 1 + 3 * index :=
    (CompactFixedWidthEntry.value_eq_tableValue htargetLeftEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        htargetLeftCanonical).symm
  have htargetRightCursor : targetRight = start + 1 + 3 * (index + 1) :=
    (CompactFixedWidthEntry.value_eq_tableValue htargetRightEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        htargetRightCanonical).symm
  have hleft : targetLeft = actualLeft := by omega
  have hright : targetRight = actualRight := by omega
  refine ⟨targetLeft, htargetLeft, targetRight, htargetRight,
    htargetLeftEntry, htargetRightEntry, ?_⟩
  rw [hleft, hright]
  exact hactualTask

#print axioms CompactAdditiveBoundaryTable.entry_eq_bodyStart_add_three_mul
#print axioms CompactAdditiveStructuredListLayout.taskEntry_eq_start_add_three_mul
#print axioms CompactAdditiveStructuredListLayout.taskFinish_eq_start_add_count
#print axioms CompactAdditiveStructuredListElementRowLayouts.taskRows_on_tripleBoundary

end FoundationCompactNumericListedDirectSyntaxTaskBoundaryRigidity
