import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropRows
import integration.FoundationCompactNumericListedDirectSyntaxTaskRowRealization

/-!
# Canonical bounded boundary table for a syntax-task-list tail

The source boundary table already stores every cursor around the three-token
task rows.  Dropping its first cursor and repacking the remaining cursors gives
a canonical table for `tasks.drop 1`.  No task token is copied or changed.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSyntaxTaskListTailTable

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows

def compactAdditiveSyntaxTaskTailBoundaryRows
    (sourceBoundary tokenCount sourceCount : Nat) : List Nat :=
  (List.range sourceCount).map fun index =>
    compactFixedWidthTableValue sourceBoundary tokenCount (index + 1)

def compactAdditiveSyntaxTaskTailBoundaryTable
    (sourceBoundary tokenCount sourceCount : Nat) : Nat :=
  compactFixedWidthTableCode tokenCount
    (compactAdditiveSyntaxTaskTailBoundaryRows
      sourceBoundary tokenCount sourceCount)

@[simp] theorem compactAdditiveSyntaxTaskTailBoundaryRows_length
    (sourceBoundary tokenCount sourceCount : Nat) :
    (compactAdditiveSyntaxTaskTailBoundaryRows
      sourceBoundary tokenCount sourceCount).length = sourceCount := by
  simp [compactAdditiveSyntaxTaskTailBoundaryRows]

theorem compactAdditiveSyntaxTaskTailBoundaryRows_getI
    (sourceBoundary tokenCount sourceCount index : Nat)
    (hindex : index < sourceCount) :
    (compactAdditiveSyntaxTaskTailBoundaryRows
      sourceBoundary tokenCount sourceCount).getI index =
        compactFixedWidthTableValue
          sourceBoundary tokenCount (index + 1) := by
  rw [List.getI_eq_getElem _ (by simpa using hindex)]
  simp [compactAdditiveSyntaxTaskTailBoundaryRows]

theorem compactAdditiveSyntaxTaskTailBoundaryRows_values_size_le
    (sourceBoundary tokenCount sourceCount : Nat) :
    ∀ value ∈ compactAdditiveSyntaxTaskTailBoundaryRows
        sourceBoundary tokenCount sourceCount,
      Nat.size value ≤ tokenCount := by
  intro value hvalue
  rcases List.mem_map.mp hvalue with ⟨index, _hindex, rfl⟩
  exact compactFixedWidthTableValue_size_le
    sourceBoundary tokenCount (index + 1)

theorem compactAdditiveSyntaxTaskTailBoundaryTable_entry
    (sourceBoundary tokenCount sourceCount index : Nat)
    (hindex : index < sourceCount) :
    CompactFixedWidthEntry
      (compactAdditiveSyntaxTaskTailBoundaryTable
        sourceBoundary tokenCount sourceCount)
      tokenCount index
      (compactFixedWidthTableValue
        sourceBoundary tokenCount (index + 1)) := by
  have hentry := compactFixedWidthTableCode_entry
    tokenCount
    (compactAdditiveSyntaxTaskTailBoundaryRows
      sourceBoundary tokenCount sourceCount)
    index (by simpa using hindex)
    (compactAdditiveSyntaxTaskTailBoundaryRows_values_size_le
      sourceBoundary tokenCount sourceCount)
  simpa [compactAdditiveSyntaxTaskTailBoundaryTable,
    compactAdditiveSyntaxTaskTailBoundaryRows_getI
      sourceBoundary tokenCount sourceCount index hindex] using hentry

theorem CompactAdditiveStructuredListElementRowLayouts.taskTailRows
    {tokenTable width tokenCount sourceBoundary : Nat}
    {tasks : List CompactSyntaxTask}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        sourceBoundary tasks)
    (hpositive : 0 < tasks.length) :
    CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        (compactAdditiveSyntaxTaskTailBoundaryTable
          sourceBoundary tokenCount tasks.length)
        (tasks.drop 1) := by
  intro index hindex
  have hsourceIndex : index + 1 < tasks.length := by
    rw [List.length_drop] at hindex
    omega
  rcases hsource (index + 1) hsourceIndex with
    ⟨sourceLeft, hsourceLeft, sourceRight, hsourceRight,
      hsourceLeftEntry, hsourceRightEntry, hsourceLayout⟩
  have hsourceLeftValue : sourceLeft =
      compactFixedWidthTableValue
        sourceBoundary tokenCount (index + 1) :=
    CompactFixedWidthEntry.value_eq_tableValue hsourceLeftEntry
  have hsourceRightValue : sourceRight =
      compactFixedWidthTableValue
        sourceBoundary tokenCount (index + 2) := by
    have hvalue :=
      CompactFixedWidthEntry.value_eq_tableValue hsourceRightEntry
    simpa [Nat.add_assoc] using hvalue
  have htargetLeftEntry : CompactFixedWidthEntry
      (compactAdditiveSyntaxTaskTailBoundaryTable
        sourceBoundary tokenCount tasks.length)
      tokenCount index sourceLeft := by
    simpa [hsourceLeftValue] using
      compactAdditiveSyntaxTaskTailBoundaryTable_entry
        sourceBoundary tokenCount tasks.length index (by omega)
  have htargetRightEntry : CompactFixedWidthEntry
      (compactAdditiveSyntaxTaskTailBoundaryTable
        sourceBoundary tokenCount tasks.length)
      tokenCount (index + 1) sourceRight := by
    simpa [hsourceRightValue, Nat.add_assoc] using
      compactAdditiveSyntaxTaskTailBoundaryTable_entry
        sourceBoundary tokenCount tasks.length (index + 1) hsourceIndex
  have htailValue :
      (tasks.drop 1).getI index = tasks.getI (index + 1) := by
    rw [List.getI_eq_getElem _ hindex]
    rw [List.getI_eq_getElem _ hsourceIndex]
    simp
  refine ⟨sourceLeft, hsourceLeft, sourceRight, hsourceRight,
    htargetLeftEntry, htargetRightEntry, ?_⟩
  simpa only [htailValue] using hsourceLayout

theorem CompactAdditiveStructuredListElementRowLayouts.taskTailDropRows
    {tokenTable width tokenCount sourceBoundary : Nat}
    {tasks : List CompactSyntaxTask}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        sourceBoundary tasks)
    (hpositive : 0 < tasks.length) :
    CompactAdditiveSyntaxTaskListDropRows
      tokenTable width tokenCount sourceBoundary tasks.length
        (compactAdditiveSyntaxTaskTailBoundaryTable
          sourceBoundary tokenCount tasks.length)
        (tasks.drop 1).length 1 := by
  have htail :=
    CompactAdditiveStructuredListElementRowLayouts.taskTailRows
      hsource hpositive
  exact CompactAdditiveStructuredListElementRowLayouts.taskDropRows
    hsource htail (by omega) rfl

theorem compactAdditiveSyntaxTaskTailBoundaryTable_size_le
    (sourceBoundary tokenCount : Nat)
    {tasks : List CompactSyntaxTask}
    (hpositive : 0 < tasks.length) :
    Nat.size (compactAdditiveSyntaxTaskTailBoundaryTable
        sourceBoundary tokenCount tasks.length) ≤
      ((tasks.drop 1).length + 1) * tokenCount := by
  have hsize := compactFixedWidthTableCode_size_le tokenCount
    (compactAdditiveSyntaxTaskTailBoundaryRows
      sourceBoundary tokenCount tasks.length)
  rw [compactAdditiveSyntaxTaskTailBoundaryTable]
  rw [compactAdditiveSyntaxTaskTailBoundaryRows_length] at hsize
  rw [List.length_drop]
  have hlength : tasks.length - 1 + 1 = tasks.length := by omega
  rw [hlength]
  exact hsize

theorem CompactAdditiveStructuredListElementRowLayouts.exists_taskTailTable
    {tokenTable width tokenCount sourceBoundary : Nat}
    {tasks : List CompactSyntaxTask}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        sourceBoundary tasks)
    (hpositive : 0 < tasks.length) :
    ∃ tailBoundary tailBoundarySize,
      CompactAdditiveStructuredListElementRowLayouts
        CompactSyntaxTaskDirectLayout tokenTable width tokenCount
          tailBoundary (tasks.drop 1) ∧
      CompactAdditiveSyntaxTaskListDropRows
        tokenTable width tokenCount sourceBoundary tasks.length
          tailBoundary (tasks.drop 1).length 1 ∧
      tailBoundarySize = Nat.size tailBoundary ∧
      tailBoundarySize ≤ ((tasks.drop 1).length + 1) * tokenCount := by
  let tailBoundary := compactAdditiveSyntaxTaskTailBoundaryTable
    sourceBoundary tokenCount tasks.length
  exact ⟨tailBoundary, Nat.size tailBoundary,
    CompactAdditiveStructuredListElementRowLayouts.taskTailRows
      hsource hpositive,
    CompactAdditiveStructuredListElementRowLayouts.taskTailDropRows
      hsource hpositive, rfl,
    compactAdditiveSyntaxTaskTailBoundaryTable_size_le
      sourceBoundary tokenCount hpositive⟩

#print axioms compactAdditiveSyntaxTaskTailBoundaryTable_entry
#print axioms CompactAdditiveStructuredListElementRowLayouts.taskTailRows
#print axioms CompactAdditiveStructuredListElementRowLayouts.taskTailDropRows
#print axioms compactAdditiveSyntaxTaskTailBoundaryTable_size_le
#print axioms CompactAdditiveStructuredListElementRowLayouts.exists_taskTailTable

end FoundationCompactNumericListedDirectSyntaxTaskListTailTable
