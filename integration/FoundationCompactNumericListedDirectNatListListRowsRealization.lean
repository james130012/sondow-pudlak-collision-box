import integration.FoundationCompactNumericListedDirectVerifierValueRealization

/-!
# Realization of nested natural-list rows without an outer list header

The row graph alone determines one typed natural-number list at every outer
index.  This weaker realization is useful for auxiliary boundary tables that
are compared to an already parsed child result but do not carry a second copy
of the outer structured-list header.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListListRowsRealization

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectVerifierValueRealization

theorem CompactAdditiveNatListListRowsWellFormed.realizeRows
    {tokenTable width tokenCount boundaryTable count : Nat}
    (hrows : CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount boundaryTable count) :
    ∃ values : List (List Nat),
      values.length = count ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          boundaryTable values := by
  classical
  have hexists (index : Nat) (hindex : index < count) :
      ∃ value : List Nat,
      ∃ left, left ≤ tokenCount ∧
      ∃ right, right ≤ tokenCount ∧
        CompactFixedWidthEntry boundaryTable tokenCount index left ∧
        CompactFixedWidthEntry boundaryTable tokenCount (index + 1) right ∧
        CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount left right value := by
    rcases hrows index hindex with
      ⟨left, hleft, right, hright, innerCount, _hinnerCount,
        hleftEntry, hrightEntry, hslice⟩
    rcases CompactAdditiveNatListSlice.realizeDirectLayout
        hslice hright with
      ⟨value, _hvalueLength, hvalue⟩
    exact ⟨value, left, hleft, right, hright,
      hleftEntry, hrightEntry, hvalue⟩
  let valueAt (index : Fin count) : List Nat :=
    Classical.choose (hexists index index.isLt)
  let values : List (List Nat) := List.ofFn valueAt
  have hvaluesLength : values.length = count := by
    simp [values]
  have hvalueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        boundaryTable values := by
    intro index hindex
    have hcount : index < count := by
      simpa [hvaluesLength] using hindex
    have hspec := Classical.choose_spec (hexists index hcount)
    rcases hspec with
      ⟨left, hleft, right, hright,
        hleftEntry, hrightEntry, hvalue⟩
    refine ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, ?_⟩
    have hget : values.getI index = valueAt ⟨index, hcount⟩ := by
      rw [List.getI_eq_getElem _
        (by simpa [hvaluesLength] using hcount)]
      simp [values]
    rw [hget]
    exact hvalue
  exact ⟨values, hvaluesLength, hvalueRows⟩

#print axioms CompactAdditiveNatListListRowsWellFormed.realizeRows

end FoundationCompactNumericListedDirectNatListListRowsRealization
