import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsDirectCompiler

/-!
# Free-variable bounds for direct additive unit-boundary rows

The row terminal is obtained by releasing the last bound row index of a
free-variable-closed terminal.  Its only possible free coordinate is therefore
the newly released coordinate zero.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsDirectFreeVariableBounds

open FoundationCompactPAValuationContextRewriting
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsDirectCompiler

private theorem freeFormulaAtArity_freeVariables_subset
    {arity : Nat}
    (formula : ArithmeticSemiformula Nat (arity + 1)) :
    (Rewriting.free formula).freeVariables ⊆
      insert 0 (formula.freeVariables.image Nat.succ) := by
  intro index hindex
  have hrewritten : (Rewriting.free formula).FVar? index := hindex
  rcases LO.FirstOrder.Semiformula.fvar?_rew hrewritten with
      hbound | hfree
  · rcases hbound with ⟨boundIndex, hboundIndex⟩
    cases boundIndex using Fin.lastCases with
    | last =>
        have hindexZero : index = 0 := by
          have hzeroIndex : 0 = index := by
            simpa [LO.FirstOrder.Semiformula.FVar?] using hboundIndex
          exact hzeroIndex.symm
        subst index
        exact Finset.mem_insert_self _ _
    | cast previous =>
        simp at hboundIndex
  · rcases hfree with ⟨sourceIndex, hsource, himage⟩
    have hindexSucc : index = sourceIndex + 1 := by
      have hsuccIndex : sourceIndex + 1 = index := by
        simpa [LO.FirstOrder.Semiformula.FVar?] using himage
      exact hsuccIndex.symm
    subst index
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨sourceIndex, hsource, rfl⟩)

theorem
    compactAdditiveUnitBoundaryRowsBranchTerminal_freeVariables_subset_singleton
    (tokenCount boundaryTable : Nat) :
    (compactAdditiveUnitBoundaryRowsBranchTerminal
      tokenCount boundaryTable).freeVariables ⊆ {0} := by
  rw [← compactAdditiveUnitBoundaryRowsTerminal_free_alignment]
  have hsubset := freeFormulaAtArity_freeVariables_subset
    (compactAdditiveUnitBoundaryRowsTerminal tokenCount boundaryTable)
  rw [compactAdditiveUnitBoundaryRowsTerminal_freeVariables_eq_empty] at hsubset
  simpa using hsubset

#print axioms
  compactAdditiveUnitBoundaryRowsBranchTerminal_freeVariables_subset_singleton

end FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsDirectFreeVariableBounds
