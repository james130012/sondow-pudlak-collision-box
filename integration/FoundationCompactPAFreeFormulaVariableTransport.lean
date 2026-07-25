import Foundation.FirstOrder.Basic.Syntax.Rew

/-!
# Free-formula variable transport

This module records the small inverse-law argument needed to control contexts
after opening one bound variable.  It avoids structural recursion over the
formula being compiled.
-/

open LO FirstOrder

namespace FoundationCompactPAFreeFormulaVariableTransport

theorem bShiftTerm_freeVariables_eq
    {L : Language} {boundArity : Nat}
    (term : LO.FirstOrder.Semiterm L Nat boundArity) :
    (Rew.bShift term).freeVariables = term.freeVariables := by
  ext coordinate
  exact LO.FirstOrder.Semiterm.fvar?_bShift

theorem freeFormula_succ_mem_of_mem
    {L : Language}
    (formula : LO.FirstOrder.Semiformula L Nat 1)
    (coordinate : Nat)
    (hcoordinate : formula.FVar? coordinate) :
    (Rewriting.free formula).FVar? (coordinate + 1) := by
  have hfixed :
      (Rew.fix ▹ Rewriting.free formula).FVar? coordinate := by
    simpa only [← TransitiveRewriting.comp_app, Rew.fix_comp_free,
      ReflectiveRewriting.id_app] using hcoordinate
  rcases LO.FirstOrder.Semiformula.fvar?_rew hfixed with
    hbound | ⟨freeCoordinate, hfree, hfixedCoordinate⟩
  · rcases hbound with ⟨boundCoordinate, hboundCoordinate⟩
    simp at hboundCoordinate
  · cases freeCoordinate with
    | zero =>
        simp at hfixedCoordinate
    | succ predecessor =>
        simp only [Rew.fix_fvar_succ, LO.FirstOrder.Semiterm.FVar?,
          LO.FirstOrder.Semiterm.freeVariables_fvar,
          Finset.mem_singleton] at hfixedCoordinate
        subst predecessor
        simpa only [Nat.succ_eq_add_one] using hfree

#print axioms freeFormula_succ_mem_of_mem
#print axioms bShiftTerm_freeVariables_eq

end FoundationCompactPAFreeFormulaVariableTransport
