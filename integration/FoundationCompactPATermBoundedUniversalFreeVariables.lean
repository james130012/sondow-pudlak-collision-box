import integration.FoundationCompactPAContextualTermBoundedUniversalCompiler
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Free variables of a term-bounded universal shell

This structural lemma keeps the shell proof independent of the size of its
body.  In particular, applying it never unfolds an embedded verifier formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationCompactPATermBoundedUniversalFreeVariables

open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables

theorem termBoundedUniversal_freeVariables_subset
    (boundTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (vars : Finset Nat)
    (hbound : boundTerm.freeVariables ⊆ vars)
    (hbody : body.freeVariables ⊆ vars) :
    (∀⁰ termBoundedUniversalBody boundTerm body).freeVariables ⊆ vars := by
  have htermBound :
      (termBoundFormula boundTerm).freeVariables ⊆ vars := by
    unfold termBoundFormula finiteCaseLessThanFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_rel]
    intro candidate hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => simp at hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact hbound hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  simp only [LO.FirstOrder.Semiformula.freeVariables_all,
    termBoundedUniversalBody, LO.FirstOrder.Semiformula.freeVariables_imp]
  exact Finset.union_subset htermBound hbody

#print axioms termBoundedUniversal_freeVariables_subset

end FoundationCompactPATermBoundedUniversalFreeVariables
