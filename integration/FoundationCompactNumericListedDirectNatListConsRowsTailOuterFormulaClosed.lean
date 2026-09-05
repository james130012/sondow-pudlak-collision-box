import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyClosed
import integration.FoundationCompactPAContextualTermBoundedUniversalCompiler
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # The bounded-universal cons-tail formula is closed -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 140000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailOuterFormulaClosed

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyClosed

theorem compactAdditiveNatListConsRowsTailOuterFormula_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary : Nat) :
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm sourceCount))
      (compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
        sourceBoundary targetBoundary)).freeVariables = ∅ := by
  have hshift :
      (Rew.bShift
        (shortBinaryNumeralTerm sourceCount : ValuationTerm)).freeVariables =
          ∅ :=
    bShift_freeVariables_eq_empty_of_empty _
      (shortBinaryNumeralTerm_freeVariables_eq_empty sourceCount)
  have htermBound :
      (termBoundFormula
        (Rew.bShift
          (shortBinaryNumeralTerm sourceCount : ValuationTerm))).freeVariables =
          ∅ := by
    unfold termBoundFormula
      FoundationCompactPAFiniteCaseSyntax.finiteCaseLessThanFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_rel]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro candidate hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => simp at hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero =>
            change candidate ∈
              (Rew.bShift
                (shortBinaryNumeralTerm sourceCount :
                  ValuationTerm)).freeVariables at hcoordinate
            rw [hshift] at hcoordinate
            simp at hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  simp only [LO.FirstOrder.Semiformula.freeVariables_all,
    termBoundedUniversalBody, LO.FirstOrder.Semiformula.freeVariables_imp,
    htermBound,
    compactAdditiveNatListConsRowsTailBody_freeVariables_eq_empty]
  simp

#print axioms
  compactAdditiveNatListConsRowsTailOuterFormula_freeVariables_eq_empty

end FoundationCompactNumericListedDirectNatListConsRowsTailOuterFormulaClosed
