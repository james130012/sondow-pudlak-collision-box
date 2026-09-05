import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds

/-! # Free variables of an explicit bounded-witness prefix -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactPAExplicitBoundedWitnessFormulaFreeVariables

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

theorem explicitBoundedWitnessFormula_freeVariables_subset
    (bound : Nat) : forall (arity : Nat)
      (body : ArithmeticSemiformula Nat arity),
      (explicitBoundedWitnessFormula (shortBinaryNumeralTerm bound) arity
        body).freeVariables ⊆ body.freeVariables
  | 0, body => by simp [explicitBoundedWitnessFormula]
  | arity + 1, body => by
      exact (explicitBoundedWitnessFormula_freeVariables_subset bound arity
        (body.bexsLTSucc
          (closedShift arity (shortBinaryNumeralTerm bound)))).trans
        (explicitBoundedWitnessRecursiveBody_freeVariables_subset bound body)

theorem explicitBoundedWitnessFormula_freeVariables_eq_empty_of_body
    (bound arity : Nat) (body : ArithmeticSemiformula Nat arity)
    (hbody : body.freeVariables = ∅) :
    (explicitBoundedWitnessFormula (shortBinaryNumeralTerm bound) arity
      body).freeVariables = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro index hindex
  have hsource := explicitBoundedWitnessFormula_freeVariables_subset bound
    arity body hindex
  rw [hbody] at hsource
  simpa using hsource

#print axioms explicitBoundedWitnessFormula_freeVariables_subset
#print axioms
  explicitBoundedWitnessFormula_freeVariables_eq_empty_of_body

end FoundationCompactPAExplicitBoundedWitnessFormulaFreeVariables
