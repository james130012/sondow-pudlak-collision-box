import integration.FoundationCompactPAExplicitWitnessHybridSigmaOneFormulaBuilder
import integration.FoundationCompactNumericFormulaSubstitution

/-!
# Explicit vector witnesses for existential closures

This module introduces the rewriting lemmas needed to assemble an existential
closure from a vector of concrete witnesses without unfolding the whole closure
at every constructor.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAExplicitWitnessExsClosureBuilder

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactNumericFormulaSubstitution
open FoundationCompactPAExplicitWitnessHybridSigmaOneFormulaBuilder

/-- `qpow` of a one-variable substitution fixes the first `depth` coordinates
and substitutes the last coordinate by the lifted closed witness. -/
theorem qpow_singleSubstitution_eq_explicitLast
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat) :
    (Rew.subst ![witness]).qpow depth =
      Rew.subst (compactSubstitutionBVarResult witness depth) := by
  apply Rew.ext
  · intro index
    simpa using (compactSubstitutionBVarResult_eq_qpow witness depth index).symm
  · intro freeIndex
    simpa using compactSubstitutionFVar_eq_qpow witness depth freeIndex

/-- Substitution of the outer coordinate commutes with the `depth` inner
existential binders. -/
theorem subst_exsItr_explicitLast
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (1 + depth))
    (witness : Nat) :
    (∃⁰^[depth] body)/[shortBinaryNumeralTerm witness] =
      ∃⁰^[depth]
        (Rew.subst
          (compactSubstitutionBVarResult
            (shortBinaryNumeralTerm witness) depth) ▹ body) := by
  simp only [Rewriting.smul_exsItr]
  rw [qpow_singleSubstitution_eq_explicitLast]

/-- After all coordinates except the lowest one have been substituted, this is
the one-variable body used by the innermost explicit witness constructor. -/
def explicitWitnessBodyAfterTail
    {arity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  (Rew.subst (fun index : Fin arity =>
    shortBinaryNumeralTerm (values index.succ))).q ▹ body

/-- Substituting the lowest coordinate after the tail substitution is exactly
simultaneous substitution by the complete witness vector. -/
theorem explicitWitnessBodyAfterTail_subst_head
    {arity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat) :
    (explicitWitnessBodyAfterTail body values)/[
        shortBinaryNumeralTerm (values 0)] =
      body ⇜ fun index => shortBinaryNumeralTerm (values index) := by
  unfold explicitWitnessBodyAfterTail
  change
    Rew.subst ![shortBinaryNumeralTerm (values 0)] ▹
        ((Rew.subst (fun index : Fin arity =>
          shortBinaryNumeralTerm (values index.succ))).q ▹ body) =
      Rew.subst (fun index => shortBinaryNumeralTerm (values index)) ▹ body
  rw [← TransitiveRewriting.comp_app]
  apply Rewriting.smul_ext'
  apply Rew.ext
  · intro index
    cases index using Fin.cases <;> simp [Rew.comp_app]
  · intro freeIndex
    simp [Rew.comp_app]

/-- Tail substitution commutes through one existential binder and exposes the
one-variable body used above. -/
theorem explicitWitnessExists_subst_tail
    {arity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (arity + 1))
    (values : Fin (arity + 1) -> Nat) :
    (∃⁰ body) ⇜ (fun index : Fin arity =>
        shortBinaryNumeralTerm (values index.succ)) =
      ∃⁰ (explicitWitnessBodyAfterTail body values) := by
  simp [explicitWitnessBodyAfterTail]

/-- Assemble an existential closure from one concrete vector.  The recursion
follows the definition of `exsClosure`: the lowest coordinate is installed in
the terminal payload, while recursive calls add the remaining coordinates from
highest to lowest. -/
noncomputable def buildExplicitWitnessHybridExsClosureFromVector
    {valuation : Nat -> Nat} :
    {arity : Nat} ->
    (body : LO.FirstOrder.ArithmeticSemiformula Nat arity) ->
    (values : Fin arity -> Nat) ->
    ExplicitWitnessHybridSigmaOnePayload valuation
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)) ->
    ExplicitWitnessHybridSigmaOnePayload valuation (∃⁰* body)
  | 0, body, values, terminal => by
      simpa using terminal
  | arity + 1, body, values, terminal => by
      let afterTail := explicitWitnessBodyAfterTail body values
      have hterminal :
          ExplicitWitnessHybridSigmaOnePayload valuation
            (afterTail/[shortBinaryNumeralTerm (values 0)]) :=
        cast
          (congrArg (ExplicitWitnessHybridSigmaOnePayload valuation)
            (explicitWitnessBodyAfterTail_subst_head body values).symm)
          terminal
      have hexists :
          ExplicitWitnessHybridSigmaOnePayload valuation (∃⁰ afterTail) :=
        .existsWitness afterTail (values 0) hterminal
      have htail :
          ExplicitWitnessHybridSigmaOnePayload valuation
            ((∃⁰ body) ⇜ (fun index : Fin arity =>
              shortBinaryNumeralTerm (values index.succ))) :=
        cast
          (congrArg (ExplicitWitnessHybridSigmaOnePayload valuation)
            (explicitWitnessExists_subst_tail body values).symm)
          hexists
      change ExplicitWitnessHybridSigmaOnePayload valuation (∃⁰* ∃⁰ body)
      exact buildExplicitWitnessHybridExsClosureFromVector
        (body := ∃⁰ body)
        (values := fun index : Fin arity => values index.succ)
        htail

#print axioms qpow_singleSubstitution_eq_explicitLast
#print axioms subst_exsItr_explicitLast
#print axioms explicitWitnessBodyAfterTail_subst_head
#print axioms explicitWitnessExists_subst_tail
#print axioms buildExplicitWitnessHybridExsClosureFromVector

end FoundationCompactPAExplicitWitnessExsClosureBuilder
