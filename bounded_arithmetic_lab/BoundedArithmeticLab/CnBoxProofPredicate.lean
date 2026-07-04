/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxEncoding

/-!
# Bounded PA proof predicate layer for finite-consistency Cn boxes

This module connects the executable finite-consistency `CnBox` layer to a
bounded proof predicate over the project-local `BAProofObject PAAxiom` carrier.
It still does not claim a full PA proof checker or the Pudlák theorem body; it
only fixes the audit-facing predicate interface and proves that S21 proof
objects embed into PA proof objects without increasing size.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

def contradictionFormula : BAFormula :=
  BAFormula.falsum

def ProofWithinBound (Ax : BAFormula → Prop)
    (proof : BAProofObject Ax) (formula : BAFormula) (bound : Nat) : Prop :=
  proof.conclusion = formula ∧ proof.size ≤ bound

abbrev ProofPAWithinBound :=
  ProofWithinBound PAAxiom

abbrev ProofS21WithinBound :=
  ProofWithinBound BussS21Axiom

def ProvableWithinBound (Ax : BAFormula → Prop)
    (formula : BAFormula) (bound : Nat) : Prop :=
  ∃ proof : BAProofObject Ax, ProofWithinBound Ax proof formula bound

abbrev PAProvableWithinBound :=
  ProvableWithinBound PAAxiom

abbrev S21ProvableWithinBound :=
  ProvableWithinBound BussS21Axiom

def NoProofWithinBound (Ax : BAFormula → Prop)
    (formula : BAFormula) (bound : Nat) : Prop :=
  ¬ ProvableWithinBound Ax formula bound

abbrev NoPAProofWithinBound :=
  NoProofWithinBound PAAxiom

abbrev NoS21ProofWithinBound :=
  NoProofWithinBound BussS21Axiom

def PAFiniteConsistencyStatement (bound : Nat) : Prop :=
  NoPAProofWithinBound contradictionFormula bound

def S21FiniteConsistencyStatement (bound : Nat) : Prop :=
  NoS21ProofWithinBound contradictionFormula bound

theorem proofWithinBound_iff_components
    {Ax : BAFormula → Prop}
    (proof : BAProofObject Ax) (formula : BAFormula) (bound : Nat) :
    ProofWithinBound Ax proof formula bound ↔
      proof.conclusion = formula ∧ proof.size ≤ bound :=
  Iff.rfl

theorem paProofWithinBound_of_s21ProofWithinBound
    {proof : BAProofObject BussS21Axiom} {formula : BAFormula}
    {bound : Nat}
    (h : ProofS21WithinBound proof formula bound) :
    ProofPAWithinBound proof.mapS21ToPA formula bound := by
  rcases h with ⟨hconcl, hsize⟩
  exact ⟨hconcl, by simpa [BAProofObject.size_mapS21ToPA] using hsize⟩

theorem paProvableWithinBound_of_s21ProvableWithinBound
    {formula : BAFormula} {bound : Nat}
    (h : S21ProvableWithinBound formula bound) :
    PAProvableWithinBound formula bound := by
  rcases h with ⟨proof, hproof⟩
  exact ⟨proof.mapS21ToPA, paProofWithinBound_of_s21ProofWithinBound hproof⟩

theorem noS21ProofWithinBound_of_noPAProofWithinBound
    {formula : BAFormula} {bound : Nat}
    (h : NoPAProofWithinBound formula bound) :
    NoS21ProofWithinBound formula bound := by
  intro hs21
  exact h (paProvableWithinBound_of_s21ProvableWithinBound hs21)

theorem s21FiniteConsistency_of_paFiniteConsistency {bound : Nat}
    (h : PAFiniteConsistencyStatement bound) :
    S21FiniteConsistencyStatement bound :=
  noS21ProofWithinBound_of_noPAProofWithinBound h

structure BoundedPAPredicateCnBoxAlignment (box : CnBox) : Prop where
  certifies : box.Certifies
  target_formula : box.formula = finiteConsistencyFormula box.n
  target_code : box.formulaCode = partialConsistencyCode box.n
  predicate_exact :
    ∀ proof : BAProofObject PAAxiom,
      ProofPAWithinBound proof contradictionFormula box.n ↔
        proof.conclusion = contradictionFormula ∧ proof.size ≤ box.n

theorem mkFiniteConsistencyCnBox_predicateAlignment (n : Nat) :
    BoundedPAPredicateCnBoxAlignment (mkFiniteConsistencyCnBox n) where
  certifies := mkFiniteConsistencyCnBox_certifies n
  target_formula := rfl
  target_code := rfl
  predicate_exact := by
    intro proof
    rfl

theorem mkFiniteConsistencyCnBox_paFiniteConsistency_statement (n : Nat) :
    PAFiniteConsistencyStatement (mkFiniteConsistencyCnBox n).n ↔
      NoPAProofWithinBound contradictionFormula n := by
  rfl

theorem mkFiniteConsistencyCnBox_s21FiniteConsistency_of_pa
    {n : Nat}
    (h : PAFiniteConsistencyStatement (mkFiniteConsistencyCnBox n).n) :
    S21FiniteConsistencyStatement n :=
  s21FiniteConsistency_of_paFiniteConsistency h

end BoundedProofPredicate
end BoundedArithmeticLab
