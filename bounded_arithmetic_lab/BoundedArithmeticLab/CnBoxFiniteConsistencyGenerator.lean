/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxProofPredicate

/-!
# Finite-consistency generator certificates for Cn boxes

This module packages the canonical finite-consistency generator and records the
audit-facing equivalence between the generated `CnBox` and the bounded PA proof
predicate statement.  It deliberately remains at the generator/certificate
interface layer; a full PA checker and the Pudlák lower-bound theorem body are
separate downstream obligations.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure FiniteConsistencyGenerator where
  formula : Nat → BAFormula
  formulaCode : Nat → FormulaCode
  box : Nat → CnBox
  statement : Nat → Prop

def canonicalFiniteConsistencyGenerator : FiniteConsistencyGenerator where
  formula := finiteConsistencyFormula
  formulaCode := partialConsistencyCode
  box := mkFiniteConsistencyCnBox
  statement := PAFiniteConsistencyStatement

theorem canonicalGenerator_formula_eq (n : Nat) :
    canonicalFiniteConsistencyGenerator.formula n =
      finiteConsistencyFormula n :=
  rfl

theorem canonicalGenerator_formulaCode_eq (n : Nat) :
    canonicalFiniteConsistencyGenerator.formulaCode n =
      partialConsistencyCode n :=
  rfl

theorem canonicalGenerator_box_eq (n : Nat) :
    canonicalFiniteConsistencyGenerator.box n =
      mkFiniteConsistencyCnBox n :=
  rfl

theorem canonicalGenerator_statement_iff (n : Nat) :
    canonicalFiniteConsistencyGenerator.statement n ↔
      PAFiniteConsistencyStatement n :=
  Iff.rfl

def CnBoxCarriesPAFiniteConsistency (box : CnBox) : Prop :=
  box.Certifies ∧ BoundedPAPredicateCnBoxAlignment box ∧
    PAFiniteConsistencyStatement box.n

theorem mkFiniteConsistencyCnBox_carriesPAFiniteConsistency_iff
    (n : Nat) :
    CnBoxCarriesPAFiniteConsistency (mkFiniteConsistencyCnBox n) ↔
      PAFiniteConsistencyStatement n := by
  constructor
  · intro h
    exact h.2.2
  · intro h
    exact ⟨mkFiniteConsistencyCnBox_certifies n,
      mkFiniteConsistencyCnBox_predicateAlignment n, h⟩

theorem canonicalGenerator_box_carriesPAFiniteConsistency_iff
    (n : Nat) :
    CnBoxCarriesPAFiniteConsistency
        (canonicalFiniteConsistencyGenerator.box n) ↔
      canonicalFiniteConsistencyGenerator.statement n := by
  exact mkFiniteConsistencyCnBox_carriesPAFiniteConsistency_iff n

structure FiniteConsistencyGenerationCertificate (n : Nat) where
  box : CnBox
  box_eq : box = mkFiniteConsistencyCnBox n
  box_certifies : box.Certifies
  predicate_alignment : BoundedPAPredicateCnBoxAlignment box
  carries_iff :
    CnBoxCarriesPAFiniteConsistency box ↔ PAFiniteConsistencyStatement n

def mkFiniteConsistencyGenerationCertificate (n : Nat) :
    FiniteConsistencyGenerationCertificate n where
  box := mkFiniteConsistencyCnBox n
  box_eq := rfl
  box_certifies := mkFiniteConsistencyCnBox_certifies n
  predicate_alignment := mkFiniteConsistencyCnBox_predicateAlignment n
  carries_iff := mkFiniteConsistencyCnBox_carriesPAFiniteConsistency_iff n

structure FiniteConsistencySameObjectCertificate (n : Nat) : Prop where
  formula_exact :
    canonicalFiniteConsistencyGenerator.formula n =
      finiteConsistencyFormula n
  formulaCode_exact :
    canonicalFiniteConsistencyGenerator.formulaCode n =
      partialConsistencyCode n
  box_exact :
    canonicalFiniteConsistencyGenerator.box n =
      mkFiniteConsistencyCnBox n
  statement_iff :
    canonicalFiniteConsistencyGenerator.statement n ↔
      PAFiniteConsistencyStatement n

theorem canonicalFiniteConsistency_sameObjectCertificate (n : Nat) :
    FiniteConsistencySameObjectCertificate n where
  formula_exact := rfl
  formulaCode_exact := rfl
  box_exact := rfl
  statement_iff := Iff.rfl

structure S21ToPABoundedCompilerCertificate
    (proof : BAProofObject BussS21Axiom)
    (formula : BAFormula) (bound : Nat) : Prop where
  s21_within : ProofS21WithinBound proof formula bound
  pa_within : ProofPAWithinBound proof.mapS21ToPA formula bound
  size_preserved : proof.mapS21ToPA.size = proof.size

theorem S21ToPABoundedCompilerCertificate.of_s21Within
    {proof : BAProofObject BussS21Axiom}
    {formula : BAFormula} {bound : Nat}
    (h : ProofS21WithinBound proof formula bound) :
    S21ToPABoundedCompilerCertificate proof formula bound where
  s21_within := h
  pa_within := paProofWithinBound_of_s21ProofWithinBound h
  size_preserved := BAProofObject.size_mapS21ToPA proof

end BoundedProofPredicate
end BoundedArithmeticLab
