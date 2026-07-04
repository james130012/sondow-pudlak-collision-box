/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxFiniteConsistencyGenerator
import BoundedArithmeticLab.ConcretePudlakPipeline

/-!
# Pudlák target-family identification for finite-consistency Cn boxes

This module gives the current Cn-box generator a target-family interface that
matches the existing concrete Pudlák pipeline.  It proves the canonical target
family is the same object as the finite-consistency generator, and it records
the exact calibration fields required before an external Buss/Pudlák lower
source can be transported into the concrete PA target.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure PudlakTargetFamilySpec where
  target : Nat → BAFormula
  code : BAFormula → FormulaCode
  box : Nat → CnBox
  statement : Nat → Prop
  length : Nat → Real

noncomputable def canonicalPudlakTargetFamilySpec :
    PudlakTargetFamilySpec where
  target := canonicalFiniteConsistencyGenerator.formula
  code := fun formula =>
    match formula with
    | BAFormula.atom FormulaFamily.partialConsistency n => partialConsistencyCode n
    | _ => { family := FormulaFamily.externalPudlak, index := formula.syntaxSize }
  box := canonicalFiniteConsistencyGenerator.box
  statement := canonicalFiniteConsistencyGenerator.statement
  length :=
    semanticBAProofLength PAAxiom canonicalFiniteConsistencyGenerator.formula

def PudlakTargetFamilyIdentifiesGenerator
    (spec : PudlakTargetFamilySpec) : Prop :=
  (∀ n : Nat, spec.target n = canonicalFiniteConsistencyGenerator.formula n) ∧
  (∀ n : Nat,
    spec.code (spec.target n) =
      canonicalFiniteConsistencyGenerator.formulaCode n) ∧
  (∀ n : Nat, spec.box n = canonicalFiniteConsistencyGenerator.box n) ∧
  (∀ n : Nat,
    spec.statement n ↔ canonicalFiniteConsistencyGenerator.statement n)

theorem canonicalPudlakTargetFamily_identifiesGenerator :
    PudlakTargetFamilyIdentifiesGenerator canonicalPudlakTargetFamilySpec := by
  constructor
  · intro n
    rfl
  constructor
  · intro n
    rfl
  constructor
  · intro n
    rfl
  · intro n
    exact Iff.rfl

def PudlakTargetFamilyCarriesPAFiniteConsistency
    (spec : PudlakTargetFamilySpec) : Prop :=
  ∀ n : Nat,
    CnBoxCarriesPAFiniteConsistency (spec.box n) ↔ spec.statement n

theorem canonicalPudlakTargetFamily_carriesPAFiniteConsistency :
    PudlakTargetFamilyCarriesPAFiniteConsistency
      canonicalPudlakTargetFamilySpec := by
  intro n
  exact canonicalGenerator_box_carriesPAFiniteConsistency_iff n

structure PudlakTargetFamilyIdentificationCertificate
    (spec : PudlakTargetFamilySpec) : Prop where
  identifies_generator : PudlakTargetFamilyIdentifiesGenerator spec
  carries_pa_finite_consistency :
    PudlakTargetFamilyCarriesPAFiniteConsistency spec
  same_object :
    ∀ n : Nat,
      spec.box n = canonicalFiniteConsistencyGenerator.box n ∧
      spec.target n = finiteConsistencyFormula n ∧
      spec.code (spec.target n) = partialConsistencyCode n

theorem canonicalPudlakTargetFamily_identificationCertificate :
    PudlakTargetFamilyIdentificationCertificate
      canonicalPudlakTargetFamilySpec where
  identifies_generator := canonicalPudlakTargetFamily_identifiesGenerator
  carries_pa_finite_consistency :=
    canonicalPudlakTargetFamily_carriesPAFiniteConsistency
  same_object := by
    intro n
    exact ⟨rfl, rfl, rfl⟩

structure PudlakExternalCalibrationCertificate
    (spec : PudlakTargetFamilySpec)
    (lower_source : BussPudlakTheorem5PALowerBoundSource) : Prop where
  formula_code_eq :
    ∀ n : Nat,
      rescaledExternalPudlakCode
        lower_source.conditions.scale_data.scale n =
        spec.code (spec.target n)
  length_eq :
    ∀ n : Nat,
      lower_source.pa_length n = spec.length n
  spec_length_eq_semantic :
    ∀ n : Nat,
      spec.length n = semanticBAProofLength PAAxiom spec.target n

def PudlakExternalCalibrationCertificate.toConcreteFormulaLengthCalibration
    {spec : PudlakTargetFamilySpec}
    {lower_source : BussPudlakTheorem5PALowerBoundSource}
    (cert : PudlakExternalCalibrationCertificate spec lower_source) :
    ConcreteBussPudlakFormulaLengthCalibration
      spec.target spec.code where
  lower_source := lower_source
  formula_code_eq := cert.formula_code_eq
  length_eq := by
    intro n
    rw [cert.length_eq n, cert.spec_length_eq_semantic n]

end BoundedProofPredicate
end BoundedArithmeticLab
