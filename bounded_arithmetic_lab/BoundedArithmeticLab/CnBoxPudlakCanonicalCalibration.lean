/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakCalibration

/-!
# Canonical Pudlak calibration for finite-consistency Cn boxes

This module exposes the exact obligations needed to calibrate an external
Buss/Pudlak lower-bound source to the canonical finite-consistency Cn target.
It proves these compact obligations are equivalent to the existing checklist
and certificate interfaces, so the canonical route does not weaken the target.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure CanonicalExternalPudlakCalibration
    (lower_source : BussPudlakTheorem5PALowerBoundSource) : Prop where
  formula_code_eq :
    ∀ n : Nat,
      rescaledExternalPudlakCode
        lower_source.conditions.scale_data.scale n =
        partialConsistencyCode n
  length_eq :
    ∀ n : Nat,
      lower_source.pa_length n =
        semanticBAProofLength PAAxiom finiteConsistencyFormula n

theorem canonicalPudlakTarget_target_eq_finiteConsistency
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.target n = finiteConsistencyFormula n :=
  rfl

theorem canonicalPudlakTarget_code_eq_partialConsistency
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        partialConsistencyCode n :=
  rfl

theorem canonicalPudlakTarget_length_eq_semantic
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.length n =
      semanticBAProofLength
        PAAxiom canonicalPudlakTargetFamilySpec.target n :=
  rfl

theorem canonicalPudlakTarget_length_eq_semanticFiniteConsistency
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.length n =
      semanticBAProofLength PAAxiom finiteConsistencyFormula n :=
  rfl

theorem canonicalExternalCalibration_iff_checklist
    (lower_source : BussPudlakTheorem5PALowerBoundSource) :
    CanonicalExternalPudlakCalibration lower_source ↔
      PudlakExternalCalibrationChecklist
        canonicalPudlakTargetFamilySpec lower_source := by
  constructor
  · intro h
    exact {
      formula_code_calibrated := by
        intro n
        rw [canonicalPudlakTarget_code_eq_partialConsistency n]
        exact h.formula_code_eq n
      source_length_matches_spec := by
        intro n
        rw [canonicalPudlakTarget_length_eq_semanticFiniteConsistency n]
        exact h.length_eq n
      spec_length_is_semantic :=
        canonicalPudlakTarget_length_eq_semantic }
  · intro h
    exact {
      formula_code_eq := by
        intro n
        rw [← canonicalPudlakTarget_code_eq_partialConsistency n]
        exact h.formula_code_calibrated n
      length_eq := by
        intro n
        rw [← canonicalPudlakTarget_length_eq_semanticFiniteConsistency n]
        exact h.source_length_matches_spec n }

theorem canonicalExternalCalibration_iff_certificate
    (lower_source : BussPudlakTheorem5PALowerBoundSource) :
    CanonicalExternalPudlakCalibration lower_source ↔
      PudlakExternalCalibrationCertificate
        canonicalPudlakTargetFamilySpec lower_source := by
  exact (canonicalExternalCalibration_iff_checklist lower_source).trans
    (externalCalibrationChecklist_iff_certificate
      canonicalPudlakTargetFamilySpec lower_source)

def CanonicalExternalPudlakCalibration.toCertificate
    {lower_source : BussPudlakTheorem5PALowerBoundSource}
    (calibration : CanonicalExternalPudlakCalibration lower_source) :
    CanonicalFiniteConsistencyPALowerBoundCertificate where
  lower_source := lower_source
  calibration :=
    (canonicalExternalCalibration_iff_checklist lower_source).1 calibration

noncomputable def CanonicalExternalPudlakCalibration.toConcretePALowerBound
    {lower_source : BussPudlakTheorem5PALowerBoundSource}
    (calibration : CanonicalExternalPudlakCalibration lower_source) :
    EventualLowerBound
      (concretePAFormalization
        canonicalPudlakTargetFamilySpec.target
        canonicalPudlakTargetFamilySpec.code).box :=
  calibration.toCertificate.toConcretePALowerBound

end BoundedProofPredicate
end BoundedArithmeticLab
