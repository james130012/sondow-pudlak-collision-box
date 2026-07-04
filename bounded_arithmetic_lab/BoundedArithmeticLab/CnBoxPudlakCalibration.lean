/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakTargetFamily

/-!
# Cn-box Pudlak calibration route

This module packages the audit-facing calibration checklist for transporting an
external Buss/Pudlak lower source into the concrete PA lower-bound interface.
The key invariant is that the checklist is exactly equivalent to the existing
calibration certificate, so this layer adds no new mathematical assumption.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure PudlakExternalCalibrationChecklist
    (spec : PudlakTargetFamilySpec)
    (lower_source : BussPudlakTheorem5PALowerBoundSource) : Prop where
  formula_code_calibrated :
    ∀ n : Nat,
      rescaledExternalPudlakCode
        lower_source.conditions.scale_data.scale n =
        spec.code (spec.target n)
  source_length_matches_spec :
    ∀ n : Nat,
      lower_source.pa_length n = spec.length n
  spec_length_is_semantic :
    ∀ n : Nat,
      spec.length n = semanticBAProofLength PAAxiom spec.target n

theorem externalCalibrationChecklist_iff_certificate
    (spec : PudlakTargetFamilySpec)
    (lower_source : BussPudlakTheorem5PALowerBoundSource) :
    PudlakExternalCalibrationChecklist spec lower_source ↔
      PudlakExternalCalibrationCertificate spec lower_source := by
  constructor
  · intro h
    exact {
      formula_code_eq := h.formula_code_calibrated
      length_eq := h.source_length_matches_spec
      spec_length_eq_semantic := h.spec_length_is_semantic }
  · intro h
    exact {
      formula_code_calibrated := h.formula_code_eq
      source_length_matches_spec := h.length_eq
      spec_length_is_semantic := h.spec_length_eq_semantic }

structure ConcretePudlakTargetLowerRoute
    (spec : PudlakTargetFamilySpec) where
  lower_source : BussPudlakTheorem5PALowerBoundSource
  identification : PudlakTargetFamilyIdentificationCertificate spec
  calibration : PudlakExternalCalibrationCertificate spec lower_source

def ConcretePudlakTargetLowerRoute.toFormulaLengthCalibration
    {spec : PudlakTargetFamilySpec}
    (route : ConcretePudlakTargetLowerRoute spec) :
    ConcreteBussPudlakFormulaLengthCalibration spec.target spec.code :=
  route.calibration.toConcreteFormulaLengthCalibration

def ConcretePudlakTargetLowerRoute.toBoxCalibration
    {spec : PudlakTargetFamilySpec}
    (route : ConcretePudlakTargetLowerRoute spec) :
    ConcreteBussPudlakBoxCalibration spec.target spec.code :=
  route.toFormulaLengthCalibration.toBoxCalibration

def ConcretePudlakTargetLowerRoute.toExactLowerForPA
    {spec : PudlakTargetFamilySpec}
    (route : ConcretePudlakTargetLowerRoute spec) :
    ConcreteBussPudlakExactLowerForPA spec.target spec.code :=
  route.toBoxCalibration.toExactLower

def ConcretePudlakTargetLowerRoute.toLowerForPA
    {spec : PudlakTargetFamilySpec}
    (route : ConcretePudlakTargetLowerRoute spec) :
    ConcreteBussPudlakLowerForPA spec.target spec.code :=
  route.toExactLowerForPA.toLowerForPA

def ConcretePudlakTargetLowerRoute.toConcretePALowerBound
    {spec : PudlakTargetFamilySpec}
    (route : ConcretePudlakTargetLowerRoute spec) :
    EventualLowerBound (concretePAFormalization spec.target spec.code).box :=
  route.toExactLowerForPA.toLowerBound

structure ConcretePudlakTargetLowerChecklist
    (spec : PudlakTargetFamilySpec) where
  lower_source : BussPudlakTheorem5PALowerBoundSource
  identification : PudlakTargetFamilyIdentificationCertificate spec
  checklist : PudlakExternalCalibrationChecklist spec lower_source

def ConcretePudlakTargetLowerChecklist.toRoute
    {spec : PudlakTargetFamilySpec}
    (checklist : ConcretePudlakTargetLowerChecklist spec) :
    ConcretePudlakTargetLowerRoute spec where
  lower_source := checklist.lower_source
  identification := checklist.identification
  calibration :=
    (externalCalibrationChecklist_iff_certificate
      spec checklist.lower_source).1 checklist.checklist

def ConcretePudlakTargetLowerChecklist.toConcretePALowerBound
    {spec : PudlakTargetFamilySpec}
    (checklist : ConcretePudlakTargetLowerChecklist spec) :
    EventualLowerBound (concretePAFormalization spec.target spec.code).box :=
  checklist.toRoute.toConcretePALowerBound

structure CanonicalFiniteConsistencyPALowerBoundCertificate where
  lower_source : BussPudlakTheorem5PALowerBoundSource
  calibration :
    PudlakExternalCalibrationChecklist
      canonicalPudlakTargetFamilySpec lower_source

noncomputable def CanonicalFiniteConsistencyPALowerBoundCertificate.toChecklist
    (cert : CanonicalFiniteConsistencyPALowerBoundCertificate) :
    ConcretePudlakTargetLowerChecklist canonicalPudlakTargetFamilySpec where
  lower_source := cert.lower_source
  identification := canonicalPudlakTargetFamily_identificationCertificate
  checklist := cert.calibration

noncomputable def CanonicalFiniteConsistencyPALowerBoundCertificate.toRoute
    (cert : CanonicalFiniteConsistencyPALowerBoundCertificate) :
    ConcretePudlakTargetLowerRoute canonicalPudlakTargetFamilySpec :=
  cert.toChecklist.toRoute

noncomputable def CanonicalFiniteConsistencyPALowerBoundCertificate.toLowerForPA
    (cert : CanonicalFiniteConsistencyPALowerBoundCertificate) :
    ConcreteBussPudlakLowerForPA
      canonicalPudlakTargetFamilySpec.target
      canonicalPudlakTargetFamilySpec.code :=
  cert.toRoute.toLowerForPA

noncomputable def
    CanonicalFiniteConsistencyPALowerBoundCertificate.toConcretePALowerBound
    (cert : CanonicalFiniteConsistencyPALowerBoundCertificate) :
    EventualLowerBound
      (concretePAFormalization
        canonicalPudlakTargetFamilySpec.target
        canonicalPudlakTargetFamilySpec.code).box :=
  cert.toRoute.toConcretePALowerBound

theorem canonicalFiniteConsistencyPALowerBoundCertificate_carriesPA
    (cert : CanonicalFiniteConsistencyPALowerBoundCertificate) :
    PudlakTargetFamilyCarriesPAFiniteConsistency
      canonicalPudlakTargetFamilySpec :=
  cert.toChecklist.identification.carries_pa_finite_consistency

end BoundedProofPredicate
end BoundedArithmeticLab
