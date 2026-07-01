/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.SondowComponentExportCompiler

/-!
# Rationality to Sondow component exports

This module is the audit-facing upper-side bridge.

The point is deliberately narrow: rationality of gamma is not treated as an
S21 proof object.  Instead, a `SondowRationalityToComponentExports` package must
explicitly compile a gamma-rationality witness into the five project component
proof exports.  Once that package and the concrete Buss/Pudlak calibration are
available, the existing component collision yields the negation of the
rationality witness.
-/

namespace BoundedArithmeticLab

/-- A named rationality context.  In the main repository this is instantiated
with `is_rational euler_mascheroni`; the sidecar keeps it abstract so the
bounded-arithmetic layer stays lightweight. -/
structure GammaRationalityContext where
  Rationality : Prop

def GammaRationalityWitness (ctx : GammaRationalityContext) : Prop :=
  ctx.Rationality

/-- Upper-side export theorem required from the main Sondow/rationality
development: under the gamma-rationality witness, produce the five component
S21 proof exports with their size bounds. -/
structure SondowRationalityToComponentExports
    (ctx : GammaRationalityContext) (bounds : SondowComponentBounds) where
  exports_of_rationality :
    GammaRationalityWitness ctx →
      SondowMainReproofBlockCertificatesEventually
        sondowProjectComponentFormulas bounds

structure SondowRationalityToComponentSystemCertificates
    (ctx : GammaRationalityContext) {bounds : SondowComponentBounds}
    (systems :
      SondowComponentCertificateSystems.{u}
        sondowProjectComponentFormulas bounds) where
  certificates_of_rationality :
    GammaRationalityWitness ctx →
      SondowComponentSystemCertificatesEventually systems

structure SondowRationalityToProjectProofObjectCertificates
    (ctx : GammaRationalityContext) (bounds : SondowComponentBounds) where
  certificates_of_rationality :
    GammaRationalityWitness ctx →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ cert : SondowComponentCertificate,
          SondowComponentCertificate.ProofObjectSystemValid
            sondowProjectComponentFormulas bounds n cert

noncomputable def
    SondowRationalityToProjectProofObjectCertificates.toComponentSystemCertificates
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    (hcerts : SondowRationalityToProjectProofObjectCertificates ctx bounds) :
    SondowRationalityToComponentSystemCertificates ctx
      (sondowProjectProofObjectCertificateSystems bounds) where
  certificates_of_rationality := by
    intro hgamma
    rcases hcerts.certificates_of_rationality hgamma with ⟨N, hN⟩
    refine ⟨?exists_eventually⟩
    exact ⟨N, fun n hn => by
      rcases hN n hn with ⟨cert, hvalid⟩
      exact ⟨hvalid.toSystemCertificateAt⟩⟩

noncomputable def SondowRationalityToComponentExports.ofComponentSystems
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    {systems :
      SondowComponentCertificateSystems.{u}
        sondowProjectComponentFormulas bounds}
    (hcerts :
      SondowRationalityToComponentSystemCertificates ctx systems) :
    SondowRationalityToComponentExports ctx bounds where
  exports_of_rationality := by
    intro hgamma
    exact
      (hcerts.certificates_of_rationality hgamma)
        |>.toMainReproofBlockCertificatesEventually

noncomputable def
    SondowRationalityToComponentExports.ofProjectProofObjectCertificates
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    (hcerts : SondowRationalityToProjectProofObjectCertificates ctx bounds) :
    SondowRationalityToComponentExports ctx bounds :=
  SondowRationalityToComponentExports.ofComponentSystems
    hcerts.toComponentSystemCertificates

def SondowRationalityToComponentExports.componentSizeCertificates
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    (h : SondowRationalityToComponentExports ctx bounds)
    (hgamma : GammaRationalityWitness ctx) :
    SondowProjectComponentSizeCertificatesEventually bounds :=
  (h.exports_of_rationality hgamma).toProjectComponentSizeCertificatesEventually

/-- The full sidecar collision input for the gamma-rationality route.  The
calibration field is where the concrete Buss/Pudlak lower-bound source is
required and aligned with the project reflection-graft target. -/
structure SondowRationalityCollisionInputs
    (ctx : GammaRationalityContext) where
  bounds : SondowComponentBounds
  exports : SondowRationalityToComponentExports ctx bounds
  calibration :
    ConcreteBussPudlakFormulaLengthCalibration
      sondowProjectComponentFormulas.target sondowProjectComponentCode

noncomputable def SondowRationalityCollisionInputs.ofComponentSystems
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    {systems :
      SondowComponentCertificateSystems.{u}
        sondowProjectComponentFormulas bounds}
    (hcerts :
      SondowRationalityToComponentSystemCertificates ctx systems)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    SondowRationalityCollisionInputs ctx where
  bounds := bounds
  exports :=
    SondowRationalityToComponentExports.ofComponentSystems hcerts
  calibration := calibration

noncomputable def SondowRationalityCollisionInputs.ofProjectProofObjectCertificates
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    (hcerts : SondowRationalityToProjectProofObjectCertificates ctx bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    SondowRationalityCollisionInputs ctx where
  bounds := bounds
  exports :=
    SondowRationalityToComponentExports.ofProjectProofObjectCertificates
      hcerts
  calibration := calibration

theorem false_of_gamma_rationality_witness
    {ctx : GammaRationalityContext}
    (h : SondowRationalityCollisionInputs ctx)
    (hgamma : GammaRationalityWitness ctx) :
    False :=
  collision_of_project_sondow_component_exports_formula_length_calibrated_pudlak
    (h.exports.exports_of_rationality hgamma) h.calibration

theorem not_gamma_rationality_witness
    {ctx : GammaRationalityContext}
    (h : SondowRationalityCollisionInputs ctx) :
    ¬ GammaRationalityWitness ctx := by
  intro hgamma
  exact false_of_gamma_rationality_witness h hgamma

theorem not_gamma_rationality_witness_of_exports_and_calibration
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    (exports : SondowRationalityToComponentExports ctx bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ GammaRationalityWitness ctx :=
  not_gamma_rationality_witness
    { bounds := bounds
      exports := exports
      calibration := calibration }

theorem
    not_gamma_rationality_witness_of_component_systems_and_calibration
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    {systems :
      SondowComponentCertificateSystems.{u}
        sondowProjectComponentFormulas bounds}
    (hcerts :
      SondowRationalityToComponentSystemCertificates ctx systems)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ GammaRationalityWitness ctx :=
  not_gamma_rationality_witness
    (SondowRationalityCollisionInputs.ofComponentSystems
      hcerts calibration)

theorem
    not_gamma_rationality_witness_of_project_proof_object_certificates
    {ctx : GammaRationalityContext} {bounds : SondowComponentBounds}
    (hcerts : SondowRationalityToProjectProofObjectCertificates ctx bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ GammaRationalityWitness ctx :=
  not_gamma_rationality_witness
    (SondowRationalityCollisionInputs.ofProjectProofObjectCertificates
      hcerts calibration)

def SondowRationalityCollisionInputs.lowerSource
    {ctx : GammaRationalityContext}
    (h : SondowRationalityCollisionInputs ctx) :
    BussPudlakTheorem5PALowerBoundSource :=
  h.calibration.lower_source

theorem SondowRationalityCollisionInputs.formula_code_calibrated
    {ctx : GammaRationalityContext}
    (h : SondowRationalityCollisionInputs ctx) (n : ℕ) :
    rescaledExternalPudlakCode
        h.lowerSource.conditions.scale_data.scale n =
      sondowProjectComponentCode (sondowProjectComponentFormulas.target n) :=
  h.calibration.formula_code_eq n

theorem SondowRationalityCollisionInputs.length_calibrated
    {ctx : GammaRationalityContext}
    (h : SondowRationalityCollisionInputs ctx) (n : ℕ) :
    h.lowerSource.pa_length n =
      semanticBAProofLength PAAxiom sondowProjectComponentFormulas.target n :=
  h.calibration.length_eq n

def mainGammaRationalityContext (MainRationality : Prop) :
    GammaRationalityContext where
  Rationality := MainRationality

/-- Thin adapter for the final main-library step.  To connect this sidecar to
the main theorem, instantiate `MainRationality` with
`is_rational euler_mascheroni`. -/
structure MainGammaRationalityBridge
    (MainRationality : Prop) (ctx : GammaRationalityContext) where
  to_gamma_witness :
    MainRationality → GammaRationalityWitness ctx

def MainGammaRationalityBridge.refl (MainRationality : Prop) :
    MainGammaRationalityBridge MainRationality
      (mainGammaRationalityContext MainRationality) where
  to_gamma_witness := fun h => h

theorem not_main_rationality_of_gamma_collision
    {MainRationality : Prop} {ctx : GammaRationalityContext}
    (bridge : MainGammaRationalityBridge MainRationality ctx)
    (collision : SondowRationalityCollisionInputs ctx) :
    ¬ MainRationality := by
  intro hmain
  exact false_of_gamma_rationality_witness collision
    (bridge.to_gamma_witness hmain)

theorem not_main_rationality_of_refl_gamma_collision
    {MainRationality : Prop}
    (collision :
      SondowRationalityCollisionInputs
        (mainGammaRationalityContext MainRationality)) :
    ¬ MainRationality :=
  not_main_rationality_of_gamma_collision
    (MainGammaRationalityBridge.refl MainRationality) collision

end BoundedArithmeticLab
