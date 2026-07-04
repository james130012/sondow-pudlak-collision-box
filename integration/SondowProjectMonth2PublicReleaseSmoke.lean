/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth2SondowAcceptedCertificateSurface

/-!
# Month 2 public release smoke surface

This module is a thin external-import smoke test for the Month 2 Sondow
accepted-certificate release surface.  It imports the public Month 2 surface
and re-exposes only the theorem-level handles that a paper or audit entry
point should consume.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth2PublicReleaseSmoke

universe u

open SondowProjectMonth2SondowAcceptedCertificateSurface
open SondowProjectMonth2SondowAcceptedCertificateSurface.Month2SondowAcceptedPublicRationalityTheorem

structure Month2PublicReleaseSmokeStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) : Prop where
  verified_public_release_theorem :
    Month2VerifiedPublicReleaseTheoremStatement
      (kit.verified_public_release_inputs h_rat)
  verified_public_release_theorem_iff_package_nonempty :
    Month2VerifiedPublicReleaseTheoremStatement
        (kit.verified_public_release_inputs h_rat) ↔
      Nonempty
        (Month2VerifiedPublicReleaseTheoremPackage
          (kit.verified_public_release_inputs h_rat))
  citation_checklist :
    Month2PublicCitationAuditChecklistStatement kit h_rat
  open_source_release_surface :
    Month2OpenSourceReleaseSurfaceStatement kit h_rat
  no_hidden_assumptions :
    NoHiddenAssumptionsStatement (kit.with_rationality h_rat)
  accepted_definition_exact :
    ∀ n : ℕ,
      Month2SondowAccepted n ↔
        _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  source_equivalence_same_object :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n
  root_accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  compiler_consumption_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
        (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
          Nonempty
            (Month2SondowAcceptedCompiledCertificateAt
              (kit.with_rationality h_rat).paper_surface.surface n) ∧
            ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
              BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
                BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
                ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
                  |>.componentCertificateOfFullCertificate hchecked)

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2PublicReleaseSmokeStatement kit h_rat where
  verified_public_release_theorem :=
    PublicInfrastructureKit.month2_verified_public_release_theorem_statement
      kit h_rat
  verified_public_release_theorem_iff_package_nonempty :=
    PublicInfrastructureKit.month2_verified_public_release_theorem_statement_iff_package_nonempty
      kit h_rat
  citation_checklist :=
    PublicInfrastructureKit.month2_public_citation_audit_checklist_statement
      kit h_rat
  open_source_release_surface :=
    PublicInfrastructureKit.month2_open_source_release_surface_statement
      kit h_rat
  no_hidden_assumptions :=
    PublicInfrastructureKit.no_hidden_assumptions_of_rationality kit h_rat
  accepted_definition_exact :=
    PublicInfrastructureKit.verified_public_release_accepted_definition_exact
      kit h_rat
  source_equivalence_same_object :=
    PublicInfrastructureKit.verified_public_release_source_equivalence_same_object
      kit h_rat
  accepted_eventually :=
    PublicInfrastructureKit.verified_public_release_accepted_eventually
      kit h_rat
  root_accepted_eventually :=
    PublicInfrastructureKit.verified_public_release_root_accepted_eventually
      kit h_rat
  compiler_consumption_after_threshold := fun hn =>
    PublicInfrastructureKit.verified_public_release_compiler_consumption_after_rationality_threshold
      kit h_rat hn

theorem statement_iff_verified_release_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2PublicReleaseSmokeStatement kit h_rat ↔
      Nonempty
        (Month2VerifiedPublicReleaseTheoremPackage
          (kit.verified_public_release_inputs h_rat)) := by
  constructor
  · intro _h
    exact
      PublicInfrastructureKit.month2_verified_public_release_theorem_package_nonempty
        kit h_rat
  · intro _h
    exact statement kit h_rat

theorem accepted_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  (statement kit h_rat).accepted_eventually

theorem compiler_consumption_after_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
      (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
        Nonempty
          (Month2SondowAcceptedCompiledCertificateAt
            (kit.with_rationality h_rat).paper_surface.surface n) ∧
          ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
            BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
              BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
              ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
                |>.componentCertificateOfFullCertificate hchecked) :=
  (statement kit h_rat).compiler_consumption_after_threshold hn

#check Month2PublicReleaseSmokeStatement
#check statement
#check statement_iff_verified_release_package_nonempty
#check accepted_eventually
#check compiler_consumption_after_threshold

end SondowProjectMonth2PublicReleaseSmoke
end SondowMainCheckedCodeBridge
