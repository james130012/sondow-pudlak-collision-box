/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth2PublicReleaseSmoke

/-!
# Month 2 canonical import surface

This module is the stable single-import surface for the Month 2 Sondow
accepted-certificate construction route.  It delegates to the public release
smoke surface and gives auditors a compact endpoint to check.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth2CanonicalImportSurface

universe u

open SondowProjectMonth2SondowAcceptedCertificateSurface
open SondowProjectMonth2SondowAcceptedCertificateSurface.Month2SondowAcceptedPublicRationalityTheorem
open SondowProjectMonth2PublicReleaseSmoke

abbrev Month2CanonicalPublicReleaseStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) : Prop :=
  Month2PublicReleaseSmokeStatement kit h_rat

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2CanonicalPublicReleaseStatement kit h_rat :=
  SondowProjectMonth2PublicReleaseSmoke.statement kit h_rat

theorem statement_iff_verified_release_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2CanonicalPublicReleaseStatement kit h_rat ↔
      Nonempty
        (Month2VerifiedPublicReleaseTheoremPackage
          (kit.verified_public_release_inputs h_rat)) :=
  SondowProjectMonth2PublicReleaseSmoke.statement_iff_verified_release_package_nonempty
    kit h_rat

theorem accepted_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  SondowProjectMonth2PublicReleaseSmoke.accepted_eventually kit h_rat

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
  SondowProjectMonth2PublicReleaseSmoke.compiler_consumption_after_threshold
    kit h_rat hn

#check Month2CanonicalPublicReleaseStatement
#check statement
#check statement_iff_verified_release_package_nonempty
#check accepted_eventually
#check compiler_consumption_after_threshold

end SondowProjectMonth2CanonicalImportSurface
end SondowMainCheckedCodeBridge
