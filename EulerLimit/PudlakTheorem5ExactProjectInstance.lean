/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.ExternalPudlakRawEncoding

/-!
# Month 4 Pudlak theorem 5 exact project instance surface

This module packages the current theorem-5 boundary as an auditable external
literature certificate.  It does not internalize Pudlak's theorem 5; it records
that the remaining external input is exactly the rescaled lower-bound witness
on the raw PA finite-consistency family, together with the power-bound/rescaled
code equivalence already proved in the project.
-/

namespace PudlakTheorem5ExactProjectInstance

structure Instance where
  certificate : LiteraturePudlakTheorem5LowerBoundCertificate
  certificate_eq_external :
    certificate = literaturePudlakTheorem5ExternalLowerBoundCertificate
  rescaled_certificate : LiteraturePudlakTheorem5RescaledLowerBoundCertificate
  rescaled_certificate_eq_external :
    rescaled_certificate =
      literaturePudlakTheorem5ExternalRescaledLowerBoundCertificate
  certificate_roundtrip :
    certificate.toRescaledCertificate.toPowerBoundCertificate.scale_data =
      certificate.scale_data ∧
      (∀ n : ℕ,
        (certificate.toRescaledCertificate.toPowerBoundCertificate
          |>.scale_data).powerBoundRawCode n =
            certificate.scale_data.powerBoundRawCode n)
  rescaled_certificate_roundtrip :
    rescaled_certificate.toPowerBoundCertificate.toRescaledCertificate.scale_data =
      rescaled_certificate.scale_data ∧
      (∀ n : ℕ,
        (rescaled_certificate.toPowerBoundCertificate.toRescaledCertificate
          |>.scale_data).rescaledRawCode n =
            rescaled_certificate.scale_data.rescaledRawCode n)
  rescaled_raw_eq_power_bound :
    ∀ n : ℕ,
      literaturePudlakTheorem5ExternalScaleData.rescaledRawCode n =
        literaturePudlakTheorem5ExternalScaleData.powerBoundRawCode n
  power_bound_eq_rescaled_pudlak :
    ∀ n : ℕ,
      literaturePudlakTheorem5ExternalScaleData.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          literaturePudlakTheorem5ExternalScaleData.scale n
  power_bound_iff_rescaled :
    LiteraturePudlakTheorem5PowerBoundLowerBound
        literaturePudlakTheorem5ExternalScaleData ↔
      StrongRescaledExternalStrengthenedLowerBound
        literaturePudlakTheorem5ExternalScaleData.rawCode
        literaturePudlakTheorem5ExternalScaleData.scale

noncomputable def external : Instance where
  certificate := literaturePudlakTheorem5ExternalLowerBoundCertificate
  certificate_eq_external := rfl
  rescaled_certificate :=
    literaturePudlakTheorem5ExternalRescaledLowerBoundCertificate
  rescaled_certificate_eq_external := rfl
  certificate_roundtrip :=
    audit_theorem5_powerBound_certificateRoundTrip
      literaturePudlakTheorem5ExternalLowerBoundCertificate
  rescaled_certificate_roundtrip :=
    audit_theorem5_rescaled_certificateRoundTrip
      literaturePudlakTheorem5ExternalRescaledLowerBoundCertificate
  rescaled_raw_eq_power_bound :=
    literaturePudlakTheorem5External_rescaledRawCode_eq_powerBoundRawCode
  power_bound_eq_rescaled_pudlak :=
    literaturePudlakTheorem5External_powerBoundRawCode_eq_rescaledPudlak
  power_bound_iff_rescaled :=
    literaturePudlakTheorem5ExternalScaleData
      |>.powerBoundLowerBound_iff_rescaledLowerBound

abbrev Statement : Prop :=
  Nonempty Instance

theorem statement : Statement :=
  ⟨external⟩

theorem statement_iff_external_instance_nonempty :
    Statement ↔ Nonempty Instance :=
  Iff.rfl

theorem certificate_nonempty_iff_rescaled_certificate_nonempty :
    Nonempty LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty LiteraturePudlakTheorem5RescaledLowerBoundCertificate :=
  literaturePudlakTheorem5Certificate_nonempty_iff_rescaledCertificate

theorem external_power_bound_iff_rescaled :
    LiteraturePudlakTheorem5PowerBoundLowerBound
        literaturePudlakTheorem5ExternalScaleData ↔
      StrongRescaledExternalStrengthenedLowerBound
        literaturePudlakTheorem5ExternalScaleData.rawCode
        literaturePudlakTheorem5ExternalScaleData.scale :=
  external.power_bound_iff_rescaled

theorem external_rescaled_raw_eq_power_bound (n : ℕ) :
    literaturePudlakTheorem5ExternalScaleData.rescaledRawCode n =
      literaturePudlakTheorem5ExternalScaleData.powerBoundRawCode n :=
  external.rescaled_raw_eq_power_bound n

theorem external_power_bound_eq_rescaled_pudlak (n : ℕ) :
    literaturePudlakTheorem5ExternalScaleData.powerBoundRawCode n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        literaturePudlakTheorem5ExternalScaleData.scale n :=
  external.power_bound_eq_rescaled_pudlak n


end PudlakTheorem5ExactProjectInstance
