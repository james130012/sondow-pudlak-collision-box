/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.PudlakTheorem5ExactProjectInstance

/-!
# Pudlak theorem 5 project statement map

This module is the Month 4 audit checklist for matching the literature theorem
5 input to the project-local raw, rescaled, and power-bound code surfaces.
-/

namespace PudlakTheorem5ProjectStatementMap

structure StatementMap : Prop where
  exact_instance : PudlakTheorem5ExactProjectInstance.Statement
  certificate_nonempty_iff_rescaled :
    Nonempty LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty LiteraturePudlakTheorem5RescaledLowerBoundCertificate
  external_power_bound_iff_rescaled :
    LiteraturePudlakTheorem5PowerBoundLowerBound
        literaturePudlakTheorem5ExternalScaleData ↔
      StrongRescaledExternalStrengthenedLowerBound
        literaturePudlakTheorem5ExternalScaleData.rawCode
        literaturePudlakTheorem5ExternalScaleData.scale
  rescaled_raw_eq_power_bound :
    ∀ n : ℕ,
      literaturePudlakTheorem5ExternalScaleData.rescaledRawCode n =
        literaturePudlakTheorem5ExternalScaleData.powerBoundRawCode n
  power_bound_eq_rescaled_pudlak :
    ∀ n : ℕ,
      literaturePudlakTheorem5ExternalScaleData.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          literaturePudlakTheorem5ExternalScaleData.scale n
  rescaled_raw_eq_rescaled_pudlak :
    ∀ n : ℕ,
      literaturePudlakTheorem5ExternalScaleData.rescaledRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          literaturePudlakTheorem5ExternalScaleData.scale n

theorem statement_map : StatementMap where
  exact_instance := PudlakTheorem5ExactProjectInstance.statement
  certificate_nonempty_iff_rescaled :=
    PudlakTheorem5ExactProjectInstance.certificate_nonempty_iff_rescaled_certificate_nonempty
  external_power_bound_iff_rescaled :=
    PudlakTheorem5ExactProjectInstance.external_power_bound_iff_rescaled
  rescaled_raw_eq_power_bound :=
    PudlakTheorem5ExactProjectInstance.external_rescaled_raw_eq_power_bound
  power_bound_eq_rescaled_pudlak :=
    PudlakTheorem5ExactProjectInstance.external_power_bound_eq_rescaled_pudlak
  rescaled_raw_eq_rescaled_pudlak := by
    intro n
    rw [PudlakTheorem5ExactProjectInstance.external_rescaled_raw_eq_power_bound n]
    exact
      PudlakTheorem5ExactProjectInstance.external_power_bound_eq_rescaled_pudlak n

abbrev Statement : Prop :=
  StatementMap

theorem statement : Statement :=
  statement_map

theorem statement_iff_statement_map_nonempty :
    Statement ↔ Nonempty StatementMap :=
  ⟨fun h => ⟨h⟩, fun h => h.elim id⟩

theorem external_rescaled_raw_eq_rescaled_pudlak (n : ℕ) :
    literaturePudlakTheorem5ExternalScaleData.rescaledRawCode n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        literaturePudlakTheorem5ExternalScaleData.scale n :=
  statement_map.rescaled_raw_eq_rescaled_pudlak n


end PudlakTheorem5ProjectStatementMap
