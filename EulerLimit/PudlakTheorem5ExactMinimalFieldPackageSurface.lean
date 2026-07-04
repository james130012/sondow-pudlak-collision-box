/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.PudlakTheorem5MinimalExternalFieldsSurface

/-!
# Pudlak theorem 5 exact minimal-field package surface

This module compresses the theorem-5 external boundary into a single auditable
package.  The package does not introduce a new mathematical assumption: every
field is projected from the existing minimal external-field surface.

The purpose is to make the raw/rescaled/power-bound code chain explicit as one
object:

`rawCode -> rescaledRawCode <=> powerBoundRawCode -> rescaled Pudlak code`.
-/

namespace PudlakTheorem5ExactMinimalFieldPackageSurface

structure ExactMinimalFieldPackage : Type where
  minimal_external_fields_statement :
    PudlakTheorem5MinimalExternalFieldsSurface.Statement
  lower_bound_source_statement :
    PudlakTheorem5LowerBoundSourceSurface.Statement
  exact_project_instance :
    PudlakTheorem5ExactProjectInstance.Statement
  scale_data_eq_external :
    PudlakTheorem5MinimalExternalFieldsSurface.scaleData =
      literaturePudlakTheorem5ExternalScaleData
  lower_source_raw_eq :
    PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw =
      PudlakTheorem5MinimalExternalFieldsSurface.rawCode
  lower_source_scale_eq :
    PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale =
      PudlakTheorem5MinimalExternalFieldsSurface.scale
  scale_eq_power_bound :
    ∀ n : Nat,
      PudlakTheorem5MinimalExternalFieldsSurface.scale n =
        PudlakTheorem5MinimalExternalFieldsSurface.timeConstructibleBound n ^
          PudlakTheorem5MinimalExternalFieldsSurface.exponent
  scale_id_le :
    ∀ n : Nat,
      n ≤ PudlakTheorem5MinimalExternalFieldsSurface.scale n
  scale_polynomial_bound :
    is_polynomial_bound
      (fun n : Nat =>
        (PudlakTheorem5MinimalExternalFieldsSurface.scale n : Real))
  rescaled_lower_bound :
    StrongRescaledExternalStrengthenedLowerBound
      PudlakTheorem5MinimalExternalFieldsSurface.rawCode
      PudlakTheorem5MinimalExternalFieldsSurface.scale
  power_bound_iff_rescaled :
    LiteraturePudlakTheorem5PowerBoundLowerBound
        PudlakTheorem5MinimalExternalFieldsSurface.scaleData ↔
      StrongRescaledExternalStrengthenedLowerBound
        PudlakTheorem5MinimalExternalFieldsSurface.rawCode
        PudlakTheorem5MinimalExternalFieldsSurface.scale
  rescaled_raw_eq_power_bound :
    ∀ n : Nat,
      PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n
  rescaled_raw_eq_rescaled_pudlak :
    ∀ n : Nat,
      PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n
  power_bound_eq_rescaled_pudlak :
    ∀ n : Nat,
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n
  lower_source_code_eq_rescaled_raw :
    ∀ n : Nat,
      rescaledExternalStrengthenedLowerBoundCode
          PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
          PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale n =
        PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n
  lower_source_code_eq_rescaled_pudlak :
    ∀ n : Nat,
      rescaledExternalStrengthenedLowerBoundCode
          PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
          PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n
  raw_rescaled_power_chain :
    ∀ n : Nat,
      PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n

noncomputable def external : ExactMinimalFieldPackage where
  minimal_external_fields_statement :=
    PudlakTheorem5MinimalExternalFieldsSurface.statement
  lower_bound_source_statement :=
    PudlakTheorem5LowerBoundSourceSurface.statement
  exact_project_instance :=
    PudlakTheorem5ExactProjectInstance.statement
  scale_data_eq_external :=
    PudlakTheorem5MinimalExternalFieldsSurface.scaleData_eq_external
  lower_source_raw_eq :=
    PudlakTheorem5MinimalExternalFieldsSurface.lowerBoundSource_raw_eq
  lower_source_scale_eq :=
    PudlakTheorem5MinimalExternalFieldsSurface.lowerBoundSource_scale_eq
  scale_eq_power_bound :=
    PudlakTheorem5MinimalExternalFieldsSurface.scale_eq_power_bound
  scale_id_le :=
    PudlakTheorem5MinimalExternalFieldsSurface.scale_id_le
  scale_polynomial_bound :=
    PudlakTheorem5MinimalExternalFieldsSurface.scale_polynomial_bound
  rescaled_lower_bound :=
    PudlakTheorem5MinimalExternalFieldsSurface.rescaled_lower_bound
  power_bound_iff_rescaled :=
    PudlakTheorem5MinimalExternalFieldsSurface.power_bound_iff_rescaled
  rescaled_raw_eq_power_bound :=
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode_eq_powerBoundRawCode
  rescaled_raw_eq_rescaled_pudlak :=
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode_eq_rescaledPudlak
  power_bound_eq_rescaled_pudlak :=
    PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode_eq_rescaledPudlak
  lower_source_code_eq_rescaled_raw :=
    PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource_rescaledCode_eq_rescaledRawCode
  lower_source_code_eq_rescaled_pudlak :=
    PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource_rescaledCode_eq_rescaledPudlak
  raw_rescaled_power_chain := by
    intro n
    exact
      ⟨PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode_eq_powerBoundRawCode n,
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode_eq_rescaledPudlak n⟩

abbrev Statement : Prop :=
  Nonempty ExactMinimalFieldPackage

theorem statement : Statement :=
  ⟨external⟩

theorem statement_iff_minimal_external_fields :
    Statement ↔ PudlakTheorem5MinimalExternalFieldsSurface.Statement := by
  constructor
  · intro h
    rcases h with ⟨pkg⟩
    exact pkg.minimal_external_fields_statement
  · intro _h
    exact statement

theorem statement_iff_lower_bound_source :
    Statement ↔ PudlakTheorem5LowerBoundSourceSurface.Statement :=
  statement_iff_minimal_external_fields.trans
    PudlakTheorem5MinimalExternalFieldsSurface.statement_iff_lower_bound_source_statement

theorem statement_iff_exact_project_instance :
    Statement ↔ PudlakTheorem5ExactProjectInstance.Statement := by
  constructor
  · intro h
    rcases h with ⟨pkg⟩
    exact pkg.exact_project_instance
  · intro _h
    exact statement

theorem package_raw_rescaled_power_chain
    (pkg : ExactMinimalFieldPackage) (n : Nat) :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  pkg.raw_rescaled_power_chain n

theorem package_lower_source_code_eq_rescaled_pudlak
    (pkg : ExactMinimalFieldPackage) (n : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  pkg.lower_source_code_eq_rescaled_pudlak n

theorem statement_raw_rescaled_power_chain
    (n : Nat) :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  external.raw_rescaled_power_chain n

theorem statement_lower_source_code_eq_rescaled_pudlak
    (n : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  external.lower_source_code_eq_rescaled_pudlak n

end PudlakTheorem5ExactMinimalFieldPackageSurface
