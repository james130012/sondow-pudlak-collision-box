/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.PudlakTheorem5LowerBoundSourceSurface

/-!
# Pudlak theorem 5 minimal external-field surface

This module names the exact fields still imported from the theorem-5 literature
boundary.  It does not add a new external assumption: each field is a projection
from `literaturePudlakTheorem5ExternalScaleData` or from the single external
rescaled lower-bound witness.
-/

namespace PudlakTheorem5MinimalExternalFieldsSurface

noncomputable def scaleData : LiteraturePudlakTheorem5ScaleData :=
  literaturePudlakTheorem5ExternalScaleData

noncomputable def timeConstructibleBound : Nat → Nat :=
  scaleData.time_constructible_bound

noncomputable def exponent : Nat :=
  scaleData.exponent

noncomputable def scale : Nat → Nat :=
  scaleData.scale

noncomputable def rawCode : Nat → FormulaCode :=
  scaleData.rawCode

noncomputable def rescaledRawCode : Nat → FormulaCode :=
  scaleData.rescaledRawCode

noncomputable def powerBoundRawCode : Nat → FormulaCode :=
  scaleData.powerBoundRawCode

theorem scaleData_eq_external :
    scaleData = literaturePudlakTheorem5ExternalScaleData := by
  rfl

theorem scale_eq_power_bound (n : Nat) :
    scale n = timeConstructibleBound n ^ exponent :=
  scaleData.scale_eq n

theorem scale_id_le (n : Nat) :
    n ≤ scale n :=
  scaleData.scale_id_le n

theorem scale_polynomial_bound :
    is_polynomial_bound (fun n : Nat => (scale n : Real)) :=
  scaleData.scale_polynomial_bound

theorem scale_properties :
    PolynomialCofinalScale scale :=
  scaleData.scale_properties

theorem rescaled_lower_bound :
    StrongRescaledExternalStrengthenedLowerBound rawCode scale :=
  literaturePudlakTheorem5ExternalRescaledLowerBound

theorem power_bound_iff_rescaled :
    LiteraturePudlakTheorem5PowerBoundLowerBound scaleData ↔
      StrongRescaledExternalStrengthenedLowerBound rawCode scale :=
  scaleData.powerBoundLowerBound_iff_rescaledLowerBound

theorem rescaledRawCode_eq_powerBoundRawCode (n : Nat) :
    rescaledRawCode n = powerBoundRawCode n :=
  scaleData.rescaledRawCode_eq_powerBoundRawCode n

theorem rescaledRawCode_eq_rescaledPudlak (n : Nat) :
    rescaledRawCode n =
      rescaledPudlakStrengthenedFiniteConsistencyCode scale n :=
  scaleData.rescaledRawCode_eq_rescaledPudlak n

theorem powerBoundRawCode_eq_rescaledPudlak (n : Nat) :
    powerBoundRawCode n =
      rescaledPudlakStrengthenedFiniteConsistencyCode scale n :=
  scaleData.powerBoundRawCode_eq_rescaledPudlak n

theorem lowerBoundSource_raw_eq :
    PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw = rawCode :=
  PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource_raw_eq

theorem lowerBoundSource_scale_eq :
    PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale = scale :=
  PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource_scale_eq

structure Statement : Prop where
  lower_bound_source_statement :
    PudlakTheorem5LowerBoundSourceSurface.Statement
  scale_data_eq_external :
    scaleData = literaturePudlakTheorem5ExternalScaleData
  scale_eq_power_bound :
    ∀ n : Nat, scale n = timeConstructibleBound n ^ exponent
  scale_id_le :
    ∀ n : Nat, n ≤ scale n
  scale_polynomial_bound :
    is_polynomial_bound (fun n : Nat => (scale n : Real))
  scale_properties :
    PolynomialCofinalScale scale
  rescaled_lower_bound :
    StrongRescaledExternalStrengthenedLowerBound rawCode scale
  power_bound_iff_rescaled :
    LiteraturePudlakTheorem5PowerBoundLowerBound scaleData ↔
      StrongRescaledExternalStrengthenedLowerBound rawCode scale
  rescaled_raw_eq_power_bound :
    ∀ n : Nat, rescaledRawCode n = powerBoundRawCode n
  rescaled_raw_eq_rescaled_pudlak :
    ∀ n : Nat,
      rescaledRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode scale n
  power_bound_eq_rescaled_pudlak :
    ∀ n : Nat,
      powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode scale n
  lower_source_raw_eq :
    PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw = rawCode
  lower_source_scale_eq :
    PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale = scale

theorem statement : Statement where
  lower_bound_source_statement :=
    PudlakTheorem5LowerBoundSourceSurface.statement
  scale_data_eq_external := scaleData_eq_external
  scale_eq_power_bound := scale_eq_power_bound
  scale_id_le := scale_id_le
  scale_polynomial_bound := scale_polynomial_bound
  scale_properties := scale_properties
  rescaled_lower_bound := rescaled_lower_bound
  power_bound_iff_rescaled := power_bound_iff_rescaled
  rescaled_raw_eq_power_bound := rescaledRawCode_eq_powerBoundRawCode
  rescaled_raw_eq_rescaled_pudlak := rescaledRawCode_eq_rescaledPudlak
  power_bound_eq_rescaled_pudlak := powerBoundRawCode_eq_rescaledPudlak
  lower_source_raw_eq := lowerBoundSource_raw_eq
  lower_source_scale_eq := lowerBoundSource_scale_eq

theorem statement_iff_lower_bound_source_statement :
    Statement ↔ PudlakTheorem5LowerBoundSourceSurface.Statement := by
  constructor
  · intro h
    exact h.lower_bound_source_statement
  · intro _h
    exact statement


end PudlakTheorem5MinimalExternalFieldsSurface
