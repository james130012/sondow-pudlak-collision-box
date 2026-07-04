/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.PudlakTheorem5MinimalExternalFieldsSurface

/-!
# Pudlak theorem 5 canonical import surface

Compact Month 4 import point for the theorem-5 exact project instance, statement
map, and normal-form code identities.
-/

namespace PudlakTheorem5CanonicalImportSurface

abbrev Statement : Prop :=
  PudlakTheorem5ProjectStatementMap.Statement

theorem statement : Statement :=
  PudlakTheorem5ProjectStatementMap.statement

abbrev NormalFormStatement
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) : Prop :=
  PudlakTheorem5NormalFormSurface.Statement hpartial

theorem normalFormStatement
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    NormalFormStatement hpartial :=
  PudlakTheorem5NormalFormSurface.statement hpartial

theorem normalFormStatement_iff_statement
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    NormalFormStatement hpartial ↔ Statement :=
  PudlakTheorem5NormalFormSurface.statement_iff_statement_map hpartial

theorem external_rescaled_raw_eq_rescaled_pudlak (n : ℕ) :
    literaturePudlakTheorem5ExternalScaleData.rescaledRawCode n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        literaturePudlakTheorem5ExternalScaleData.scale n :=
  PudlakTheorem5ProjectStatementMap.external_rescaled_raw_eq_rescaled_pudlak n

theorem normalForm_code_eq_rescaledPudlak
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (n : ℕ) :
    (PudlakTheorem5NormalFormSurface.normalForm hpartial).code n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        literaturePudlakTheorem5ExternalScaleData.scale n :=
  PudlakTheorem5NormalFormSurface.normalForm_code_eq_rescaledPudlak
    hpartial n

abbrev LowerBoundSourceStatement : Prop :=
  PudlakTheorem5LowerBoundSourceSurface.Statement

theorem lowerBoundSourceStatement : LowerBoundSourceStatement :=
  PudlakTheorem5LowerBoundSourceSurface.statement

noncomputable def lowerBoundSource :
    RescaledRawPudlakStrengthenedLowerBoundSource :=
  PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource

theorem lowerBoundSource_rescaledCode_eq_rescaledPudlak (n : ℕ) :
    rescaledExternalStrengthenedLowerBoundCode
        lowerBoundSource.raw lowerBoundSource.scale n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        literaturePudlakTheorem5ExternalScaleData.scale n :=
  PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource_rescaledCode_eq_rescaledPudlak
    n

abbrev MinimalExternalFieldsStatement : Prop :=
  PudlakTheorem5MinimalExternalFieldsSurface.Statement

theorem minimalExternalFieldsStatement : MinimalExternalFieldsStatement :=
  PudlakTheorem5MinimalExternalFieldsSurface.statement

noncomputable def theorem5Scale : ℕ → ℕ :=
  PudlakTheorem5MinimalExternalFieldsSurface.scale

noncomputable def theorem5TimeConstructibleBound : ℕ → ℕ :=
  PudlakTheorem5MinimalExternalFieldsSurface.timeConstructibleBound

noncomputable def theorem5Exponent : ℕ :=
  PudlakTheorem5MinimalExternalFieldsSurface.exponent

theorem theorem5_scale_eq_power_bound (n : ℕ) :
    theorem5Scale n =
      theorem5TimeConstructibleBound n ^ theorem5Exponent :=
  PudlakTheorem5MinimalExternalFieldsSurface.scale_eq_power_bound n

theorem theorem5_scale_id_le (n : ℕ) :
    n ≤ theorem5Scale n :=
  PudlakTheorem5MinimalExternalFieldsSurface.scale_id_le n

theorem theorem5_scale_polynomial_bound :
    is_polynomial_bound (fun n : ℕ => (theorem5Scale n : ℝ)) :=
  PudlakTheorem5MinimalExternalFieldsSurface.scale_polynomial_bound


end PudlakTheorem5CanonicalImportSurface
