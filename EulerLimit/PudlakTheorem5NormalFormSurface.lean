/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.PudlakTheorem5ProjectStatementMap

/-!
# Pudlak theorem 5 normal-form surface

This module records the exact code identities after the external theorem-5
certificate is transported to the partial-consistency normal form.
-/

namespace PudlakTheorem5NormalFormSurface

noncomputable def normalForm
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    PartialConsistencyLowerBoundNormalForm :=
  literaturePudlakTheorem5ExternalLowerBoundCertificate.toNormalForm hpartial

theorem normalForm_code_eq_powerBoundRawCode
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (normalForm hpartial).code =
      literaturePudlakTheorem5ExternalScaleData.powerBoundRawCode :=
  literaturePudlakTheorem5ExternalLowerBoundCertificate
    |>.normalForm_code_eq_powerBoundRawCode hpartial

theorem normalForm_code_eq_rescaledPudlak
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (n : ℕ) :
    (normalForm hpartial).code n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        literaturePudlakTheorem5ExternalScaleData.scale n :=
  literaturePudlakTheorem5ExternalLowerBoundCertificate
    |>.normalForm_code_eq_rescaledPudlak hpartial n

structure Statement
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) : Prop where
  statement_map : PudlakTheorem5ProjectStatementMap.Statement
  code_eq_powerBoundRawCode :
    (normalForm hpartial).code =
      literaturePudlakTheorem5ExternalScaleData.powerBoundRawCode
  code_eq_rescaledPudlak :
    ∀ n : ℕ,
      (normalForm hpartial).code n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          literaturePudlakTheorem5ExternalScaleData.scale n

theorem statement
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    Statement hpartial where
  statement_map := PudlakTheorem5ProjectStatementMap.statement
  code_eq_powerBoundRawCode :=
    normalForm_code_eq_powerBoundRawCode hpartial
  code_eq_rescaledPudlak :=
    normalForm_code_eq_rescaledPudlak hpartial

theorem statement_iff_statement_map
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    Statement hpartial ↔ PudlakTheorem5ProjectStatementMap.Statement := by
  constructor
  · intro h
    exact h.statement_map
  · intro _h
    exact statement hpartial


end PudlakTheorem5NormalFormSurface
