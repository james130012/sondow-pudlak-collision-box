/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.PudlakTheorem5NormalFormSurface

/-!
# Pudlak theorem 5 lower-bound source surface

This module exposes the exact project object obtained from the theorem-5
external certificate: a rescaled raw Pudlak lower-bound source and its
transport to the partial-consistency normal form.  It keeps the literature
axioms as the only opaque mathematical input.
-/

namespace PudlakTheorem5LowerBoundSourceSurface

noncomputable def lowerBoundCertificate :
    LiteraturePudlakTheorem5LowerBoundCertificate :=
  literaturePudlakTheorem5ExternalLowerBoundCertificate

noncomputable def rescaledCertificate :
    LiteraturePudlakTheorem5RescaledLowerBoundCertificate :=
  literaturePudlakTheorem5ExternalRescaledLowerBoundCertificate

noncomputable def lowerBoundSource :
    RescaledRawPudlakStrengthenedLowerBoundSource :=
  lowerBoundCertificate.toLowerBoundSource

theorem lowerBoundCertificate_eq_external :
    lowerBoundCertificate =
      literaturePudlakTheorem5ExternalLowerBoundCertificate := by
  rfl

theorem rescaledCertificate_eq_external :
    rescaledCertificate =
      literaturePudlakTheorem5ExternalRescaledLowerBoundCertificate := by
  rfl

theorem lowerBoundSource_raw_eq :
    lowerBoundSource.raw =
      literaturePudlakTheorem5ExternalScaleData.rawCode := by
  rfl

theorem lowerBoundSource_scale_eq :
    lowerBoundSource.scale =
      literaturePudlakTheorem5ExternalScaleData.scale := by
  rfl

theorem lowerBoundSource_rescaledCode_eq_rescaledRawCode
    (n : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        lowerBoundSource.raw lowerBoundSource.scale n =
      literaturePudlakTheorem5ExternalScaleData.rescaledRawCode n := by
  rfl

theorem lowerBoundSource_rescaledCode_eq_rescaledPudlak
    (n : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        lowerBoundSource.raw lowerBoundSource.scale n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        literaturePudlakTheorem5ExternalScaleData.scale n := by
  rw [lowerBoundSource_rescaledCode_eq_rescaledRawCode n]
  exact
    PudlakTheorem5ProjectStatementMap.external_rescaled_raw_eq_rescaled_pudlak
      n

noncomputable def normalForm
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    PartialConsistencyLowerBoundNormalForm :=
  lowerBoundSource.toNormalForm hpartial

theorem normalForm_eq_canonical
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    normalForm hpartial =
      PudlakTheorem5NormalFormSurface.normalForm hpartial := by
  rfl

theorem normalForm_code_eq_source_rescaledCode
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    (normalForm hpartial).code =
      rescaledExternalStrengthenedLowerBoundCode
        lowerBoundSource.raw lowerBoundSource.scale := by
  rfl

theorem normalForm_code_eq_rescaledPudlak
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (n : Nat) :
    (normalForm hpartial).code n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        literaturePudlakTheorem5ExternalScaleData.scale n := by
  rw [normalForm_code_eq_source_rescaledCode hpartial]
  exact lowerBoundSource_rescaledCode_eq_rescaledPudlak n

structure Statement : Prop where
  theorem5_statement : PudlakTheorem5ProjectStatementMap.Statement
  exact_instance : PudlakTheorem5ExactProjectInstance.Statement
  certificate_eq_external :
    lowerBoundCertificate =
      literaturePudlakTheorem5ExternalLowerBoundCertificate
  rescaled_certificate_eq_external :
    rescaledCertificate =
      literaturePudlakTheorem5ExternalRescaledLowerBoundCertificate
  source_raw_eq :
    lowerBoundSource.raw =
      literaturePudlakTheorem5ExternalScaleData.rawCode
  source_scale_eq :
    lowerBoundSource.scale =
      literaturePudlakTheorem5ExternalScaleData.scale
  source_rescaled_code_eq_rescaledPudlak :
    ∀ n : Nat,
      rescaledExternalStrengthenedLowerBoundCode
          lowerBoundSource.raw lowerBoundSource.scale n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          literaturePudlakTheorem5ExternalScaleData.scale n
  normal_form_eq_canonical :
    ∀ hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer,
      normalForm hpartial =
        PudlakTheorem5NormalFormSurface.normalForm hpartial
  normal_form_code_eq_rescaledPudlak :
    ∀ hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer,
      ∀ n : Nat,
        (normalForm hpartial).code n =
          rescaledPudlakStrengthenedFiniteConsistencyCode
            literaturePudlakTheorem5ExternalScaleData.scale n

theorem statement : Statement where
  theorem5_statement := PudlakTheorem5ProjectStatementMap.statement
  exact_instance := PudlakTheorem5ExactProjectInstance.statement
  certificate_eq_external := lowerBoundCertificate_eq_external
  rescaled_certificate_eq_external := rescaledCertificate_eq_external
  source_raw_eq := lowerBoundSource_raw_eq
  source_scale_eq := lowerBoundSource_scale_eq
  source_rescaled_code_eq_rescaledPudlak :=
    lowerBoundSource_rescaledCode_eq_rescaledPudlak
  normal_form_eq_canonical := normalForm_eq_canonical
  normal_form_code_eq_rescaledPudlak :=
    normalForm_code_eq_rescaledPudlak

theorem statement_iff_theorem5_statement :
    Statement ↔ PudlakTheorem5ProjectStatementMap.Statement := by
  constructor
  · intro h
    exact h.theorem5_statement
  · intro _h
    exact statement


end PudlakTheorem5LowerBoundSourceSurface
