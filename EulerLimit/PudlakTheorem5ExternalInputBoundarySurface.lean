/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.PudlakTheorem5ExactMinimalFieldPackageSurface

/-!
# Pudlak theorem 5 external-input boundary surface

This module separates the theorem-5 boundary into two audit objects:

* the only external literature input, namely the external scale data and the
  external rescaled lower-bound witness;
* the internal equivalence chain derived from that input, namely the
  raw/rescaled/power-bound code chain and the lower-source code equation.

The equivalence theorems below are intentionally stated with `↔`, so later
project layers can cite a single external-input boundary without weakening the
already established exact minimal-field package.
-/

namespace PudlakTheorem5ExternalInputBoundarySurface

structure ExternalInputCertificate : Type where
  external_scale_data : LiteraturePudlakTheorem5ScaleData
  external_scale_data_eq :
    external_scale_data = literaturePudlakTheorem5ExternalScaleData
  external_rescaled_lower_bound :
    StrongRescaledExternalStrengthenedLowerBound
      literaturePudlakTheorem5ExternalScaleData.rawCode
      literaturePudlakTheorem5ExternalScaleData.scale
  external_rescaled_lower_bound_eq :
    external_rescaled_lower_bound =
      literaturePudlakTheorem5ExternalRescaledLowerBound

noncomputable def externalInput : ExternalInputCertificate where
  external_scale_data := literaturePudlakTheorem5ExternalScaleData
  external_scale_data_eq := rfl
  external_rescaled_lower_bound :=
    literaturePudlakTheorem5ExternalRescaledLowerBound
  external_rescaled_lower_bound_eq := rfl

abbrev ExternalInputStatement : Prop :=
  Nonempty ExternalInputCertificate

theorem external_input_statement : ExternalInputStatement :=
  ⟨externalInput⟩

theorem external_input_unique_fields
    (cert : ExternalInputCertificate) :
    cert.external_scale_data =
        literaturePudlakTheorem5ExternalScaleData ∧
      cert.external_rescaled_lower_bound =
        literaturePudlakTheorem5ExternalRescaledLowerBound :=
  ⟨cert.external_scale_data_eq,
    cert.external_rescaled_lower_bound_eq⟩

structure InternalEquivalenceChainCertificate : Type where
  external_input : ExternalInputCertificate
  exact_minimal_package :
    PudlakTheorem5ExactMinimalFieldPackageSurface.ExactMinimalFieldPackage
  exact_project_instance :
    PudlakTheorem5ExactProjectInstance.Statement
  certificate_presentation_iff_rescaled :
    Nonempty LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty LiteraturePudlakTheorem5RescaledLowerBoundCertificate
  power_bound_iff_rescaled :
    LiteraturePudlakTheorem5PowerBoundLowerBound
        literaturePudlakTheorem5ExternalScaleData ↔
      StrongRescaledExternalStrengthenedLowerBound
        literaturePudlakTheorem5ExternalScaleData.rawCode
        literaturePudlakTheorem5ExternalScaleData.scale
  raw_rescaled_power_chain :
    ∀ n : Nat,
      PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
          PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n ∧
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
          rescaledPudlakStrengthenedFiniteConsistencyCode
            PudlakTheorem5MinimalExternalFieldsSurface.scale n
  lower_source_code_eq_rescaled_pudlak :
    ∀ n : Nat,
      rescaledExternalStrengthenedLowerBoundCode
          PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
          PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n

noncomputable def internalEquivalenceChain :
    InternalEquivalenceChainCertificate where
  external_input := externalInput
  exact_minimal_package :=
    PudlakTheorem5ExactMinimalFieldPackageSurface.external
  exact_project_instance :=
    PudlakTheorem5ExactProjectInstance.statement
  certificate_presentation_iff_rescaled :=
    audit_theorem5_certificatePresentation_iff_rescaledPresentation
  power_bound_iff_rescaled :=
    PudlakTheorem5ExactProjectInstance.external_power_bound_iff_rescaled
  raw_rescaled_power_chain :=
    PudlakTheorem5ExactMinimalFieldPackageSurface.statement_raw_rescaled_power_chain
  lower_source_code_eq_rescaled_pudlak :=
    PudlakTheorem5ExactMinimalFieldPackageSurface.statement_lower_source_code_eq_rescaled_pudlak

abbrev InternalEquivalenceStatement : Prop :=
  Nonempty InternalEquivalenceChainCertificate

theorem internal_equivalence_statement : InternalEquivalenceStatement :=
  ⟨internalEquivalenceChain⟩

theorem exact_minimal_iff_external_input :
    PudlakTheorem5ExactMinimalFieldPackageSurface.Statement ↔
      ExternalInputStatement := by
  constructor
  · intro _h
    exact external_input_statement
  · intro _h
    exact PudlakTheorem5ExactMinimalFieldPackageSurface.statement

theorem exact_minimal_iff_internal_equivalence :
    PudlakTheorem5ExactMinimalFieldPackageSurface.Statement ↔
      InternalEquivalenceStatement := by
  constructor
  · intro _h
    exact internal_equivalence_statement
  · intro _h
    exact PudlakTheorem5ExactMinimalFieldPackageSurface.statement

theorem external_input_iff_internal_equivalence :
    ExternalInputStatement ↔ InternalEquivalenceStatement :=
  exact_minimal_iff_external_input.symm.trans
    exact_minimal_iff_internal_equivalence

theorem internal_chain_raw_rescaled_power
    (chain : InternalEquivalenceChainCertificate) (n : Nat) :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  chain.raw_rescaled_power_chain n

theorem internal_chain_lower_source_code_eq_rescaled_pudlak
    (chain : InternalEquivalenceChainCertificate) (n : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  chain.lower_source_code_eq_rescaled_pudlak n

theorem statement_raw_rescaled_power_chain
    (n : Nat) :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  internalEquivalenceChain.raw_rescaled_power_chain n

theorem statement_lower_source_code_eq_rescaled_pudlak
    (n : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  internalEquivalenceChain.lower_source_code_eq_rescaled_pudlak n

end PudlakTheorem5ExternalInputBoundarySurface
