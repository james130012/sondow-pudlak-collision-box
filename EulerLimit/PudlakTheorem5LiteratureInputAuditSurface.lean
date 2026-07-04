/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.PudlakTheorem5ExternalInputBoundarySurface

/-!
# Pudlak theorem 5 literature-input audit surface

This module records the remaining theorem-5 literature boundary as an audit
ledger.  The ledger has one external-input certificate, and that certificate is
required to point exactly at the two existing literature objects:

* `literaturePudlakTheorem5ExternalScaleData`;
* `literaturePudlakTheorem5ExternalRescaledLowerBound`.

All project-facing theorem-5 statements below are equivalent to this ledger.
Thus the public theorem surface can cite one audit object without hiding any
additional external assumption.
-/

namespace PudlakTheorem5LiteratureInputAuditSurface

structure LiteratureInputAuditLedger : Type where
  external_input :
    PudlakTheorem5ExternalInputBoundarySurface.ExternalInputCertificate
  external_scale_data_eq :
    external_input.external_scale_data =
      literaturePudlakTheorem5ExternalScaleData
  external_rescaled_lower_bound_eq :
    external_input.external_rescaled_lower_bound =
      literaturePudlakTheorem5ExternalRescaledLowerBound

noncomputable def auditLedger : LiteratureInputAuditLedger where
  external_input :=
    PudlakTheorem5ExternalInputBoundarySurface.externalInput
  external_scale_data_eq := rfl
  external_rescaled_lower_bound_eq := rfl

abbrev Statement : Prop :=
  Nonempty LiteratureInputAuditLedger

theorem statement : Statement :=
  ⟨auditLedger⟩

theorem ledger_unique_external_fields
    (ledger : LiteratureInputAuditLedger) :
    ledger.external_input.external_scale_data =
        literaturePudlakTheorem5ExternalScaleData ∧
      ledger.external_input.external_rescaled_lower_bound =
        literaturePudlakTheorem5ExternalRescaledLowerBound :=
  ⟨ledger.external_scale_data_eq,
    ledger.external_rescaled_lower_bound_eq⟩

theorem statement_iff_external_input :
    Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement := by
  constructor
  · intro h
    rcases h with ⟨ledger⟩
    exact ⟨ledger.external_input⟩
  · intro h
    rcases h with ⟨cert⟩
    exact
      ⟨{ external_input := cert
         external_scale_data_eq := cert.external_scale_data_eq
         external_rescaled_lower_bound_eq :=
           cert.external_rescaled_lower_bound_eq }⟩

theorem statement_iff_internal_equivalence :
    Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement :=
  statement_iff_external_input.trans
    PudlakTheorem5ExternalInputBoundarySurface.external_input_iff_internal_equivalence

theorem statement_iff_exact_minimal_package :
    Statement ↔ PudlakTheorem5ExactMinimalFieldPackageSurface.Statement :=
  statement_iff_external_input.trans
    PudlakTheorem5ExternalInputBoundarySurface.exact_minimal_iff_external_input.symm

theorem statement_iff_exact_project_instance :
    Statement ↔ PudlakTheorem5ExactProjectInstance.Statement :=
  statement_iff_exact_minimal_package.trans
    PudlakTheorem5ExactMinimalFieldPackageSurface.statement_iff_exact_project_instance

theorem statement_iff_full_boundary :
    Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement ∧
        PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement ∧
          PudlakTheorem5ExactMinimalFieldPackageSurface.Statement := by
  constructor
  · intro h
    exact
      ⟨statement_iff_external_input.mp h,
        statement_iff_internal_equivalence.mp h,
        statement_iff_exact_minimal_package.mp h⟩
  · intro h
    exact statement_iff_external_input.mpr h.1

theorem statement_raw_rescaled_power_chain
    (n : Nat) :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  PudlakTheorem5ExternalInputBoundarySurface.statement_raw_rescaled_power_chain n

theorem statement_lower_source_code_eq_rescaled_pudlak
    (n : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  PudlakTheorem5ExternalInputBoundarySurface.statement_lower_source_code_eq_rescaled_pudlak n

structure ProjectTheorem5AuditWitness : Prop where
  literature_input_audit : Statement
  external_input_statement :
    PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement
  internal_equivalence_statement :
    PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement
  exact_minimal_package_statement :
    PudlakTheorem5ExactMinimalFieldPackageSurface.Statement
  exact_project_instance_statement :
    PudlakTheorem5ExactProjectInstance.Statement
  literature_audit_iff_external_input :
    Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement
  literature_audit_iff_internal_equivalence :
    Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement
  literature_audit_iff_exact_minimal_package :
    Statement ↔ PudlakTheorem5ExactMinimalFieldPackageSurface.Statement
  literature_audit_iff_exact_project_instance :
    Statement ↔ PudlakTheorem5ExactProjectInstance.Statement
  literature_audit_iff_full_boundary :
    Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement ∧
        PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement ∧
          PudlakTheorem5ExactMinimalFieldPackageSurface.Statement
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
  ledger_unique_external_fields :
    ∀ ledger : LiteratureInputAuditLedger,
      ledger.external_input.external_scale_data =
          literaturePudlakTheorem5ExternalScaleData ∧
        ledger.external_input.external_rescaled_lower_bound =
          literaturePudlakTheorem5ExternalRescaledLowerBound

theorem statement_to_project_theorem5_audit_witness
    (h : Statement) :
    ProjectTheorem5AuditWitness where
  literature_input_audit := h
  external_input_statement :=
    statement_iff_external_input.mp h
  internal_equivalence_statement :=
    statement_iff_internal_equivalence.mp h
  exact_minimal_package_statement :=
    statement_iff_exact_minimal_package.mp h
  exact_project_instance_statement :=
    statement_iff_exact_project_instance.mp h
  literature_audit_iff_external_input :=
    statement_iff_external_input
  literature_audit_iff_internal_equivalence :=
    statement_iff_internal_equivalence
  literature_audit_iff_exact_minimal_package :=
    statement_iff_exact_minimal_package
  literature_audit_iff_exact_project_instance :=
    statement_iff_exact_project_instance
  literature_audit_iff_full_boundary :=
    statement_iff_full_boundary
  certificate_presentation_iff_rescaled :=
    PudlakTheorem5ExactProjectInstance.certificate_nonempty_iff_rescaled_certificate_nonempty
  power_bound_iff_rescaled :=
    PudlakTheorem5ExactProjectInstance.external_power_bound_iff_rescaled
  raw_rescaled_power_chain :=
    statement_raw_rescaled_power_chain
  lower_source_code_eq_rescaled_pudlak :=
    statement_lower_source_code_eq_rescaled_pudlak
  ledger_unique_external_fields :=
    ledger_unique_external_fields

theorem project_theorem5_audit_witness :
    ProjectTheorem5AuditWitness :=
  statement_to_project_theorem5_audit_witness statement

theorem statement_iff_project_theorem5_audit_witness :
    Statement ↔ ProjectTheorem5AuditWitness := by
  constructor
  · intro h
    exact statement_to_project_theorem5_audit_witness h
  · intro h
    exact h.literature_input_audit

end PudlakTheorem5LiteratureInputAuditSurface
