/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.PudlakTheorem5CanonicalImportSurface
import EulerLimit.PudlakTheorem5LiteratureInputAuditSurface

/-!
# Pudlak theorem 5 exact external-boundary surface

This module compresses the remaining theorem-5 external boundary into one
project-facing audit certificate.  It does not internalize Pudlak theorem 5
and does not introduce a new assumption.  It records the exact equivalences
between:

* the literature audit ledger;
* the canonical theorem-5 import statement;
* the project theorem-5 audit witness;
* the explicit external-input/internal-equivalence/minimal-field boundary.
-/

namespace PudlakTheorem5ExactExternalBoundarySurface

structure ExactExternalBoundaryCertificate : Prop where
  literature_input_audit :
    PudlakTheorem5LiteratureInputAuditSurface.Statement
  project_theorem5_audit_witness :
    PudlakTheorem5LiteratureInputAuditSurface.ProjectTheorem5AuditWitness
  canonical_import_statement :
    PudlakTheorem5CanonicalImportSurface.Statement
  lower_bound_source_statement :
    PudlakTheorem5CanonicalImportSurface.LowerBoundSourceStatement
  minimal_external_fields_statement :
    PudlakTheorem5CanonicalImportSurface.MinimalExternalFieldsStatement
  exact_project_instance_statement :
    PudlakTheorem5ExactProjectInstance.Statement
  external_input_statement :
    PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement
  internal_equivalence_statement :
    PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement
  exact_minimal_package_statement :
    PudlakTheorem5ExactMinimalFieldPackageSurface.Statement
  literature_audit_iff_project_witness :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5LiteratureInputAuditSurface.ProjectTheorem5AuditWitness
  literature_audit_iff_external_input :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement
  literature_audit_iff_internal_equivalence :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement
  literature_audit_iff_exact_minimal_package :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExactMinimalFieldPackageSurface.Statement
  literature_audit_iff_exact_project_instance :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExactProjectInstance.Statement
  exact_project_instance_iff_canonical_import :
    PudlakTheorem5ExactProjectInstance.Statement ↔
      PudlakTheorem5CanonicalImportSurface.Statement
  literature_audit_iff_canonical_import :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5CanonicalImportSurface.Statement
  literature_audit_iff_full_boundary :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
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
  canonical_scale_eq_power_bound :
    ∀ n : Nat,
      PudlakTheorem5CanonicalImportSurface.theorem5Scale n =
        PudlakTheorem5CanonicalImportSurface.theorem5TimeConstructibleBound n ^
          PudlakTheorem5CanonicalImportSurface.theorem5Exponent
  canonical_scale_id_le :
    ∀ n : Nat, n ≤ PudlakTheorem5CanonicalImportSurface.theorem5Scale n
  canonical_scale_polynomial_bound :
    is_polynomial_bound
      (fun n : Nat =>
        (PudlakTheorem5CanonicalImportSurface.theorem5Scale n : Real))
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
    ∀ ledger : PudlakTheorem5LiteratureInputAuditSurface.LiteratureInputAuditLedger,
      ledger.external_input.external_scale_data =
          literaturePudlakTheorem5ExternalScaleData ∧
        ledger.external_input.external_rescaled_lower_bound =
          literaturePudlakTheorem5ExternalRescaledLowerBound

theorem exact_project_instance_iff_canonical_import :
    PudlakTheorem5ExactProjectInstance.Statement ↔
      PudlakTheorem5CanonicalImportSurface.Statement := by
  constructor
  · intro _h
    exact PudlakTheorem5CanonicalImportSurface.statement
  · intro h
    exact h.exact_instance

theorem literature_audit_iff_canonical_import :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5CanonicalImportSurface.Statement :=
  PudlakTheorem5LiteratureInputAuditSurface.statement_iff_exact_project_instance.trans
    exact_project_instance_iff_canonical_import

theorem canonical_import_iff_literature_audit :
    PudlakTheorem5CanonicalImportSurface.Statement ↔
      PudlakTheorem5LiteratureInputAuditSurface.Statement :=
  literature_audit_iff_canonical_import.symm

theorem exactExternalBoundaryCertificate :
    ExactExternalBoundaryCertificate where
  literature_input_audit :=
    PudlakTheorem5LiteratureInputAuditSurface.statement
  project_theorem5_audit_witness :=
    PudlakTheorem5LiteratureInputAuditSurface.project_theorem5_audit_witness
  canonical_import_statement :=
    PudlakTheorem5CanonicalImportSurface.statement
  lower_bound_source_statement :=
    PudlakTheorem5CanonicalImportSurface.lowerBoundSourceStatement
  minimal_external_fields_statement :=
    PudlakTheorem5CanonicalImportSurface.minimalExternalFieldsStatement
  exact_project_instance_statement :=
    PudlakTheorem5ExactProjectInstance.statement
  external_input_statement :=
    PudlakTheorem5ExternalInputBoundarySurface.external_input_statement
  internal_equivalence_statement :=
    PudlakTheorem5ExternalInputBoundarySurface.internal_equivalence_statement
  exact_minimal_package_statement :=
    PudlakTheorem5ExactMinimalFieldPackageSurface.statement
  literature_audit_iff_project_witness :=
    PudlakTheorem5LiteratureInputAuditSurface.statement_iff_project_theorem5_audit_witness
  literature_audit_iff_external_input :=
    PudlakTheorem5LiteratureInputAuditSurface.statement_iff_external_input
  literature_audit_iff_internal_equivalence :=
    PudlakTheorem5LiteratureInputAuditSurface.statement_iff_internal_equivalence
  literature_audit_iff_exact_minimal_package :=
    PudlakTheorem5LiteratureInputAuditSurface.statement_iff_exact_minimal_package
  literature_audit_iff_exact_project_instance :=
    PudlakTheorem5LiteratureInputAuditSurface.statement_iff_exact_project_instance
  exact_project_instance_iff_canonical_import :=
    exact_project_instance_iff_canonical_import
  literature_audit_iff_canonical_import :=
    literature_audit_iff_canonical_import
  literature_audit_iff_full_boundary :=
    PudlakTheorem5LiteratureInputAuditSurface.statement_iff_full_boundary
  certificate_presentation_iff_rescaled :=
    PudlakTheorem5ExactProjectInstance.certificate_nonempty_iff_rescaled_certificate_nonempty
  power_bound_iff_rescaled :=
    PudlakTheorem5ExactProjectInstance.external_power_bound_iff_rescaled
  canonical_scale_eq_power_bound :=
    PudlakTheorem5CanonicalImportSurface.theorem5_scale_eq_power_bound
  canonical_scale_id_le :=
    PudlakTheorem5CanonicalImportSurface.theorem5_scale_id_le
  canonical_scale_polynomial_bound :=
    PudlakTheorem5CanonicalImportSurface.theorem5_scale_polynomial_bound
  raw_rescaled_power_chain :=
    PudlakTheorem5LiteratureInputAuditSurface.statement_raw_rescaled_power_chain
  lower_source_code_eq_rescaled_pudlak :=
    PudlakTheorem5LiteratureInputAuditSurface.statement_lower_source_code_eq_rescaled_pudlak
  ledger_unique_external_fields :=
    PudlakTheorem5LiteratureInputAuditSurface.ledger_unique_external_fields

abbrev Statement : Prop :=
  ExactExternalBoundaryCertificate

theorem statement : Statement :=
  exactExternalBoundaryCertificate

theorem statement_iff_literature_audit :
    Statement ↔ PudlakTheorem5LiteratureInputAuditSurface.Statement := by
  constructor
  · intro h
    exact h.literature_input_audit
  · intro _h
    exact statement

theorem statement_iff_project_theorem5_audit_witness :
    Statement ↔
      PudlakTheorem5LiteratureInputAuditSurface.ProjectTheorem5AuditWitness :=
  statement_iff_literature_audit.trans
    PudlakTheorem5LiteratureInputAuditSurface.statement_iff_project_theorem5_audit_witness

theorem statement_iff_canonical_import :
    Statement ↔ PudlakTheorem5CanonicalImportSurface.Statement :=
  statement_iff_literature_audit.trans literature_audit_iff_canonical_import

theorem statement_iff_full_boundary :
    Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement ∧
        PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement ∧
          PudlakTheorem5ExactMinimalFieldPackageSurface.Statement :=
  statement_iff_literature_audit.trans
    PudlakTheorem5LiteratureInputAuditSurface.statement_iff_full_boundary

theorem statement_iff_exact_project_instance :
    Statement ↔ PudlakTheorem5ExactProjectInstance.Statement :=
  statement_iff_literature_audit.trans
    PudlakTheorem5LiteratureInputAuditSurface.statement_iff_exact_project_instance

theorem statement_iff_exact_minimal_package :
    Statement ↔ PudlakTheorem5ExactMinimalFieldPackageSurface.Statement :=
  statement_iff_literature_audit.trans
    PudlakTheorem5LiteratureInputAuditSurface.statement_iff_exact_minimal_package

theorem statement_raw_rescaled_power_chain
    (n : Nat) :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  statement.raw_rescaled_power_chain n

theorem statement_lower_source_code_eq_rescaled_pudlak
    (n : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  statement.lower_source_code_eq_rescaled_pudlak n

theorem statement_canonical_scale_eq_power_bound
    (n : Nat) :
    PudlakTheorem5CanonicalImportSurface.theorem5Scale n =
      PudlakTheorem5CanonicalImportSurface.theorem5TimeConstructibleBound n ^
        PudlakTheorem5CanonicalImportSurface.theorem5Exponent :=
  statement.canonical_scale_eq_power_bound n

theorem statement_canonical_scale_id_le
    (n : Nat) :
    n ≤ PudlakTheorem5CanonicalImportSurface.theorem5Scale n :=
  statement.canonical_scale_id_le n

theorem statement_canonical_scale_polynomial_bound :
    is_polynomial_bound
      (fun n : Nat =>
        (PudlakTheorem5CanonicalImportSurface.theorem5Scale n : Real)) :=
  statement.canonical_scale_polynomial_bound

theorem statement_unique_external_fields
    (ledger :
      PudlakTheorem5LiteratureInputAuditSurface.LiteratureInputAuditLedger) :
    ledger.external_input.external_scale_data =
        literaturePudlakTheorem5ExternalScaleData ∧
      ledger.external_input.external_rescaled_lower_bound =
        literaturePudlakTheorem5ExternalRescaledLowerBound :=
  statement.ledger_unique_external_fields ledger

theorem statement_external_input_unique_fields
    (cert :
      PudlakTheorem5ExternalInputBoundarySurface.ExternalInputCertificate) :
    cert.external_scale_data =
        literaturePudlakTheorem5ExternalScaleData ∧
      cert.external_rescaled_lower_bound =
        literaturePudlakTheorem5ExternalRescaledLowerBound :=
  PudlakTheorem5ExternalInputBoundarySurface.external_input_unique_fields cert

end PudlakTheorem5ExactExternalBoundarySurface
