/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakMonth3CheckerTraceBudgetSurface
import EulerLimit.PudlakTheorem5CanonicalImportSurface

/-!
# Month 3/Month 4 collision-readiness surface

This module is a project-level checklist joining the Month 3 bounded PA
assembly route with the Month 4 Pudlak theorem-5 statement map.  It deliberately
does not assert the final collision; it records that the two public audit
surfaces can be consumed together without changing either statement.
-/

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4CollisionReadinessSurface

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate

structure CollisionReadinessStatement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) : Prop where
  month3_statement :
    Month3CanonicalImportSurface.CanonicalStatement field_index
  month3_source_size_statement :
    Month3SourceSizeAuditSurface.Statement field_index
  month3_provider_closure_statement :
    Month3ProviderClosureSurface.Statement field_index
  month3_checker_trace_budget_statement :
    Month3CheckerTraceBudgetSurface.Statement field_index
  month4_statement :
    PudlakTheorem5ProjectStatementMap.Statement
  month4_lower_bound_source_statement :
    PudlakTheorem5CanonicalImportSurface.LowerBoundSourceStatement
  month4_minimal_external_fields_statement :
    PudlakTheorem5CanonicalImportSurface.MinimalExternalFieldsStatement
  accepted_to_canonical_nonempty :
    ∀ n : Nat, SondowAccepted n →
      Nonempty (CanonicalProofCertificateAt bound n)
  accepted_to_canonical_accepted :
    ∀ n : Nat, SondowAccepted n →
      CanonicalProofCertificateAccepted bound n
  accepted_to_checker_trace :
    ∀ n : Nat, ∀ _haccepted : SondowAccepted n,
      Nonempty
        (CertificateVerifierMachine.AcceptedTrace
          (canonicalProofCertificateVerifierMachine bound) n)
  checker_trace_size_le_bound :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((Month3CheckerTraceBudgetSurface.traceAt
        field_index n haccepted).size : Real) ≤ bound n
  canonical_certificate_size_plus_two_le :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((Month3CanonicalImportSurface.accepted_to_canonical_certificate
        field_index n haccepted).proof.size + 2 : Nat) : Real)) ≤ bound n
  canonical_source_size_eq :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (Month3CanonicalImportSurface.accepted_to_canonical_certificate
        field_index n haccepted).sourceSize =
          Month3SourceSizeAuditSurface.accepted_source_size
            field_index n haccepted
  canonical_proof_eq_assembled :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (Month3CanonicalImportSurface.accepted_to_canonical_certificate
        field_index n haccepted).proof =
        ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
          (Month3ProviderClosureSurface.assemblyIndex field_index)
          (Month3ProviderClosureSurface.sourceAt
            field_index n haccepted)
  canonical_certificate_conclusion_eq_finiteConsistency :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (Month3CanonicalImportSurface.accepted_to_canonical_certificate
        field_index n haccepted).proof.conclusion =
          BoundedArithmeticLab.finiteConsistencyFormula n
  month3_target_eq_finiteConsistency :
    ∀ n : Nat,
      canonicalPudlakTargetFamilySpec.target n =
        BoundedArithmeticLab.finiteConsistencyFormula n
  month3_code_eq_partialConsistency :
    ∀ n : Nat,
      canonicalPudlakTargetFamilySpec.code
          (canonicalPudlakTargetFamilySpec.target n) =
        BoundedArithmeticLab.partialConsistencyCode n
  theorem5_rescaled_raw_eq_rescaled_pudlak :
    ∀ n : Nat,
      literaturePudlakTheorem5ExternalScaleData.rescaledRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          literaturePudlakTheorem5ExternalScaleData.scale n
  theorem5_lower_source_code_eq_rescaled_pudlak :
    ∀ n : Nat,
      rescaledExternalStrengthenedLowerBoundCode
          PudlakTheorem5CanonicalImportSurface.lowerBoundSource.raw
          PudlakTheorem5CanonicalImportSurface.lowerBoundSource.scale n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          literaturePudlakTheorem5ExternalScaleData.scale n
  theorem5_scale_eq_power_bound :
    ∀ n : Nat,
      PudlakTheorem5CanonicalImportSurface.theorem5Scale n =
        PudlakTheorem5CanonicalImportSurface.theorem5TimeConstructibleBound n ^
          PudlakTheorem5CanonicalImportSurface.theorem5Exponent
  theorem5_scale_id_le :
    ∀ n : Nat, n ≤ PudlakTheorem5CanonicalImportSurface.theorem5Scale n
  theorem5_scale_polynomial_bound :
    is_polynomial_bound
      (fun n : Nat =>
        (PudlakTheorem5CanonicalImportSurface.theorem5Scale n : Real))

def statement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    CollisionReadinessStatement field_index where
  month3_statement :=
    Month3CanonicalImportSurface.statement field_index
  month3_source_size_statement :=
    Month3SourceSizeAuditSurface.statement field_index
  month3_provider_closure_statement :=
    Month3ProviderClosureSurface.statement field_index
  month3_checker_trace_budget_statement :=
    Month3CheckerTraceBudgetSurface.statement field_index
  month4_statement :=
    PudlakTheorem5ProjectStatementMap.statement
  month4_lower_bound_source_statement :=
    PudlakTheorem5CanonicalImportSurface.lowerBoundSourceStatement
  month4_minimal_external_fields_statement :=
    PudlakTheorem5CanonicalImportSurface.minimalExternalFieldsStatement
  accepted_to_canonical_nonempty :=
    Month3CanonicalImportSurface.accepted_to_canonical_nonempty
      field_index
  accepted_to_canonical_accepted :=
    Month3CanonicalImportSurface.accepted_to_canonical_accepted
      field_index
  accepted_to_checker_trace :=
    Month3CheckerTraceBudgetSurface.trace_nonempty field_index
  checker_trace_size_le_bound :=
    Month3CheckerTraceBudgetSurface.trace_size_le_bound field_index
  canonical_certificate_size_plus_two_le :=
    Month3CanonicalImportSurface.canonical_certificate_size_plus_two_le
      field_index
  canonical_source_size_eq :=
    Month3SourceSizeAuditSurface.canonical_certificate_source_size_eq_accepted_source_size
      field_index
  canonical_proof_eq_assembled := by
    intro n haccepted
    exact
      Month3ProviderClosureSurface.canonical_proof_eq_assembledProof
        field_index n haccepted
  canonical_certificate_conclusion_eq_finiteConsistency := by
    intro n haccepted
    exact
      (Month3CanonicalImportSurface.accepted_to_canonical_certificate
        field_index n haccepted)
          |>.proof_conclusion_eq_finiteConsistency
  month3_target_eq_finiteConsistency :=
    field_index.target_eq_finiteConsistency
  month3_code_eq_partialConsistency :=
    field_index.code_eq_partialConsistency
  theorem5_rescaled_raw_eq_rescaled_pudlak :=
    PudlakTheorem5ProjectStatementMap.external_rescaled_raw_eq_rescaled_pudlak
  theorem5_lower_source_code_eq_rescaled_pudlak :=
    PudlakTheorem5CanonicalImportSurface.lowerBoundSource_rescaledCode_eq_rescaledPudlak
  theorem5_scale_eq_power_bound :=
    PudlakTheorem5CanonicalImportSurface.theorem5_scale_eq_power_bound
  theorem5_scale_id_le :=
    PudlakTheorem5CanonicalImportSurface.theorem5_scale_id_le
  theorem5_scale_polynomial_bound :=
    PudlakTheorem5CanonicalImportSurface.theorem5_scale_polynomial_bound

theorem statement_iff_month3_package_and_month4_statement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    CollisionReadinessStatement field_index ↔
      Nonempty
        (Month3BoundedPAProofPredicateAssemblySurface.Package
          MainRationality SondowAccepted bounds bound) ∧
        PudlakTheorem5ProjectStatementMap.Statement ∧
          PudlakTheorem5CanonicalImportSurface.LowerBoundSourceStatement ∧
            PudlakTheorem5CanonicalImportSurface.MinimalExternalFieldsStatement := by
  constructor
  · intro h
    exact
      ⟨⟨Month3BoundedPAProofPredicateAssemblySurface.Package.ofFieldIndex
        field_index⟩, h.month4_statement,
        h.month4_lower_bound_source_statement,
        h.month4_minimal_external_fields_statement⟩
  · intro _h
    exact statement field_index

structure CollisionReadinessWithNormalFormStatement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) : Prop where
  readiness : CollisionReadinessStatement field_index
  month4_normal_form :
    PudlakTheorem5CanonicalImportSurface.NormalFormStatement hpartial
  normal_form_code_eq_rescaledPudlak :
    ∀ n : Nat,
      (PudlakTheorem5NormalFormSurface.normalForm hpartial).code n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          literaturePudlakTheorem5ExternalScaleData.scale n

def statementWithNormalForm
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    CollisionReadinessWithNormalFormStatement field_index hpartial where
  readiness := statement field_index
  month4_normal_form :=
    PudlakTheorem5CanonicalImportSurface.normalFormStatement hpartial
  normal_form_code_eq_rescaledPudlak :=
    PudlakTheorem5CanonicalImportSurface.normalForm_code_eq_rescaledPudlak
      hpartial

theorem statementWithNormalForm_iff_readiness_and_month4_normal_form
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    CollisionReadinessWithNormalFormStatement field_index hpartial ↔
      CollisionReadinessStatement field_index ∧
        PudlakTheorem5CanonicalImportSurface.NormalFormStatement hpartial := by
  constructor
  · intro h
    exact ⟨h.readiness, h.month4_normal_form⟩
  · intro _h
    exact statementWithNormalForm field_index hpartial


end SondowProjectMonth3Month4CollisionReadinessSurface
end SondowMainCheckedCodeBridge
