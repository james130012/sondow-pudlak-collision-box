/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4PublicReleaseIndexSurface

/-!
# Month 4 exact external-boundary projection surface

This module exposes the Pudlak theorem-5 exact external boundary as a single
same-object closure.  The closure is intentionally thin: all fields are
projected from one `ExactExternalBoundaryCertificate`, so the public release
does not present the raw/rescaled/power-bound equations as unrelated facts.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4Month4ExactExternalBoundaryProjectionSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4TheoremIndexSurface
open SondowProjectMonth3Month4ReleaseTheoremExportSurface
open SondowProjectMonth3Month4PublicReleaseIndexSurface

structure Month4ExactExternalSameObjectClosure
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop where
  exact_external_boundary :
    Month4ExactExternalBoundaryExport
      rootSide MainRationality SondowAccepted bounds bound
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
  literature_audit_iff_full_boundary :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement ∧
        PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement ∧
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
  ledger_unique_external_fields :
    ∀ ledger :
        PudlakTheorem5LiteratureInputAuditSurface.LiteratureInputAuditLedger,
      ledger.external_input.external_scale_data =
          literaturePudlakTheorem5ExternalScaleData ∧
        ledger.external_input.external_rescaled_lower_bound =
          literaturePudlakTheorem5ExternalRescaledLowerBound

theorem month4_same_object_closure_of_exact_external_boundary
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (boundary :
      Month4ExactExternalBoundaryExport
        rootSide MainRationality SondowAccepted bounds bound) :
    Month4ExactExternalSameObjectClosure
      rootSide MainRationality SondowAccepted bounds bound where
  exact_external_boundary := boundary
  literature_input_audit := boundary.literature_input_audit
  project_theorem5_audit_witness :=
    boundary.project_theorem5_audit_witness
  canonical_import_statement := boundary.canonical_import_statement
  lower_bound_source_statement := boundary.lower_bound_source_statement
  minimal_external_fields_statement :=
    boundary.minimal_external_fields_statement
  exact_project_instance_statement :=
    boundary.exact_project_instance_statement
  external_input_statement := boundary.external_input_statement
  internal_equivalence_statement := boundary.internal_equivalence_statement
  exact_minimal_package_statement :=
    boundary.exact_minimal_package_statement
  literature_audit_iff_full_boundary :=
    boundary.literature_audit_iff_full_boundary
  literature_audit_iff_exact_project_instance :=
    boundary.literature_audit_iff_exact_project_instance
  exact_project_instance_iff_canonical_import :=
    boundary.exact_project_instance_iff_canonical_import
  literature_audit_iff_canonical_import :=
    boundary.literature_audit_iff_canonical_import
  certificate_presentation_iff_rescaled :=
    boundary.certificate_presentation_iff_rescaled
  power_bound_iff_rescaled := boundary.power_bound_iff_rescaled
  raw_rescaled_power_chain := boundary.raw_rescaled_power_chain
  lower_source_code_eq_rescaled_pudlak :=
    boundary.lower_source_code_eq_rescaled_pudlak
  canonical_scale_eq_power_bound :=
    boundary.canonical_scale_eq_power_bound
  canonical_scale_id_le := boundary.canonical_scale_id_le
  canonical_scale_polynomial_bound :=
    boundary.canonical_scale_polynomial_bound
  ledger_unique_external_fields := boundary.ledger_unique_external_fields

theorem public_release_index_to_month4_same_object_closure
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index :
      PublicReleaseIndex
        rootSide MainRationality SondowAccepted bounds bound) :
    Month4ExactExternalSameObjectClosure
      rootSide MainRationality SondowAccepted bounds bound :=
  month4_same_object_closure_of_exact_external_boundary
    index.month4_exact_external_boundary

theorem public_release_index_to_month4_full_boundary_interface
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index :
      PublicReleaseIndex
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement ∧
        PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement ∧
          PudlakTheorem5ExactMinimalFieldPackageSurface.Statement :=
  (public_release_index_to_month4_same_object_closure
    index).literature_audit_iff_full_boundary

theorem public_release_index_to_month4_exact_project_iff_canonical_import
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index :
      PublicReleaseIndex
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5ExactProjectInstance.Statement ↔
      PudlakTheorem5CanonicalImportSurface.Statement :=
  (public_release_index_to_month4_same_object_closure
    index).exact_project_instance_iff_canonical_import

theorem public_release_index_to_month4_same_object_raw_rescaled_power_chain
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index :
      PublicReleaseIndex
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  (public_release_index_to_month4_same_object_closure
    index).raw_rescaled_power_chain n

theorem public_release_index_to_month4_same_object_power_bound_iff_rescaled
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index :
      PublicReleaseIndex
        rootSide MainRationality SondowAccepted bounds bound) :
    LiteraturePudlakTheorem5PowerBoundLowerBound
        literaturePudlakTheorem5ExternalScaleData ↔
      StrongRescaledExternalStrengthenedLowerBound
        literaturePudlakTheorem5ExternalScaleData.rawCode
        literaturePudlakTheorem5ExternalScaleData.scale :=
  (public_release_index_to_month4_same_object_closure
    index).power_bound_iff_rescaled

theorem exactFamily_route_to_month4_same_object_closure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (route :
      Nonempty (Σ' gap_cert :
          ProjectComputableGapCertificate
            MainRationality SondowAccepted bounds bound,
          SondowProjectPudlakConcreteBridgeChecklist
            h.toPudlakSideInputs gap_cert) ∧
        ∃ m : Nat, SondowAccepted m) :
    Month4ExactExternalSameObjectClosure
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  public_release_index_to_month4_same_object_closure
    (exactFamily_route_to_public_release_index h route)

end SondowProjectMonth3Month4Month4ExactExternalBoundaryProjectionSurface
end SondowMainCheckedCodeBridge
