/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4ReleaseChecklistExactnessSurface

/-!
# Month 3/Month 4 public audit index surface

This module gives a single reviewer-facing index for the current Month 3 and
Month 4 route.  It does not introduce a new endpoint: the audit package is
definitionally assembled from the release-checklist exactness package.

The index is meant to answer the public audit question in one place:

* the paper theorem route and the audit package are equivalent;
* the canonical import package and the audit package are equivalent;
* each public checklist is equivalent to the same audit package;
* the package exposes the Month 3 bounded-checker budget fields;
* the package exposes the Month 4 minimal external theorem-5 fields;
* the package keeps the gap no-weakening and public-gap consequences visible.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4PublicAuditIndexSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4CanonicalImportSurface
open SondowProjectMonth3Month4GapNoWeakeningSurface
open SondowProjectMonth3Month4TheoremIndexSurface
open SondowProjectMonth3Month4ReleaseChecklistExactnessSurface

structure PublicAuditIndexStatement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      ReleaseChecklistExactnessPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Prop where
  exactness :
    ReleaseChecklistExactnessStatement pkg.public_release
  paper_route :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound
  paper_route_iff_exactness_package :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Nonempty (ReleaseChecklistExactnessPackage
        rootSide MainRationality SondowAccepted bounds bound)
  canonical_import_iff_exactness_package :
    Nonempty (Month3Month4CanonicalPackage
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ReleaseChecklistExactnessPackage
        rootSide MainRationality SondowAccepted bounds bound)
  gap_no_weakening_statement :
    Month3Month4GapNoWeakeningStatement pkg.public_release.assembly
  external_gap_same_object :
    ∀ n : Nat,
      ExternalGapSameObjectBridge.Certificate
        (externalGapCriterion pkg.public_release.assembly) n
  month3_checker_trace_budget_statement :
    Month3CheckerTraceBudgetSurface.Statement
      pkg.public_release.assembly.index
  month3_trace_size_le_bound :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((Month3CheckerTraceBudgetSurface.traceAt
        pkg.public_release.assembly.index n haccepted).size : Real) ≤ bound n
  month4_lower_bound_source_statement :
    PudlakTheorem5CanonicalImportSurface.LowerBoundSourceStatement
  month4_minimal_external_fields_statement :
    PudlakTheorem5CanonicalImportSurface.MinimalExternalFieldsStatement
  theorem5_scale_eq_power_bound :
    ∀ n : Nat,
      PudlakTheorem5CanonicalImportSurface.theorem5Scale n =
        PudlakTheorem5CanonicalImportSurface.theorem5TimeConstructibleBound n ^
          PudlakTheorem5CanonicalImportSurface.theorem5Exponent
  public_gap_instantiation :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality)
  not_main_rationality : ¬ MainRationality

def statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      ReleaseChecklistExactnessPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PublicAuditIndexStatement pkg where
  exactness := pkg.exactness
  paper_route := pkg.exactness.theorem_index_paper_route
  paper_route_iff_exactness_package :=
    _root_.SondowMainCheckedCodeBridge.SondowProjectMonth3Month4ReleaseChecklistExactnessSurface.paper_route_iff_exactness_package
  canonical_import_iff_exactness_package :=
    _root_.SondowMainCheckedCodeBridge.SondowProjectMonth3Month4ReleaseChecklistExactnessSurface.canonical_import_iff_exactness_package
  gap_no_weakening_statement :=
    pkg.exactness.gap_no_weakening_statement
  external_gap_same_object :=
    pkg.exactness.gap_no_weakening_statement.external_gap_same_object
  month3_checker_trace_budget_statement :=
    pkg.exactness.month3_checker_trace_budget_statement
  month3_trace_size_le_bound :=
    pkg.exactness.checker_trace_size_le_bound
  month4_lower_bound_source_statement :=
    pkg.exactness.month4_lower_bound_source_statement
  month4_minimal_external_fields_statement :=
    pkg.exactness.month4_minimal_external_fields_statement
  theorem5_scale_eq_power_bound :=
    pkg.exactness.theorem5_scale_eq_power_bound
  public_gap_instantiation :=
    pkg.exactness.public_gap_instantiation
  not_main_rationality :=
    pkg.exactness.not_main_rationality

theorem statement_iff_exactness_and_gap_no_weakening
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      ReleaseChecklistExactnessPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PublicAuditIndexStatement pkg ↔
      ReleaseChecklistExactnessStatement pkg.public_release ∧
        Month3Month4GapNoWeakeningStatement
          pkg.public_release.assembly := by
  constructor
  · intro h
    exact ⟨h.exactness, h.gap_no_weakening_statement⟩
  · intro _h
    exact statement pkg

structure PublicAuditIndexPackage
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) where
  exactness_package :
    ReleaseChecklistExactnessPackage
      rootSide MainRationality SondowAccepted bounds bound
  audit :
    PublicAuditIndexStatement exactness_package

namespace PublicAuditIndexPackage

def ofExactnessPackage
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (exactness_package :
      ReleaseChecklistExactnessPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PublicAuditIndexPackage
      rootSide MainRationality SondowAccepted bounds bound where
  exactness_package := exactness_package
  audit := statement exactness_package

end PublicAuditIndexPackage

theorem auditIndex_nonempty_iff_exactness_package_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty
        (PublicAuditIndexPackage
          rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty
        (ReleaseChecklistExactnessPackage
          rootSide MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨pkg⟩
    exact ⟨pkg.exactness_package⟩
  · intro h
    rcases h with ⟨pkg⟩
    exact ⟨PublicAuditIndexPackage.ofExactnessPackage pkg⟩

theorem paper_route_iff_audit_index
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Nonempty
        (PublicAuditIndexPackage
          rootSide MainRationality SondowAccepted bounds bound) :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectMonth3Month4ReleaseChecklistExactnessSurface.paper_route_iff_exactness_package.trans
    auditIndex_nonempty_iff_exactness_package_nonempty.symm

def auditIndex_to_paperAuditPackage
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PaperAuditPackage
      rootSide MainRationality SondowAccepted bounds bound :=
  PaperAuditPackage.ofRoute pkg.audit.paper_route

theorem audit_index_iff_paper_audit_package_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty
        (PublicAuditIndexPackage
          rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty
        (PaperAuditPackage
          rootSide MainRationality SondowAccepted bounds bound) :=
  paper_route_iff_audit_index.symm.trans
    paper_route_iff_paper_audit_package_nonempty

theorem auditIndex_to_paper_audit_package_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty
      (PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :=
  ⟨auditIndex_to_paperAuditPackage pkg⟩

theorem paper_audit_package_to_audit_index_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty
      (PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :=
  paper_route_iff_audit_index.mp pkg.route

theorem canonical_import_iff_audit_index
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (Month3Month4CanonicalPackage
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty
        (PublicAuditIndexPackage
          rootSide MainRationality SondowAccepted bounds bound) :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectMonth3Month4ReleaseChecklistExactnessSurface.canonical_import_iff_exactness_package.trans
    auditIndex_nonempty_iff_exactness_package_nonempty.symm

theorem exactConvention_checklist_iff_audit_index
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty
        (PublicAuditIndexPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (_root_.SondowMainCheckedCodeBridge.SondowProjectMonth3Month4ReleaseChecklistExactnessSurface.exactConvention_checklist_iff_exactness_package h).trans
      auditIndex_nonempty_iff_exactness_package_nonempty.symm

theorem splitMinChecked_checklist_iff_audit_index
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty
        (PublicAuditIndexPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (_root_.SondowMainCheckedCodeBridge.SondowProjectMonth3Month4ReleaseChecklistExactnessSurface.splitMinChecked_checklist_iff_exactness_package h).trans
      auditIndex_nonempty_iff_exactness_package_nonempty.symm

theorem exactFamily_checklist_iff_audit_index
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty
        (PublicAuditIndexPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (_root_.SondowMainCheckedCodeBridge.SondowProjectMonth3Month4ReleaseChecklistExactnessSurface.exactFamily_checklist_iff_exactness_package h).trans
      auditIndex_nonempty_iff_exactness_package_nonempty.symm

theorem auditIndex_month3_checker_trace_budget_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Month3CheckerTraceBudgetSurface.Statement
      pkg.exactness_package.public_release.assembly.index :=
  pkg.audit.month3_checker_trace_budget_statement

theorem auditIndex_month4_minimal_external_fields_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (_pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5CanonicalImportSurface.MinimalExternalFieldsStatement :=
  PudlakTheorem5CanonicalImportSurface.minimalExternalFieldsStatement

theorem auditIndex_month4_lower_bound_source_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5CanonicalImportSurface.LowerBoundSourceStatement :=
  pkg.audit.month4_lower_bound_source_statement

theorem auditIndex_theorem5_literature_input_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5LiteratureInputAuditSurface.Statement :=
  paperAuditPackage_theorem5_literature_input_audit
    (auditIndex_to_paperAuditPackage pkg)

theorem auditIndex_theorem5_exact_external_boundary
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    _root_.PudlakTheorem5ExactExternalBoundarySurface.Statement :=
  paperAuditPackage_theorem5_exact_external_boundary
    (auditIndex_to_paperAuditPackage pkg)

theorem auditIndex_theorem5_exact_minimal_package
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5ExactMinimalFieldPackageSurface.Statement :=
  paperAuditPackage_theorem5_exact_minimal_package
    (auditIndex_to_paperAuditPackage pkg)

theorem auditIndex_theorem5_internal_equivalence_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement :=
  paperAuditPackage_theorem5_internal_equivalence_statement
    (auditIndex_to_paperAuditPackage pkg)

theorem auditIndex_theorem5_external_input_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement :=
  paperAuditPackage_theorem5_external_input_statement
    (auditIndex_to_paperAuditPackage pkg)

theorem auditIndex_theorem5_raw_rescaled_power_chain
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  paperAuditPackage_theorem5_raw_rescaled_power_chain
    (auditIndex_to_paperAuditPackage pkg) n

theorem auditIndex_theorem5_lower_source_code_eq_rescaled_pudlak
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  paperAuditPackage_theorem5_lower_source_code_eq_rescaled_pudlak
    (auditIndex_to_paperAuditPackage pkg) n

theorem auditIndex_theorem5_power_bound_iff_rescaled
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    LiteraturePudlakTheorem5PowerBoundLowerBound
        literaturePudlakTheorem5ExternalScaleData ↔
      StrongRescaledExternalStrengthenedLowerBound
        literaturePudlakTheorem5ExternalScaleData.rawCode
        literaturePudlakTheorem5ExternalScaleData.scale :=
  paperAuditPackage_theorem5_power_bound_iff_rescaled
    (auditIndex_to_paperAuditPackage pkg)

theorem auditIndex_theorem5_certificate_presentation_iff_rescaled
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty LiteraturePudlakTheorem5RescaledLowerBoundCertificate :=
  paperAuditPackage_theorem5_certificate_presentation_iff_rescaled
    (auditIndex_to_paperAuditPackage pkg)

theorem auditIndex_gap_no_weakening_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Month3Month4GapNoWeakeningStatement
      pkg.exactness_package.public_release.assembly :=
  pkg.audit.gap_no_weakening_statement

theorem auditIndex_external_gap_same_object
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    ExternalGapSameObjectBridge.Certificate
      (externalGapCriterion
        pkg.exactness_package.public_release.assembly) n :=
  pkg.audit.external_gap_same_object n

theorem auditIndex_trace_size_le_bound
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((Month3CheckerTraceBudgetSurface.traceAt
      pkg.exactness_package.public_release.assembly.index
        n haccepted).size : Real) ≤ bound n :=
  pkg.audit.month3_trace_size_le_bound n haccepted

def auditIndex_source_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CompiledSondowProjectSourceCertificateAt bounds n :=
  paperAuditPackage_source_at
    (auditIndex_to_paperAuditPackage pkg) n haccepted

def auditIndex_canonical_certificate_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CanonicalProofCertificateAt bound n :=
  paperAuditPackage_canonical_certificate_at
    (auditIndex_to_paperAuditPackage pkg) n haccepted

def auditIndex_checker_trace_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CertificateVerifierMachine.AcceptedTrace
      (canonicalProofCertificateVerifierMachine bound) n :=
  paperAuditPackage_checker_trace_at
    (auditIndex_to_paperAuditPackage pkg) n haccepted

theorem auditIndex_accepted_to_source_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (CompiledSondowProjectSourceCertificateAt bounds n) :=
  paperAuditPackage_accepted_to_source_nonempty
    (auditIndex_to_paperAuditPackage pkg) n haccepted

theorem auditIndex_accepted_to_canonical_certificate_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (CanonicalProofCertificateAt bound n) :=
  paperAuditPackage_accepted_to_canonical_certificate_nonempty
    (auditIndex_to_paperAuditPackage pkg) n haccepted

theorem auditIndex_accepted_to_checker_trace_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty
      (CertificateVerifierMachine.AcceptedTrace
        (canonicalProofCertificateVerifierMachine bound) n) :=
  paperAuditPackage_accepted_to_checker_trace_nonempty
    (auditIndex_to_paperAuditPackage pkg) n haccepted

theorem auditIndex_accepted_to_month3_ledger_proof_predicate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n :=
  paperAuditPackage_accepted_to_month3_ledger_proof_predicate
    (auditIndex_to_paperAuditPackage pkg) n haccepted

theorem auditIndex_month3_ledger_proof_predicate_iff_certificate_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ↔
      Nonempty (CanonicalProofCertificateAt bound n) :=
  paperAuditPackage_month3_ledger_proof_predicate_iff_certificate_at
    (auditIndex_to_paperAuditPackage pkg) n

theorem auditIndex_checker_trace_cert_eq_canonical_proof
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (auditIndex_checker_trace_at pkg n haccepted).cert =
      (auditIndex_canonical_certificate_at pkg n haccepted).proof :=
  paperAuditPackage_checker_trace_cert_eq_canonical_proof
    (auditIndex_to_paperAuditPackage pkg) n haccepted

theorem auditIndex_checker_trace_cert_eq_assembled_proof
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (auditIndex_checker_trace_at pkg n haccepted).cert =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          (auditIndex_to_paperAuditPackage
            pkg).release_package.assembly.index)
        (auditIndex_source_at pkg n haccepted) :=
  paperAuditPackage_checker_trace_cert_eq_assembled_proof
    (auditIndex_to_paperAuditPackage pkg) n haccepted

theorem auditIndex_canonical_proof_eq_assembled_proof
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (auditIndex_canonical_certificate_at pkg n haccepted).proof =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          (auditIndex_to_paperAuditPackage
            pkg).release_package.assembly.index)
        (auditIndex_source_at pkg n haccepted) :=
  paperAuditPackage_canonical_proof_eq_assembled_proof
    (auditIndex_to_paperAuditPackage pkg) n haccepted

theorem auditIndex_source_size_eq_component_sum
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CompiledSondowProjectSourceCertificateAt.sourceSize
        (auditIndex_source_at pkg n haccepted) =
      (auditIndex_source_at pkg n haccepted).product.sourceSize +
        (auditIndex_source_at pkg n haccepted).logRelation.sourceSize +
          (auditIndex_source_at pkg n haccepted).decomposition.sourceSize +
            (auditIndex_source_at pkg n haccepted).threePow.sourceSize +
              (auditIndex_source_at pkg n haccepted).payload.sourceSize :=
  paperAuditPackage_source_size_eq_component_sum
    (auditIndex_to_paperAuditPackage pkg) n haccepted

theorem auditIndex_canonical_source_size_eq_source_size
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (auditIndex_canonical_certificate_at pkg n haccepted).sourceSize =
      CompiledSondowProjectSourceCertificateAt.sourceSize
        (auditIndex_source_at pkg n haccepted) :=
  paperAuditPackage_canonical_source_size_eq_source_size
    (auditIndex_to_paperAuditPackage pkg) n haccepted

theorem auditIndex_checker_trace_size_le_bound
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((auditIndex_checker_trace_at pkg n haccepted).size : Real) ≤
      bound n :=
  paperAuditPackage_checker_trace_size_le_bound
    (auditIndex_to_paperAuditPackage pkg) n haccepted

theorem auditIndex_canonical_certificate_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((auditIndex_canonical_certificate_at
      pkg n haccepted).proof.size + 2 : Nat) : Real)) ≤ bound n :=
  paperAuditPackage_canonical_certificate_size_plus_two_le
    (auditIndex_to_paperAuditPackage pkg) n haccepted

theorem auditIndex_source_product_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((auditIndex_source_at
      pkg n haccepted).product.proof.size + 2 : Nat) : Real)) ≤
      bounds.product n :=
  paperAuditPackage_source_product_size_plus_two_le
    (auditIndex_to_paperAuditPackage pkg) n haccepted

theorem auditIndex_source_log_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((auditIndex_source_at
      pkg n haccepted).logRelation.proof.size + 2 : Nat) : Real)) ≤
      bounds.logRelation n :=
  paperAuditPackage_source_log_size_plus_two_le
    (auditIndex_to_paperAuditPackage pkg) n haccepted

theorem auditIndex_source_decomposition_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((auditIndex_source_at
      pkg n haccepted).decomposition.proof.size + 2 : Nat) : Real)) ≤
      bounds.decomposition n :=
  paperAuditPackage_source_decomposition_size_plus_two_le
    (auditIndex_to_paperAuditPackage pkg) n haccepted

theorem auditIndex_source_threePow_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((auditIndex_source_at
      pkg n haccepted).threePow.proof.size + 2 : Nat) : Real)) ≤
      bounds.threePow n :=
  paperAuditPackage_source_threePow_size_plus_two_le
    (auditIndex_to_paperAuditPackage pkg) n haccepted

theorem auditIndex_source_payload_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((auditIndex_source_at
      pkg n haccepted).payload.proof.size + 2 : Nat) : Real)) ≤
      bounds.payload n :=
  paperAuditPackage_source_payload_size_plus_two_le
    (auditIndex_to_paperAuditPackage pkg) n haccepted

theorem auditIndex_assembled_proof_size_plus_two_le_bound
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
      (Month3ProviderClosureSurface.assemblyIndex
        (auditIndex_to_paperAuditPackage
          pkg).release_package.assembly.index)
      (auditIndex_source_at pkg n haccepted)).size + 2 : Nat) :
        Real)) ≤ bound n :=
  paperAuditPackage_assembled_proof_size_plus_two_le_bound
    (auditIndex_to_paperAuditPackage pkg) n haccepted

structure Month3SourceAssemblyAudit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) : Prop where
  trace_cert_eq_assembled :
    (auditIndex_checker_trace_at pkg n haccepted).cert =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          (auditIndex_to_paperAuditPackage
            pkg).release_package.assembly.index)
        (auditIndex_source_at pkg n haccepted)
  canonical_proof_eq_assembled :
    (auditIndex_canonical_certificate_at pkg n haccepted).proof =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          (auditIndex_to_paperAuditPackage
            pkg).release_package.assembly.index)
        (auditIndex_source_at pkg n haccepted)
  source_size_eq_component_sum :
    CompiledSondowProjectSourceCertificateAt.sourceSize
        (auditIndex_source_at pkg n haccepted) =
      (auditIndex_source_at pkg n haccepted).product.sourceSize +
        (auditIndex_source_at pkg n haccepted).logRelation.sourceSize +
          (auditIndex_source_at pkg n haccepted).decomposition.sourceSize +
            (auditIndex_source_at pkg n haccepted).threePow.sourceSize +
              (auditIndex_source_at pkg n haccepted).payload.sourceSize
  canonical_source_size_eq_source_size :
    (auditIndex_canonical_certificate_at pkg n haccepted).sourceSize =
      CompiledSondowProjectSourceCertificateAt.sourceSize
        (auditIndex_source_at pkg n haccepted)
  source_product_size_plus_two_le :
    ((((auditIndex_source_at
      pkg n haccepted).product.proof.size + 2 : Nat) : Real)) ≤
      bounds.product n
  source_log_size_plus_two_le :
    ((((auditIndex_source_at
      pkg n haccepted).logRelation.proof.size + 2 : Nat) : Real)) ≤
      bounds.logRelation n
  source_decomposition_size_plus_two_le :
    ((((auditIndex_source_at
      pkg n haccepted).decomposition.proof.size + 2 : Nat) : Real)) ≤
      bounds.decomposition n
  source_threePow_size_plus_two_le :
    ((((auditIndex_source_at
      pkg n haccepted).threePow.proof.size + 2 : Nat) : Real)) ≤
      bounds.threePow n
  source_payload_size_plus_two_le :
    ((((auditIndex_source_at
      pkg n haccepted).payload.proof.size + 2 : Nat) : Real)) ≤
      bounds.payload n
  assembled_proof_size_plus_two_le_bound :
    ((((ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
      (Month3ProviderClosureSurface.assemblyIndex
        (auditIndex_to_paperAuditPackage
          pkg).release_package.assembly.index)
      (auditIndex_source_at pkg n haccepted)).size + 2 : Nat) :
        Real)) ≤ bound n

theorem auditIndex_month3_source_assembly_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3SourceAssemblyAudit pkg n haccepted where
  trace_cert_eq_assembled :=
    auditIndex_checker_trace_cert_eq_assembled_proof pkg n haccepted
  canonical_proof_eq_assembled :=
    auditIndex_canonical_proof_eq_assembled_proof pkg n haccepted
  source_size_eq_component_sum :=
    auditIndex_source_size_eq_component_sum pkg n haccepted
  canonical_source_size_eq_source_size :=
    auditIndex_canonical_source_size_eq_source_size pkg n haccepted
  source_product_size_plus_two_le :=
    auditIndex_source_product_size_plus_two_le pkg n haccepted
  source_log_size_plus_two_le :=
    auditIndex_source_log_size_plus_two_le pkg n haccepted
  source_decomposition_size_plus_two_le :=
    auditIndex_source_decomposition_size_plus_two_le pkg n haccepted
  source_threePow_size_plus_two_le :=
    auditIndex_source_threePow_size_plus_two_le pkg n haccepted
  source_payload_size_plus_two_le :=
    auditIndex_source_payload_size_plus_two_le pkg n haccepted
  assembled_proof_size_plus_two_le_bound :=
    auditIndex_assembled_proof_size_plus_two_le_bound pkg n haccepted

structure ProjectLevelFinalAudit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) : Prop where
  month3_source_nonempty :
    Nonempty (CompiledSondowProjectSourceCertificateAt bounds n)
  month3_canonical_certificate_nonempty :
    Nonempty (CanonicalProofCertificateAt bound n)
  month3_checker_trace_nonempty :
    Nonempty
      (CertificateVerifierMachine.AcceptedTrace
        (canonicalProofCertificateVerifierMachine bound) n)
  month3_ledger_proof_predicate :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n
  month3_ledger_proof_predicate_iff_certificate_at :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ↔
      Nonempty (CanonicalProofCertificateAt bound n)
  month3_source_assembly :
    Month3SourceAssemblyAudit pkg n haccepted
  month4_project_theorem5_audit_witness :
    PudlakTheorem5LiteratureInputAuditSurface.ProjectTheorem5AuditWitness
  month4_exact_external_boundary_statement :
    _root_.PudlakTheorem5ExactExternalBoundarySurface.Statement
  month4_exact_minimal_package :
    PudlakTheorem5ExactMinimalFieldPackageSurface.Statement
  month4_internal_equivalence :
    PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement
  month4_raw_rescaled_power_chain :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n
  month4_lower_source_code_eq_rescaled_pudlak :
    rescaledExternalStrengthenedLowerBoundCode
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        PudlakTheorem5MinimalExternalFieldsSurface.scale n
  month4_power_bound_iff_rescaled :
    LiteraturePudlakTheorem5PowerBoundLowerBound
        literaturePudlakTheorem5ExternalScaleData ↔
      StrongRescaledExternalStrengthenedLowerBound
        literaturePudlakTheorem5ExternalScaleData.rawCode
        literaturePudlakTheorem5ExternalScaleData.scale
  month4_certificate_presentation_iff_rescaled :
    Nonempty LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty LiteraturePudlakTheorem5RescaledLowerBoundCertificate
  public_gap_instantiation :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality)
  not_main_rationality : ¬ MainRationality

theorem auditIndex_project_level_final_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ProjectLevelFinalAudit pkg n haccepted where
  month3_source_nonempty :=
    auditIndex_accepted_to_source_nonempty pkg n haccepted
  month3_canonical_certificate_nonempty :=
    auditIndex_accepted_to_canonical_certificate_nonempty pkg n haccepted
  month3_checker_trace_nonempty :=
    auditIndex_accepted_to_checker_trace_nonempty pkg n haccepted
  month3_ledger_proof_predicate :=
    auditIndex_accepted_to_month3_ledger_proof_predicate pkg n haccepted
  month3_ledger_proof_predicate_iff_certificate_at :=
    auditIndex_month3_ledger_proof_predicate_iff_certificate_at pkg n
  month3_source_assembly :=
    auditIndex_month3_source_assembly_audit pkg n haccepted
  month4_project_theorem5_audit_witness :=
    paperAuditPackage_theorem5_project_audit_witness
      (auditIndex_to_paperAuditPackage pkg)
  month4_exact_external_boundary_statement :=
    auditIndex_theorem5_exact_external_boundary pkg
  month4_exact_minimal_package :=
    auditIndex_theorem5_exact_minimal_package pkg
  month4_internal_equivalence :=
    auditIndex_theorem5_internal_equivalence_statement pkg
  month4_raw_rescaled_power_chain :=
    auditIndex_theorem5_raw_rescaled_power_chain pkg n
  month4_lower_source_code_eq_rescaled_pudlak :=
    auditIndex_theorem5_lower_source_code_eq_rescaled_pudlak pkg n
  month4_power_bound_iff_rescaled :=
    auditIndex_theorem5_power_bound_iff_rescaled pkg
  month4_certificate_presentation_iff_rescaled :=
    auditIndex_theorem5_certificate_presentation_iff_rescaled pkg
  public_gap_instantiation :=
    pkg.audit.public_gap_instantiation
  not_main_rationality :=
    pkg.audit.not_main_rationality

theorem auditIndex_project_level_final_audit_nonempty_iff_audit_index
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (Σ' pkg : PublicAuditIndexPackage
      rootSide MainRationality SondowAccepted bounds bound,
      ProjectLevelFinalAudit pkg n haccepted) ↔
      Nonempty (PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) := by
  constructor
  · rintro ⟨⟨pkg, _audit⟩⟩
    exact ⟨pkg⟩
  · rintro ⟨pkg⟩
    exact ⟨⟨pkg,
      auditIndex_project_level_final_audit pkg n haccepted⟩⟩

theorem audit_index_iff_project_level_final_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (PublicAuditIndexPackage
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Σ' pkg : PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound,
        ProjectLevelFinalAudit pkg n haccepted) :=
  (auditIndex_project_level_final_audit_nonempty_iff_audit_index
    n haccepted).symm

theorem paper_route_iff_project_level_final_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Nonempty (Σ' pkg : PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound,
        ProjectLevelFinalAudit pkg n haccepted) :=
  paper_route_iff_audit_index.trans
    (audit_index_iff_project_level_final_audit n haccepted)

theorem exactConvention_checklist_iff_project_level_final_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty (Σ' pkg : PublicAuditIndexPackage
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
        ProjectLevelFinalAudit pkg m haccepted) :=
  (exactConvention_checklist_iff_audit_index h).trans
    (audit_index_iff_project_level_final_audit m haccepted)

theorem splitMinChecked_checklist_iff_project_level_final_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty (Σ' pkg : PublicAuditIndexPackage
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
        ProjectLevelFinalAudit pkg m haccepted) :=
  (splitMinChecked_checklist_iff_audit_index h).trans
    (audit_index_iff_project_level_final_audit m haccepted)

theorem exactFamily_checklist_iff_project_level_final_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty (Σ' pkg : PublicAuditIndexPackage
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
        ProjectLevelFinalAudit pkg m haccepted) :=
  (exactFamily_checklist_iff_audit_index h).trans
    (audit_index_iff_project_level_final_audit m haccepted)

theorem auditIndex_theorem5_scale_eq_power_bound
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (_pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    PudlakTheorem5CanonicalImportSurface.theorem5Scale n =
      PudlakTheorem5CanonicalImportSurface.theorem5TimeConstructibleBound n ^
        PudlakTheorem5CanonicalImportSurface.theorem5Exponent :=
  PudlakTheorem5CanonicalImportSurface.theorem5_scale_eq_power_bound n

theorem auditIndex_to_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  pkg.audit.public_gap_instantiation

theorem auditIndex_not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  pkg.audit.not_main_rationality

theorem exactConvention_checklist_to_audit_index
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    Nonempty
      (PublicAuditIndexPackage
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactConvention_checklist_iff_audit_index h).1 checklist

theorem splitMinChecked_checklist_to_audit_index
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    Nonempty
      (PublicAuditIndexPackage
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (splitMinChecked_checklist_iff_audit_index h).1 checklist

theorem exactFamily_checklist_to_audit_index
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    Nonempty
      (PublicAuditIndexPackage
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactFamily_checklist_iff_audit_index h).1 checklist

theorem exactConvention_checklist_to_month3_checker_trace_budget_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    Nonempty (Σ' pkg : PublicAuditIndexPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      Month3CheckerTraceBudgetSurface.Statement
        pkg.exactness_package.public_release.assembly.index) := by
  rcases exactConvention_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact ⟨⟨pkg, auditIndex_month3_checker_trace_budget_statement pkg⟩⟩

theorem exactConvention_checklist_to_month3_accepted_chain_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' pkg : PublicAuditIndexPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      Nonempty (CompiledSondowProjectSourceCertificateAt bounds m) ∧
        Nonempty (CanonicalProofCertificateAt bound m) ∧
        Nonempty
          (CertificateVerifierMachine.AcceptedTrace
            (canonicalProofCertificateVerifierMachine bound) m) ∧
        Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound m ∧
        (auditIndex_checker_trace_at pkg m haccepted).cert =
          (auditIndex_canonical_certificate_at pkg m haccepted).proof ∧
        ((auditIndex_checker_trace_at pkg m haccepted).size : Real) ≤
          bound m ∧
        ((((auditIndex_canonical_certificate_at
          pkg m haccepted).proof.size + 2 : Nat) : Real)) ≤ bound m) := by
  rcases exactConvention_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      auditIndex_accepted_to_source_nonempty pkg m haccepted,
      auditIndex_accepted_to_canonical_certificate_nonempty pkg m haccepted,
      auditIndex_accepted_to_checker_trace_nonempty pkg m haccepted,
      auditIndex_accepted_to_month3_ledger_proof_predicate pkg m haccepted,
      auditIndex_checker_trace_cert_eq_canonical_proof pkg m haccepted,
      auditIndex_checker_trace_size_le_bound pkg m haccepted,
      auditIndex_canonical_certificate_size_plus_two_le pkg m haccepted⟩⟩

theorem splitMinChecked_checklist_to_month3_accepted_chain_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' pkg : PublicAuditIndexPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      Nonempty (CompiledSondowProjectSourceCertificateAt bounds m) ∧
        Nonempty (CanonicalProofCertificateAt bound m) ∧
        Nonempty
          (CertificateVerifierMachine.AcceptedTrace
            (canonicalProofCertificateVerifierMachine bound) m) ∧
        Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound m ∧
        (auditIndex_checker_trace_at pkg m haccepted).cert =
          (auditIndex_canonical_certificate_at pkg m haccepted).proof ∧
        ((auditIndex_checker_trace_at pkg m haccepted).size : Real) ≤
          bound m ∧
        ((((auditIndex_canonical_certificate_at
          pkg m haccepted).proof.size + 2 : Nat) : Real)) ≤ bound m) := by
  rcases splitMinChecked_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      auditIndex_accepted_to_source_nonempty pkg m haccepted,
      auditIndex_accepted_to_canonical_certificate_nonempty pkg m haccepted,
      auditIndex_accepted_to_checker_trace_nonempty pkg m haccepted,
      auditIndex_accepted_to_month3_ledger_proof_predicate pkg m haccepted,
      auditIndex_checker_trace_cert_eq_canonical_proof pkg m haccepted,
      auditIndex_checker_trace_size_le_bound pkg m haccepted,
      auditIndex_canonical_certificate_size_plus_two_le pkg m haccepted⟩⟩

theorem exactFamily_checklist_to_month3_accepted_chain_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' pkg : PublicAuditIndexPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      Nonempty (CompiledSondowProjectSourceCertificateAt bounds m) ∧
        Nonempty (CanonicalProofCertificateAt bound m) ∧
        Nonempty
          (CertificateVerifierMachine.AcceptedTrace
            (canonicalProofCertificateVerifierMachine bound) m) ∧
        Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound m ∧
        (auditIndex_checker_trace_at pkg m haccepted).cert =
          (auditIndex_canonical_certificate_at pkg m haccepted).proof ∧
        ((auditIndex_checker_trace_at pkg m haccepted).size : Real) ≤
          bound m ∧
        ((((auditIndex_canonical_certificate_at
          pkg m haccepted).proof.size + 2 : Nat) : Real)) ≤ bound m) := by
  rcases exactFamily_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      auditIndex_accepted_to_source_nonempty pkg m haccepted,
      auditIndex_accepted_to_canonical_certificate_nonempty pkg m haccepted,
      auditIndex_accepted_to_checker_trace_nonempty pkg m haccepted,
      auditIndex_accepted_to_month3_ledger_proof_predicate pkg m haccepted,
      auditIndex_checker_trace_cert_eq_canonical_proof pkg m haccepted,
      auditIndex_checker_trace_size_le_bound pkg m haccepted,
      auditIndex_canonical_certificate_size_plus_two_le pkg m haccepted⟩⟩

theorem exactConvention_checklist_to_month3_source_assembly_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' pkg : PublicAuditIndexPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      Month3SourceAssemblyAudit pkg m haccepted) := by
  rcases exactConvention_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact ⟨⟨pkg, auditIndex_month3_source_assembly_audit pkg m haccepted⟩⟩

theorem splitMinChecked_checklist_to_month3_source_assembly_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' pkg : PublicAuditIndexPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      Month3SourceAssemblyAudit pkg m haccepted) := by
  rcases splitMinChecked_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact ⟨⟨pkg, auditIndex_month3_source_assembly_audit pkg m haccepted⟩⟩

theorem exactFamily_checklist_to_month3_source_assembly_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' pkg : PublicAuditIndexPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      Month3SourceAssemblyAudit pkg m haccepted) := by
  rcases exactFamily_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact ⟨⟨pkg, auditIndex_month3_source_assembly_audit pkg m haccepted⟩⟩

theorem exactConvention_checklist_to_project_level_final_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' pkg : PublicAuditIndexPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      ProjectLevelFinalAudit pkg m haccepted) := by
  rcases exactConvention_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact ⟨⟨pkg, auditIndex_project_level_final_audit pkg m haccepted⟩⟩

theorem splitMinChecked_checklist_to_project_level_final_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' pkg : PublicAuditIndexPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      ProjectLevelFinalAudit pkg m haccepted) := by
  rcases splitMinChecked_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact ⟨⟨pkg, auditIndex_project_level_final_audit pkg m haccepted⟩⟩

theorem exactFamily_checklist_to_project_level_final_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' pkg : PublicAuditIndexPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      ProjectLevelFinalAudit pkg m haccepted) := by
  rcases exactFamily_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact ⟨⟨pkg, auditIndex_project_level_final_audit pkg m haccepted⟩⟩

theorem exactConvention_checklist_to_month4_minimal_fields_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    Nonempty (Σ' _pkg : PublicAuditIndexPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      PudlakTheorem5CanonicalImportSurface.MinimalExternalFieldsStatement) := by
  rcases exactConvention_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact ⟨⟨pkg, auditIndex_month4_minimal_external_fields_statement pkg⟩⟩

theorem splitMinChecked_checklist_to_month4_minimal_fields_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    Nonempty (Σ' _pkg : PublicAuditIndexPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      PudlakTheorem5CanonicalImportSurface.MinimalExternalFieldsStatement) := by
  rcases splitMinChecked_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact ⟨⟨pkg, auditIndex_month4_minimal_external_fields_statement pkg⟩⟩

theorem exactFamily_checklist_to_month4_minimal_fields_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    Nonempty (Σ' _pkg : PublicAuditIndexPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      PudlakTheorem5CanonicalImportSurface.MinimalExternalFieldsStatement) := by
  rcases exactFamily_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact ⟨⟨pkg, auditIndex_month4_minimal_external_fields_statement pkg⟩⟩

theorem exactConvention_checklist_to_theorem5_exact_minimal_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    PudlakTheorem5ExactMinimalFieldPackageSurface.Statement := by
  rcases exactConvention_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact auditIndex_theorem5_exact_minimal_package pkg

theorem splitMinChecked_checklist_to_theorem5_exact_minimal_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    PudlakTheorem5ExactMinimalFieldPackageSurface.Statement := by
  rcases splitMinChecked_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact auditIndex_theorem5_exact_minimal_package pkg

theorem exactFamily_checklist_to_theorem5_exact_minimal_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    PudlakTheorem5ExactMinimalFieldPackageSurface.Statement := by
  rcases exactFamily_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact auditIndex_theorem5_exact_minimal_package pkg

theorem exactConvention_checklist_to_theorem5_raw_rescaled_power_chain
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode m =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode m ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode m =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale m := by
  rcases exactConvention_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact auditIndex_theorem5_raw_rescaled_power_chain pkg m

theorem splitMinChecked_checklist_to_theorem5_raw_rescaled_power_chain
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode m =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode m ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode m =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale m := by
  rcases splitMinChecked_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact auditIndex_theorem5_raw_rescaled_power_chain pkg m

theorem exactFamily_checklist_to_theorem5_raw_rescaled_power_chain
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode m =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode m ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode m =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale m := by
  rcases exactFamily_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact auditIndex_theorem5_raw_rescaled_power_chain pkg m

theorem exactConvention_checklist_to_theorem5_power_bound_iff_rescaled
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    LiteraturePudlakTheorem5PowerBoundLowerBound
        literaturePudlakTheorem5ExternalScaleData ↔
      StrongRescaledExternalStrengthenedLowerBound
        literaturePudlakTheorem5ExternalScaleData.rawCode
        literaturePudlakTheorem5ExternalScaleData.scale := by
  rcases exactConvention_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact auditIndex_theorem5_power_bound_iff_rescaled pkg

theorem splitMinChecked_checklist_to_theorem5_power_bound_iff_rescaled
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    LiteraturePudlakTheorem5PowerBoundLowerBound
        literaturePudlakTheorem5ExternalScaleData ↔
      StrongRescaledExternalStrengthenedLowerBound
        literaturePudlakTheorem5ExternalScaleData.rawCode
        literaturePudlakTheorem5ExternalScaleData.scale := by
  rcases splitMinChecked_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact auditIndex_theorem5_power_bound_iff_rescaled pkg

theorem exactFamily_checklist_to_theorem5_power_bound_iff_rescaled
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    LiteraturePudlakTheorem5PowerBoundLowerBound
        literaturePudlakTheorem5ExternalScaleData ↔
      StrongRescaledExternalStrengthenedLowerBound
        literaturePudlakTheorem5ExternalScaleData.rawCode
        literaturePudlakTheorem5ExternalScaleData.scale := by
  rcases exactFamily_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact auditIndex_theorem5_power_bound_iff_rescaled pkg

theorem exactConvention_checklist_to_theorem5_lower_source_code_eq_rescaled_pudlak
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale m =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        PudlakTheorem5MinimalExternalFieldsSurface.scale m := by
  rcases exactConvention_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact auditIndex_theorem5_lower_source_code_eq_rescaled_pudlak pkg m

theorem splitMinChecked_checklist_to_theorem5_lower_source_code_eq_rescaled_pudlak
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale m =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        PudlakTheorem5MinimalExternalFieldsSurface.scale m := by
  rcases splitMinChecked_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact auditIndex_theorem5_lower_source_code_eq_rescaled_pudlak pkg m

theorem exactFamily_checklist_to_theorem5_lower_source_code_eq_rescaled_pudlak
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale m =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        PudlakTheorem5MinimalExternalFieldsSurface.scale m := by
  rcases exactFamily_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact auditIndex_theorem5_lower_source_code_eq_rescaled_pudlak pkg m

theorem exactConvention_checklist_to_theorem5_certificate_presentation_iff_rescaled
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    Nonempty LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty LiteraturePudlakTheorem5RescaledLowerBoundCertificate := by
  rcases exactConvention_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact auditIndex_theorem5_certificate_presentation_iff_rescaled pkg

theorem splitMinChecked_checklist_to_theorem5_certificate_presentation_iff_rescaled
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    Nonempty LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty LiteraturePudlakTheorem5RescaledLowerBoundCertificate := by
  rcases splitMinChecked_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact auditIndex_theorem5_certificate_presentation_iff_rescaled pkg

theorem exactFamily_checklist_to_theorem5_certificate_presentation_iff_rescaled
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    Nonempty LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty LiteraturePudlakTheorem5RescaledLowerBoundCertificate := by
  rcases exactFamily_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact auditIndex_theorem5_certificate_presentation_iff_rescaled pkg

theorem exactConvention_checklist_to_gap_no_weakening_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    Nonempty (Σ' pkg : PublicAuditIndexPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      Month3Month4GapNoWeakeningStatement
        pkg.exactness_package.public_release.assembly) := by
  rcases exactConvention_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact ⟨⟨pkg, auditIndex_gap_no_weakening_statement pkg⟩⟩

theorem exactConvention_checklist_to_public_gap_instantiation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) := by
  rcases exactConvention_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact auditIndex_to_public_gap_instantiation pkg

theorem exactConvention_checklist_not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert)) :
    ¬ MainRationality := by
  rcases exactConvention_checklist_to_audit_index h checklist with ⟨pkg⟩
  exact auditIndex_not_main_rationality pkg

end SondowProjectMonth3Month4PublicAuditIndexSurface
end SondowMainCheckedCodeBridge
