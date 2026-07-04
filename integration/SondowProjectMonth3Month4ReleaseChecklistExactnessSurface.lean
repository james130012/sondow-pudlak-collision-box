/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4TheoremIndexSurface

/-!
# Month 3/Month 4 release-checklist exactness surface

This module packages the final Month 3/Month 4 release route with the exact
audit fields that a reviewer should be able to trace from the paper-facing
theorem index:

* the public release package and the theorem-index paper route are equivalent;
* the canonical import package and the paper route are equivalent;
* the release package exposes the Month 3 checker-trace budget statement;
* the same release package exposes the Month 4 minimal external fields.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4ReleaseChecklistExactnessSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4BridgeLinkSurface
open SondowProjectMonth3Month4CanonicalImportSurface
open SondowProjectMonth3Month4CollisionReadinessSurface
open SondowProjectMonth3Month4GapNoWeakeningSurface
open SondowProjectMonth3Month4PublicReleaseSurface
open SondowProjectMonth3Month4PaperReadyTheoremSurface
open SondowProjectMonth3Month4TheoremIndexSurface

structure ReleaseChecklistExactnessStatement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (public_release :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Prop where
  public_release_statement :
    Month3Month4PublicReleaseStatement public_release.assembly
  theorem_index_paper_route :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound
  paper_route_iff_public_release :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Nonempty (Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound)
  canonical_import_iff_paper_route :
    Nonempty (Month3Month4CanonicalPackage
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Month3Month4IndexedPaperRoute
        rootSide MainRationality SondowAccepted bounds bound
  gap_no_weakening_statement :
    Month3Month4GapNoWeakeningStatement public_release.assembly
  canonical_bridge_link :
    Month3Month4CanonicalBridgeLinkStatement public_release.assembly
  readiness :
    CollisionReadinessStatement public_release.assembly.index
  month3_checker_trace_budget_statement :
    Month3CheckerTraceBudgetSurface.Statement
      public_release.assembly.index
  month4_lower_bound_source_statement :
    PudlakTheorem5CanonicalImportSurface.LowerBoundSourceStatement
  month4_minimal_external_fields_statement :
    PudlakTheorem5CanonicalImportSurface.MinimalExternalFieldsStatement
  checker_trace_size_le_bound :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((Month3CheckerTraceBudgetSurface.traceAt
        public_release.assembly.index n haccepted).size : Real) ≤ bound n
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
    (public_release :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound) :
    ReleaseChecklistExactnessStatement public_release where
  public_release_statement :=
    SondowProjectMonth3Month4PublicReleaseSurface.statement
      public_release.assembly
  theorem_index_paper_route := ⟨public_release⟩
  paper_route_iff_public_release :=
    SondowProjectMonth3Month4TheoremIndexSurface.paper_route_iff_public_release
  canonical_import_iff_paper_route :=
    SondowProjectMonth3Month4PaperReadyTheoremSurface.canonical_import_iff_paper_ready_route
  gap_no_weakening_statement :=
    public_release.gap_no_weakening_statement
  canonical_bridge_link :=
    public_release.gap_no_weakening_statement.canonical_import
  readiness :=
    public_release.gap_no_weakening_statement.canonical_import.readiness
  month3_checker_trace_budget_statement :=
    public_release.gap_no_weakening_statement.canonical_import
      |>.readiness.month3_checker_trace_budget_statement
  month4_lower_bound_source_statement :=
    public_release.gap_no_weakening_statement.canonical_import
      |>.readiness.month4_lower_bound_source_statement
  month4_minimal_external_fields_statement :=
    public_release.gap_no_weakening_statement.canonical_import
      |>.readiness.month4_minimal_external_fields_statement
  checker_trace_size_le_bound :=
    public_release.gap_no_weakening_statement.canonical_import
      |>.readiness.checker_trace_size_le_bound
  theorem5_scale_eq_power_bound :=
    public_release.gap_no_weakening_statement.canonical_import
      |>.readiness.theorem5_scale_eq_power_bound
  public_gap_instantiation :=
    public_release_to_public_gap_instantiation public_release
  not_main_rationality :=
    public_release_not_main_rationality public_release

theorem statement_iff_public_release_and_readiness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (public_release :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound) :
    ReleaseChecklistExactnessStatement public_release ↔
      Month3Month4PublicReleaseStatement public_release.assembly ∧
        CollisionReadinessStatement public_release.assembly.index := by
  constructor
  · intro h
    exact ⟨h.public_release_statement, h.readiness⟩
  · intro _h
    exact statement public_release

structure ReleaseChecklistExactnessPackage
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) where
  public_release :
    Month3Month4PublicReleasePackage
      rootSide MainRationality SondowAccepted bounds bound
  exactness :
    ReleaseChecklistExactnessStatement public_release

namespace ReleaseChecklistExactnessPackage

def ofPublicRelease
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (public_release :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound) :
    ReleaseChecklistExactnessPackage
      rootSide MainRationality SondowAccepted bounds bound where
  public_release := public_release
  exactness := statement public_release

end ReleaseChecklistExactnessPackage

theorem exactnessPackage_nonempty_iff_public_release_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty
        (ReleaseChecklistExactnessPackage
          rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty
        (Month3Month4PublicReleasePackage
          rootSide MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨pkg⟩
    exact ⟨pkg.public_release⟩
  · intro h
    rcases h with ⟨public_release⟩
    exact ⟨ReleaseChecklistExactnessPackage.ofPublicRelease public_release⟩

theorem paper_route_iff_exactness_package
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Nonempty
        (ReleaseChecklistExactnessPackage
          rootSide MainRationality SondowAccepted bounds bound) :=
  SondowProjectMonth3Month4TheoremIndexSurface.paper_route_iff_public_release.trans
    exactnessPackage_nonempty_iff_public_release_nonempty.symm

theorem canonical_import_iff_exactness_package
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty
        (Month3Month4CanonicalPackage
          rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty
        (ReleaseChecklistExactnessPackage
          rootSide MainRationality SondowAccepted bounds bound) :=
  SondowProjectMonth3Month4PaperReadyTheoremSurface.canonical_import_iff_paper_ready_route.trans
      paper_route_iff_exactness_package

theorem exactConvention_checklist_iff_exactness_package
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
        (ReleaseChecklistExactnessPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (SondowProjectMonth3Month4TheoremIndexSurface.exactConvention_checklist_iff_paper_route
    h).trans
      paper_route_iff_exactness_package

theorem splitMinChecked_checklist_iff_exactness_package
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
        (ReleaseChecklistExactnessPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (SondowProjectMonth3Month4TheoremIndexSurface.splitMinChecked_checklist_iff_paper_route
    h).trans
      paper_route_iff_exactness_package

theorem exactFamily_checklist_iff_exactness_package
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
        (ReleaseChecklistExactnessPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (SondowProjectMonth3Month4TheoremIndexSurface.exactFamily_checklist_iff_paper_route
    h).trans
      paper_route_iff_exactness_package

theorem exactnessPackage_month3_checker_trace_budget_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      ReleaseChecklistExactnessPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Month3CheckerTraceBudgetSurface.Statement
      pkg.public_release.assembly.index :=
  pkg.exactness.month3_checker_trace_budget_statement

theorem exactnessPackage_month4_minimal_external_fields_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (_pkg :
      ReleaseChecklistExactnessPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5CanonicalImportSurface.MinimalExternalFieldsStatement :=
  PudlakTheorem5CanonicalImportSurface.minimalExternalFieldsStatement

theorem exactnessPackage_trace_size_le_bound
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      ReleaseChecklistExactnessPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((Month3CheckerTraceBudgetSurface.traceAt
      pkg.public_release.assembly.index n haccepted).size : Real) ≤ bound n :=
  pkg.exactness.checker_trace_size_le_bound n haccepted

theorem exactnessPackage_to_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      ReleaseChecklistExactnessPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  pkg.exactness.public_gap_instantiation

theorem exactnessPackage_not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      ReleaseChecklistExactnessPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  pkg.exactness.not_main_rationality

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
    Nonempty (Σ' pkg : ReleaseChecklistExactnessPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      Month3CheckerTraceBudgetSurface.Statement
        pkg.public_release.assembly.index) := by
  rcases (exactConvention_checklist_iff_exactness_package h).1
    checklist with ⟨pkg⟩
  exact ⟨⟨pkg, exactnessPackage_month3_checker_trace_budget_statement pkg⟩⟩

theorem splitMinChecked_checklist_to_month3_checker_trace_budget_package
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
    Nonempty (Σ' pkg : ReleaseChecklistExactnessPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      Month3CheckerTraceBudgetSurface.Statement
        pkg.public_release.assembly.index) := by
  rcases (splitMinChecked_checklist_iff_exactness_package h).1
    checklist with ⟨pkg⟩
  exact ⟨⟨pkg, exactnessPackage_month3_checker_trace_budget_statement pkg⟩⟩

theorem exactFamily_checklist_to_month3_checker_trace_budget_package
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
    Nonempty (Σ' pkg : ReleaseChecklistExactnessPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      Month3CheckerTraceBudgetSurface.Statement
        pkg.public_release.assembly.index) := by
  rcases (exactFamily_checklist_iff_exactness_package h).1
    checklist with ⟨pkg⟩
  exact ⟨⟨pkg, exactnessPackage_month3_checker_trace_budget_statement pkg⟩⟩

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
    Nonempty (Σ' _pkg : ReleaseChecklistExactnessPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      PudlakTheorem5CanonicalImportSurface.MinimalExternalFieldsStatement) := by
  rcases (exactConvention_checklist_iff_exactness_package h).1
    checklist with ⟨pkg⟩
  exact ⟨⟨pkg, exactnessPackage_month4_minimal_external_fields_statement pkg⟩⟩

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
    Nonempty (Σ' _pkg : ReleaseChecklistExactnessPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      PudlakTheorem5CanonicalImportSurface.MinimalExternalFieldsStatement) := by
  rcases (splitMinChecked_checklist_iff_exactness_package h).1
    checklist with ⟨pkg⟩
  exact ⟨⟨pkg, exactnessPackage_month4_minimal_external_fields_statement pkg⟩⟩

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
    Nonempty (Σ' _pkg : ReleaseChecklistExactnessPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      PudlakTheorem5CanonicalImportSurface.MinimalExternalFieldsStatement) := by
  rcases (exactFamily_checklist_iff_exactness_package h).1
    checklist with ⟨pkg⟩
  exact ⟨⟨pkg, exactnessPackage_month4_minimal_external_fields_statement pkg⟩⟩

end SondowProjectMonth3Month4ReleaseChecklistExactnessSurface
end SondowMainCheckedCodeBridge
