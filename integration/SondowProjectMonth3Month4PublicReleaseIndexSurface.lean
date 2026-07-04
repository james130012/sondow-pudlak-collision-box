/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4PublicCitationEndpointSurface

/-!
# Month 3/Month 4 public release index surface

This module is the compact public release index for the Month 3/Month 4
route.  It turns the citation endpoint into a single release-level object and
projects the theorem-5 exact-boundary equations that should be cited from the
paper or public README.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4PublicReleaseIndexSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4TheoremIndexSurface
open SondowProjectMonth3Month4ReleaseTheoremExportSurface
open SondowProjectMonth3Month4PublicCitationEndpointSurface

structure PublicReleaseIndex
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop where
  citation_endpoint :
    PublicReleaseCitationEndpoint
      rootSide MainRationality SondowAccepted bounds bound
  month3_budget_projection :
    Month3AcceptedBudgetProjection
      rootSide MainRationality SondowAccepted bounds bound
  public_gap_instantiation :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality)
  not_main_rationality : ¬ MainRationality
  month4_exact_external_boundary :
    Month4ExactExternalBoundaryExport
      rootSide MainRationality SondowAccepted bounds bound
  month4_raw_rescaled_power_chain :
    ∀ n : Nat,
      PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
          PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n ∧
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
          rescaledPudlakStrengthenedFiniteConsistencyCode
            PudlakTheorem5MinimalExternalFieldsSurface.scale n
  month4_lower_source_code_eq_rescaled_pudlak :
    ∀ n : Nat,
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
  month4_canonical_scale_eq_power_bound :
    ∀ n : Nat,
      PudlakTheorem5CanonicalImportSurface.theorem5Scale n =
        PudlakTheorem5CanonicalImportSurface.theorem5TimeConstructibleBound n ^
          PudlakTheorem5CanonicalImportSurface.theorem5Exponent
  month4_canonical_scale_id_le :
    ∀ n : Nat, n ≤ PudlakTheorem5CanonicalImportSurface.theorem5Scale n
  month4_canonical_scale_polynomial_bound :
    is_polynomial_bound
      (fun n : Nat =>
        (PudlakTheorem5CanonicalImportSurface.theorem5Scale n : Real))

theorem public_release_index_of_citation_endpoint
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (endpoint :
      PublicReleaseCitationEndpoint
        rootSide MainRationality SondowAccepted bounds bound) :
    PublicReleaseIndex
      rootSide MainRationality SondowAccepted bounds bound where
  citation_endpoint := endpoint
  month3_budget_projection :=
    public_release_citation_endpoint_to_month3_budget_projection endpoint
  public_gap_instantiation :=
    public_release_citation_endpoint_to_public_gap_instantiation endpoint
  not_main_rationality :=
    public_release_citation_endpoint_not_main_rationality endpoint
  month4_exact_external_boundary :=
    public_release_citation_endpoint_to_month4_exact_external_boundary endpoint
  month4_raw_rescaled_power_chain :=
    endpoint.month4_exact_external_boundary.raw_rescaled_power_chain
  month4_lower_source_code_eq_rescaled_pudlak :=
    endpoint.month4_exact_external_boundary.lower_source_code_eq_rescaled_pudlak
  month4_power_bound_iff_rescaled :=
    endpoint.month4_exact_external_boundary.power_bound_iff_rescaled
  month4_certificate_presentation_iff_rescaled :=
    endpoint.month4_exact_external_boundary.certificate_presentation_iff_rescaled
  month4_canonical_scale_eq_power_bound :=
    endpoint.month4_exact_external_boundary.canonical_scale_eq_power_bound
  month4_canonical_scale_id_le :=
    endpoint.month4_exact_external_boundary.canonical_scale_id_le
  month4_canonical_scale_polynomial_bound :=
    endpoint.month4_exact_external_boundary.canonical_scale_polynomial_bound

theorem citation_endpoint_iff_public_release_index
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    PublicReleaseCitationEndpoint
      rootSide MainRationality SondowAccepted bounds bound ↔
      PublicReleaseIndex
        rootSide MainRationality SondowAccepted bounds bound := by
  constructor
  · intro endpoint
    exact public_release_index_of_citation_endpoint endpoint
  · intro index
    exact index.citation_endpoint

abbrev PublicReleaseIndexStatement
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop :=
  (Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ∧
    ∃ n : Nat, SondowAccepted n) ↔
    PublicReleaseIndex
      rootSide MainRationality SondowAccepted bounds bound

theorem paper_route_and_accepted_iff_public_release_index
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    PublicReleaseIndexStatement
      rootSide MainRationality SondowAccepted bounds bound :=
  paper_route_and_accepted_iff_public_release_citation_endpoint.trans
    citation_endpoint_iff_public_release_index

theorem exactConvention_checklist_and_accepted_iff_public_release_index
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    (Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert) ∧
      ∃ m : Nat, SondowAccepted m) ↔
      PublicReleaseIndex
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (exactConvention_checklist_and_accepted_iff_public_release_citation_endpoint
    h).trans
    citation_endpoint_iff_public_release_index

theorem splitMinChecked_checklist_and_accepted_iff_public_release_index
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    (Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert) ∧
      ∃ m : Nat, SondowAccepted m) ↔
      PublicReleaseIndex
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (splitMinChecked_checklist_and_accepted_iff_public_release_citation_endpoint
    h).trans
    citation_endpoint_iff_public_release_index

theorem exactFamily_checklist_and_accepted_iff_public_release_index
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    (Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert) ∧
      ∃ m : Nat, SondowAccepted m) ↔
      PublicReleaseIndex
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (exactFamily_checklist_and_accepted_iff_public_release_citation_endpoint
    h).trans
    citation_endpoint_iff_public_release_index

theorem public_release_index_to_month3_budget_projection
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index :
      PublicReleaseIndex
        rootSide MainRationality SondowAccepted bounds bound) :
    Month3AcceptedBudgetProjection
      rootSide MainRationality SondowAccepted bounds bound :=
  index.month3_budget_projection

theorem public_release_index_to_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index :
      PublicReleaseIndex
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  index.public_gap_instantiation

theorem public_release_index_not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index :
      PublicReleaseIndex
        rootSide MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  index.not_main_rationality

theorem public_release_index_to_month4_raw_rescaled_power_chain
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
  index.month4_raw_rescaled_power_chain n

theorem public_release_index_to_month4_lower_source_code_eq_rescaled_pudlak
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index :
      PublicReleaseIndex
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  index.month4_lower_source_code_eq_rescaled_pudlak n

theorem public_release_index_to_month4_power_bound_iff_rescaled
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
  index.month4_power_bound_iff_rescaled

theorem public_release_index_to_month4_certificate_presentation_iff_rescaled
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index :
      PublicReleaseIndex
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty LiteraturePudlakTheorem5RescaledLowerBoundCertificate :=
  index.month4_certificate_presentation_iff_rescaled

theorem public_release_index_to_month4_canonical_scale_eq_power_bound
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index :
      PublicReleaseIndex
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    PudlakTheorem5CanonicalImportSurface.theorem5Scale n =
      PudlakTheorem5CanonicalImportSurface.theorem5TimeConstructibleBound n ^
        PudlakTheorem5CanonicalImportSurface.theorem5Exponent :=
  index.month4_canonical_scale_eq_power_bound n

theorem exactFamily_route_to_public_release_index
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
    PublicReleaseIndex
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (exactFamily_checklist_and_accepted_iff_public_release_index h).mp route

theorem exactFamily_route_to_month3_budget_projection
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
    Month3AcceptedBudgetProjection
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  public_release_index_to_month3_budget_projection
    (exactFamily_route_to_public_release_index h route)

theorem exactFamily_route_to_public_gap_instantiation
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
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  public_release_index_to_public_gap_instantiation
    (exactFamily_route_to_public_release_index h route)

theorem exactFamily_route_not_main_rationality
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
    ¬ MainRationality :=
  public_release_index_not_main_rationality
    (exactFamily_route_to_public_release_index h route)

theorem exactFamily_route_to_month4_raw_rescaled_power_chain
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
        ∃ m : Nat, SondowAccepted m)
    (m : Nat) :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode m =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode m ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode m =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale m :=
  public_release_index_to_month4_raw_rescaled_power_chain
    (exactFamily_route_to_public_release_index h route) m

theorem exactFamily_route_to_month4_lower_source_code_eq_rescaled_pudlak
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
        ∃ m : Nat, SondowAccepted m)
    (m : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale m =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        PudlakTheorem5MinimalExternalFieldsSurface.scale m :=
  public_release_index_to_month4_lower_source_code_eq_rescaled_pudlak
    (exactFamily_route_to_public_release_index h route) m

theorem exactFamily_route_to_month4_power_bound_iff_rescaled
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
    LiteraturePudlakTheorem5PowerBoundLowerBound
        literaturePudlakTheorem5ExternalScaleData ↔
      StrongRescaledExternalStrengthenedLowerBound
        literaturePudlakTheorem5ExternalScaleData.rawCode
        literaturePudlakTheorem5ExternalScaleData.scale :=
  public_release_index_to_month4_power_bound_iff_rescaled
    (exactFamily_route_to_public_release_index h route)

theorem exactFamily_route_to_month4_certificate_presentation_iff_rescaled
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
    Nonempty LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty LiteraturePudlakTheorem5RescaledLowerBoundCertificate :=
  public_release_index_to_month4_certificate_presentation_iff_rescaled
    (exactFamily_route_to_public_release_index h route)

theorem exactFamily_route_to_month4_canonical_scale_eq_power_bound
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
        ∃ m : Nat, SondowAccepted m)
    (m : Nat) :
    PudlakTheorem5CanonicalImportSurface.theorem5Scale m =
      PudlakTheorem5CanonicalImportSurface.theorem5TimeConstructibleBound m ^
        PudlakTheorem5CanonicalImportSurface.theorem5Exponent :=
  public_release_index_to_month4_canonical_scale_eq_power_bound
    (exactFamily_route_to_public_release_index h route) m

end SondowProjectMonth3Month4PublicReleaseIndexSurface
end SondowMainCheckedCodeBridge
