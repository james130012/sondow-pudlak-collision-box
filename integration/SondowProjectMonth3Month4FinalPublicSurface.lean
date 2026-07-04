/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4Month3ObjectProjectionSurface
import integration.SondowProjectMonth3Month4Month4ExactExternalBoundaryProjectionSurface

/-!
# Month 3/Month 4 final public surface

This is the thin public entrypoint for the Month 3/Month 4 route.  It gives
short final theorem names for the release-level collision statement, the public
gap consequence, the Month 3 accepted object projection, and the Month 4 exact
Pudlak-theorem-5 boundary equations.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4FinalPublicSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4TheoremIndexSurface
open SondowProjectMonth3Month4VerifiedProjectIndexSurface
open SondowProjectMonth3Month4AcceptedBoundedPAChainSurface
open SondowProjectMonth3Month4PublicReleaseIndexSurface
open SondowProjectMonth3Month4Month3ObjectProjectionSurface
open SondowProjectMonth3Month4Month4ExactExternalBoundaryProjectionSurface

abbrev FinalPublicRelease
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop :=
  PublicReleaseIndex rootSide MainRationality SondowAccepted bounds bound

abbrev FinalPublicReleaseStatement
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop :=
  (Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ∧
    ∃ n : Nat, SondowAccepted n) ↔
    FinalPublicRelease
      rootSide MainRationality SondowAccepted bounds bound

structure FinalCombinedAuditCertificate
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop where
  final_release :
    FinalPublicRelease
      rootSide MainRationality SondowAccepted bounds bound
  month3_same_object_closure :
    Month3AcceptedSameObjectClosureExport
      rootSide MainRationality SondowAccepted bounds bound
  month3_bounded_pa_interface :
    ∃ n : Nat, ∃ _haccepted : SondowAccepted n,
      ∃ _pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        Nonempty (CanonicalProofCertificateAt bound n) ∧
        CanonicalProofCertificateAccepted bound n ∧
        Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ∧
        (Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ↔
          Nonempty (CanonicalProofCertificateAt bound n))
  month3_checker_trace_conclusion_eq_finiteConsistency :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        (chainPackage_accepted_to_checker_trace
          pkg.chain_package n haccepted).cert.conclusion =
          finiteConsistencyFormula n
  month4_same_object_closure :
    Month4ExactExternalSameObjectClosure
      rootSide MainRationality SondowAccepted bounds bound
  month4_full_boundary_interface :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement ∧
        PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement ∧
          PudlakTheorem5ExactMinimalFieldPackageSurface.Statement
  month4_exact_project_iff_canonical_import :
    PudlakTheorem5ExactProjectInstance.Statement ↔
      PudlakTheorem5CanonicalImportSurface.Statement
  public_gap_instantiation :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality)
  not_main_rationality : ¬ MainRationality

abbrev FinalCombinedAuditStatement
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop :=
  (Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ∧
    ∃ n : Nat, SondowAccepted n) ↔
    FinalCombinedAuditCertificate
      rootSide MainRationality SondowAccepted bounds bound

theorem paper_route_and_accepted_iff_final_public_release
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    FinalPublicReleaseStatement
      rootSide MainRationality SondowAccepted bounds bound :=
  paper_route_and_accepted_iff_public_release_index

theorem exactConvention_checklist_and_accepted_iff_final_public_release
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
      FinalPublicRelease
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  exactConvention_checklist_and_accepted_iff_public_release_index h

theorem splitMinChecked_checklist_and_accepted_iff_final_public_release
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
      FinalPublicRelease
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  splitMinChecked_checklist_and_accepted_iff_public_release_index h

theorem exactFamily_checklist_and_accepted_iff_final_public_release
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
      FinalPublicRelease
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  exactFamily_checklist_and_accepted_iff_public_release_index h

theorem final_public_release_to_month3_object_projection
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (release :
      FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound) :
    Month3AcceptedObjectProjection
      rootSide MainRationality SondowAccepted bounds bound :=
  public_release_index_to_month3_object_projection release

theorem final_public_release_to_month3_same_object_closure
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (release :
      FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound) :
    Month3AcceptedSameObjectClosureExport
      rootSide MainRationality SondowAccepted bounds bound :=
  (final_public_release_to_month3_object_projection
    release).same_object_closure

theorem final_public_release_to_month3_bounded_pa_interface
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (release :
      FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound) :
    ∃ n : Nat, ∃ _haccepted : SondowAccepted n,
      ∃ _pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        Nonempty (CanonicalProofCertificateAt bound n) ∧
        CanonicalProofCertificateAccepted bound n ∧
        Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ∧
        (Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ↔
          Nonempty (CanonicalProofCertificateAt bound n)) := by
  rcases final_public_release_to_month3_same_object_closure release with
    ⟨n, haccepted, pkg, closure⟩
  exact
    ⟨n, haccepted, pkg,
      closure.canonical_nonempty,
      closure.canonical_certificate_accepted,
      closure.bounded_pa_proof_predicate,
      closure.proof_predicate_iff_certificate_at⟩

theorem final_public_release_to_month3_checker_trace_conclusion
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (release :
      FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound) :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        (chainPackage_accepted_to_checker_trace
          pkg.chain_package n haccepted).cert.conclusion =
          canonicalPudlakTargetFamilySpec.target n :=
  (final_public_release_to_month3_object_projection
    release).checker_trace_conclusion

theorem final_public_release_to_month3_canonical_conclusion_eq_finiteConsistency
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (release :
      FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound) :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        (chainPackage_accepted_to_canonical_certificate
          pkg.chain_package n haccepted).proof.conclusion =
          finiteConsistencyFormula n :=
  (final_public_release_to_month3_object_projection
    release).canonical_conclusion_eq_finiteConsistency

theorem final_public_release_to_month3_checker_trace_conclusion_eq_finiteConsistency
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (release :
      FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound) :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        (chainPackage_accepted_to_checker_trace
          pkg.chain_package n haccepted).cert.conclusion =
          finiteConsistencyFormula n := by
  rcases final_public_release_to_month3_same_object_closure release with
    ⟨n, haccepted, pkg, closure⟩
  exact
    ⟨n, haccepted, pkg,
      closure.checker_trace_conclusion_eq_finiteConsistency⟩

theorem final_public_release_to_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (release :
      FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  public_release_index_to_public_gap_instantiation release

theorem final_public_release_not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (release :
      FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  public_release_index_not_main_rationality release

theorem final_public_release_to_month4_raw_rescaled_power_chain
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (release :
      FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  public_release_index_to_month4_raw_rescaled_power_chain release n

theorem final_public_release_to_month4_same_object_closure
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (release :
      FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound) :
    Month4ExactExternalSameObjectClosure
      rootSide MainRationality SondowAccepted bounds bound :=
  public_release_index_to_month4_same_object_closure release

theorem final_public_release_to_month4_full_boundary_interface
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (release :
      FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement ∧
        PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement ∧
          PudlakTheorem5ExactMinimalFieldPackageSurface.Statement :=
  public_release_index_to_month4_full_boundary_interface release

theorem final_public_release_to_month4_exact_project_iff_canonical_import
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (release :
      FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5ExactProjectInstance.Statement ↔
      PudlakTheorem5CanonicalImportSurface.Statement :=
  public_release_index_to_month4_exact_project_iff_canonical_import release

theorem final_public_release_to_month4_lower_source_code_eq_rescaled_pudlak
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (release :
      FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  public_release_index_to_month4_lower_source_code_eq_rescaled_pudlak
    release n

theorem final_public_release_to_month4_power_bound_iff_rescaled
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (release :
      FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound) :
    LiteraturePudlakTheorem5PowerBoundLowerBound
        literaturePudlakTheorem5ExternalScaleData ↔
      StrongRescaledExternalStrengthenedLowerBound
        literaturePudlakTheorem5ExternalScaleData.rawCode
        literaturePudlakTheorem5ExternalScaleData.scale :=
  public_release_index_to_month4_power_bound_iff_rescaled release

theorem final_public_release_to_month4_certificate_presentation_iff_rescaled
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (release :
      FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty LiteraturePudlakTheorem5RescaledLowerBoundCertificate :=
  public_release_index_to_month4_certificate_presentation_iff_rescaled release

theorem final_public_release_to_month4_canonical_scale_eq_power_bound
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (release :
      FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    PudlakTheorem5CanonicalImportSurface.theorem5Scale n =
      PudlakTheorem5CanonicalImportSurface.theorem5TimeConstructibleBound n ^
        PudlakTheorem5CanonicalImportSurface.theorem5Exponent :=
  public_release_index_to_month4_canonical_scale_eq_power_bound release n

theorem final_combined_audit_certificate_of_release
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (release :
      FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound) :
    FinalCombinedAuditCertificate
      rootSide MainRationality SondowAccepted bounds bound where
  final_release := release
  month3_same_object_closure :=
    final_public_release_to_month3_same_object_closure release
  month3_bounded_pa_interface :=
    final_public_release_to_month3_bounded_pa_interface release
  month3_checker_trace_conclusion_eq_finiteConsistency :=
    final_public_release_to_month3_checker_trace_conclusion_eq_finiteConsistency
      release
  month4_same_object_closure :=
    final_public_release_to_month4_same_object_closure release
  month4_full_boundary_interface :=
    final_public_release_to_month4_full_boundary_interface release
  month4_exact_project_iff_canonical_import :=
    final_public_release_to_month4_exact_project_iff_canonical_import release
  public_gap_instantiation :=
    final_public_release_to_public_gap_instantiation release
  not_main_rationality :=
    final_public_release_not_main_rationality release

theorem final_public_release_iff_final_combined_audit_certificate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound ↔
      FinalCombinedAuditCertificate
        rootSide MainRationality SondowAccepted bounds bound := by
  constructor
  · intro release
    exact final_combined_audit_certificate_of_release release
  · intro cert
    exact cert.final_release

theorem paper_route_and_accepted_iff_final_combined_audit_certificate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    FinalCombinedAuditStatement
      rootSide MainRationality SondowAccepted bounds bound :=
  paper_route_and_accepted_iff_final_public_release.trans
    final_public_release_iff_final_combined_audit_certificate

theorem exactConvention_checklist_and_accepted_iff_final_combined_audit_certificate
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
      FinalCombinedAuditCertificate
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (exactConvention_checklist_and_accepted_iff_final_public_release h).trans
    final_public_release_iff_final_combined_audit_certificate

theorem splitMinChecked_checklist_and_accepted_iff_final_combined_audit_certificate
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
      FinalCombinedAuditCertificate
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (splitMinChecked_checklist_and_accepted_iff_final_public_release h).trans
    final_public_release_iff_final_combined_audit_certificate

theorem exactFamily_checklist_and_accepted_iff_final_combined_audit_certificate
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
      FinalCombinedAuditCertificate
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (exactFamily_checklist_and_accepted_iff_final_public_release h).trans
    final_public_release_iff_final_combined_audit_certificate

theorem exactFamily_route_to_final_public_release
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
    FinalPublicRelease
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  exactFamily_route_to_public_release_index h route

theorem exactFamily_route_to_final_month3_object_projection
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
    Month3AcceptedObjectProjection
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  final_public_release_to_month3_object_projection
    (exactFamily_route_to_final_public_release h route)

theorem exactFamily_route_to_final_month3_same_object_closure
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
    Month3AcceptedSameObjectClosureExport
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  final_public_release_to_month3_same_object_closure
    (exactFamily_route_to_final_public_release h route)

theorem exactFamily_route_to_final_month3_bounded_pa_interface
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
    ∃ k : Nat, ∃ _haccepted : SondowAccepted k,
      ∃ _pkg : Month3Month4VerifiedProjectInstantiation
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
        Nonempty (CanonicalProofCertificateAt bound k) ∧
        CanonicalProofCertificateAccepted bound k ∧
        Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound k ∧
        (Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound k ↔
          Nonempty (CanonicalProofCertificateAt bound k)) :=
  final_public_release_to_month3_bounded_pa_interface
    (exactFamily_route_to_final_public_release h route)

theorem exactFamily_route_to_final_month4_same_object_closure
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
  final_public_release_to_month4_same_object_closure
    (exactFamily_route_to_final_public_release h route)

theorem exactFamily_route_to_final_month4_full_boundary_interface
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
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement ∧
        PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement ∧
          PudlakTheorem5ExactMinimalFieldPackageSurface.Statement :=
  final_public_release_to_month4_full_boundary_interface
    (exactFamily_route_to_final_public_release h route)

theorem exactFamily_route_to_final_month3_checker_trace_conclusion
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
    ∃ k : Nat, ∃ haccepted : SondowAccepted k,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
        (chainPackage_accepted_to_checker_trace
          pkg.chain_package k haccepted).cert.conclusion =
          canonicalPudlakTargetFamilySpec.target k :=
  final_public_release_to_month3_checker_trace_conclusion
    (exactFamily_route_to_final_public_release h route)

theorem exactFamily_route_to_final_month3_canonical_conclusion_eq_finiteConsistency
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
    ∃ k : Nat, ∃ haccepted : SondowAccepted k,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
        (chainPackage_accepted_to_canonical_certificate
          pkg.chain_package k haccepted).proof.conclusion =
          finiteConsistencyFormula k :=
  final_public_release_to_month3_canonical_conclusion_eq_finiteConsistency
    (exactFamily_route_to_final_public_release h route)

theorem exactFamily_route_to_final_month3_checker_trace_conclusion_eq_finiteConsistency
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
    ∃ k : Nat, ∃ haccepted : SondowAccepted k,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
        (chainPackage_accepted_to_checker_trace
          pkg.chain_package k haccepted).cert.conclusion =
          finiteConsistencyFormula k :=
  final_public_release_to_month3_checker_trace_conclusion_eq_finiteConsistency
    (exactFamily_route_to_final_public_release h route)

theorem exactFamily_route_to_final_public_gap_instantiation
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
  final_public_release_to_public_gap_instantiation
    (exactFamily_route_to_final_public_release h route)

theorem exactFamily_route_to_final_not_main_rationality
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
  final_public_release_not_main_rationality
    (exactFamily_route_to_final_public_release h route)

end SondowProjectMonth3Month4FinalPublicSurface
end SondowMainCheckedCodeBridge
