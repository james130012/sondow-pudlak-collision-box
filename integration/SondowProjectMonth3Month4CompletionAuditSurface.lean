/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4FinalPublicSurface

/-!
# Month 3/Month 4 completion audit surface

This module is the final audit checklist for the Month 3/Month 4 route.  It
does not introduce a new proof path: it repackages the final combined audit
certificate into explicitly named completion fields, so an auditor can check
that the bounded PA predicate interface, the Pudlak theorem-5 exact boundary,
the public gap object, and `¬ MainRationality` are all present at the same
public entrypoint.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4CompletionAuditSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4TheoremIndexSurface
open SondowProjectMonth3Month4VerifiedProjectIndexSurface
open SondowProjectMonth3Month4AcceptedBoundedPAChainSurface
open SondowProjectMonth3Month4Month3ObjectProjectionSurface
open SondowProjectMonth3Month4Month4ExactExternalBoundaryProjectionSurface
open SondowProjectMonth3Month4FinalPublicSurface

structure CompletionAuditCertificate
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop where
  combined_certificate :
    FinalCombinedAuditCertificate
      rootSide MainRationality SondowAccepted bounds bound
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
  public_gap_instantiation :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality)
  not_main_rationality : ¬ MainRationality

abbrev CompletionAuditStatement
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop :=
  (Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ∧
    ∃ n : Nat, SondowAccepted n) ↔
    CompletionAuditCertificate
      rootSide MainRationality SondowAccepted bounds bound

abbrev PublicCompletionCertificate
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop :=
  CompletionAuditCertificate
    rootSide MainRationality SondowAccepted bounds bound

abbrev PublicCompletionStatement
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop :=
  CompletionAuditStatement
    rootSide MainRationality SondowAccepted bounds bound

theorem completion_audit_certificate_of_final_combined
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      FinalCombinedAuditCertificate
        rootSide MainRationality SondowAccepted bounds bound) :
    CompletionAuditCertificate
      rootSide MainRationality SondowAccepted bounds bound where
  combined_certificate := cert
  final_release := cert.final_release
  month3_same_object_closure := cert.month3_same_object_closure
  month3_bounded_pa_interface := cert.month3_bounded_pa_interface
  month3_checker_trace_conclusion_eq_finiteConsistency :=
    cert.month3_checker_trace_conclusion_eq_finiteConsistency
  month4_same_object_closure := cert.month4_same_object_closure
  month4_full_boundary_interface := cert.month4_full_boundary_interface
  month4_exact_project_iff_canonical_import :=
    cert.month4_exact_project_iff_canonical_import
  month4_raw_rescaled_power_chain :=
    cert.month4_same_object_closure.raw_rescaled_power_chain
  month4_lower_source_code_eq_rescaled_pudlak :=
    cert.month4_same_object_closure.lower_source_code_eq_rescaled_pudlak
  month4_power_bound_iff_rescaled :=
    cert.month4_same_object_closure.power_bound_iff_rescaled
  month4_certificate_presentation_iff_rescaled :=
    cert.month4_same_object_closure.certificate_presentation_iff_rescaled
  public_gap_instantiation := cert.public_gap_instantiation
  not_main_rationality := cert.not_main_rationality

theorem final_combined_iff_completion_audit_certificate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    FinalCombinedAuditCertificate
        rootSide MainRationality SondowAccepted bounds bound ↔
      CompletionAuditCertificate
        rootSide MainRationality SondowAccepted bounds bound := by
  constructor
  · intro cert
    exact completion_audit_certificate_of_final_combined cert
  · intro audit
    exact audit.combined_certificate

theorem final_public_release_iff_completion_audit_certificate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    FinalPublicRelease
        rootSide MainRationality SondowAccepted bounds bound ↔
      CompletionAuditCertificate
        rootSide MainRationality SondowAccepted bounds bound :=
  final_public_release_iff_final_combined_audit_certificate.trans
    final_combined_iff_completion_audit_certificate

theorem paper_route_and_accepted_iff_completion_audit_certificate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    CompletionAuditStatement
      rootSide MainRationality SondowAccepted bounds bound :=
  paper_route_and_accepted_iff_final_combined_audit_certificate.trans
    final_combined_iff_completion_audit_certificate

theorem paper_route_and_accepted_iff_public_completion
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    PublicCompletionStatement
      rootSide MainRationality SondowAccepted bounds bound :=
  paper_route_and_accepted_iff_completion_audit_certificate

theorem exactConvention_checklist_and_accepted_iff_completion_audit_certificate
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
      CompletionAuditCertificate
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (exactConvention_checklist_and_accepted_iff_final_combined_audit_certificate
    h).trans
    final_combined_iff_completion_audit_certificate

theorem splitMinChecked_checklist_and_accepted_iff_completion_audit_certificate
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
      CompletionAuditCertificate
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (splitMinChecked_checklist_and_accepted_iff_final_combined_audit_certificate
    h).trans
    final_combined_iff_completion_audit_certificate

theorem exactFamily_checklist_and_accepted_iff_completion_audit_certificate
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
      CompletionAuditCertificate
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (exactFamily_checklist_and_accepted_iff_final_combined_audit_certificate
    h).trans
    final_combined_iff_completion_audit_certificate

theorem exactFamily_checklist_and_accepted_iff_public_completion
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
      PublicCompletionCertificate
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  exactFamily_checklist_and_accepted_iff_completion_audit_certificate h

theorem exactFamily_route_to_completion_audit_certificate
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
    CompletionAuditCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (exactFamily_checklist_and_accepted_iff_completion_audit_certificate
    h).mp route

theorem exactFamily_route_to_public_completion_certificate
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
    PublicCompletionCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  exactFamily_route_to_completion_audit_certificate h route

theorem completion_audit_to_month3_bounded_pa_interface
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (audit :
      CompletionAuditCertificate
        rootSide MainRationality SondowAccepted bounds bound) :
    ∃ n : Nat, ∃ _haccepted : SondowAccepted n,
      ∃ _pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        Nonempty (CanonicalProofCertificateAt bound n) ∧
        CanonicalProofCertificateAccepted bound n ∧
        Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ∧
        (Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ↔
          Nonempty (CanonicalProofCertificateAt bound n)) :=
  audit.month3_bounded_pa_interface

theorem completion_audit_to_month4_full_boundary_interface
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (audit :
      CompletionAuditCertificate
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement ∧
        PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement ∧
          PudlakTheorem5ExactMinimalFieldPackageSurface.Statement :=
  audit.month4_full_boundary_interface

theorem completion_audit_to_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (audit :
      CompletionAuditCertificate
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  audit.public_gap_instantiation

theorem completion_audit_not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (audit :
      CompletionAuditCertificate
        rootSide MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  audit.not_main_rationality

theorem public_completion_to_month3_bounded_pa_interface
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (audit :
      PublicCompletionCertificate
        rootSide MainRationality SondowAccepted bounds bound) :
    ∃ n : Nat, ∃ _haccepted : SondowAccepted n,
      ∃ _pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        Nonempty (CanonicalProofCertificateAt bound n) ∧
        CanonicalProofCertificateAccepted bound n ∧
        Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ∧
        (Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ↔
          Nonempty (CanonicalProofCertificateAt bound n)) :=
  completion_audit_to_month3_bounded_pa_interface audit

theorem public_completion_to_month4_full_boundary_interface
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (audit :
      PublicCompletionCertificate
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement ∧
        PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement ∧
          PudlakTheorem5ExactMinimalFieldPackageSurface.Statement :=
  completion_audit_to_month4_full_boundary_interface audit

theorem public_completion_to_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (audit :
      PublicCompletionCertificate
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  completion_audit_to_public_gap_instantiation audit

theorem public_completion_not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (audit :
      PublicCompletionCertificate
        rootSide MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  completion_audit_not_main_rationality audit

end SondowProjectMonth3Month4CompletionAuditSurface
end SondowMainCheckedCodeBridge
