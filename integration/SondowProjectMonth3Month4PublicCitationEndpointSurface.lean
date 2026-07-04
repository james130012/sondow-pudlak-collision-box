/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4PaperFacingCollisionTheoremSurface

/-!
# Month 3/Month 4 public citation endpoint surface

This module is the compact citation endpoint for the public Month 3/Month 4
route.  It keeps the paper-facing collision certificate as the central object
and exposes the Month 3 bounded-PA proof-predicate budget projections that an
auditor needs to see.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4PublicCitationEndpointSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4TheoremIndexSurface
open SondowProjectMonth3Month4VerifiedProjectIndexSurface
open SondowProjectMonth3Month4ReleaseTheoremExportSurface
open SondowProjectMonth3Month4AcceptedBoundedPAChainSurface
open SondowProjectMonth3Month4PaperFacingCollisionTheoremSurface

structure Month3AcceptedBudgetProjection
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop where
  witness_export :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      Month3AcceptedProofPredicateWitnessExport
        rootSide MainRationality SondowAccepted bounds bound n haccepted
  canonical_certificate_nonempty :
    ∃ n : Nat, ∃ _haccepted : SondowAccepted n,
      Nonempty (CanonicalProofCertificateAt bound n)
  canonical_certificate_accepted :
    ∃ n : Nat, ∃ _haccepted : SondowAccepted n,
      CanonicalProofCertificateAccepted bound n
  bounded_pa_proof_predicate :
    ∃ n : Nat, ∃ _haccepted : SondowAccepted n,
      Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n
  proof_predicate_iff_certificate_at :
    ∃ n : Nat, ∃ _haccepted : SondowAccepted n,
      Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ↔
        Nonempty (CanonicalProofCertificateAt bound n)
  checker_trace_nonempty :
    ∃ n : Nat, ∃ _haccepted : SondowAccepted n,
      Nonempty
        (CertificateVerifierMachine.AcceptedTrace
          (canonicalProofCertificateVerifierMachine bound) n)
  source_component_budget :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        ((((chainPackage_accepted_to_source
          pkg.chain_package n haccepted).product.proof.size + 2 : Nat) :
            Real)) ≤ bounds.product n ∧
        ((((chainPackage_accepted_to_source
          pkg.chain_package n haccepted).logRelation.proof.size + 2 : Nat) :
            Real)) ≤ bounds.logRelation n ∧
        ((((chainPackage_accepted_to_source
          pkg.chain_package n haccepted).decomposition.proof.size + 2 : Nat) :
            Real)) ≤ bounds.decomposition n ∧
        ((((chainPackage_accepted_to_source
          pkg.chain_package n haccepted).threePow.proof.size + 2 : Nat) :
            Real)) ≤ bounds.threePow n ∧
        ((((chainPackage_accepted_to_source
          pkg.chain_package n haccepted).payload.proof.size + 2 : Nat) :
            Real)) ≤ bounds.payload n
  assembled_checker_canonical_budget :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        ((((ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
          (Month3ProviderClosureSurface.assemblyIndex
            (auditFieldIndex pkg.chain_package.audit_package))
          (chainPackage_accepted_to_source
            pkg.chain_package n haccepted)).size + 2 : Nat) :
            Real)) ≤ bound n ∧
        ((chainPackage_accepted_to_checker_trace
          pkg.chain_package n haccepted).size : Real) ≤ bound n ∧
        ((((chainPackage_accepted_to_canonical_certificate
          pkg.chain_package n haccepted).proof.size + 2 : Nat) :
            Real)) ≤ bound n

theorem month3_budget_projection_of_witness_export
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (witness :
      ∃ n : Nat, ∃ haccepted : SondowAccepted n,
        Month3AcceptedProofPredicateWitnessExport
          rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month3AcceptedBudgetProjection
      rootSide MainRationality SondowAccepted bounds bound where
  witness_export := witness
  canonical_certificate_nonempty := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨pkg, accepted_witness⟩⟩
    exact ⟨n, haccepted, accepted_witness.canonical_nonempty⟩
  canonical_certificate_accepted := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨pkg, accepted_witness⟩⟩
    exact ⟨n, haccepted, accepted_witness.canonical_accepted⟩
  bounded_pa_proof_predicate := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨pkg, accepted_witness⟩⟩
    exact ⟨n, haccepted, accepted_witness.ledger_proof_predicate⟩
  proof_predicate_iff_certificate_at := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨pkg, accepted_witness⟩⟩
    exact
      ⟨n, haccepted,
        accepted_witness.ledger_proof_predicate_iff_certificate_at⟩
  checker_trace_nonempty := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨pkg, accepted_witness⟩⟩
    exact ⟨n, haccepted, accepted_witness.checker_trace_nonempty⟩
  source_component_budget := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨pkg, accepted_witness⟩⟩
    exact
      ⟨n, haccepted, pkg,
        accepted_witness.source_product_size_plus_two_le,
        accepted_witness.source_log_size_plus_two_le,
        accepted_witness.source_decomposition_size_plus_two_le,
        accepted_witness.source_threePow_size_plus_two_le,
        accepted_witness.source_payload_size_plus_two_le⟩
  assembled_checker_canonical_budget := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨pkg, accepted_witness⟩⟩
    exact
      ⟨n, haccepted, pkg,
        accepted_witness.assembled_proof_size_plus_two_le_bound,
        accepted_witness.checker_trace_size_le_bound,
        accepted_witness.canonical_size_plus_two_le_bound⟩

structure PublicReleaseCitationEndpoint
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop where
  paper_facing_certificate :
    PaperFacingCollisionCertificate
      rootSide MainRationality SondowAccepted bounds bound
  month3_budget_projection :
    Month3AcceptedBudgetProjection
      rootSide MainRationality SondowAccepted bounds bound
  public_gap_instantiation :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality)
  not_main_rationality : ¬ MainRationality
  month4_theorem5_audit_witness :
    Month4Theorem5AuditWitnessExport
      rootSide MainRationality SondowAccepted bounds bound
  month4_exact_external_boundary :
    Month4ExactExternalBoundaryExport
      rootSide MainRationality SondowAccepted bounds bound

theorem citation_endpoint_of_paper_facing_collision_certificate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      PaperFacingCollisionCertificate
        rootSide MainRationality SondowAccepted bounds bound) :
    PublicReleaseCitationEndpoint
      rootSide MainRationality SondowAccepted bounds bound where
  paper_facing_certificate := cert
  month3_budget_projection :=
    month3_budget_projection_of_witness_export
      cert.month3_accepted_proof_predicate_witness
  public_gap_instantiation :=
    paper_facing_collision_certificate_to_public_gap_instantiation cert
  not_main_rationality :=
    paper_facing_collision_certificate_not_main_rationality cert
  month4_theorem5_audit_witness :=
    paper_facing_collision_certificate_to_month4_theorem5_audit_witness cert
  month4_exact_external_boundary :=
    paper_facing_collision_certificate_to_month4_exact_external_boundary cert

theorem paper_facing_collision_certificate_iff_citation_endpoint
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    PaperFacingCollisionCertificate
      rootSide MainRationality SondowAccepted bounds bound ↔
      PublicReleaseCitationEndpoint
        rootSide MainRationality SondowAccepted bounds bound := by
  constructor
  · intro cert
    exact citation_endpoint_of_paper_facing_collision_certificate cert
  · intro endpoint
    exact endpoint.paper_facing_certificate

abbrev PublicReleaseCitationStatement
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop :=
  (Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ∧
    ∃ n : Nat, SondowAccepted n) ↔
    PublicReleaseCitationEndpoint
      rootSide MainRationality SondowAccepted bounds bound

theorem paper_route_and_accepted_iff_public_release_citation_endpoint
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    PublicReleaseCitationStatement
      rootSide MainRationality SondowAccepted bounds bound :=
  paper_route_and_accepted_iff_paper_facing_collision_certificate.trans
    paper_facing_collision_certificate_iff_citation_endpoint

theorem exactConvention_checklist_and_accepted_iff_public_release_citation_endpoint
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
      PublicReleaseCitationEndpoint
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (exactConvention_checklist_and_accepted_iff_paper_facing_collision_certificate
    h).trans
    paper_facing_collision_certificate_iff_citation_endpoint

theorem splitMinChecked_checklist_and_accepted_iff_public_release_citation_endpoint
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
      PublicReleaseCitationEndpoint
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (splitMinChecked_checklist_and_accepted_iff_paper_facing_collision_certificate
    h).trans
    paper_facing_collision_certificate_iff_citation_endpoint

theorem exactFamily_checklist_and_accepted_iff_public_release_citation_endpoint
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
      PublicReleaseCitationEndpoint
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (exactFamily_checklist_and_accepted_iff_paper_facing_collision_certificate
    h).trans
    paper_facing_collision_certificate_iff_citation_endpoint

theorem public_release_citation_endpoint_to_month3_budget_projection
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (endpoint :
      PublicReleaseCitationEndpoint
        rootSide MainRationality SondowAccepted bounds bound) :
    Month3AcceptedBudgetProjection
      rootSide MainRationality SondowAccepted bounds bound :=
  endpoint.month3_budget_projection

theorem public_release_citation_endpoint_to_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (endpoint :
      PublicReleaseCitationEndpoint
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  endpoint.public_gap_instantiation

theorem public_release_citation_endpoint_not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (endpoint :
      PublicReleaseCitationEndpoint
        rootSide MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  endpoint.not_main_rationality

theorem public_release_citation_endpoint_to_month4_exact_external_boundary
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (endpoint :
      PublicReleaseCitationEndpoint
        rootSide MainRationality SondowAccepted bounds bound) :
    Month4ExactExternalBoundaryExport
      rootSide MainRationality SondowAccepted bounds bound :=
  endpoint.month4_exact_external_boundary

theorem exactFamily_route_to_public_release_citation_endpoint
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
    PublicReleaseCitationEndpoint
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (exactFamily_checklist_and_accepted_iff_public_release_citation_endpoint
    h).mp route

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
  public_release_citation_endpoint_to_month3_budget_projection
    (exactFamily_route_to_public_release_citation_endpoint h route)

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
  public_release_citation_endpoint_to_public_gap_instantiation
    (exactFamily_route_to_public_release_citation_endpoint h route)

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
  public_release_citation_endpoint_not_main_rationality
    (exactFamily_route_to_public_release_citation_endpoint h route)

end SondowProjectMonth3Month4PublicCitationEndpointSurface
end SondowMainCheckedCodeBridge
