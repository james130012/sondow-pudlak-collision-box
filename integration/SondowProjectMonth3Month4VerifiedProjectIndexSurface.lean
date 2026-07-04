/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4BoundedPAProofPredicateClosureSurface
import EulerLimit.PudlakTheorem5ExactMinimalFieldPackageSurface
import EulerLimit.PudlakTheorem5ExactExternalBoundarySurface
import EulerLimit.PudlakTheorem5ExternalInputBoundarySurface
import EulerLimit.PudlakTheorem5LiteratureInputAuditSurface

/-!
# Month 3/Month 4 verified project index surface

This module is the public index extension for the current Month 3/Month 4
route.  It makes the paper-facing route, the bounded PA proof-predicate
closure, the theorem-5 fields, and the public collision consequences available
from one package.

The package is only an abbreviation for the bounded proof-predicate closure
package.  The index therefore does not weaken or restate the route: it gives
stable theorem names for the same verified project instantiation.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4VerifiedProjectIndexSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4TheoremIndexSurface
open SondowProjectMonth3Month4BoundedPAProofPredicateClosureSurface

abbrev Month3Month4VerifiedProjectInstantiation :=
  BoundedPAProofPredicateClosurePackage

abbrev verifiedProjectBoundedPAProofPredicate :=
  canonicalBoundedPAProofPredicate

theorem verifiedProjectBoundedPAProofPredicate_eq_verifier_accepts
    (bound : Nat → Real) :
    verifiedProjectBoundedPAProofPredicate bound =
      (canonicalProofCertificateVerifierMachine bound).acceptsInput :=
  canonicalBoundedPAProofPredicate_eq_verifier_accepts bound

theorem paper_route_iff_verified_project_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Nonempty
        (Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound) :=
  paper_route_iff_bounded_pa_closure

def verifiedProject_to_paperAuditPackage
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :
    PaperAuditPackage
      rootSide MainRationality SondowAccepted bounds bound :=
  PaperAuditPackage.ofRoute
    (paper_route_iff_verified_project_instantiation.mpr ⟨pkg⟩)

theorem verified_project_iff_paper_audit_package_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty
        (Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty
        (PaperAuditPackage
          rootSide MainRationality SondowAccepted bounds bound) :=
  paper_route_iff_verified_project_instantiation.symm.trans
    paper_route_iff_paper_audit_package_nonempty

theorem paper_audit_package_iff_verified_project_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty
        (PaperAuditPackage
          rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty
        (Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound) :=
  verified_project_iff_paper_audit_package_nonempty.symm

theorem verifiedProject_to_paper_audit_package_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty
      (PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :=
  ⟨verifiedProject_to_paperAuditPackage pkg⟩

theorem paperAuditPackage_to_verified_project_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty
      (Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :=
  paper_route_iff_verified_project_instantiation.mp pkg.route

theorem public_audit_index_iff_verified_project_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty
        (SondowProjectMonth3Month4PublicAuditIndexSurface.PublicAuditIndexPackage
          rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty
        (Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound) :=
  SondowProjectMonth3Month4PublicAuditIndexSurface.audit_index_iff_paper_audit_package_nonempty.trans
    paper_audit_package_iff_verified_project_nonempty

theorem verifiedProject_to_public_audit_index_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty
      (SondowProjectMonth3Month4PublicAuditIndexSurface.PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :=
  SondowProjectMonth3Month4PublicAuditIndexSurface.paper_audit_package_to_audit_index_nonempty
    (verifiedProject_to_paperAuditPackage pkg)

theorem publicAuditIndex_to_verified_project_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      SondowProjectMonth3Month4PublicAuditIndexSurface.PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty
      (Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :=
  public_audit_index_iff_verified_project_nonempty.mp ⟨pkg⟩

theorem exactConvention_checklist_iff_verified_project_instantiation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty
        (Month3Month4VerifiedProjectInstantiation
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  exactConvention_checklist_iff_bounded_pa_closure h

theorem splitMinChecked_checklist_iff_verified_project_instantiation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty
        (Month3Month4VerifiedProjectInstantiation
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  splitMinChecked_checklist_iff_bounded_pa_closure h

theorem exactFamily_checklist_iff_verified_project_instantiation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty
        (Month3Month4VerifiedProjectInstantiation
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  exactFamily_checklist_iff_bounded_pa_closure h

theorem exactConvention_checklist_to_verified_project_month3_witness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
    Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      SondowProjectMonth3Month4AcceptedBoundedPAChainSurface.AcceptedMonth3ProofPredicateWitness
        pkg.chain_package m haccepted) :=
  exactConvention_checklist_to_closure_accepted_month3_witness
    h checklist m haccepted

theorem splitMinChecked_checklist_to_verified_project_month3_witness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
    Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      SondowProjectMonth3Month4AcceptedBoundedPAChainSurface.AcceptedMonth3ProofPredicateWitness
        pkg.chain_package m haccepted) :=
  splitMinChecked_checklist_to_closure_accepted_month3_witness
    h checklist m haccepted

theorem exactFamily_checklist_to_verified_project_month3_witness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
    Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      SondowProjectMonth3Month4AcceptedBoundedPAChainSurface.AcceptedMonth3ProofPredicateWitness
        pkg.chain_package m haccepted) :=
  exactFamily_checklist_to_closure_accepted_month3_witness
    h checklist m haccepted

theorem verifiedProject_accepted_to_bounded_pa_proof_predicate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    verifiedProjectBoundedPAProofPredicate bound n :=
  closurePackage_accepted_to_bounded_pa_proof_predicate
    pkg n haccepted

theorem verifiedProject_accepted_to_checker_trace_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty
      (CertificateVerifierMachine.AcceptedTrace
        (canonicalProofCertificateVerifierMachine bound) n) :=
  closurePackage_accepted_to_checker_trace_nonempty pkg n haccepted

theorem verifiedProject_accepted_month3_proof_predicate_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    SondowProjectMonth3Month4AcceptedBoundedPAChainSurface.AcceptedMonth3ProofPredicateWitness
      pkg.chain_package n haccepted :=
  closurePackage_accepted_month3_proof_predicate_witness
    pkg n haccepted

theorem verifiedProject_month3_proof_predicate_ledger_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :
    Month3ProofPredicateLedgerSurface.Statement
      (SondowProjectMonth3Month4AcceptedBoundedPAChainSurface.auditFieldIndex
        pkg.chain_package.audit_package) :=
  SondowProjectMonth3Month4AcceptedBoundedPAChainSurface.chainPackage_month3_proof_predicate_ledger_statement
    pkg.chain_package

theorem verifiedProject_accepted_to_month3_ledger_proof_predicate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n :=
  SondowProjectMonth3Month4AcceptedBoundedPAChainSurface.chainPackage_accepted_to_ledger_proof_predicate
    pkg.chain_package n haccepted

theorem verifiedProject_month3_ledger_proof_predicate_iff_certificate_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ↔
      Nonempty (CanonicalProofCertificateAt bound n) :=
  SondowProjectMonth3Month4AcceptedBoundedPAChainSurface.chainPackage_ledger_proof_predicate_iff_certificate_at
    pkg.chain_package n

def verifiedProject_source_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CompiledSondowProjectSourceCertificateAt bounds n :=
  paperAuditPackage_source_at
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

def verifiedProject_canonical_certificate_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CanonicalProofCertificateAt bound n :=
  paperAuditPackage_canonical_certificate_at
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

def verifiedProject_checker_trace_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CertificateVerifierMachine.AcceptedTrace
      (canonicalProofCertificateVerifierMachine bound) n :=
  paperAuditPackage_checker_trace_at
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

theorem verifiedProject_accepted_to_source_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (CompiledSondowProjectSourceCertificateAt bounds n) :=
  paperAuditPackage_accepted_to_source_nonempty
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

theorem verifiedProject_accepted_to_canonical_certificate_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (CanonicalProofCertificateAt bound n) :=
  paperAuditPackage_accepted_to_canonical_certificate_nonempty
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

theorem verifiedProject_checker_trace_cert_eq_canonical_proof
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (verifiedProject_checker_trace_at pkg n haccepted).cert =
      (verifiedProject_canonical_certificate_at pkg n haccepted).proof :=
  paperAuditPackage_checker_trace_cert_eq_canonical_proof
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

theorem verifiedProject_checker_trace_cert_eq_assembled_proof
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (verifiedProject_checker_trace_at pkg n haccepted).cert =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          (verifiedProject_to_paperAuditPackage
            pkg).release_package.assembly.index)
        (verifiedProject_source_at pkg n haccepted) :=
  paperAuditPackage_checker_trace_cert_eq_assembled_proof
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

theorem verifiedProject_canonical_proof_eq_assembled_proof
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (verifiedProject_canonical_certificate_at pkg n haccepted).proof =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          (verifiedProject_to_paperAuditPackage
            pkg).release_package.assembly.index)
        (verifiedProject_source_at pkg n haccepted) :=
  paperAuditPackage_canonical_proof_eq_assembled_proof
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

theorem verifiedProject_source_size_eq_component_sum
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CompiledSondowProjectSourceCertificateAt.sourceSize
        (verifiedProject_source_at pkg n haccepted) =
      (verifiedProject_source_at pkg n haccepted).product.sourceSize +
        (verifiedProject_source_at pkg n haccepted).logRelation.sourceSize +
          (verifiedProject_source_at pkg n haccepted).decomposition.sourceSize +
            (verifiedProject_source_at pkg n haccepted).threePow.sourceSize +
              (verifiedProject_source_at pkg n haccepted).payload.sourceSize :=
  paperAuditPackage_source_size_eq_component_sum
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

theorem verifiedProject_canonical_source_size_eq_source_size
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (verifiedProject_canonical_certificate_at pkg n haccepted).sourceSize =
      CompiledSondowProjectSourceCertificateAt.sourceSize
        (verifiedProject_source_at pkg n haccepted) :=
  paperAuditPackage_canonical_source_size_eq_source_size
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

theorem verifiedProject_checker_trace_size_le_bound
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((verifiedProject_checker_trace_at pkg n haccepted).size : Real) ≤
      bound n :=
  paperAuditPackage_checker_trace_size_le_bound
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

theorem verifiedProject_canonical_certificate_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((verifiedProject_canonical_certificate_at
      pkg n haccepted).proof.size + 2 : Nat) : Real)) ≤ bound n :=
  paperAuditPackage_canonical_certificate_size_plus_two_le
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

theorem verifiedProject_source_product_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((verifiedProject_source_at
      pkg n haccepted).product.proof.size + 2 : Nat) : Real)) ≤
      bounds.product n :=
  paperAuditPackage_source_product_size_plus_two_le
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

theorem verifiedProject_source_log_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((verifiedProject_source_at
      pkg n haccepted).logRelation.proof.size + 2 : Nat) : Real)) ≤
      bounds.logRelation n :=
  paperAuditPackage_source_log_size_plus_two_le
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

theorem verifiedProject_source_decomposition_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((verifiedProject_source_at
      pkg n haccepted).decomposition.proof.size + 2 : Nat) : Real)) ≤
      bounds.decomposition n :=
  paperAuditPackage_source_decomposition_size_plus_two_le
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

theorem verifiedProject_source_threePow_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((verifiedProject_source_at
      pkg n haccepted).threePow.proof.size + 2 : Nat) : Real)) ≤
      bounds.threePow n :=
  paperAuditPackage_source_threePow_size_plus_two_le
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

theorem verifiedProject_source_payload_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((verifiedProject_source_at
      pkg n haccepted).payload.proof.size + 2 : Nat) : Real)) ≤
      bounds.payload n :=
  paperAuditPackage_source_payload_size_plus_two_le
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

theorem verifiedProject_assembled_proof_size_plus_two_le_bound
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
      (Month3ProviderClosureSurface.assemblyIndex
        (verifiedProject_to_paperAuditPackage
          pkg).release_package.assembly.index)
      (verifiedProject_source_at pkg n haccepted)).size + 2 : Nat) :
        Real)) ≤ bound n :=
  paperAuditPackage_assembled_proof_size_plus_two_le_bound
    (verifiedProject_to_paperAuditPackage pkg) n haccepted

structure VerifiedMonth3SourceAssemblyAudit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) : Prop where
  trace_cert_eq_assembled :
    (verifiedProject_checker_trace_at pkg n haccepted).cert =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          (verifiedProject_to_paperAuditPackage
            pkg).release_package.assembly.index)
        (verifiedProject_source_at pkg n haccepted)
  canonical_proof_eq_assembled :
    (verifiedProject_canonical_certificate_at pkg n haccepted).proof =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          (verifiedProject_to_paperAuditPackage
            pkg).release_package.assembly.index)
        (verifiedProject_source_at pkg n haccepted)
  source_size_eq_component_sum :
    CompiledSondowProjectSourceCertificateAt.sourceSize
        (verifiedProject_source_at pkg n haccepted) =
      (verifiedProject_source_at pkg n haccepted).product.sourceSize +
        (verifiedProject_source_at pkg n haccepted).logRelation.sourceSize +
          (verifiedProject_source_at pkg n haccepted).decomposition.sourceSize +
            (verifiedProject_source_at pkg n haccepted).threePow.sourceSize +
              (verifiedProject_source_at pkg n haccepted).payload.sourceSize
  canonical_source_size_eq_source_size :
    (verifiedProject_canonical_certificate_at pkg n haccepted).sourceSize =
      CompiledSondowProjectSourceCertificateAt.sourceSize
        (verifiedProject_source_at pkg n haccepted)
  source_product_size_plus_two_le :
    ((((verifiedProject_source_at
      pkg n haccepted).product.proof.size + 2 : Nat) : Real)) ≤
      bounds.product n
  source_log_size_plus_two_le :
    ((((verifiedProject_source_at
      pkg n haccepted).logRelation.proof.size + 2 : Nat) : Real)) ≤
      bounds.logRelation n
  source_decomposition_size_plus_two_le :
    ((((verifiedProject_source_at
      pkg n haccepted).decomposition.proof.size + 2 : Nat) : Real)) ≤
      bounds.decomposition n
  source_threePow_size_plus_two_le :
    ((((verifiedProject_source_at
      pkg n haccepted).threePow.proof.size + 2 : Nat) : Real)) ≤
      bounds.threePow n
  source_payload_size_plus_two_le :
    ((((verifiedProject_source_at
      pkg n haccepted).payload.proof.size + 2 : Nat) : Real)) ≤
      bounds.payload n
  assembled_proof_size_plus_two_le_bound :
    ((((ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
      (Month3ProviderClosureSurface.assemblyIndex
        (verifiedProject_to_paperAuditPackage
          pkg).release_package.assembly.index)
      (verifiedProject_source_at pkg n haccepted)).size + 2 : Nat) :
        Real)) ≤ bound n

theorem verifiedProject_month3_source_assembly_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    VerifiedMonth3SourceAssemblyAudit pkg n haccepted where
  trace_cert_eq_assembled :=
    verifiedProject_checker_trace_cert_eq_assembled_proof pkg n haccepted
  canonical_proof_eq_assembled :=
    verifiedProject_canonical_proof_eq_assembled_proof pkg n haccepted
  source_size_eq_component_sum :=
    verifiedProject_source_size_eq_component_sum pkg n haccepted
  canonical_source_size_eq_source_size :=
    verifiedProject_canonical_source_size_eq_source_size pkg n haccepted
  source_product_size_plus_two_le :=
    verifiedProject_source_product_size_plus_two_le pkg n haccepted
  source_log_size_plus_two_le :=
    verifiedProject_source_log_size_plus_two_le pkg n haccepted
  source_decomposition_size_plus_two_le :=
    verifiedProject_source_decomposition_size_plus_two_le pkg n haccepted
  source_threePow_size_plus_two_le :=
    verifiedProject_source_threePow_size_plus_two_le pkg n haccepted
  source_payload_size_plus_two_le :=
    verifiedProject_source_payload_size_plus_two_le pkg n haccepted
  assembled_proof_size_plus_two_le_bound :=
    verifiedProject_assembled_proof_size_plus_two_le_bound pkg n haccepted

theorem verifiedProject_month4_lower_bound_source_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5CanonicalImportSurface.LowerBoundSourceStatement :=
  closurePackage_month4_lower_bound_source_statement pkg

theorem verifiedProject_month4_minimal_external_fields_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :
  PudlakTheorem5CanonicalImportSurface.MinimalExternalFieldsStatement :=
  closurePackage_month4_minimal_external_fields_statement pkg

theorem verifiedProject_theorem5_exact_minimal_field_package
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :
  PudlakTheorem5ExactMinimalFieldPackageSurface.Statement :=
  paperAuditPackage_theorem5_exact_minimal_package
    (verifiedProject_to_paperAuditPackage pkg)

theorem verifiedProject_theorem5_external_input_boundary
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement :=
  paperAuditPackage_theorem5_external_input_statement
    (verifiedProject_to_paperAuditPackage pkg)

theorem verifiedProject_theorem5_internal_equivalence_chain
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement :=
  paperAuditPackage_theorem5_internal_equivalence_statement
    (verifiedProject_to_paperAuditPackage pkg)

theorem verifiedProject_theorem5_literature_input_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5LiteratureInputAuditSurface.Statement :=
  paperAuditPackage_theorem5_literature_input_audit
    (verifiedProject_to_paperAuditPackage pkg)

theorem verifiedProject_theorem5_project_audit_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5LiteratureInputAuditSurface.ProjectTheorem5AuditWitness :=
  PudlakTheorem5LiteratureInputAuditSurface.statement_to_project_theorem5_audit_witness
    (verifiedProject_theorem5_literature_input_audit pkg)

theorem verifiedProject_theorem5_exact_external_boundary
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :
    _root_.PudlakTheorem5ExactExternalBoundarySurface.Statement :=
  paperAuditPackage_theorem5_exact_external_boundary
    (verifiedProject_to_paperAuditPackage pkg)

theorem verifiedProject_theorem5_exact_minimal_iff_minimal_fields :
    PudlakTheorem5ExactMinimalFieldPackageSurface.Statement ↔
      PudlakTheorem5MinimalExternalFieldsSurface.Statement :=
  PudlakTheorem5ExactMinimalFieldPackageSurface.statement_iff_minimal_external_fields

theorem verifiedProject_theorem5_literature_audit_iff_external_input :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement :=
  PudlakTheorem5LiteratureInputAuditSurface.statement_iff_external_input

theorem verifiedProject_theorem5_literature_audit_iff_internal_chain :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement :=
  PudlakTheorem5LiteratureInputAuditSurface.statement_iff_internal_equivalence

theorem verifiedProject_theorem5_literature_audit_iff_exact_project_instance :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExactProjectInstance.Statement :=
  PudlakTheorem5LiteratureInputAuditSurface.statement_iff_exact_project_instance

theorem verifiedProject_theorem5_external_input_iff_exact_minimal :
    PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement ↔
      PudlakTheorem5ExactMinimalFieldPackageSurface.Statement :=
  PudlakTheorem5ExternalInputBoundarySurface.exact_minimal_iff_external_input.symm

theorem verifiedProject_theorem5_external_input_iff_internal_chain :
    PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement ↔
      PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement :=
  PudlakTheorem5ExternalInputBoundarySurface.external_input_iff_internal_equivalence

theorem verifiedProject_theorem5_lower_source_code_eq_rescaled_pudlak
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        PudlakTheorem5CanonicalImportSurface.lowerBoundSource.raw
        PudlakTheorem5CanonicalImportSurface.lowerBoundSource.scale n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        literaturePudlakTheorem5ExternalScaleData.scale n :=
  closurePackage_theorem5_lower_source_code_eq_rescaled_pudlak pkg n

theorem verifiedProject_theorem5_raw_rescaled_power_chain
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  paperAuditPackage_theorem5_raw_rescaled_power_chain
    (verifiedProject_to_paperAuditPackage pkg) n

theorem verifiedProject_theorem5_external_boundary_raw_rescaled_power_chain
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  paperAuditPackage_theorem5_raw_rescaled_power_chain
    (verifiedProject_to_paperAuditPackage pkg) n

theorem verifiedProject_theorem5_literature_audit_raw_rescaled_power_chain
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  paperAuditPackage_theorem5_raw_rescaled_power_chain
    (verifiedProject_to_paperAuditPackage pkg) n

theorem verifiedProject_theorem5_power_bound_iff_rescaled
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :
    LiteraturePudlakTheorem5PowerBoundLowerBound
        literaturePudlakTheorem5ExternalScaleData ↔
      StrongRescaledExternalStrengthenedLowerBound
        literaturePudlakTheorem5ExternalScaleData.rawCode
        literaturePudlakTheorem5ExternalScaleData.scale :=
  paperAuditPackage_theorem5_power_bound_iff_rescaled
    (verifiedProject_to_paperAuditPackage pkg)

theorem verifiedProject_theorem5_certificate_presentation_iff_rescaled
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty LiteraturePudlakTheorem5RescaledLowerBoundCertificate :=
  paperAuditPackage_theorem5_certificate_presentation_iff_rescaled
    (verifiedProject_to_paperAuditPackage pkg)

theorem verifiedProject_to_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  pkg.chain_package.audit_package.audit.public_gap_instantiation

theorem verifiedProject_not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  pkg.chain_package.audit_package.audit.not_main_rationality

structure VerifiedProjectLevelFinalAudit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
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
  month3_verified_bounded_pa_proof_predicate :
    verifiedProjectBoundedPAProofPredicate bound n
  month3_ledger_proof_predicate :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n
  month3_ledger_proof_predicate_iff_certificate_at :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ↔
      Nonempty (CanonicalProofCertificateAt bound n)
  month3_accepted_proof_predicate_witness :
    SondowProjectMonth3Month4AcceptedBoundedPAChainSurface.AcceptedMonth3ProofPredicateWitness
        pkg.chain_package n haccepted
  month3_source_assembly :
    VerifiedMonth3SourceAssemblyAudit pkg n haccepted
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

theorem verifiedProject_project_level_final_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    VerifiedProjectLevelFinalAudit pkg n haccepted where
  month3_source_nonempty :=
    verifiedProject_accepted_to_source_nonempty pkg n haccepted
  month3_canonical_certificate_nonempty :=
    verifiedProject_accepted_to_canonical_certificate_nonempty pkg n haccepted
  month3_checker_trace_nonempty :=
    verifiedProject_accepted_to_checker_trace_nonempty pkg n haccepted
  month3_verified_bounded_pa_proof_predicate :=
    verifiedProject_accepted_to_bounded_pa_proof_predicate
      pkg n haccepted
  month3_ledger_proof_predicate :=
    verifiedProject_accepted_to_month3_ledger_proof_predicate
      pkg n haccepted
  month3_ledger_proof_predicate_iff_certificate_at :=
    verifiedProject_month3_ledger_proof_predicate_iff_certificate_at
      pkg n
  month3_accepted_proof_predicate_witness :=
    verifiedProject_accepted_month3_proof_predicate_witness
      pkg n haccepted
  month3_source_assembly :=
    verifiedProject_month3_source_assembly_audit pkg n haccepted
  month4_project_theorem5_audit_witness :=
    verifiedProject_theorem5_project_audit_witness pkg
  month4_exact_external_boundary_statement :=
    verifiedProject_theorem5_exact_external_boundary pkg
  month4_exact_minimal_package :=
    verifiedProject_theorem5_exact_minimal_field_package pkg
  month4_internal_equivalence :=
    verifiedProject_theorem5_internal_equivalence_chain pkg
  month4_raw_rescaled_power_chain :=
    verifiedProject_theorem5_raw_rescaled_power_chain pkg n
  month4_lower_source_code_eq_rescaled_pudlak :=
    verifiedProject_theorem5_lower_source_code_eq_rescaled_pudlak
      pkg n
  month4_power_bound_iff_rescaled :=
    verifiedProject_theorem5_power_bound_iff_rescaled pkg
  month4_certificate_presentation_iff_rescaled :=
    verifiedProject_theorem5_certificate_presentation_iff_rescaled pkg
  public_gap_instantiation :=
    verifiedProject_to_public_gap_instantiation pkg
  not_main_rationality :=
    verifiedProject_not_main_rationality pkg

theorem verifiedProject_project_level_final_audit_nonempty_iff_project
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
      rootSide MainRationality SondowAccepted bounds bound,
      VerifiedProjectLevelFinalAudit pkg n haccepted) ↔
      Nonempty (Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound) := by
  constructor
  · rintro ⟨⟨pkg, _audit⟩⟩
    exact ⟨pkg⟩
  · rintro ⟨pkg⟩
    exact ⟨⟨pkg,
      verifiedProject_project_level_final_audit pkg n haccepted⟩⟩

theorem verified_project_iff_dual_witness_final_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (Month3Month4VerifiedProjectInstantiation
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound,
        VerifiedProjectLevelFinalAudit pkg n haccepted) :=
  (verifiedProject_project_level_final_audit_nonempty_iff_project
    n haccepted).symm

theorem paper_route_iff_dual_witness_final_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound,
        VerifiedProjectLevelFinalAudit pkg n haccepted) :=
  paper_route_iff_verified_project_instantiation.trans
    (verified_project_iff_dual_witness_final_audit n haccepted)

theorem exactConvention_checklist_iff_dual_witness_final_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
        VerifiedProjectLevelFinalAudit pkg m haccepted) :=
  (exactConvention_checklist_iff_verified_project_instantiation h).trans
    (verified_project_iff_dual_witness_final_audit m haccepted)

theorem splitMinChecked_checklist_iff_dual_witness_final_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
        VerifiedProjectLevelFinalAudit pkg m haccepted) :=
  (splitMinChecked_checklist_iff_verified_project_instantiation h).trans
    (verified_project_iff_dual_witness_final_audit m haccepted)

theorem exactFamily_checklist_iff_dual_witness_final_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
        VerifiedProjectLevelFinalAudit pkg m haccepted) :=
  (exactFamily_checklist_iff_verified_project_instantiation h).trans
    (verified_project_iff_dual_witness_final_audit m haccepted)

theorem exactConvention_checklist_to_verified_project
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
      (Month3Month4VerifiedProjectInstantiation
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactConvention_checklist_iff_verified_project_instantiation h).1
    checklist

theorem splitMinChecked_checklist_to_verified_project
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
      (Month3Month4VerifiedProjectInstantiation
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (splitMinChecked_checklist_iff_verified_project_instantiation h).1
    checklist

theorem exactFamily_checklist_to_verified_project
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
      (Month3Month4VerifiedProjectInstantiation
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactFamily_checklist_iff_verified_project_instantiation h).1
    checklist

theorem exactConvention_checklist_to_verified_bounded_pa_proof_predicate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
    verifiedProjectBoundedPAProofPredicate bound m :=
  exactConvention_checklist_to_bounded_pa_proof_predicate
    h checklist m haccepted

theorem splitMinChecked_checklist_to_verified_bounded_pa_proof_predicate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
    verifiedProjectBoundedPAProofPredicate bound m :=
  splitMinChecked_checklist_to_bounded_pa_proof_predicate
    h checklist m haccepted

theorem exactFamily_checklist_to_verified_bounded_pa_proof_predicate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
    verifiedProjectBoundedPAProofPredicate bound m :=
  exactFamily_checklist_to_bounded_pa_proof_predicate
    h checklist m haccepted

theorem exactConvention_checklist_to_verified_month3_accepted_chain_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
    Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      Nonempty (CompiledSondowProjectSourceCertificateAt bounds m) ∧
        Nonempty (CanonicalProofCertificateAt bound m) ∧
        Nonempty
          (CertificateVerifierMachine.AcceptedTrace
            (canonicalProofCertificateVerifierMachine bound) m) ∧
        verifiedProjectBoundedPAProofPredicate bound m ∧
        Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound m ∧
        (verifiedProject_checker_trace_at pkg m haccepted).cert =
          (verifiedProject_canonical_certificate_at pkg m haccepted).proof ∧
        ((verifiedProject_checker_trace_at pkg m haccepted).size : Real) ≤
          bound m ∧
        ((((verifiedProject_canonical_certificate_at
          pkg m haccepted).proof.size + 2 : Nat) : Real)) ≤ bound m) := by
  rcases exactConvention_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      verifiedProject_accepted_to_source_nonempty pkg m haccepted,
      verifiedProject_accepted_to_canonical_certificate_nonempty pkg m haccepted,
      verifiedProject_accepted_to_checker_trace_nonempty pkg m haccepted,
      verifiedProject_accepted_to_bounded_pa_proof_predicate
        pkg m haccepted,
      verifiedProject_accepted_to_month3_ledger_proof_predicate
        pkg m haccepted,
      verifiedProject_checker_trace_cert_eq_canonical_proof
        pkg m haccepted,
      verifiedProject_checker_trace_size_le_bound pkg m haccepted,
      verifiedProject_canonical_certificate_size_plus_two_le
        pkg m haccepted⟩⟩

theorem splitMinChecked_checklist_to_verified_month3_accepted_chain_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
    Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      Nonempty (CompiledSondowProjectSourceCertificateAt bounds m) ∧
        Nonempty (CanonicalProofCertificateAt bound m) ∧
        Nonempty
          (CertificateVerifierMachine.AcceptedTrace
            (canonicalProofCertificateVerifierMachine bound) m) ∧
        verifiedProjectBoundedPAProofPredicate bound m ∧
        Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound m ∧
        (verifiedProject_checker_trace_at pkg m haccepted).cert =
          (verifiedProject_canonical_certificate_at pkg m haccepted).proof ∧
        ((verifiedProject_checker_trace_at pkg m haccepted).size : Real) ≤
          bound m ∧
        ((((verifiedProject_canonical_certificate_at
          pkg m haccepted).proof.size + 2 : Nat) : Real)) ≤ bound m) := by
  rcases splitMinChecked_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      verifiedProject_accepted_to_source_nonempty pkg m haccepted,
      verifiedProject_accepted_to_canonical_certificate_nonempty pkg m haccepted,
      verifiedProject_accepted_to_checker_trace_nonempty pkg m haccepted,
      verifiedProject_accepted_to_bounded_pa_proof_predicate
        pkg m haccepted,
      verifiedProject_accepted_to_month3_ledger_proof_predicate
        pkg m haccepted,
      verifiedProject_checker_trace_cert_eq_canonical_proof
        pkg m haccepted,
      verifiedProject_checker_trace_size_le_bound pkg m haccepted,
      verifiedProject_canonical_certificate_size_plus_two_le
        pkg m haccepted⟩⟩

theorem exactFamily_checklist_to_verified_month3_accepted_chain_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
    Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      Nonempty (CompiledSondowProjectSourceCertificateAt bounds m) ∧
        Nonempty (CanonicalProofCertificateAt bound m) ∧
        Nonempty
          (CertificateVerifierMachine.AcceptedTrace
            (canonicalProofCertificateVerifierMachine bound) m) ∧
        verifiedProjectBoundedPAProofPredicate bound m ∧
        Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound m ∧
        (verifiedProject_checker_trace_at pkg m haccepted).cert =
          (verifiedProject_canonical_certificate_at pkg m haccepted).proof ∧
        ((verifiedProject_checker_trace_at pkg m haccepted).size : Real) ≤
          bound m ∧
        ((((verifiedProject_canonical_certificate_at
          pkg m haccepted).proof.size + 2 : Nat) : Real)) ≤ bound m) := by
  rcases exactFamily_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      verifiedProject_accepted_to_source_nonempty pkg m haccepted,
      verifiedProject_accepted_to_canonical_certificate_nonempty pkg m haccepted,
      verifiedProject_accepted_to_checker_trace_nonempty pkg m haccepted,
      verifiedProject_accepted_to_bounded_pa_proof_predicate
        pkg m haccepted,
      verifiedProject_accepted_to_month3_ledger_proof_predicate
        pkg m haccepted,
      verifiedProject_checker_trace_cert_eq_canonical_proof
        pkg m haccepted,
      verifiedProject_checker_trace_size_le_bound pkg m haccepted,
      verifiedProject_canonical_certificate_size_plus_two_le
        pkg m haccepted⟩⟩

theorem exactConvention_checklist_to_verified_month3_source_assembly_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
    Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      VerifiedMonth3SourceAssemblyAudit pkg m haccepted) := by
  rcases exactConvention_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      verifiedProject_month3_source_assembly_audit pkg m haccepted⟩⟩

theorem splitMinChecked_checklist_to_verified_month3_source_assembly_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
    Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      VerifiedMonth3SourceAssemblyAudit pkg m haccepted) := by
  rcases splitMinChecked_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      verifiedProject_month3_source_assembly_audit pkg m haccepted⟩⟩

theorem exactFamily_checklist_to_verified_month3_source_assembly_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
    Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      VerifiedMonth3SourceAssemblyAudit pkg m haccepted) := by
  rcases exactFamily_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      verifiedProject_month3_source_assembly_audit pkg m haccepted⟩⟩

theorem exactConvention_checklist_to_verified_project_level_final_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
    Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      VerifiedProjectLevelFinalAudit pkg m haccepted) := by
  rcases exactConvention_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      verifiedProject_project_level_final_audit pkg m haccepted⟩⟩

theorem splitMinChecked_checklist_to_verified_project_level_final_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
    Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      VerifiedProjectLevelFinalAudit pkg m haccepted) := by
  rcases splitMinChecked_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      verifiedProject_project_level_final_audit pkg m haccepted⟩⟩

theorem exactFamily_checklist_to_verified_project_level_final_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
    Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      VerifiedProjectLevelFinalAudit pkg m haccepted) := by
  rcases exactFamily_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      verifiedProject_project_level_final_audit pkg m haccepted⟩⟩

theorem exactConvention_checklist_to_verified_theorem5_exact_minimal_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
  rcases exactConvention_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact verifiedProject_theorem5_exact_minimal_field_package pkg

theorem splitMinChecked_checklist_to_verified_theorem5_exact_minimal_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
  rcases splitMinChecked_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact verifiedProject_theorem5_exact_minimal_field_package pkg

theorem exactFamily_checklist_to_verified_theorem5_exact_minimal_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
  rcases exactFamily_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact verifiedProject_theorem5_exact_minimal_field_package pkg

theorem exactConvention_checklist_to_verified_theorem5_raw_rescaled_power_chain
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
  rcases exactConvention_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact verifiedProject_theorem5_raw_rescaled_power_chain pkg m

theorem splitMinChecked_checklist_to_verified_theorem5_raw_rescaled_power_chain
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
  rcases splitMinChecked_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact verifiedProject_theorem5_raw_rescaled_power_chain pkg m

theorem exactFamily_checklist_to_verified_theorem5_raw_rescaled_power_chain
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
  rcases exactFamily_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact verifiedProject_theorem5_raw_rescaled_power_chain pkg m

theorem exactConvention_checklist_to_verified_theorem5_power_bound_iff_rescaled
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
  rcases exactConvention_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact verifiedProject_theorem5_power_bound_iff_rescaled pkg

theorem splitMinChecked_checklist_to_verified_theorem5_power_bound_iff_rescaled
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
  rcases splitMinChecked_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact verifiedProject_theorem5_power_bound_iff_rescaled pkg

theorem exactFamily_checklist_to_verified_theorem5_power_bound_iff_rescaled
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
  rcases exactFamily_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact verifiedProject_theorem5_power_bound_iff_rescaled pkg

theorem exactConvention_checklist_to_verified_theorem5_lower_source_code_eq_rescaled_pudlak
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
  rcases exactConvention_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact
    paperAuditPackage_theorem5_lower_source_code_eq_rescaled_pudlak
      (verifiedProject_to_paperAuditPackage pkg) m

theorem splitMinChecked_checklist_to_verified_theorem5_lower_source_code_eq_rescaled_pudlak
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
  rcases splitMinChecked_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact
    paperAuditPackage_theorem5_lower_source_code_eq_rescaled_pudlak
      (verifiedProject_to_paperAuditPackage pkg) m

theorem exactFamily_checklist_to_verified_theorem5_lower_source_code_eq_rescaled_pudlak
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
  rcases exactFamily_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact
    paperAuditPackage_theorem5_lower_source_code_eq_rescaled_pudlak
      (verifiedProject_to_paperAuditPackage pkg) m

theorem exactConvention_checklist_to_verified_theorem5_certificate_presentation_iff_rescaled
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
  rcases exactConvention_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact verifiedProject_theorem5_certificate_presentation_iff_rescaled pkg

theorem splitMinChecked_checklist_to_verified_theorem5_certificate_presentation_iff_rescaled
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
  rcases splitMinChecked_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact verifiedProject_theorem5_certificate_presentation_iff_rescaled pkg

theorem exactFamily_checklist_to_verified_theorem5_certificate_presentation_iff_rescaled
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
  rcases exactFamily_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact verifiedProject_theorem5_certificate_presentation_iff_rescaled pkg

theorem exactConvention_checklist_to_verified_public_gap
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
  rcases exactConvention_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact verifiedProject_to_public_gap_instantiation pkg

theorem exactConvention_checklist_to_verified_not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
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
  rcases exactConvention_checklist_to_verified_project h checklist with ⟨pkg⟩
  exact verifiedProject_not_main_rationality pkg

end SondowProjectMonth3Month4VerifiedProjectIndexSurface
end SondowMainCheckedCodeBridge
