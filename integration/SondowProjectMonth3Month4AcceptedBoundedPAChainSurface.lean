/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakMonth3ProofPredicateLedgerSurface
import integration.SondowProjectMonth3Month4PublicAuditIndexSurface

/-!
# Month 3/Month 4 accepted-to-bounded-PA chain surface

This module exposes the accepted-certificate chain behind the public audit
index.  Its purpose is to make the Month 3 proof-predicate route directly
auditable from the same Month 3/Month 4 package:

`SondowAccepted n -> source certificate -> canonical PA certificate
 -> accepted checker trace -> bounded proof predicate`.

The fields are projections from the same concrete field index stored in the
public audit package.  The module also keeps the Month 4 minimal theorem-5
fields visible, so the accepted-chain audit remains connected to the same
Pudlak theorem-5 instantiation.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4AcceptedBoundedPAChainSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4PublicAuditIndexSurface
open SondowProjectMonth3Month4TheoremIndexSurface

abbrev auditFieldIndex
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound :=
  pkg.exactness_package.public_release.assembly.index

def sourceAt
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CompiledSondowProjectSourceCertificateAt bounds n :=
  Month3ProviderClosureSurface.sourceAt
    (auditFieldIndex pkg) n haccepted

def canonicalCertificateAt
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CanonicalProofCertificateAt bound n :=
  Month3ProviderClosureSurface.canonicalAt
    (auditFieldIndex pkg) n haccepted

def checkerTraceAt
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CertificateVerifierMachine.AcceptedTrace
      (canonicalProofCertificateVerifierMachine bound) n :=
  Month3CheckerTraceBudgetSurface.traceAt
    (auditFieldIndex pkg) n haccepted

structure AcceptedBoundedPAChainStatement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Prop where
  audit_statement :
    PublicAuditIndexStatement pkg.exactness_package
  month3_checker_trace_budget_statement :
    Month3CheckerTraceBudgetSurface.Statement (auditFieldIndex pkg)
  month4_minimal_external_fields_statement :
    PudlakTheorem5CanonicalImportSurface.MinimalExternalFieldsStatement
  accepted_to_source_nonempty :
    ∀ n : Nat, ∀ _haccepted : SondowAccepted n,
      Nonempty (CompiledSondowProjectSourceCertificateAt bounds n)
  accepted_to_canonical_nonempty :
    ∀ n : Nat, ∀ _haccepted : SondowAccepted n,
      Nonempty (CanonicalProofCertificateAt bound n)
  accepted_to_canonical_accepted :
    ∀ n : Nat, ∀ _haccepted : SondowAccepted n,
      CanonicalProofCertificateAccepted bound n
  accepted_to_checker_trace :
    ∀ n : Nat, ∀ _haccepted : SondowAccepted n,
      Nonempty
        (CertificateVerifierMachine.AcceptedTrace
          (canonicalProofCertificateVerifierMachine bound) n)
  accepted_to_ledger_proof_predicate :
    ∀ n : Nat, ∀ _haccepted : SondowAccepted n,
      Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n
  ledger_proof_predicate_iff_certificate_at :
    ∀ n : Nat,
      Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ↔
        Nonempty (CanonicalProofCertificateAt bound n)
  source_eq_provider_closure_source :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      sourceAt pkg n haccepted =
        Month3ProviderClosureSurface.sourceAt
          (auditFieldIndex pkg) n haccepted
  canonical_eq_provider_closure_canonical :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      canonicalCertificateAt pkg n haccepted =
        Month3ProviderClosureSurface.canonicalAt
          (auditFieldIndex pkg) n haccepted
  checker_trace_eq_budget_surface_trace :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      checkerTraceAt pkg n haccepted =
        Month3CheckerTraceBudgetSurface.traceAt
          (auditFieldIndex pkg) n haccepted
  checker_trace_cert_eq_canonical_proof :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (checkerTraceAt pkg n haccepted).cert =
        (canonicalCertificateAt pkg n haccepted).proof
  checker_trace_cert_eq_assembled_proof :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (checkerTraceAt pkg n haccepted).cert =
        ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
          (Month3ProviderClosureSurface.assemblyIndex
            (auditFieldIndex pkg))
          (sourceAt pkg n haccepted)
  canonical_proof_eq_assembled_proof :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (canonicalCertificateAt pkg n haccepted).proof =
        ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
          (Month3ProviderClosureSurface.assemblyIndex
            (auditFieldIndex pkg))
          (sourceAt pkg n haccepted)
  source_size_eq_component_sum :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      CompiledSondowProjectSourceCertificateAt.sourceSize
          (sourceAt pkg n haccepted) =
        (sourceAt pkg n haccepted).product.sourceSize +
          (sourceAt pkg n haccepted).logRelation.sourceSize +
            (sourceAt pkg n haccepted).decomposition.sourceSize +
              (sourceAt pkg n haccepted).threePow.sourceSize +
                (sourceAt pkg n haccepted).payload.sourceSize
  checker_trace_conclusion :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (checkerTraceAt pkg n haccepted).cert.conclusion =
        canonicalPudlakTargetFamilySpec.target n
  canonical_conclusion_eq_finiteConsistency :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (canonicalCertificateAt pkg n haccepted).proof.conclusion =
        finiteConsistencyFormula n
  canonical_source_size_eq :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (canonicalCertificateAt pkg n haccepted).sourceSize =
        Month3SourceSizeAuditSurface.accepted_source_size
          (auditFieldIndex pkg) n haccepted
  source_product_size_plus_two_le :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((sourceAt pkg n haccepted).product.proof.size + 2 : Nat) :
        Real)) ≤ bounds.product n
  source_log_size_plus_two_le :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((sourceAt pkg n haccepted).logRelation.proof.size + 2 : Nat) :
        Real)) ≤ bounds.logRelation n
  source_decomposition_size_plus_two_le :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((sourceAt pkg n haccepted).decomposition.proof.size + 2 : Nat) :
        Real)) ≤ bounds.decomposition n
  source_threePow_size_plus_two_le :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((sourceAt pkg n haccepted).threePow.proof.size + 2 : Nat) :
        Real)) ≤ bounds.threePow n
  source_payload_size_plus_two_le :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((sourceAt pkg n haccepted).payload.proof.size + 2 : Nat) :
        Real)) ≤ bounds.payload n
  assembled_proof_size_plus_two_le_bound :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          (auditFieldIndex pkg))
        (sourceAt pkg n haccepted)).size + 2 : Nat) : Real)) ≤
          bound n
  checker_trace_size_le_bound :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((checkerTraceAt pkg n haccepted).size : Real) ≤ bound n
  canonical_certificate_size_plus_two_le :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((canonicalCertificateAt pkg n haccepted).proof.size + 2 : Nat) :
        Real)) ≤ bound n
  theorem5_scale_eq_power_bound :
    ∀ n : Nat,
      PudlakTheorem5CanonicalImportSurface.theorem5Scale n =
        PudlakTheorem5CanonicalImportSurface.theorem5TimeConstructibleBound n ^
          PudlakTheorem5CanonicalImportSurface.theorem5Exponent

def statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    AcceptedBoundedPAChainStatement pkg where
  audit_statement := pkg.audit
  month3_checker_trace_budget_statement :=
    pkg.audit.month3_checker_trace_budget_statement
  month4_minimal_external_fields_statement :=
    pkg.audit.month4_minimal_external_fields_statement
  accepted_to_source_nonempty := by
    intro n haccepted
    exact
      (pkg.exactness_package.exactness.readiness.month3_statement)
          |>.accepted_to_source_nonempty n haccepted
  accepted_to_canonical_nonempty := by
    intro n haccepted
    exact
      pkg.exactness_package.exactness.readiness
        |>.accepted_to_canonical_nonempty n haccepted
  accepted_to_canonical_accepted := by
    intro n haccepted
    exact
      pkg.exactness_package.exactness.readiness
        |>.accepted_to_canonical_accepted n haccepted
  accepted_to_checker_trace := by
    intro n haccepted
    exact
      pkg.exactness_package.exactness.readiness
        |>.accepted_to_checker_trace n haccepted
  accepted_to_ledger_proof_predicate := by
    intro n haccepted
    exact
      Month3ProofPredicateLedgerSurface.statement (auditFieldIndex pkg)
        |>.accepted_to_proof_predicate n haccepted
  ledger_proof_predicate_iff_certificate_at := by
    intro n
    exact
      Month3ProofPredicateLedgerSurface.statement (auditFieldIndex pkg)
        |>.proof_predicate_iff_certificate_at n
  source_eq_provider_closure_source := by
    intro n haccepted
    rfl
  canonical_eq_provider_closure_canonical := by
    intro n haccepted
    rfl
  checker_trace_eq_budget_surface_trace := by
    intro n haccepted
    rfl
  checker_trace_cert_eq_canonical_proof := by
    intro n haccepted
    exact
      Month3CheckerTraceBudgetSurface.trace_cert_eq_canonical_proof
        (auditFieldIndex pkg) n haccepted
  checker_trace_cert_eq_assembled_proof := by
    intro n haccepted
    exact
      Month3CheckerTraceBudgetSurface.trace_cert_eq_assembled_proof
        (auditFieldIndex pkg) n haccepted
  canonical_proof_eq_assembled_proof := by
    intro n haccepted
    exact
      Month3ProviderClosureSurface.canonical_proof_eq_assembledProof
        (auditFieldIndex pkg) n haccepted
  source_size_eq_component_sum := by
    intro n haccepted
    simpa [sourceAt, auditFieldIndex,
      Month3ProviderClosureSurface.sourceAt,
      Month3ProviderClosureSurface.acceptedCompiler,
      Month3SourceSizeAuditSurface.accepted_source,
      Month3SourceSizeAuditSurface.accepted_source_size]
      using
        Month3SourceSizeAuditSurface.accepted_source_size_eq_component_sum
          (auditFieldIndex pkg) n haccepted
  checker_trace_conclusion := by
    intro n haccepted
    exact
      Month3CheckerTraceBudgetSurface.trace_conclusion
        (auditFieldIndex pkg) n haccepted
  canonical_conclusion_eq_finiteConsistency := by
    intro n haccepted
    exact
      pkg.exactness_package.exactness.readiness
        |>.canonical_certificate_conclusion_eq_finiteConsistency
          n haccepted
  canonical_source_size_eq := by
    intro n haccepted
    exact
      pkg.exactness_package.exactness.readiness
        |>.canonical_source_size_eq n haccepted
  source_product_size_plus_two_le := by
    intro n haccepted
    simpa [sourceAt, auditFieldIndex,
      Month3ProviderClosureSurface.sourceAt,
      Month3ProviderClosureSurface.acceptedCompiler]
      using
        (Month3BoundedPAProofPredicateAssemblySurface.statement
          (auditFieldIndex pkg)
            |>.source_product_size_plus_two_le n haccepted)
  source_log_size_plus_two_le := by
    intro n haccepted
    simpa [sourceAt, auditFieldIndex,
      Month3ProviderClosureSurface.sourceAt,
      Month3ProviderClosureSurface.acceptedCompiler]
      using
        (Month3BoundedPAProofPredicateAssemblySurface.statement
          (auditFieldIndex pkg)
            |>.source_log_size_plus_two_le n haccepted)
  source_decomposition_size_plus_two_le := by
    intro n haccepted
    simpa [sourceAt, auditFieldIndex,
      Month3ProviderClosureSurface.sourceAt,
      Month3ProviderClosureSurface.acceptedCompiler]
      using
        (Month3BoundedPAProofPredicateAssemblySurface.statement
          (auditFieldIndex pkg)
            |>.source_decomposition_size_plus_two_le n haccepted)
  source_threePow_size_plus_two_le := by
    intro n haccepted
    simpa [sourceAt, auditFieldIndex,
      Month3ProviderClosureSurface.sourceAt,
      Month3ProviderClosureSurface.acceptedCompiler]
      using
        (Month3BoundedPAProofPredicateAssemblySurface.statement
          (auditFieldIndex pkg)
            |>.source_threePow_size_plus_two_le n haccepted)
  source_payload_size_plus_two_le := by
    intro n haccepted
    simpa [sourceAt, auditFieldIndex,
      Month3ProviderClosureSurface.sourceAt,
      Month3ProviderClosureSurface.acceptedCompiler]
      using
        (Month3BoundedPAProofPredicateAssemblySurface.statement
          (auditFieldIndex pkg)
            |>.source_payload_size_plus_two_le n haccepted)
  assembled_proof_size_plus_two_le_bound := by
    intro n haccepted
    exact
      Month3BoundedPAProofPredicateAssemblySurface.statement
        (auditFieldIndex pkg)
          |>.assembled_size_plus_two_le_bound n
            (sourceAt pkg n haccepted)
  checker_trace_size_le_bound := by
    intro n haccepted
    exact
      Month3CheckerTraceBudgetSurface.trace_size_le_bound
        (auditFieldIndex pkg) n haccepted
  canonical_certificate_size_plus_two_le := by
    intro n haccepted
    exact
      Month3ProviderClosureSurface.canonical_size_plus_two_le
        (auditFieldIndex pkg) n haccepted
  theorem5_scale_eq_power_bound :=
    pkg.audit.theorem5_scale_eq_power_bound

theorem statement_iff_public_audit_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    AcceptedBoundedPAChainStatement pkg ↔
      PublicAuditIndexStatement pkg.exactness_package := by
  constructor
  · intro h
    exact h.audit_statement
  · intro _h
    exact statement pkg

structure AcceptedBoundedPAChainPackage
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  audit_package :
    PublicAuditIndexPackage
      rootSide MainRationality SondowAccepted bounds bound
  chain :
    AcceptedBoundedPAChainStatement audit_package

namespace AcceptedBoundedPAChainPackage

def ofAuditPackage
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (audit_package :
      PublicAuditIndexPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    AcceptedBoundedPAChainPackage
      rootSide MainRationality SondowAccepted bounds bound where
  audit_package := audit_package
  chain := statement audit_package

end AcceptedBoundedPAChainPackage

theorem chainPackage_nonempty_iff_audit_index_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty
        (AcceptedBoundedPAChainPackage
          rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty
        (PublicAuditIndexPackage
          rootSide MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨pkg⟩
    exact ⟨pkg.audit_package⟩
  · intro h
    rcases h with ⟨pkg⟩
    exact ⟨AcceptedBoundedPAChainPackage.ofAuditPackage pkg⟩

theorem paper_route_iff_chain_package
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Nonempty
        (AcceptedBoundedPAChainPackage
          rootSide MainRationality SondowAccepted bounds bound) :=
  paper_route_iff_audit_index.trans
    chainPackage_nonempty_iff_audit_index_nonempty.symm

theorem exactConvention_checklist_iff_chain_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
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
        (AcceptedBoundedPAChainPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactConvention_checklist_iff_audit_index h).trans
      chainPackage_nonempty_iff_audit_index_nonempty.symm

theorem splitMinChecked_checklist_iff_chain_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
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
        (AcceptedBoundedPAChainPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (splitMinChecked_checklist_iff_audit_index h).trans
      chainPackage_nonempty_iff_audit_index_nonempty.symm

theorem exactFamily_checklist_iff_chain_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
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
        (AcceptedBoundedPAChainPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactFamily_checklist_iff_audit_index h).trans
      chainPackage_nonempty_iff_audit_index_nonempty.symm

theorem exactConvention_checklist_to_chain_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
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
      (AcceptedBoundedPAChainPackage
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactConvention_checklist_iff_chain_package h).1 checklist

theorem splitMinChecked_checklist_to_chain_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
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
      (AcceptedBoundedPAChainPackage
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (splitMinChecked_checklist_iff_chain_package h).1 checklist

theorem exactFamily_checklist_to_chain_package
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
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
      (AcceptedBoundedPAChainPackage
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactFamily_checklist_iff_chain_package h).1 checklist

def chainPackage_accepted_to_source
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CompiledSondowProjectSourceCertificateAt bounds n :=
  sourceAt pkg.audit_package n haccepted

theorem chainPackage_accepted_to_source_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (CompiledSondowProjectSourceCertificateAt bounds n) :=
  pkg.chain.accepted_to_source_nonempty n haccepted

def chainPackage_accepted_to_canonical_certificate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
  CanonicalProofCertificateAt bound n :=
  canonicalCertificateAt pkg.audit_package n haccepted

theorem chainPackage_accepted_to_canonical_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (CanonicalProofCertificateAt bound n) :=
  pkg.chain.accepted_to_canonical_nonempty n haccepted

theorem chainPackage_accepted_to_canonical_accepted
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CanonicalProofCertificateAccepted bound n :=
  pkg.chain.accepted_to_canonical_accepted n haccepted

def chainPackage_month3_proof_predicate_ledger_package
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Month3ProofPredicateLedgerSurface.Package
      MainRationality SondowAccepted bounds bound :=
  Month3ProofPredicateLedgerSurface.Package.ofFieldIndex
    (auditFieldIndex pkg.audit_package)

theorem chainPackage_month3_proof_predicate_ledger_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Month3ProofPredicateLedgerSurface.Statement
      (auditFieldIndex pkg.audit_package) :=
  (chainPackage_month3_proof_predicate_ledger_package pkg).ledger

theorem chainPackage_accepted_to_ledger_proof_predicate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n :=
  Month3ProofPredicateLedgerSurface.package_accepted_to_proof_predicate
    (chainPackage_month3_proof_predicate_ledger_package pkg) n haccepted

theorem chainPackage_ledger_proof_predicate_iff_certificate_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ↔
      Nonempty (CanonicalProofCertificateAt bound n) :=
  Month3ProofPredicateLedgerSurface.package_proof_predicate_iff_certificate_at
    (chainPackage_month3_proof_predicate_ledger_package pkg) n

def chainPackage_accepted_to_checker_trace
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CertificateVerifierMachine.AcceptedTrace
      (canonicalProofCertificateVerifierMachine bound) n :=
  checkerTraceAt pkg.audit_package n haccepted

theorem chainPackage_accepted_to_checker_trace_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty
      (CertificateVerifierMachine.AcceptedTrace
        (canonicalProofCertificateVerifierMachine bound) n) :=
  pkg.chain.accepted_to_checker_trace n haccepted

theorem chainPackage_checker_trace_cert_eq_canonical_proof
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (chainPackage_accepted_to_checker_trace pkg n haccepted).cert =
      (chainPackage_accepted_to_canonical_certificate pkg n haccepted).proof :=
  pkg.chain.checker_trace_cert_eq_canonical_proof n haccepted

theorem chainPackage_checker_trace_cert_eq_assembled_proof
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (chainPackage_accepted_to_checker_trace pkg n haccepted).cert =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          (auditFieldIndex pkg.audit_package))
        (chainPackage_accepted_to_source pkg n haccepted) :=
  pkg.chain.checker_trace_cert_eq_assembled_proof n haccepted

theorem chainPackage_canonical_proof_eq_assembled_proof
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (chainPackage_accepted_to_canonical_certificate
      pkg n haccepted).proof =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          (auditFieldIndex pkg.audit_package))
        (chainPackage_accepted_to_source pkg n haccepted) :=
  pkg.chain.canonical_proof_eq_assembled_proof n haccepted

theorem chainPackage_source_size_eq_component_sum
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CompiledSondowProjectSourceCertificateAt.sourceSize
        (chainPackage_accepted_to_source pkg n haccepted) =
      (chainPackage_accepted_to_source pkg n haccepted).product.sourceSize +
        (chainPackage_accepted_to_source
          pkg n haccepted).logRelation.sourceSize +
          (chainPackage_accepted_to_source
            pkg n haccepted).decomposition.sourceSize +
            (chainPackage_accepted_to_source
              pkg n haccepted).threePow.sourceSize +
              (chainPackage_accepted_to_source
                pkg n haccepted).payload.sourceSize :=
  pkg.chain.source_size_eq_component_sum n haccepted

theorem chainPackage_checker_trace_conclusion
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (chainPackage_accepted_to_checker_trace
      pkg n haccepted).cert.conclusion =
        canonicalPudlakTargetFamilySpec.target n :=
  pkg.chain.checker_trace_conclusion n haccepted

theorem chainPackage_canonical_conclusion_eq_finiteConsistency
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (chainPackage_accepted_to_canonical_certificate
      pkg n haccepted).proof.conclusion =
        finiteConsistencyFormula n :=
  pkg.chain.canonical_conclusion_eq_finiteConsistency n haccepted

theorem chainPackage_canonical_source_size_eq
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (chainPackage_accepted_to_canonical_certificate
      pkg n haccepted).sourceSize =
        Month3SourceSizeAuditSurface.accepted_source_size
          (auditFieldIndex pkg.audit_package) n haccepted :=
  pkg.chain.canonical_source_size_eq n haccepted

theorem chainPackage_source_product_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((chainPackage_accepted_to_source
      pkg n haccepted).product.proof.size + 2 : Nat) : Real)) ≤
      bounds.product n :=
  pkg.chain.source_product_size_plus_two_le n haccepted

theorem chainPackage_source_log_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((chainPackage_accepted_to_source
      pkg n haccepted).logRelation.proof.size + 2 : Nat) : Real)) ≤
      bounds.logRelation n :=
  pkg.chain.source_log_size_plus_two_le n haccepted

theorem chainPackage_source_decomposition_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((chainPackage_accepted_to_source
      pkg n haccepted).decomposition.proof.size + 2 : Nat) : Real)) ≤
      bounds.decomposition n :=
  pkg.chain.source_decomposition_size_plus_two_le n haccepted

theorem chainPackage_source_threePow_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((chainPackage_accepted_to_source
      pkg n haccepted).threePow.proof.size + 2 : Nat) : Real)) ≤
      bounds.threePow n :=
  pkg.chain.source_threePow_size_plus_two_le n haccepted

theorem chainPackage_source_payload_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((chainPackage_accepted_to_source
      pkg n haccepted).payload.proof.size + 2 : Nat) : Real)) ≤
      bounds.payload n :=
  pkg.chain.source_payload_size_plus_two_le n haccepted

theorem chainPackage_assembled_proof_size_plus_two_le_bound
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
      (Month3ProviderClosureSurface.assemblyIndex
        (auditFieldIndex pkg.audit_package))
      (chainPackage_accepted_to_source pkg n haccepted)).size + 2 : Nat) :
        Real)) ≤ bound n :=
  pkg.chain.assembled_proof_size_plus_two_le_bound n haccepted

theorem chainPackage_checker_trace_size_le_bound
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((chainPackage_accepted_to_checker_trace
      pkg n haccepted).size : Real) ≤ bound n :=
  pkg.chain.checker_trace_size_le_bound n haccepted

theorem chainPackage_canonical_size_plus_two_le_bound
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((chainPackage_accepted_to_canonical_certificate
      pkg n haccepted).proof.size + 2 : Nat) : Real)) ≤ bound n :=
  pkg.chain.canonical_certificate_size_plus_two_le n haccepted

structure AcceptedMonth3ProofPredicateWitness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) : Prop where
  source_nonempty :
    Nonempty (CompiledSondowProjectSourceCertificateAt bounds n)
  canonical_nonempty :
    Nonempty (CanonicalProofCertificateAt bound n)
  checker_trace_nonempty :
    Nonempty
      (CertificateVerifierMachine.AcceptedTrace
        (canonicalProofCertificateVerifierMachine bound) n)
  canonical_accepted :
    CanonicalProofCertificateAccepted bound n
  ledger_proof_predicate :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n
  ledger_proof_predicate_iff_certificate_at :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ↔
      Nonempty (CanonicalProofCertificateAt bound n)
  checker_trace_cert_eq_canonical_proof :
    (chainPackage_accepted_to_checker_trace pkg n haccepted).cert =
      (chainPackage_accepted_to_canonical_certificate pkg n haccepted).proof
  checker_trace_cert_eq_assembled_proof :
    (chainPackage_accepted_to_checker_trace pkg n haccepted).cert =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          (auditFieldIndex pkg.audit_package))
        (chainPackage_accepted_to_source pkg n haccepted)
  canonical_proof_eq_assembled_proof :
    (chainPackage_accepted_to_canonical_certificate pkg n haccepted).proof =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          (auditFieldIndex pkg.audit_package))
        (chainPackage_accepted_to_source pkg n haccepted)
  source_size_eq_component_sum :
    CompiledSondowProjectSourceCertificateAt.sourceSize
        (chainPackage_accepted_to_source pkg n haccepted) =
      (chainPackage_accepted_to_source pkg n haccepted).product.sourceSize +
        (chainPackage_accepted_to_source
          pkg n haccepted).logRelation.sourceSize +
          (chainPackage_accepted_to_source
            pkg n haccepted).decomposition.sourceSize +
            (chainPackage_accepted_to_source
              pkg n haccepted).threePow.sourceSize +
              (chainPackage_accepted_to_source
                pkg n haccepted).payload.sourceSize
  canonical_source_size_eq :
    (chainPackage_accepted_to_canonical_certificate
      pkg n haccepted).sourceSize =
        Month3SourceSizeAuditSurface.accepted_source_size
          (auditFieldIndex pkg.audit_package) n haccepted
  source_product_size_plus_two_le :
    ((((chainPackage_accepted_to_source
      pkg n haccepted).product.proof.size + 2 : Nat) : Real)) ≤
      bounds.product n
  source_log_size_plus_two_le :
    ((((chainPackage_accepted_to_source
      pkg n haccepted).logRelation.proof.size + 2 : Nat) : Real)) ≤
      bounds.logRelation n
  source_decomposition_size_plus_two_le :
    ((((chainPackage_accepted_to_source
      pkg n haccepted).decomposition.proof.size + 2 : Nat) : Real)) ≤
      bounds.decomposition n
  source_threePow_size_plus_two_le :
    ((((chainPackage_accepted_to_source
      pkg n haccepted).threePow.proof.size + 2 : Nat) : Real)) ≤
      bounds.threePow n
  source_payload_size_plus_two_le :
    ((((chainPackage_accepted_to_source
      pkg n haccepted).payload.proof.size + 2 : Nat) : Real)) ≤
      bounds.payload n
  assembled_proof_size_plus_two_le_bound :
    ((((ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
      (Month3ProviderClosureSurface.assemblyIndex
        (auditFieldIndex pkg.audit_package))
      (chainPackage_accepted_to_source pkg n haccepted)).size + 2 : Nat) :
        Real)) ≤ bound n
  checker_trace_size_le_bound :
    ((chainPackage_accepted_to_checker_trace
      pkg n haccepted).size : Real) ≤ bound n
  canonical_size_plus_two_le_bound :
    ((((chainPackage_accepted_to_canonical_certificate
      pkg n haccepted).proof.size + 2 : Nat) : Real)) ≤ bound n

theorem chainPackage_accepted_month3_proof_predicate_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    AcceptedMonth3ProofPredicateWitness pkg n haccepted where
  source_nonempty :=
    chainPackage_accepted_to_source_nonempty pkg n haccepted
  canonical_nonempty :=
    chainPackage_accepted_to_canonical_nonempty pkg n haccepted
  checker_trace_nonempty :=
    chainPackage_accepted_to_checker_trace_nonempty pkg n haccepted
  canonical_accepted :=
    chainPackage_accepted_to_canonical_accepted pkg n haccepted
  ledger_proof_predicate :=
    chainPackage_accepted_to_ledger_proof_predicate pkg n haccepted
  ledger_proof_predicate_iff_certificate_at :=
    chainPackage_ledger_proof_predicate_iff_certificate_at pkg n
  checker_trace_cert_eq_canonical_proof :=
    chainPackage_checker_trace_cert_eq_canonical_proof pkg n haccepted
  checker_trace_cert_eq_assembled_proof :=
    chainPackage_checker_trace_cert_eq_assembled_proof pkg n haccepted
  canonical_proof_eq_assembled_proof :=
    chainPackage_canonical_proof_eq_assembled_proof pkg n haccepted
  source_size_eq_component_sum :=
    chainPackage_source_size_eq_component_sum pkg n haccepted
  canonical_source_size_eq :=
    chainPackage_canonical_source_size_eq pkg n haccepted
  source_product_size_plus_two_le :=
    chainPackage_source_product_size_plus_two_le pkg n haccepted
  source_log_size_plus_two_le :=
    chainPackage_source_log_size_plus_two_le pkg n haccepted
  source_decomposition_size_plus_two_le :=
    chainPackage_source_decomposition_size_plus_two_le pkg n haccepted
  source_threePow_size_plus_two_le :=
    chainPackage_source_threePow_size_plus_two_le pkg n haccepted
  source_payload_size_plus_two_le :=
    chainPackage_source_payload_size_plus_two_le pkg n haccepted
  assembled_proof_size_plus_two_le_bound :=
    chainPackage_assembled_proof_size_plus_two_le_bound pkg n haccepted
  checker_trace_size_le_bound :=
    chainPackage_checker_trace_size_le_bound pkg n haccepted
  canonical_size_plus_two_le_bound :=
    chainPackage_canonical_size_plus_two_le_bound pkg n haccepted

theorem exactConvention_checklist_to_accepted_month3_witness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
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
    Nonempty (Σ' pkg : AcceptedBoundedPAChainPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      AcceptedMonth3ProofPredicateWitness pkg m haccepted) := by
  rcases exactConvention_checklist_to_chain_package h checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      chainPackage_accepted_month3_proof_predicate_witness
        pkg m haccepted⟩⟩

theorem splitMinChecked_checklist_to_accepted_month3_witness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
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
    Nonempty (Σ' pkg : AcceptedBoundedPAChainPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      AcceptedMonth3ProofPredicateWitness pkg m haccepted) := by
  rcases splitMinChecked_checklist_to_chain_package h checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      chainPackage_accepted_month3_proof_predicate_witness
        pkg m haccepted⟩⟩

theorem exactFamily_checklist_to_accepted_month3_witness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
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
    Nonempty (Σ' pkg : AcceptedBoundedPAChainPackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      AcceptedMonth3ProofPredicateWitness pkg m haccepted) := by
  rcases exactFamily_checklist_to_chain_package h checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      chainPackage_accepted_month3_proof_predicate_witness
        pkg m haccepted⟩⟩

theorem exactConvention_checklist_to_canonical_accepted
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
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
    CanonicalProofCertificateAccepted bound m := by
  rcases exactConvention_checklist_to_chain_package h checklist with ⟨pkg⟩
  exact chainPackage_accepted_to_canonical_accepted pkg m haccepted

theorem exactConvention_checklist_to_checker_trace_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
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
    Nonempty
      (CertificateVerifierMachine.AcceptedTrace
        (canonicalProofCertificateVerifierMachine bound) m) := by
  rcases exactConvention_checklist_to_chain_package h checklist with ⟨pkg⟩
  exact chainPackage_accepted_to_checker_trace_nonempty pkg m haccepted

end SondowProjectMonth3Month4AcceptedBoundedPAChainSurface
end SondowMainCheckedCodeBridge
