/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4PublicReleaseIndexSurface

/-!
# Month 3 accepted object projection surface

This module projects the Month 3 accepted witness export down to the concrete
source certificate, canonical PA certificate, checker trace, and the assembly
equalities that connect those three objects.  It is a thin audit surface: every
field is obtained by eliminating the already-exported
`Month3AcceptedProofPredicateWitnessExport`.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4Month3ObjectProjectionSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4TheoremIndexSurface
open SondowProjectMonth3Month4VerifiedProjectIndexSurface
open SondowProjectMonth3Month4ReleaseTheoremExportSurface
open SondowProjectMonth3Month4AcceptedBoundedPAChainSurface
open SondowProjectMonth3Month4PublicCitationEndpointSurface
open SondowProjectMonth3Month4PublicReleaseIndexSurface

theorem chainPackage_checker_trace_conclusion_eq_finiteConsistency
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (chainPackage_accepted_to_checker_trace pkg n haccepted).cert.conclusion =
      finiteConsistencyFormula n := by
  have hcert :
      (chainPackage_accepted_to_checker_trace pkg n haccepted).cert =
        (chainPackage_accepted_to_canonical_certificate
          pkg n haccepted).proof :=
    chainPackage_checker_trace_cert_eq_canonical_proof pkg n haccepted
  have hconclusion :
      (chainPackage_accepted_to_checker_trace
        pkg n haccepted).cert.conclusion =
        (chainPackage_accepted_to_canonical_certificate
          pkg n haccepted).proof.conclusion := by
    exact congrArg (fun proof => proof.conclusion) hcert
  exact
    hconclusion.trans
      (chainPackage_canonical_conclusion_eq_finiteConsistency
        pkg n haccepted)

structure Month3AcceptedSameObjectClosure
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) : Prop where
  accepted_witness :
    AcceptedMonth3ProofPredicateWitness pkg.chain_package n haccepted
  source_nonempty :
    Nonempty (CompiledSondowProjectSourceCertificateAt bounds n)
  canonical_nonempty :
    Nonempty (CanonicalProofCertificateAt bound n)
  checker_trace_nonempty :
    Nonempty
      (CertificateVerifierMachine.AcceptedTrace
        (canonicalProofCertificateVerifierMachine bound) n)
  canonical_certificate_accepted :
    CanonicalProofCertificateAccepted bound n
  bounded_pa_proof_predicate :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n
  proof_predicate_iff_certificate_at :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ↔
      Nonempty (CanonicalProofCertificateAt bound n)
  checker_trace_cert_eq_canonical_proof :
    (chainPackage_accepted_to_checker_trace
      pkg.chain_package n haccepted).cert =
      (chainPackage_accepted_to_canonical_certificate
        pkg.chain_package n haccepted).proof
  checker_trace_cert_eq_assembled_proof :
    (chainPackage_accepted_to_checker_trace
      pkg.chain_package n haccepted).cert =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          (auditFieldIndex pkg.chain_package.audit_package))
        (chainPackage_accepted_to_source
          pkg.chain_package n haccepted)
  canonical_proof_eq_assembled_proof :
    (chainPackage_accepted_to_canonical_certificate
      pkg.chain_package n haccepted).proof =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          (auditFieldIndex pkg.chain_package.audit_package))
        (chainPackage_accepted_to_source
          pkg.chain_package n haccepted)
  checker_trace_conclusion :
    (chainPackage_accepted_to_checker_trace
      pkg.chain_package n haccepted).cert.conclusion =
      canonicalPudlakTargetFamilySpec.target n
  canonical_conclusion_eq_finiteConsistency :
    (chainPackage_accepted_to_canonical_certificate
      pkg.chain_package n haccepted).proof.conclusion =
      finiteConsistencyFormula n
  checker_trace_conclusion_eq_finiteConsistency :
    (chainPackage_accepted_to_checker_trace
      pkg.chain_package n haccepted).cert.conclusion =
      finiteConsistencyFormula n
  source_size_eq_component_sum :
    CompiledSondowProjectSourceCertificateAt.sourceSize
        (chainPackage_accepted_to_source
          pkg.chain_package n haccepted) =
      (chainPackage_accepted_to_source
        pkg.chain_package n haccepted).product.sourceSize +
        (chainPackage_accepted_to_source
          pkg.chain_package n haccepted).logRelation.sourceSize +
          (chainPackage_accepted_to_source
            pkg.chain_package n haccepted).decomposition.sourceSize +
            (chainPackage_accepted_to_source
              pkg.chain_package n haccepted).threePow.sourceSize +
              (chainPackage_accepted_to_source
                pkg.chain_package n haccepted).payload.sourceSize
  canonical_source_size_eq :
    (chainPackage_accepted_to_canonical_certificate
      pkg.chain_package n haccepted).sourceSize =
      Month3SourceSizeAuditSurface.accepted_source_size
        (auditFieldIndex pkg.chain_package.audit_package) n haccepted
  source_product_size_plus_two_le :
    ((((chainPackage_accepted_to_source
      pkg.chain_package n haccepted).product.proof.size + 2 : Nat) :
        Real)) ≤ bounds.product n
  source_log_size_plus_two_le :
    ((((chainPackage_accepted_to_source
      pkg.chain_package n haccepted).logRelation.proof.size + 2 : Nat) :
        Real)) ≤ bounds.logRelation n
  source_decomposition_size_plus_two_le :
    ((((chainPackage_accepted_to_source
      pkg.chain_package n haccepted).decomposition.proof.size + 2 : Nat) :
        Real)) ≤ bounds.decomposition n
  source_threePow_size_plus_two_le :
    ((((chainPackage_accepted_to_source
      pkg.chain_package n haccepted).threePow.proof.size + 2 : Nat) :
        Real)) ≤ bounds.threePow n
  source_payload_size_plus_two_le :
    ((((chainPackage_accepted_to_source
      pkg.chain_package n haccepted).payload.proof.size + 2 : Nat) :
        Real)) ≤ bounds.payload n
  assembled_proof_size_plus_two_le_bound :
    ((((ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
      (Month3ProviderClosureSurface.assemblyIndex
        (auditFieldIndex pkg.chain_package.audit_package))
      (chainPackage_accepted_to_source
        pkg.chain_package n haccepted)).size + 2 : Nat) :
        Real)) ≤ bound n
  checker_trace_size_le_bound :
    ((chainPackage_accepted_to_checker_trace
      pkg.chain_package n haccepted).size : Real) ≤ bound n
  canonical_size_plus_two_le_bound :
    ((((chainPackage_accepted_to_canonical_certificate
      pkg.chain_package n haccepted).proof.size + 2 : Nat) :
        Real)) ≤ bound n

theorem month3_same_object_closure_of_accepted_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n)
    (accepted_witness :
      AcceptedMonth3ProofPredicateWitness pkg.chain_package n haccepted) :
    Month3AcceptedSameObjectClosure pkg n haccepted where
  accepted_witness := accepted_witness
  source_nonempty := accepted_witness.source_nonempty
  canonical_nonempty := accepted_witness.canonical_nonempty
  checker_trace_nonempty := accepted_witness.checker_trace_nonempty
  canonical_certificate_accepted := accepted_witness.canonical_accepted
  bounded_pa_proof_predicate := accepted_witness.ledger_proof_predicate
  proof_predicate_iff_certificate_at :=
    accepted_witness.ledger_proof_predicate_iff_certificate_at
  checker_trace_cert_eq_canonical_proof :=
    accepted_witness.checker_trace_cert_eq_canonical_proof
  checker_trace_cert_eq_assembled_proof :=
    accepted_witness.checker_trace_cert_eq_assembled_proof
  canonical_proof_eq_assembled_proof :=
    accepted_witness.canonical_proof_eq_assembled_proof
  checker_trace_conclusion :=
    chainPackage_checker_trace_conclusion pkg.chain_package n haccepted
  canonical_conclusion_eq_finiteConsistency :=
    chainPackage_canonical_conclusion_eq_finiteConsistency
      pkg.chain_package n haccepted
  checker_trace_conclusion_eq_finiteConsistency :=
    chainPackage_checker_trace_conclusion_eq_finiteConsistency
      pkg.chain_package n haccepted
  source_size_eq_component_sum :=
    accepted_witness.source_size_eq_component_sum
  canonical_source_size_eq :=
    accepted_witness.canonical_source_size_eq
  source_product_size_plus_two_le :=
    accepted_witness.source_product_size_plus_two_le
  source_log_size_plus_two_le :=
    accepted_witness.source_log_size_plus_two_le
  source_decomposition_size_plus_two_le :=
    accepted_witness.source_decomposition_size_plus_two_le
  source_threePow_size_plus_two_le :=
    accepted_witness.source_threePow_size_plus_two_le
  source_payload_size_plus_two_le :=
    accepted_witness.source_payload_size_plus_two_le
  assembled_proof_size_plus_two_le_bound :=
    accepted_witness.assembled_proof_size_plus_two_le_bound
  checker_trace_size_le_bound :=
    accepted_witness.checker_trace_size_le_bound
  canonical_size_plus_two_le_bound :=
    accepted_witness.canonical_size_plus_two_le_bound

abbrev Month3AcceptedSameObjectClosureExport
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop :=
  ∃ n : Nat, ∃ haccepted : SondowAccepted n,
    ∃ pkg : Month3Month4VerifiedProjectInstantiation
        rootSide MainRationality SondowAccepted bounds bound,
      Month3AcceptedSameObjectClosure pkg n haccepted

theorem month3_same_object_closure_of_witness_export
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (witness :
      ∃ n : Nat, ∃ haccepted : SondowAccepted n,
        Month3AcceptedProofPredicateWitnessExport
          rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month3AcceptedSameObjectClosureExport
      rootSide MainRationality SondowAccepted bounds bound := by
  rcases witness with ⟨n, haccepted, hwitness⟩
  rcases hwitness with ⟨⟨pkg, accepted_witness⟩⟩
  exact
    ⟨n, haccepted, pkg,
      month3_same_object_closure_of_accepted_witness
        pkg n haccepted accepted_witness⟩

structure Month3AcceptedObjectProjection
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop where
  witness_export :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      Month3AcceptedProofPredicateWitnessExport
        rootSide MainRationality SondowAccepted bounds bound n haccepted
  same_object_closure :
    Month3AcceptedSameObjectClosureExport
      rootSide MainRationality SondowAccepted bounds bound
  source_object :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        ∃ source : CompiledSondowProjectSourceCertificateAt bounds n,
          source =
            chainPackage_accepted_to_source pkg.chain_package n haccepted
  canonical_certificate_object :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        ∃ cert : CanonicalProofCertificateAt bound n,
          cert =
            chainPackage_accepted_to_canonical_certificate
              pkg.chain_package n haccepted
  checker_trace_object :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        ∃ trace :
          CertificateVerifierMachine.AcceptedTrace
            (canonicalProofCertificateVerifierMachine bound) n,
          trace =
            chainPackage_accepted_to_checker_trace
              pkg.chain_package n haccepted
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
  checker_trace_cert_eq_canonical_proof :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        (chainPackage_accepted_to_checker_trace
          pkg.chain_package n haccepted).cert =
          (chainPackage_accepted_to_canonical_certificate
            pkg.chain_package n haccepted).proof
  checker_trace_cert_eq_assembled_proof :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        (chainPackage_accepted_to_checker_trace
          pkg.chain_package n haccepted).cert =
          ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
            (Month3ProviderClosureSurface.assemblyIndex
              (auditFieldIndex pkg.chain_package.audit_package))
            (chainPackage_accepted_to_source
              pkg.chain_package n haccepted)
  canonical_proof_eq_assembled_proof :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        (chainPackage_accepted_to_canonical_certificate
          pkg.chain_package n haccepted).proof =
          ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
            (Month3ProviderClosureSurface.assemblyIndex
              (auditFieldIndex pkg.chain_package.audit_package))
            (chainPackage_accepted_to_source
              pkg.chain_package n haccepted)
  checker_trace_conclusion :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        (chainPackage_accepted_to_checker_trace
          pkg.chain_package n haccepted).cert.conclusion =
          canonicalPudlakTargetFamilySpec.target n
  canonical_conclusion_eq_finiteConsistency :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        (chainPackage_accepted_to_canonical_certificate
          pkg.chain_package n haccepted).proof.conclusion =
          finiteConsistencyFormula n
  source_size_eq_component_sum :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        CompiledSondowProjectSourceCertificateAt.sourceSize
            (chainPackage_accepted_to_source
              pkg.chain_package n haccepted) =
          (chainPackage_accepted_to_source
            pkg.chain_package n haccepted).product.sourceSize +
            (chainPackage_accepted_to_source
              pkg.chain_package n haccepted).logRelation.sourceSize +
              (chainPackage_accepted_to_source
                pkg.chain_package n haccepted).decomposition.sourceSize +
                (chainPackage_accepted_to_source
                  pkg.chain_package n haccepted).threePow.sourceSize +
                  (chainPackage_accepted_to_source
                    pkg.chain_package n haccepted).payload.sourceSize
  canonical_source_size_eq :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      ∃ pkg : Month3Month4VerifiedProjectInstantiation
          rootSide MainRationality SondowAccepted bounds bound,
        (chainPackage_accepted_to_canonical_certificate
          pkg.chain_package n haccepted).sourceSize =
          Month3SourceSizeAuditSurface.accepted_source_size
            (auditFieldIndex pkg.chain_package.audit_package) n haccepted
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

theorem month3_object_projection_of_witness_export
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (witness :
      ∃ n : Nat, ∃ haccepted : SondowAccepted n,
        Month3AcceptedProofPredicateWitnessExport
          rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month3AcceptedObjectProjection
      rootSide MainRationality SondowAccepted bounds bound where
  witness_export := witness
  same_object_closure :=
    month3_same_object_closure_of_witness_export witness
  source_object := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨pkg, _accepted_witness⟩⟩
    exact
      ⟨n, haccepted, pkg,
        chainPackage_accepted_to_source pkg.chain_package n haccepted, rfl⟩
  canonical_certificate_object := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨pkg, _accepted_witness⟩⟩
    exact
      ⟨n, haccepted, pkg,
        chainPackage_accepted_to_canonical_certificate
          pkg.chain_package n haccepted, rfl⟩
  checker_trace_object := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨pkg, _accepted_witness⟩⟩
    exact
      ⟨n, haccepted, pkg,
        chainPackage_accepted_to_checker_trace
          pkg.chain_package n haccepted, rfl⟩
  canonical_certificate_accepted := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨_pkg, accepted_witness⟩⟩
    exact ⟨n, haccepted, accepted_witness.canonical_accepted⟩
  bounded_pa_proof_predicate := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨_pkg, accepted_witness⟩⟩
    exact ⟨n, haccepted, accepted_witness.ledger_proof_predicate⟩
  proof_predicate_iff_certificate_at := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨_pkg, accepted_witness⟩⟩
    exact
      ⟨n, haccepted,
        accepted_witness.ledger_proof_predicate_iff_certificate_at⟩
  checker_trace_cert_eq_canonical_proof := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨pkg, accepted_witness⟩⟩
    exact
      ⟨n, haccepted, pkg,
        accepted_witness.checker_trace_cert_eq_canonical_proof⟩
  checker_trace_cert_eq_assembled_proof := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨pkg, accepted_witness⟩⟩
    exact
      ⟨n, haccepted, pkg,
        accepted_witness.checker_trace_cert_eq_assembled_proof⟩
  canonical_proof_eq_assembled_proof := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨pkg, accepted_witness⟩⟩
    exact
      ⟨n, haccepted, pkg,
        accepted_witness.canonical_proof_eq_assembled_proof⟩
  checker_trace_conclusion := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨pkg, _accepted_witness⟩⟩
    exact
      ⟨n, haccepted, pkg,
        chainPackage_checker_trace_conclusion
          pkg.chain_package n haccepted⟩
  canonical_conclusion_eq_finiteConsistency := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨pkg, _accepted_witness⟩⟩
    exact
      ⟨n, haccepted, pkg,
        chainPackage_canonical_conclusion_eq_finiteConsistency
          pkg.chain_package n haccepted⟩
  source_size_eq_component_sum := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨pkg, accepted_witness⟩⟩
    exact
      ⟨n, haccepted, pkg,
        accepted_witness.source_size_eq_component_sum⟩
  canonical_source_size_eq := by
    rcases witness with ⟨n, haccepted, hwitness⟩
    rcases hwitness with ⟨⟨pkg, accepted_witness⟩⟩
    exact
      ⟨n, haccepted, pkg,
        accepted_witness.canonical_source_size_eq⟩
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

theorem public_release_index_to_month3_object_projection
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index :
      PublicReleaseIndex
        rootSide MainRationality SondowAccepted bounds bound) :
    Month3AcceptedObjectProjection
      rootSide MainRationality SondowAccepted bounds bound :=
  month3_object_projection_of_witness_export
    index.month3_budget_projection.witness_export

theorem public_release_citation_endpoint_to_month3_object_projection
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (endpoint :
      PublicReleaseCitationEndpoint
        rootSide MainRationality SondowAccepted bounds bound) :
    Month3AcceptedObjectProjection
      rootSide MainRationality SondowAccepted bounds bound :=
  month3_object_projection_of_witness_export
    endpoint.month3_budget_projection.witness_export

theorem exactConvention_route_to_month3_object_projection
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
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
  public_release_index_to_month3_object_projection
    ((exactConvention_checklist_and_accepted_iff_public_release_index h).mp
      route)

theorem splitMinChecked_route_to_month3_object_projection
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
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
  public_release_index_to_month3_object_projection
    ((splitMinChecked_checklist_and_accepted_iff_public_release_index h).mp
      route)

theorem exactFamily_route_to_month3_object_projection
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
  public_release_index_to_month3_object_projection
    (exactFamily_route_to_public_release_index h route)

end SondowProjectMonth3Month4Month3ObjectProjectionSurface
end SondowMainCheckedCodeBridge
