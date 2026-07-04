/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4GapNoWeakeningSurface
import BoundedArithmeticLab.CnBoxPudlakMonth3ProofPredicateLedgerSurface
import EulerLimit.PudlakTheorem5LiteratureInputAuditSurface

/-!
# Month 3/Month 4 public release surface

This is the public-facing import surface for the current Month 3/Month 4
route.  It exposes the gap no-weakening package under release-level names and
keeps the three exact checklist entries as equivalences to that package.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4PublicReleaseSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4BridgeLinkSurface
open SondowProjectMonth3Month4CanonicalImportSurface
open SondowProjectMonth3Month4GapNoWeakeningSurface

abbrev Month3Month4PublicReleaseStatement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound) :=
  Month3Month4GapNoWeakeningStatement assembly

abbrev Month3Month4PublicReleasePackage
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) :=
  Month3Month4GapNoWeakeningPackage
    rootSide MainRationality SondowAccepted bounds bound

theorem statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound) :
    Month3Month4PublicReleaseStatement assembly :=
  SondowProjectMonth3Month4GapNoWeakeningSurface.statement assembly

theorem canonical_import_iff_public_release
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty
        (Month3Month4CanonicalPackage
          rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty
        (Month3Month4PublicReleasePackage
          rootSide MainRationality SondowAccepted bounds bound) :=
  canonical_import_iff_gap_no_weakening_package

theorem public_release_to_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  gapNoWeakeningPackage_to_public_gap_instantiation pkg

theorem public_release_not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  gapNoWeakeningPackage_not_main_rationality pkg

theorem public_release_month3_proof_predicate_ledger_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Month3ProofPredicateLedgerSurface.Statement pkg.assembly.index :=
  Month3ProofPredicateLedgerSurface.statement pkg.assembly.index

def public_release_source_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CompiledSondowProjectSourceCertificateAt bounds n :=
  Month3ProviderClosureSurface.sourceAt
    pkg.assembly.index n haccepted

def public_release_canonical_certificate_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CanonicalProofCertificateAt bound n :=
  Month3ProviderClosureSurface.canonicalAt
    pkg.assembly.index n haccepted

def public_release_checker_trace_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CertificateVerifierMachine.AcceptedTrace
      (canonicalProofCertificateVerifierMachine bound) n :=
  Month3CheckerTraceBudgetSurface.traceAt
    pkg.assembly.index n haccepted

theorem public_release_accepted_to_source_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (CompiledSondowProjectSourceCertificateAt bounds n) :=
  ⟨public_release_source_at pkg n haccepted⟩

theorem public_release_accepted_to_canonical_certificate_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (CanonicalProofCertificateAt bound n) :=
  ⟨public_release_canonical_certificate_at pkg n haccepted⟩

theorem public_release_accepted_to_checker_trace_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty
      (CertificateVerifierMachine.AcceptedTrace
        (canonicalProofCertificateVerifierMachine bound) n) :=
  ⟨public_release_checker_trace_at pkg n haccepted⟩

theorem public_release_checker_trace_cert_eq_canonical_proof
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (public_release_checker_trace_at pkg n haccepted).cert =
      (public_release_canonical_certificate_at pkg n haccepted).proof :=
  Month3CheckerTraceBudgetSurface.trace_cert_eq_canonical_proof
    pkg.assembly.index n haccepted

theorem public_release_checker_trace_cert_eq_assembled_proof
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (public_release_checker_trace_at pkg n haccepted).cert =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex pkg.assembly.index)
        (public_release_source_at pkg n haccepted) :=
  Month3CheckerTraceBudgetSurface.trace_cert_eq_assembled_proof
    pkg.assembly.index n haccepted

theorem public_release_checker_trace_size_le_bound
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((public_release_checker_trace_at pkg n haccepted).size : Real) ≤
      bound n :=
  Month3CheckerTraceBudgetSurface.trace_size_le_bound
    pkg.assembly.index n haccepted

theorem public_release_canonical_certificate_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((public_release_canonical_certificate_at
      pkg n haccepted).proof.size + 2 : Nat) : Real)) ≤ bound n :=
  Month3ProviderClosureSurface.canonical_size_plus_two_le
    pkg.assembly.index n haccepted

theorem public_release_accepted_to_month3_ledger_proof_predicate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n :=
  Month3ProofPredicateLedgerSurface.package_accepted_to_proof_predicate
    (Month3ProofPredicateLedgerSurface.Package.ofFieldIndex
      pkg.assembly.index) n haccepted

theorem public_release_month3_ledger_proof_predicate_iff_certificate_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ↔
      Nonempty (CanonicalProofCertificateAt bound n) :=
  Month3ProofPredicateLedgerSurface.package_proof_predicate_iff_certificate_at
    (Month3ProofPredicateLedgerSurface.Package.ofFieldIndex
      pkg.assembly.index) n

theorem public_release_theorem5_literature_input_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (_pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5LiteratureInputAuditSurface.Statement :=
  PudlakTheorem5LiteratureInputAuditSurface.statement

theorem public_release_theorem5_literature_audit_iff_exact_project_instance :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExactProjectInstance.Statement :=
  PudlakTheorem5LiteratureInputAuditSurface.statement_iff_exact_project_instance

theorem exactConvention_checklist_iff_public_release
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
        (Month3Month4PublicReleasePackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  exactConvention_checklist_iff_gap_no_weakening_package h

theorem splitMinChecked_checklist_iff_public_release
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
        (Month3Month4PublicReleasePackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  splitMinChecked_checklist_iff_gap_no_weakening_package h

theorem exactFamily_checklist_iff_public_release
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
        (Month3Month4PublicReleasePackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  exactFamily_checklist_iff_gap_no_weakening_package h

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
    ¬ MainRationality :=
  SondowProjectMonth3Month4GapNoWeakeningSurface.exactConvention_checklist_not_main_rationality
    h checklist

theorem splitMinChecked_checklist_not_main_rationality
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
    ¬ MainRationality :=
  SondowProjectMonth3Month4GapNoWeakeningSurface.splitMinChecked_checklist_not_main_rationality
    h checklist

theorem exactFamily_checklist_not_main_rationality
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
    ¬ MainRationality :=
  SondowProjectMonth3Month4GapNoWeakeningSurface.exactFamily_checklist_not_main_rationality
    h checklist


end SondowProjectMonth3Month4PublicReleaseSurface
end SondowMainCheckedCodeBridge
