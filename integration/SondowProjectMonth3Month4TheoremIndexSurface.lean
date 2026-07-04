/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4PaperReadyTheoremSurface
import EulerLimit.PudlakTheorem5ExactExternalBoundarySurface

/-!
# Month 3/Month 4 theorem index surface

This module is a compact theorem index for the current Month 3/Month 4 public
route.  It gives stable names for the no-weakening equivalences and for the
final public-gap and not-main-rationality consequences.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4TheoremIndexSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4PublicReleaseSurface
open SondowProjectMonth3Month4PaperReadyTheoremSurface

abbrev Month3Month4IndexedPaperRoute :=
  Month3Month4PaperReadyCollisionRoute

theorem paper_route_iff_public_release
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Nonempty (Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound) :=
  paper_ready_route_iff_public_release

theorem paper_route_to_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (route :
      Month3Month4IndexedPaperRoute
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  paper_ready_route_to_public_gap_instantiation route

theorem paper_route_not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (route :
      Month3Month4IndexedPaperRoute
        rootSide MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  paper_ready_not_main_rationality route

theorem paper_route_to_month3_proof_predicate_ledger_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (route :
      Month3Month4IndexedPaperRoute
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound,
      Month3ProofPredicateLedgerSurface.Statement
        pkg.assembly.index) :=
  paper_ready_route_to_month3_proof_predicate_ledger_statement route

theorem paper_route_accepted_to_month3_ledger_proof_predicate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (route :
      Month3Month4IndexedPaperRoute
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n :=
  paper_ready_route_accepted_to_month3_ledger_proof_predicate
    route n haccepted

theorem paper_route_month3_ledger_proof_predicate_iff_certificate_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (route :
      Month3Month4IndexedPaperRoute
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ↔
      Nonempty (CanonicalProofCertificateAt bound n) :=
  paper_ready_route_month3_ledger_proof_predicate_iff_certificate_at
    route n

theorem paper_route_theorem5_literature_input_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (route :
      Month3Month4IndexedPaperRoute
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5LiteratureInputAuditSurface.Statement :=
  paper_ready_route_theorem5_literature_input_audit route

theorem paper_route_theorem5_project_audit_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (route :
      Month3Month4IndexedPaperRoute
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5LiteratureInputAuditSurface.ProjectTheorem5AuditWitness :=
  PudlakTheorem5LiteratureInputAuditSurface.statement_to_project_theorem5_audit_witness
      (paper_route_theorem5_literature_input_audit route)

theorem paper_route_theorem5_exact_external_boundary
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (route :
      Month3Month4IndexedPaperRoute
        rootSide MainRationality SondowAccepted bounds bound) :
    _root_.PudlakTheorem5ExactExternalBoundarySurface.Statement :=
  _root_.PudlakTheorem5ExactExternalBoundarySurface.statement_iff_literature_audit.mpr
    (paper_route_theorem5_literature_input_audit route)

theorem paper_route_theorem5_literature_audit_iff_exact_project_instance :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExactProjectInstance.Statement :=
  paper_ready_theorem5_literature_audit_iff_exact_project_instance

theorem paper_route_theorem5_literature_audit_iff_exact_minimal_package :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExactMinimalFieldPackageSurface.Statement :=
  PudlakTheorem5LiteratureInputAuditSurface.statement_iff_exact_minimal_package

theorem paper_route_theorem5_literature_audit_iff_internal_equivalence :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement :=
  PudlakTheorem5LiteratureInputAuditSurface.statement_iff_internal_equivalence

structure PaperAuditBundle
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop where
  paper_route :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound
  month3_proof_predicate_ledger :
    Nonempty (Σ' pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound,
      Month3ProofPredicateLedgerSurface.Statement
        pkg.assembly.index)
  accepted_to_month3_ledger_proof_predicate :
    ∀ n : Nat, ∀ _haccepted : SondowAccepted n,
      Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n
  month3_ledger_proof_predicate_iff_certificate_at :
    ∀ n : Nat,
      Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ↔
        Nonempty (CanonicalProofCertificateAt bound n)
  month4_literature_input_audit :
    PudlakTheorem5LiteratureInputAuditSurface.Statement
  month4_exact_external_boundary_statement :
    _root_.PudlakTheorem5ExactExternalBoundarySurface.Statement
  month4_literature_audit_iff_exact_project_instance :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExactProjectInstance.Statement
  month4_literature_audit_iff_exact_minimal_package :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExactMinimalFieldPackageSurface.Statement
  month4_literature_audit_iff_internal_equivalence :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement
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
  public_gap_instantiation :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality)
  not_main_rationality : ¬ MainRationality

def paperAuditBundle
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (route :
      Month3Month4IndexedPaperRoute
        rootSide MainRationality SondowAccepted bounds bound) :
    PaperAuditBundle
      rootSide MainRationality SondowAccepted bounds bound where
  paper_route := route
  month3_proof_predicate_ledger :=
    paper_route_to_month3_proof_predicate_ledger_statement route
  accepted_to_month3_ledger_proof_predicate :=
    paper_route_accepted_to_month3_ledger_proof_predicate route
  month3_ledger_proof_predicate_iff_certificate_at :=
    paper_route_month3_ledger_proof_predicate_iff_certificate_at route
  month4_literature_input_audit :=
    paper_route_theorem5_literature_input_audit route
  month4_exact_external_boundary_statement :=
    paper_route_theorem5_exact_external_boundary route
  month4_literature_audit_iff_exact_project_instance :=
    paper_route_theorem5_literature_audit_iff_exact_project_instance
  month4_literature_audit_iff_exact_minimal_package :=
    paper_route_theorem5_literature_audit_iff_exact_minimal_package
  month4_literature_audit_iff_internal_equivalence :=
    paper_route_theorem5_literature_audit_iff_internal_equivalence
  month4_raw_rescaled_power_chain :=
    PudlakTheorem5LiteratureInputAuditSurface.statement_raw_rescaled_power_chain
  month4_lower_source_code_eq_rescaled_pudlak :=
    PudlakTheorem5LiteratureInputAuditSurface.statement_lower_source_code_eq_rescaled_pudlak
  public_gap_instantiation :=
    paper_route_to_public_gap_instantiation route
  not_main_rationality :=
    paper_route_not_main_rationality route

theorem paper_route_iff_paper_audit_bundle
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      PaperAuditBundle
        rootSide MainRationality SondowAccepted bounds bound := by
  constructor
  · intro route
    exact paperAuditBundle route
  · intro bundle
    exact bundle.paper_route

structure PaperAuditPackage
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Type where
  release_package :
    Month3Month4PublicReleasePackage
      rootSide MainRationality SondowAccepted bounds bound
  route :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound
  audit :
    PaperAuditBundle
      rootSide MainRationality SondowAccepted bounds bound

namespace PaperAuditPackage

def ofRoute
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (route :
      Month3Month4IndexedPaperRoute
        rootSide MainRationality SondowAccepted bounds bound) :
    PaperAuditPackage
      rootSide MainRationality SondowAccepted bounds bound where
  release_package := Classical.choice route
  route := route
  audit := paperAuditBundle route

end PaperAuditPackage

theorem paper_route_iff_paper_audit_package_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Nonempty
        (PaperAuditPackage
          rootSide MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro route
    exact ⟨PaperAuditPackage.ofRoute route⟩
  · intro h
    rcases h with ⟨pkg⟩
    exact pkg.route

theorem paperAuditPackage_month3_proof_predicate_ledger
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' release_pkg :
      Month3Month4PublicReleasePackage
        rootSide MainRationality SondowAccepted bounds bound,
      Month3ProofPredicateLedgerSurface.Statement
        release_pkg.assembly.index) :=
  pkg.audit.month3_proof_predicate_ledger

theorem paperAuditPackage_theorem5_literature_input_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5LiteratureInputAuditSurface.Statement :=
  pkg.audit.month4_literature_input_audit

theorem paperAuditPackage_theorem5_project_audit_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5LiteratureInputAuditSurface.ProjectTheorem5AuditWitness :=
  PudlakTheorem5LiteratureInputAuditSurface.statement_to_project_theorem5_audit_witness
      (paperAuditPackage_theorem5_literature_input_audit pkg)

theorem paperAuditPackage_theorem5_exact_external_boundary
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    _root_.PudlakTheorem5ExactExternalBoundarySurface.Statement :=
  pkg.audit.month4_exact_external_boundary_statement

theorem paperAuditPackage_theorem5_literature_audit_iff_exact_project_instance
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExactProjectInstance.Statement :=
  pkg.audit.month4_literature_audit_iff_exact_project_instance

theorem paperAuditPackage_theorem5_literature_audit_iff_exact_minimal_package
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExactMinimalFieldPackageSurface.Statement :=
  pkg.audit.month4_literature_audit_iff_exact_minimal_package

theorem paperAuditPackage_theorem5_literature_audit_iff_internal_equivalence
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5LiteratureInputAuditSurface.Statement ↔
      PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement :=
  pkg.audit.month4_literature_audit_iff_internal_equivalence

theorem paperAuditPackage_theorem5_exact_project_instance
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5ExactProjectInstance.Statement :=
  (paperAuditPackage_theorem5_literature_audit_iff_exact_project_instance
    pkg).mp
    (paperAuditPackage_theorem5_literature_input_audit pkg)

theorem paperAuditPackage_theorem5_exact_minimal_package
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5ExactMinimalFieldPackageSurface.Statement :=
  (paperAuditPackage_theorem5_literature_audit_iff_exact_minimal_package
    pkg).mp
    (paperAuditPackage_theorem5_literature_input_audit pkg)

theorem paperAuditPackage_theorem5_internal_equivalence_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5ExternalInputBoundarySurface.InternalEquivalenceStatement :=
  (paperAuditPackage_theorem5_literature_audit_iff_internal_equivalence
    pkg).mp
    (paperAuditPackage_theorem5_literature_input_audit pkg)

theorem paperAuditPackage_theorem5_external_input_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5ExternalInputBoundarySurface.ExternalInputStatement :=
  PudlakTheorem5LiteratureInputAuditSurface.statement_iff_external_input.mp
    (paperAuditPackage_theorem5_literature_input_audit pkg)

theorem paperAuditPackage_theorem5_raw_rescaled_power_chain
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    PudlakTheorem5MinimalExternalFieldsSurface.rescaledRawCode n =
        PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n ∧
      PudlakTheorem5MinimalExternalFieldsSurface.powerBoundRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  pkg.audit.month4_raw_rescaled_power_chain n

theorem paperAuditPackage_theorem5_lower_source_code_eq_rescaled_pudlak
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.raw
        PudlakTheorem5LowerBoundSourceSurface.lowerBoundSource.scale n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        PudlakTheorem5MinimalExternalFieldsSurface.scale n :=
  pkg.audit.month4_lower_source_code_eq_rescaled_pudlak n

theorem paperAuditPackage_theorem5_power_bound_iff_rescaled
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    LiteraturePudlakTheorem5PowerBoundLowerBound
        literaturePudlakTheorem5ExternalScaleData ↔
      StrongRescaledExternalStrengthenedLowerBound
        literaturePudlakTheorem5ExternalScaleData.rawCode
        literaturePudlakTheorem5ExternalScaleData.scale := by
  rcases paperAuditPackage_theorem5_internal_equivalence_statement pkg
    with ⟨chain⟩
  exact chain.power_bound_iff_rescaled

theorem paperAuditPackage_theorem5_certificate_presentation_iff_rescaled
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty LiteraturePudlakTheorem5LowerBoundCertificate ↔
      Nonempty LiteraturePudlakTheorem5RescaledLowerBoundCertificate := by
  rcases paperAuditPackage_theorem5_internal_equivalence_statement pkg
    with ⟨chain⟩
  exact chain.certificate_presentation_iff_rescaled

theorem paperAuditPackage_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  pkg.audit.public_gap_instantiation

def paperAuditPackage_source_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CompiledSondowProjectSourceCertificateAt bounds n :=
  public_release_source_at pkg.release_package n haccepted

def paperAuditPackage_canonical_certificate_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CanonicalProofCertificateAt bound n :=
  public_release_canonical_certificate_at pkg.release_package n haccepted

def paperAuditPackage_checker_trace_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CertificateVerifierMachine.AcceptedTrace
      (canonicalProofCertificateVerifierMachine bound) n :=
  public_release_checker_trace_at pkg.release_package n haccepted

theorem paperAuditPackage_accepted_to_source_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (CompiledSondowProjectSourceCertificateAt bounds n) :=
  ⟨paperAuditPackage_source_at pkg n haccepted⟩

theorem paperAuditPackage_accepted_to_canonical_certificate_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (CanonicalProofCertificateAt bound n) :=
  ⟨paperAuditPackage_canonical_certificate_at pkg n haccepted⟩

theorem paperAuditPackage_accepted_to_checker_trace_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty
      (CertificateVerifierMachine.AcceptedTrace
        (canonicalProofCertificateVerifierMachine bound) n) :=
  ⟨paperAuditPackage_checker_trace_at pkg n haccepted⟩

theorem paperAuditPackage_accepted_to_month3_ledger_proof_predicate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n :=
  pkg.audit.accepted_to_month3_ledger_proof_predicate n haccepted

theorem paperAuditPackage_month3_ledger_proof_predicate_iff_certificate_at
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    Month3ProofPredicateLedgerSurface.boundedPAProofPredicate bound n ↔
      Nonempty (CanonicalProofCertificateAt bound n) :=
  pkg.audit.month3_ledger_proof_predicate_iff_certificate_at n

theorem paperAuditPackage_checker_trace_cert_eq_canonical_proof
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (paperAuditPackage_checker_trace_at pkg n haccepted).cert =
      (paperAuditPackage_canonical_certificate_at pkg n haccepted).proof := by
  exact
    public_release_checker_trace_cert_eq_canonical_proof
      pkg.release_package n haccepted

theorem paperAuditPackage_checker_trace_cert_eq_assembled_proof
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (paperAuditPackage_checker_trace_at pkg n haccepted).cert =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          pkg.release_package.assembly.index)
        (paperAuditPackage_source_at pkg n haccepted) :=
  public_release_checker_trace_cert_eq_assembled_proof
    pkg.release_package n haccepted

theorem paperAuditPackage_canonical_proof_eq_assembled_proof
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (paperAuditPackage_canonical_certificate_at pkg n haccepted).proof =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          pkg.release_package.assembly.index)
        (paperAuditPackage_source_at pkg n haccepted) :=
  (paperAuditPackage_checker_trace_cert_eq_canonical_proof
    pkg n haccepted).symm.trans
    (paperAuditPackage_checker_trace_cert_eq_assembled_proof
      pkg n haccepted)

theorem paperAuditPackage_source_size_audit_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Month3SourceSizeAuditSurface.Statement
      pkg.release_package.assembly.index :=
  Month3SourceSizeAuditSurface.statement
    pkg.release_package.assembly.index

theorem paperAuditPackage_source_size_eq_component_sum
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CompiledSondowProjectSourceCertificateAt.sourceSize
        (paperAuditPackage_source_at pkg n haccepted) =
      (paperAuditPackage_source_at pkg n haccepted).product.sourceSize +
        (paperAuditPackage_source_at pkg n haccepted).logRelation.sourceSize +
          (paperAuditPackage_source_at pkg n haccepted).decomposition.sourceSize +
            (paperAuditPackage_source_at pkg n haccepted).threePow.sourceSize +
              (paperAuditPackage_source_at pkg n haccepted).payload.sourceSize := by
  simpa [paperAuditPackage_source_at, public_release_source_at,
    Month3ProviderClosureSurface.sourceAt,
    Month3ProviderClosureSurface.acceptedCompiler,
    Month3SourceSizeAuditSurface.accepted_source,
    Month3SourceSizeAuditSurface.accepted_source_size]
    using
      Month3SourceSizeAuditSurface.accepted_source_size_eq_component_sum
        pkg.release_package.assembly.index n haccepted

theorem paperAuditPackage_canonical_source_size_eq_source_size
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (paperAuditPackage_canonical_certificate_at pkg n haccepted).sourceSize =
      CompiledSondowProjectSourceCertificateAt.sourceSize
        (paperAuditPackage_source_at pkg n haccepted) := by
  simpa [paperAuditPackage_source_at, public_release_source_at,
    paperAuditPackage_canonical_certificate_at,
    public_release_canonical_certificate_at]
    using
      Month3ProviderClosureSurface.canonical_sourceSize_eq_sourceAt_size
        pkg.release_package.assembly.index n haccepted

theorem paperAuditPackage_source_product_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((paperAuditPackage_source_at
      pkg n haccepted).product.proof.size + 2 : Nat) : Real)) ≤
      bounds.product n := by
  simpa [paperAuditPackage_source_at, public_release_source_at,
    Month3ProviderClosureSurface.sourceAt,
    Month3ProviderClosureSurface.acceptedCompiler]
    using
      (Month3BoundedPAProofPredicateAssemblySurface.statement
        pkg.release_package.assembly.index
          |>.source_product_size_plus_two_le n haccepted)

theorem paperAuditPackage_source_log_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((paperAuditPackage_source_at
      pkg n haccepted).logRelation.proof.size + 2 : Nat) : Real)) ≤
      bounds.logRelation n := by
  simpa [paperAuditPackage_source_at, public_release_source_at,
    Month3ProviderClosureSurface.sourceAt,
    Month3ProviderClosureSurface.acceptedCompiler]
    using
      (Month3BoundedPAProofPredicateAssemblySurface.statement
        pkg.release_package.assembly.index
          |>.source_log_size_plus_two_le n haccepted)

theorem paperAuditPackage_source_decomposition_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((paperAuditPackage_source_at
      pkg n haccepted).decomposition.proof.size + 2 : Nat) : Real)) ≤
      bounds.decomposition n := by
  simpa [paperAuditPackage_source_at, public_release_source_at,
    Month3ProviderClosureSurface.sourceAt,
    Month3ProviderClosureSurface.acceptedCompiler]
    using
      (Month3BoundedPAProofPredicateAssemblySurface.statement
        pkg.release_package.assembly.index
          |>.source_decomposition_size_plus_two_le n haccepted)

theorem paperAuditPackage_source_threePow_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((paperAuditPackage_source_at
      pkg n haccepted).threePow.proof.size + 2 : Nat) : Real)) ≤
      bounds.threePow n := by
  simpa [paperAuditPackage_source_at, public_release_source_at,
    Month3ProviderClosureSurface.sourceAt,
    Month3ProviderClosureSurface.acceptedCompiler]
    using
      (Month3BoundedPAProofPredicateAssemblySurface.statement
        pkg.release_package.assembly.index
          |>.source_threePow_size_plus_two_le n haccepted)

theorem paperAuditPackage_source_payload_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((paperAuditPackage_source_at
      pkg n haccepted).payload.proof.size + 2 : Nat) : Real)) ≤
      bounds.payload n := by
  simpa [paperAuditPackage_source_at, public_release_source_at,
    Month3ProviderClosureSurface.sourceAt,
    Month3ProviderClosureSurface.acceptedCompiler]
    using
      (Month3BoundedPAProofPredicateAssemblySurface.statement
        pkg.release_package.assembly.index
          |>.source_payload_size_plus_two_le n haccepted)

theorem paperAuditPackage_assembled_proof_size_plus_two_le_bound
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
      (Month3ProviderClosureSurface.assemblyIndex
        pkg.release_package.assembly.index)
      (paperAuditPackage_source_at pkg n haccepted)).size + 2 : Nat) :
        Real)) ≤ bound n :=
  (Month3BoundedPAProofPredicateAssemblySurface.statement
    pkg.release_package.assembly.index
      |>.assembled_size_plus_two_le_bound n
        (paperAuditPackage_source_at pkg n haccepted))

theorem paperAuditPackage_checker_trace_size_le_bound
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((paperAuditPackage_checker_trace_at pkg n haccepted).size : Real) ≤
      bound n := by
  exact
    public_release_checker_trace_size_le_bound
      pkg.release_package n haccepted

theorem paperAuditPackage_canonical_certificate_size_plus_two_le
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((paperAuditPackage_canonical_certificate_at
      pkg n haccepted).proof.size + 2 : Nat) : Real)) ≤ bound n := by
  exact
    public_release_canonical_certificate_size_plus_two_le
      pkg.release_package n haccepted

structure PaperProjectLevelFinalAudit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
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
  month3_checker_trace_cert_eq_assembled_proof :
    (paperAuditPackage_checker_trace_at pkg n haccepted).cert =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          pkg.release_package.assembly.index)
        (paperAuditPackage_source_at pkg n haccepted)
  month3_canonical_proof_eq_assembled_proof :
    (paperAuditPackage_canonical_certificate_at pkg n haccepted).proof =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex
          pkg.release_package.assembly.index)
        (paperAuditPackage_source_at pkg n haccepted)
  month3_source_size_eq_component_sum :
    CompiledSondowProjectSourceCertificateAt.sourceSize
        (paperAuditPackage_source_at pkg n haccepted) =
      (paperAuditPackage_source_at pkg n haccepted).product.sourceSize +
        (paperAuditPackage_source_at pkg n haccepted).logRelation.sourceSize +
          (paperAuditPackage_source_at pkg n haccepted).decomposition.sourceSize +
            (paperAuditPackage_source_at pkg n haccepted).threePow.sourceSize +
              (paperAuditPackage_source_at pkg n haccepted).payload.sourceSize
  month3_canonical_source_size_eq_source_size :
    (paperAuditPackage_canonical_certificate_at pkg n haccepted).sourceSize =
      CompiledSondowProjectSourceCertificateAt.sourceSize
        (paperAuditPackage_source_at pkg n haccepted)
  month3_source_product_size_plus_two_le :
    ((((paperAuditPackage_source_at
      pkg n haccepted).product.proof.size + 2 : Nat) : Real)) ≤
      bounds.product n
  month3_source_log_size_plus_two_le :
    ((((paperAuditPackage_source_at
      pkg n haccepted).logRelation.proof.size + 2 : Nat) : Real)) ≤
      bounds.logRelation n
  month3_source_decomposition_size_plus_two_le :
    ((((paperAuditPackage_source_at
      pkg n haccepted).decomposition.proof.size + 2 : Nat) : Real)) ≤
      bounds.decomposition n
  month3_source_threePow_size_plus_two_le :
    ((((paperAuditPackage_source_at
      pkg n haccepted).threePow.proof.size + 2 : Nat) : Real)) ≤
      bounds.threePow n
  month3_source_payload_size_plus_two_le :
    ((((paperAuditPackage_source_at
      pkg n haccepted).payload.proof.size + 2 : Nat) : Real)) ≤
      bounds.payload n
  month3_assembled_proof_size_plus_two_le_bound :
    ((((ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
      (Month3ProviderClosureSurface.assemblyIndex
        pkg.release_package.assembly.index)
      (paperAuditPackage_source_at pkg n haccepted)).size + 2 : Nat) :
        Real)) ≤ bound n
  month3_checker_trace_size_le_bound :
    ((paperAuditPackage_checker_trace_at pkg n haccepted).size : Real) ≤
      bound n
  month3_canonical_certificate_size_plus_two_le :
    ((((paperAuditPackage_canonical_certificate_at
      pkg n haccepted).proof.size + 2 : Nat) : Real)) ≤ bound n
  month4_literature_input_audit :
    PudlakTheorem5LiteratureInputAuditSurface.Statement
  month4_project_theorem5_audit_witness :
    PudlakTheorem5LiteratureInputAuditSurface.ProjectTheorem5AuditWitness
  month4_exact_external_boundary_statement :
    _root_.PudlakTheorem5ExactExternalBoundarySurface.Statement
  month4_exact_project_instance :
    PudlakTheorem5ExactProjectInstance.Statement
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

theorem paperAuditPackage_project_level_final_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    PaperProjectLevelFinalAudit pkg n haccepted where
  month3_source_nonempty :=
    paperAuditPackage_accepted_to_source_nonempty pkg n haccepted
  month3_canonical_certificate_nonempty :=
    paperAuditPackage_accepted_to_canonical_certificate_nonempty
      pkg n haccepted
  month3_checker_trace_nonempty :=
    paperAuditPackage_accepted_to_checker_trace_nonempty
      pkg n haccepted
  month3_ledger_proof_predicate :=
    paperAuditPackage_accepted_to_month3_ledger_proof_predicate
      pkg n haccepted
  month3_ledger_proof_predicate_iff_certificate_at :=
    paperAuditPackage_month3_ledger_proof_predicate_iff_certificate_at
      pkg n
  month3_checker_trace_cert_eq_assembled_proof :=
    paperAuditPackage_checker_trace_cert_eq_assembled_proof
      pkg n haccepted
  month3_canonical_proof_eq_assembled_proof :=
    paperAuditPackage_canonical_proof_eq_assembled_proof
      pkg n haccepted
  month3_source_size_eq_component_sum :=
    paperAuditPackage_source_size_eq_component_sum pkg n haccepted
  month3_canonical_source_size_eq_source_size :=
    paperAuditPackage_canonical_source_size_eq_source_size pkg n haccepted
  month3_source_product_size_plus_two_le :=
    paperAuditPackage_source_product_size_plus_two_le pkg n haccepted
  month3_source_log_size_plus_two_le :=
    paperAuditPackage_source_log_size_plus_two_le pkg n haccepted
  month3_source_decomposition_size_plus_two_le :=
    paperAuditPackage_source_decomposition_size_plus_two_le
      pkg n haccepted
  month3_source_threePow_size_plus_two_le :=
    paperAuditPackage_source_threePow_size_plus_two_le pkg n haccepted
  month3_source_payload_size_plus_two_le :=
    paperAuditPackage_source_payload_size_plus_two_le pkg n haccepted
  month3_assembled_proof_size_plus_two_le_bound :=
    paperAuditPackage_assembled_proof_size_plus_two_le_bound
      pkg n haccepted
  month3_checker_trace_size_le_bound :=
    paperAuditPackage_checker_trace_size_le_bound pkg n haccepted
  month3_canonical_certificate_size_plus_two_le :=
    paperAuditPackage_canonical_certificate_size_plus_two_le
      pkg n haccepted
  month4_literature_input_audit :=
    paperAuditPackage_theorem5_literature_input_audit pkg
  month4_project_theorem5_audit_witness :=
    paperAuditPackage_theorem5_project_audit_witness pkg
  month4_exact_external_boundary_statement :=
    paperAuditPackage_theorem5_exact_external_boundary pkg
  month4_exact_project_instance :=
    paperAuditPackage_theorem5_exact_project_instance pkg
  month4_exact_minimal_package :=
    paperAuditPackage_theorem5_exact_minimal_package pkg
  month4_internal_equivalence :=
    paperAuditPackage_theorem5_internal_equivalence_statement pkg
  month4_raw_rescaled_power_chain :=
    paperAuditPackage_theorem5_raw_rescaled_power_chain pkg n
  month4_lower_source_code_eq_rescaled_pudlak :=
    paperAuditPackage_theorem5_lower_source_code_eq_rescaled_pudlak
      pkg n
  month4_power_bound_iff_rescaled :=
    paperAuditPackage_theorem5_power_bound_iff_rescaled pkg
  month4_certificate_presentation_iff_rescaled :=
    paperAuditPackage_theorem5_certificate_presentation_iff_rescaled pkg
  public_gap_instantiation :=
    paperAuditPackage_public_gap_instantiation pkg
  not_main_rationality :=
    pkg.audit.not_main_rationality

theorem paperAuditPackage_project_level_final_audit_nonempty_iff_package
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (Σ' pkg :
      PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound,
      PaperProjectLevelFinalAudit pkg n haccepted) ↔
      Nonempty (PaperAuditPackage
        rootSide MainRationality SondowAccepted bounds bound) := by
  constructor
  · rintro ⟨⟨pkg, _audit⟩⟩
    exact ⟨pkg⟩
  · rintro ⟨pkg⟩
    exact ⟨⟨pkg,
      paperAuditPackage_project_level_final_audit pkg n haccepted⟩⟩

theorem paper_route_iff_project_level_final_audit_package
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Nonempty (Σ' pkg :
        PaperAuditPackage
          rootSide MainRationality SondowAccepted bounds bound,
        PaperProjectLevelFinalAudit pkg n haccepted) :=
  paper_route_iff_paper_audit_package_nonempty.trans
    (paperAuditPackage_project_level_final_audit_nonempty_iff_package
      n haccepted).symm

theorem exactConvention_checklist_iff_paper_route
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
      Month3Month4IndexedPaperRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  exactConvention_checklist_iff_paper_ready_route h

theorem exactConvention_checklist_iff_paper_audit_bundle
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
      PaperAuditBundle
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (exactConvention_checklist_iff_paper_route h).trans
    paper_route_iff_paper_audit_bundle

theorem exactConvention_checklist_iff_paper_audit_package
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
        (PaperAuditPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactConvention_checklist_iff_paper_route h).trans
    paper_route_iff_paper_audit_package_nonempty

theorem splitMinChecked_checklist_iff_paper_route
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
      Month3Month4IndexedPaperRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  splitMinChecked_checklist_iff_paper_ready_route h

theorem splitMinChecked_checklist_iff_paper_audit_bundle
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
      PaperAuditBundle
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (splitMinChecked_checklist_iff_paper_route h).trans
    paper_route_iff_paper_audit_bundle

theorem splitMinChecked_checklist_iff_paper_audit_package
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
        (PaperAuditPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (splitMinChecked_checklist_iff_paper_route h).trans
    paper_route_iff_paper_audit_package_nonempty

theorem exactFamily_checklist_iff_paper_route
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
      Month3Month4IndexedPaperRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  exactFamily_checklist_iff_paper_ready_route h

theorem exactFamily_checklist_iff_paper_audit_bundle
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
      PaperAuditBundle
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (exactFamily_checklist_iff_paper_route h).trans
    paper_route_iff_paper_audit_bundle

theorem exactFamily_checklist_iff_paper_audit_package
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
        (PaperAuditPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactFamily_checklist_iff_paper_route h).trans
    paper_route_iff_paper_audit_package_nonempty

theorem exactConvention_checklist_iff_project_level_final_audit_package
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
      Nonempty (Σ' pkg :
        PaperAuditPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
        PaperProjectLevelFinalAudit pkg m haccepted) :=
  (exactConvention_checklist_iff_paper_route h).trans
    (paper_route_iff_project_level_final_audit_package m haccepted)

theorem splitMinChecked_checklist_iff_project_level_final_audit_package
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
      Nonempty (Σ' pkg :
        PaperAuditPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
        PaperProjectLevelFinalAudit pkg m haccepted) :=
  (splitMinChecked_checklist_iff_paper_route h).trans
    (paper_route_iff_project_level_final_audit_package m haccepted)

theorem exactFamily_checklist_iff_project_level_final_audit_package
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
      Nonempty (Σ' pkg :
        PaperAuditPackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
        PaperProjectLevelFinalAudit pkg m haccepted) :=
  (exactFamily_checklist_iff_paper_route h).trans
    (paper_route_iff_project_level_final_audit_package m haccepted)

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
      MainRationality) :=
  SondowProjectMonth3Month4PaperReadyTheoremSurface.exactConvention_checklist_to_public_gap_instantiation
    h checklist

theorem splitMinChecked_checklist_to_public_gap_instantiation
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
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  SondowProjectMonth3Month4PaperReadyTheoremSurface.splitMinChecked_checklist_to_public_gap_instantiation
    h checklist

theorem exactFamily_checklist_to_public_gap_instantiation
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
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  SondowProjectMonth3Month4PaperReadyTheoremSurface.exactFamily_checklist_to_public_gap_instantiation
    h checklist

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
  SondowProjectMonth3Month4PaperReadyTheoremSurface.exactConvention_checklist_not_main_rationality
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
  SondowProjectMonth3Month4PaperReadyTheoremSurface.splitMinChecked_checklist_not_main_rationality
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
  SondowProjectMonth3Month4PaperReadyTheoremSurface.exactFamily_checklist_not_main_rationality
    h checklist


end SondowProjectMonth3Month4TheoremIndexSurface
end SondowMainCheckedCodeBridge
