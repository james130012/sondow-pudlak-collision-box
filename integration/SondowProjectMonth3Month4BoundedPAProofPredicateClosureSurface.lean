/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4AcceptedBoundedPAChainSurface

/-!
# Month 3/Month 4 bounded PA proof-predicate closure surface

This module names the bounded PA proof-predicate endpoint exposed by the
accepted-certificate chain.  The endpoint is not a new predicate: it is exactly
the `acceptsInput` predicate of the canonical proof-certificate verifier
machine.

The public audit route therefore closes the Month 3 chain as:

`SondowAccepted n -> CanonicalProofCertificateAccepted bound n`

where `CanonicalProofCertificateAccepted bound` is definitionally the accepted
input predicate of `canonicalProofCertificateVerifierMachine bound`.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4BoundedPAProofPredicateClosureSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4TheoremIndexSurface
open SondowProjectMonth3Month4AcceptedBoundedPAChainSurface

abbrev canonicalBoundedPAProofPredicate (bound : Nat → Real) : Nat → Prop :=
  CanonicalProofCertificateAccepted bound

theorem canonicalBoundedPAProofPredicate_eq_verifier_accepts
    (bound : Nat → Real) :
    canonicalBoundedPAProofPredicate bound =
      (canonicalProofCertificateVerifierMachine bound).acceptsInput := by
  rfl

structure BoundedPAProofPredicateClosureStatement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    Prop where
  chain_statement :
    AcceptedBoundedPAChainStatement pkg.audit_package
  month4_lower_bound_source_statement :
    PudlakTheorem5CanonicalImportSurface.LowerBoundSourceStatement
  month4_minimal_external_fields_statement :
    PudlakTheorem5CanonicalImportSurface.MinimalExternalFieldsStatement
  proof_predicate_eq_verifier_accepts :
    canonicalBoundedPAProofPredicate bound =
      (canonicalProofCertificateVerifierMachine bound).acceptsInput
  accepted_to_certificate_nonempty :
    ∀ n : Nat, ∀ _haccepted : SondowAccepted n,
      Nonempty (CanonicalProofCertificateAt bound n)
  accepted_to_bounded_pa_proof_predicate :
    ∀ n : Nat, ∀ _haccepted : SondowAccepted n,
      canonicalBoundedPAProofPredicate bound n
  accepted_to_checker_trace_nonempty :
    ∀ n : Nat, ∀ _haccepted : SondowAccepted n,
      Nonempty
        (CertificateVerifierMachine.AcceptedTrace
          (canonicalProofCertificateVerifierMachine bound) n)
  certificate_iff_bounded_pa_proof_predicate :
    ∀ n : Nat,
      canonicalBoundedPAProofPredicate bound n ↔
        Nonempty (CanonicalProofCertificateAt bound n)
  checker_trace_cert_eq_canonical_proof :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (chainPackage_accepted_to_checker_trace pkg n haccepted).cert =
        (chainPackage_accepted_to_canonical_certificate
          pkg n haccepted).proof
  checker_trace_size_le_bound :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((chainPackage_accepted_to_checker_trace
        pkg n haccepted).size : Real) ≤ bound n
  canonical_certificate_size_plus_two_le :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((chainPackage_accepted_to_canonical_certificate
        pkg n haccepted).proof.size + 2 : Nat) : Real)) ≤ bound n
  theorem5_rescaled_raw_eq_rescaled_pudlak :
    ∀ n : Nat,
      literaturePudlakTheorem5ExternalScaleData.rescaledRawCode n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          literaturePudlakTheorem5ExternalScaleData.scale n
  theorem5_lower_source_code_eq_rescaled_pudlak :
    ∀ n : Nat,
      rescaledExternalStrengthenedLowerBoundCode
          PudlakTheorem5CanonicalImportSurface.lowerBoundSource.raw
          PudlakTheorem5CanonicalImportSurface.lowerBoundSource.scale n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          literaturePudlakTheorem5ExternalScaleData.scale n
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
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    BoundedPAProofPredicateClosureStatement pkg where
  chain_statement := pkg.chain
  month4_lower_bound_source_statement :=
    pkg.audit_package.exactness_package.exactness
      |>.month4_lower_bound_source_statement
  month4_minimal_external_fields_statement :=
    pkg.audit_package.exactness_package.exactness
      |>.month4_minimal_external_fields_statement
  proof_predicate_eq_verifier_accepts :=
    canonicalBoundedPAProofPredicate_eq_verifier_accepts bound
  accepted_to_certificate_nonempty := by
    intro n haccepted
    exact ⟨chainPackage_accepted_to_canonical_certificate pkg n haccepted⟩
  accepted_to_bounded_pa_proof_predicate := by
    intro n haccepted
    exact chainPackage_accepted_to_canonical_accepted pkg n haccepted
  accepted_to_checker_trace_nonempty := by
    intro n haccepted
    exact chainPackage_accepted_to_checker_trace_nonempty pkg n haccepted
  certificate_iff_bounded_pa_proof_predicate := by
    intro n
    exact canonicalProofCertificateAccepted_iff_certificateAt
  checker_trace_cert_eq_canonical_proof := by
    intro n haccepted
    exact
      chainPackage_checker_trace_cert_eq_canonical_proof
        pkg n haccepted
  checker_trace_size_le_bound := by
    intro n haccepted
    exact chainPackage_checker_trace_size_le_bound pkg n haccepted
  canonical_certificate_size_plus_two_le := by
    intro n haccepted
    exact
      chainPackage_canonical_size_plus_two_le_bound
        pkg n haccepted
  theorem5_rescaled_raw_eq_rescaled_pudlak :=
    pkg.audit_package.exactness_package.exactness
      |>.readiness.theorem5_rescaled_raw_eq_rescaled_pudlak
  theorem5_lower_source_code_eq_rescaled_pudlak :=
    pkg.audit_package.exactness_package.exactness
      |>.readiness.theorem5_lower_source_code_eq_rescaled_pudlak
  theorem5_scale_eq_power_bound :=
    pkg.chain.theorem5_scale_eq_power_bound

theorem statement_iff_chain_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    BoundedPAProofPredicateClosureStatement pkg ↔
      AcceptedBoundedPAChainStatement pkg.audit_package := by
  constructor
  · intro h
    exact h.chain_statement
  · intro _h
    exact statement pkg

structure BoundedPAProofPredicateClosurePackage
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  chain_package :
    AcceptedBoundedPAChainPackage
      rootSide MainRationality SondowAccepted bounds bound
  closure :
    BoundedPAProofPredicateClosureStatement chain_package

namespace BoundedPAProofPredicateClosurePackage

def ofChainPackage
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (chain_package :
      AcceptedBoundedPAChainPackage
        rootSide MainRationality SondowAccepted bounds bound) :
    BoundedPAProofPredicateClosurePackage
      rootSide MainRationality SondowAccepted bounds bound where
  chain_package := chain_package
  closure := statement chain_package

end BoundedPAProofPredicateClosurePackage

theorem closurePackage_nonempty_iff_chain_package_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty
        (BoundedPAProofPredicateClosurePackage
          rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty
        (AcceptedBoundedPAChainPackage
          rootSide MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨pkg⟩
    exact ⟨pkg.chain_package⟩
  · intro h
    rcases h with ⟨pkg⟩
    exact ⟨BoundedPAProofPredicateClosurePackage.ofChainPackage pkg⟩

theorem paper_route_iff_bounded_pa_closure
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Nonempty
        (BoundedPAProofPredicateClosurePackage
          rootSide MainRationality SondowAccepted bounds bound) :=
  paper_route_iff_chain_package.trans
    closurePackage_nonempty_iff_chain_package_nonempty.symm

theorem exactConvention_checklist_iff_bounded_pa_closure
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
        (BoundedPAProofPredicateClosurePackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactConvention_checklist_iff_chain_package h).trans
      closurePackage_nonempty_iff_chain_package_nonempty.symm

theorem splitMinChecked_checklist_iff_bounded_pa_closure
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
        (BoundedPAProofPredicateClosurePackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (splitMinChecked_checklist_iff_chain_package h).trans
      closurePackage_nonempty_iff_chain_package_nonempty.symm

theorem exactFamily_checklist_iff_bounded_pa_closure
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
        (BoundedPAProofPredicateClosurePackage
          h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactFamily_checklist_iff_chain_package h).trans
      closurePackage_nonempty_iff_chain_package_nonempty.symm

theorem closurePackage_accepted_to_bounded_pa_proof_predicate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      BoundedPAProofPredicateClosurePackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    canonicalBoundedPAProofPredicate bound n :=
  pkg.closure.accepted_to_bounded_pa_proof_predicate n haccepted

theorem closurePackage_accepted_to_checker_trace_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      BoundedPAProofPredicateClosurePackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty
      (CertificateVerifierMachine.AcceptedTrace
        (canonicalProofCertificateVerifierMachine bound) n) :=
  pkg.closure.accepted_to_checker_trace_nonempty n haccepted

theorem closurePackage_accepted_month3_proof_predicate_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      BoundedPAProofPredicateClosurePackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    AcceptedMonth3ProofPredicateWitness pkg.chain_package n haccepted :=
  chainPackage_accepted_month3_proof_predicate_witness
    pkg.chain_package n haccepted

theorem closurePackage_month4_lower_bound_source_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      BoundedPAProofPredicateClosurePackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5CanonicalImportSurface.LowerBoundSourceStatement :=
  pkg.closure.month4_lower_bound_source_statement

theorem closurePackage_month4_minimal_external_fields_statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      BoundedPAProofPredicateClosurePackage
        rootSide MainRationality SondowAccepted bounds bound) :
    PudlakTheorem5CanonicalImportSurface.MinimalExternalFieldsStatement :=
  pkg.closure.month4_minimal_external_fields_statement

theorem closurePackage_theorem5_lower_source_code_eq_rescaled_pudlak
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg :
      BoundedPAProofPredicateClosurePackage
        rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    rescaledExternalStrengthenedLowerBoundCode
        PudlakTheorem5CanonicalImportSurface.lowerBoundSource.raw
        PudlakTheorem5CanonicalImportSurface.lowerBoundSource.scale n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        literaturePudlakTheorem5ExternalScaleData.scale n :=
  pkg.closure.theorem5_lower_source_code_eq_rescaled_pudlak n

theorem exactConvention_checklist_to_bounded_pa_proof_predicate
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
    canonicalBoundedPAProofPredicate bound m := by
  rcases (exactConvention_checklist_iff_bounded_pa_closure h).1
    checklist with ⟨pkg⟩
  exact
    closurePackage_accepted_to_bounded_pa_proof_predicate
      pkg m haccepted

theorem exactConvention_checklist_to_closure_accepted_month3_witness
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
    Nonempty (Σ' pkg : BoundedPAProofPredicateClosurePackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      AcceptedMonth3ProofPredicateWitness
        pkg.chain_package m haccepted) := by
  rcases (exactConvention_checklist_iff_bounded_pa_closure h).1
    checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      closurePackage_accepted_month3_proof_predicate_witness
        pkg m haccepted⟩⟩

theorem splitMinChecked_checklist_to_bounded_pa_proof_predicate
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
    canonicalBoundedPAProofPredicate bound m := by
  rcases (splitMinChecked_checklist_iff_bounded_pa_closure h).1
    checklist with ⟨pkg⟩
  exact
    closurePackage_accepted_to_bounded_pa_proof_predicate
      pkg m haccepted

theorem splitMinChecked_checklist_to_closure_accepted_month3_witness
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
    Nonempty (Σ' pkg : BoundedPAProofPredicateClosurePackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      AcceptedMonth3ProofPredicateWitness
        pkg.chain_package m haccepted) := by
  rcases (splitMinChecked_checklist_iff_bounded_pa_closure h).1
    checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      closurePackage_accepted_month3_proof_predicate_witness
        pkg m haccepted⟩⟩

theorem exactFamily_checklist_to_bounded_pa_proof_predicate
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
    canonicalBoundedPAProofPredicate bound m := by
  rcases (exactFamily_checklist_iff_bounded_pa_closure h).1
    checklist with ⟨pkg⟩
  exact
    closurePackage_accepted_to_bounded_pa_proof_predicate
      pkg m haccepted

theorem exactFamily_checklist_to_closure_accepted_month3_witness
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
    Nonempty (Σ' pkg : BoundedPAProofPredicateClosurePackage
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound,
      AcceptedMonth3ProofPredicateWitness
        pkg.chain_package m haccepted) := by
  rcases (exactFamily_checklist_iff_bounded_pa_closure h).1
    checklist with ⟨pkg⟩
  exact
    ⟨⟨pkg,
      closurePackage_accepted_month3_proof_predicate_witness
        pkg m haccepted⟩⟩

end SondowProjectMonth3Month4BoundedPAProofPredicateClosureSurface
end SondowMainCheckedCodeBridge
