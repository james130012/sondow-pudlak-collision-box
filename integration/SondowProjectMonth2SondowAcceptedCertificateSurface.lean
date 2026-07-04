/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectS21Kernel

/-!
# Month 2 Sondow accepted certificate surface

This file is the public Month 2 entry point for the Sondow accepted-certificate
route.  It does not introduce a new unconditional conclusion.  It packages the
already checked Sondow-side objects that Month 2 will extend:

* eventual component proof-object certificates from rationality;
* eventual S²₁ semantic nonemptiness for the reflection-graft sidecar;
* the root proof-length convention needed to move from sidecar semantics to
  the root proof-length coordinate;
* the C-line minimal closure bundle used to produce the project-local
  reflection-graft verifier.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth2SondowAcceptedCertificateSurface

universe u

def Month2SondowAccepted (n : ℕ) : Prop :=
  _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)

theorem month2SondowAccepted_iff_root_accepted (n : ℕ) :
    Month2SondowAccepted n ↔
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  Iff.rfl

theorem month2SondowAccepted_eventually_of_reflection_graft_collapse_inputs
    (hcollapse :
      _root_.EventualCertificateCollapseInputs
        _root_.sondowReflectionGraftCode)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n := by
  simpa [Month2SondowAccepted] using
    hcollapse.accepted_eventually_under_rationality h_rat

structure Month2SondowComponentCertificateFields
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  witness :
    SondowReflectionGraftSidecarComponentProofObjectExistsEventually
      bounds

namespace Month2SondowComponentCertificateFields

def threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (fields : Month2SondowComponentCertificateFields bounds) : ℕ :=
  fields.witness.threshold

theorem product_exists_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (fields : Month2SondowComponentCertificateFields bounds)
    {n : ℕ} (hn : fields.threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.product n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.product n :=
  fields.witness.product_exists n hn

theorem log_exists_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (fields : Month2SondowComponentCertificateFields bounds)
    {n : ℕ} (hn : fields.threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.logRelation n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.logRelation n :=
  fields.witness.log_exists n hn

theorem decomposition_exists_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (fields : Month2SondowComponentCertificateFields bounds)
    {n : ℕ} (hn : fields.threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.decomposition n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.decomposition n :=
  fields.witness.decomposition_exists n hn

theorem threePow_exists_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (fields : Month2SondowComponentCertificateFields bounds)
    {n : ℕ} (hn : fields.threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.threePow n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.threePow n :=
  fields.witness.threePow_exists n hn

theorem payload_exists_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (fields : Month2SondowComponentCertificateFields bounds)
    {n : ℕ} (hn : fields.threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.payload n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.payload n :=
  fields.witness.payload_exists n hn

theorem component_eventual_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (fields : Month2SondowComponentCertificateFields bounds) :
    Nonempty
      (SondowReflectionGraftSidecarComponentProofObjectExistsEventually
        bounds) :=
  ⟨fields.witness⟩

theorem system_eventual_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (fields : Month2SondowComponentCertificateFields bounds) :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectSystemValidEventually
        bounds) :=
  (sondowReflectionGraftSidecarComponentProofObjectExistsEventually_nonempty_iff_systemValidEventually_nonempty).mp
    fields.component_eventual_nonempty

theorem semantic_eventual_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (fields : Month2SondowComponentCertificateFields bounds) :
    Nonempty SondowReflectionGraftSidecarS21SemanticNonemptyEventually :=
  sidecarS21SemanticNonemptyEventually_nonempty_of_componentProofObjectExistsEventually
    fields.component_eventual_nonempty

end Month2SondowComponentCertificateFields

noncomputable def component_fields_of_rationality_project_proof_objects
    {ctx : BoundedArithmeticLab.GammaRationalityContext}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcerts :
      BoundedArithmeticLab.SondowRationalityToProjectProofObjectCertificates
        ctx bounds)
    (hgamma : BoundedArithmeticLab.GammaRationalityWitness ctx) :
    Month2SondowComponentCertificateFields bounds where
  witness :=
    sidecarComponentProofObjectExistsEventually_of_rationalityProjectProofObjects
      hcerts hgamma

noncomputable def component_fields_of_main_eventual_compiler_and_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2SondowComponentCertificateFields bounds :=
  component_fields_of_rationality_project_proof_objects
    compiler.toProjectProofObjectCertificates h_rat

noncomputable def component_fields_of_main_full_compiler_and_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowFullCertificateComponentProofCompiler bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2SondowComponentCertificateFields bounds :=
  component_fields_of_main_eventual_compiler_and_rationality
    compiler.toEventualCompiler h_rat

noncomputable def component_fields_of_source_component_compilers_and_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2SondowComponentCertificateFields bounds :=
  component_fields_of_main_full_compiler_and_rationality
    compilers.toFullCertificateComponentProofCompiler h_rat

structure Month2SondowAcceptedAndComponentFields
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  accepted_threshold : ℕ
  accepted_after :
    ∀ n : ℕ, accepted_threshold ≤ n → Month2SondowAccepted n
  component_fields : Month2SondowComponentCertificateFields bounds

namespace Month2SondowAcceptedAndComponentFields

theorem product_exists_after_component_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAndComponentFields bounds)
    {n : ℕ} (hn : pkg.component_fields.threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.product n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.product n :=
  pkg.component_fields.product_exists_after hn

theorem log_exists_after_component_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAndComponentFields bounds)
    {n : ℕ} (hn : pkg.component_fields.threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.logRelation n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.logRelation n :=
  pkg.component_fields.log_exists_after hn

theorem decomposition_exists_after_component_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAndComponentFields bounds)
    {n : ℕ} (hn : pkg.component_fields.threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.decomposition n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.decomposition n :=
  pkg.component_fields.decomposition_exists_after hn

theorem threePow_exists_after_component_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAndComponentFields bounds)
    {n : ℕ} (hn : pkg.component_fields.threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.threePow n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.threePow n :=
  pkg.component_fields.threePow_exists_after hn

theorem payload_exists_after_component_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAndComponentFields bounds)
    {n : ℕ} (hn : pkg.component_fields.threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.payload n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.payload n :=
  pkg.component_fields.payload_exists_after hn

theorem semantic_eventual_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAndComponentFields bounds) :
    Nonempty SondowReflectionGraftSidecarS21SemanticNonemptyEventually :=
  pkg.component_fields.semantic_eventual_nonempty

end Month2SondowAcceptedAndComponentFields

noncomputable def accepted_and_component_fields_of_collapse_compiler_and_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcollapse :
      _root_.EventualCertificateCollapseInputs
        _root_.sondowReflectionGraftCode)
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2SondowAcceptedAndComponentFields bounds where
  accepted_threshold :=
    Classical.choose
      (month2SondowAccepted_eventually_of_reflection_graft_collapse_inputs
        hcollapse h_rat)
  accepted_after :=
    Classical.choose_spec
      (month2SondowAccepted_eventually_of_reflection_graft_collapse_inputs
        hcollapse h_rat)
  component_fields :=
    component_fields_of_main_eventual_compiler_and_rationality
      compiler h_rat

noncomputable def accepted_and_component_fields_of_collapse_full_compiler_and_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcollapse :
      _root_.EventualCertificateCollapseInputs
        _root_.sondowReflectionGraftCode)
    (compiler :
      MainSondowFullCertificateComponentProofCompiler bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2SondowAcceptedAndComponentFields bounds :=
  accepted_and_component_fields_of_collapse_compiler_and_rationality
    hcollapse compiler.toEventualCompiler h_rat

noncomputable def accepted_and_component_fields_of_collapse_source_compilers_and_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcollapse :
      _root_.EventualCertificateCollapseInputs
        _root_.sondowReflectionGraftCode)
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2SondowAcceptedAndComponentFields bounds :=
  accepted_and_component_fields_of_collapse_full_compiler_and_rationality
    hcollapse compilers.toFullCertificateComponentProofCompiler h_rat

structure Month2SondowAcceptedForwardReproofBoundary : Prop where
  forward_inputs : _root_.SondowForwardInputs
  explicit_eventual_of_rationality :
    _root_.is_rational _root_.euler_mascheroni →
      _root_.sondow_identity_explicit_eventual
  identity_eventual_of_rationality :
    _root_.is_rational _root_.euler_mascheroni →
      _root_.sondow_identity_eventual
  certificate_accepted_eventually_of_rationality :
    _root_.is_rational _root_.euler_mascheroni →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        _root_.accepted_certificate (_root_.sondowCertificateValidCode n)
  reflection_graft_collapse_inputs_of_payload_spec :
    _root_.PartialConsistencyPayloadSpec →
      _root_.ReflectionGraftConcreteVerificationPackage →
        _root_.EventualCertificateCollapseInputs
          _root_.sondowReflectionGraftCode
  reflection_graft_collapse_inputs_of_bridge_package :
    _root_.SondowCollapseVerificationBridgePackage →
      _root_.EventualCertificateCollapseInputs
        _root_.sondowReflectionGraftCode

def month2SondowAcceptedForwardReproofBoundary :
    Month2SondowAcceptedForwardReproofBoundary where
  forward_inputs := _root_.SondowForwardInputs.of_reproof
  explicit_eventual_of_rationality :=
    _root_.sondow_identity_explicit_eventual_of_rational_reproof
  identity_eventual_of_rationality :=
    _root_.sondow_identity_eventual_of_rational_reproof
  certificate_accepted_eventually_of_rationality :=
    _root_.accepted_sondow_certificate_eventual_of_rationality_reproof
  reflection_graft_collapse_inputs_of_payload_spec :=
    _root_.reflection_graft_eventual_collapse_inputs_of_reproof
  reflection_graft_collapse_inputs_of_bridge_package :=
    _root_.SondowCollapseVerificationBridgePackage.toReflectionGraftCollapseInputsOfReproof

theorem month2SondowAcceptedForwardReproofBoundary_forward_inputs_eq :
    month2SondowAcceptedForwardReproofBoundary.forward_inputs =
      _root_.SondowForwardInputs.of_reproof :=
  rfl

namespace Month2SondowAcceptedForwardReproofBoundary

theorem reflection_graft_accepted_eventually_of_payload_spec
    (boundary : Month2SondowAcceptedForwardReproofBoundary)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  month2SondowAccepted_eventually_of_reflection_graft_collapse_inputs
    (boundary.reflection_graft_collapse_inputs_of_payload_spec hspec hver)
    h_rat

theorem reflection_graft_accepted_eventually_of_bridge_package
    (boundary : Month2SondowAcceptedForwardReproofBoundary)
    (hbridge : _root_.SondowCollapseVerificationBridgePackage)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  month2SondowAccepted_eventually_of_reflection_graft_collapse_inputs
    (boundary.reflection_graft_collapse_inputs_of_bridge_package hbridge)
    h_rat

end Month2SondowAcceptedForwardReproofBoundary

noncomputable def accepted_and_component_fields_of_reproof_payload_spec_source_compilers_and_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2SondowAcceptedAndComponentFields bounds :=
  accepted_and_component_fields_of_collapse_source_compilers_and_rationality
    (_root_.reflection_graft_eventual_collapse_inputs_of_reproof hspec hver)
    compilers h_rat

noncomputable def accepted_and_component_fields_of_reproof_bridge_package_source_compilers_and_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hbridge : _root_.SondowCollapseVerificationBridgePackage)
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2SondowAcceptedAndComponentFields bounds :=
  accepted_and_component_fields_of_collapse_source_compilers_and_rationality
    (_root_.SondowCollapseVerificationBridgePackage.toReflectionGraftCollapseInputsOfReproof
      hbridge)
    compilers h_rat

structure Month2SondowAcceptedCertificateConstructionLayer
    (bounds : BoundedArithmeticLab.SondowComponentBounds) : Prop where
  component_eventual :
    Nonempty
      (SondowReflectionGraftSidecarComponentProofObjectExistsEventually
        bounds)
  root_convention :
    Nonempty SondowReflectionGraftRootProofLengthConvention

namespace Month2SondowAcceptedCertificateConstructionLayer

theorem system_eventual
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (layer : Month2SondowAcceptedCertificateConstructionLayer bounds) :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectSystemValidEventually
        bounds) :=
  (sondowReflectionGraftSidecarComponentProofObjectExistsEventually_nonempty_iff_systemValidEventually_nonempty).mp
    layer.component_eventual

theorem semantic_eventual
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (layer : Month2SondowAcceptedCertificateConstructionLayer bounds) :
    Nonempty SondowReflectionGraftSidecarS21SemanticNonemptyEventually :=
  sidecarS21SemanticNonemptyEventually_nonempty_of_componentProofObjectExistsEventually
    layer.component_eventual

theorem recognition_split
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (layer : Month2SondowAcceptedCertificateConstructionLayer bounds) :
    Nonempty
      SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate :=
  (sondowReflectionGraftRecognitionSplit_nonempty_iff_rootConvention_nonempty).mpr
    layer.root_convention

theorem checked_code_witness
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (layer : Month2SondowAcceptedCertificateConstructionLayer bounds) :
    Nonempty SondowReflectionGraftRootCheckedCodeConventionWitness :=
  (sondowReflectionGraftCheckedCodeConventionWitness_nonempty_iff_rootConvention_nonempty).mpr
    layer.root_convention

end Month2SondowAcceptedCertificateConstructionLayer

theorem component_eventual_of_rationality_project_proof_objects
    {ctx : BoundedArithmeticLab.GammaRationalityContext}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcerts :
      Nonempty
        (BoundedArithmeticLab.SondowRationalityToProjectProofObjectCertificates
          ctx bounds))
    (hgamma : BoundedArithmeticLab.GammaRationalityWitness ctx) :
    Nonempty
      (SondowReflectionGraftSidecarComponentProofObjectExistsEventually
        bounds) :=
  sidecarComponentProofObjectExistsEventually_nonempty_of_rationalityProjectProofObjects
    hcerts hgamma

theorem construction_layer_of_component_fields_and_root_convention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (fields : Month2SondowComponentCertificateFields bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Month2SondowAcceptedCertificateConstructionLayer bounds where
  component_eventual := fields.component_eventual_nonempty
  root_convention := hroot

noncomputable def construction_layer_of_main_eventual_compiler_rationality_and_root_convention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Month2SondowAcceptedCertificateConstructionLayer bounds :=
  construction_layer_of_component_fields_and_root_convention
    (component_fields_of_main_eventual_compiler_and_rationality
      compiler h_rat)
    hroot

noncomputable def construction_layer_of_main_full_compiler_rationality_and_root_convention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowFullCertificateComponentProofCompiler bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Month2SondowAcceptedCertificateConstructionLayer bounds :=
  construction_layer_of_component_fields_and_root_convention
    (component_fields_of_main_full_compiler_and_rationality compiler h_rat)
    hroot

noncomputable def construction_layer_of_source_component_compilers_rationality_and_root_convention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Month2SondowAcceptedCertificateConstructionLayer bounds :=
  construction_layer_of_component_fields_and_root_convention
    (component_fields_of_source_component_compilers_and_rationality
      compilers h_rat)
    hroot

structure Month2SondowAcceptedPublicConstructionPackage
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  accepted_and_components :
    Month2SondowAcceptedAndComponentFields bounds
  construction_layer :
    Month2SondowAcceptedCertificateConstructionLayer bounds

namespace Month2SondowAcceptedPublicConstructionPackage

theorem accepted_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedPublicConstructionPackage bounds)
    {n : ℕ}
    (hn : pkg.accepted_and_components.accepted_threshold ≤ n) :
    Month2SondowAccepted n :=
  pkg.accepted_and_components.accepted_after n hn

theorem root_accepted_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedPublicConstructionPackage bounds)
    {n : ℕ}
    (hn : pkg.accepted_and_components.accepted_threshold ≤ n) :
    _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) := by
  simpa [Month2SondowAccepted] using pkg.accepted_after hn

theorem product_exists_after_component_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedPublicConstructionPackage bounds)
    {n : ℕ}
    (hn : pkg.accepted_and_components.component_fields.threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.product n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.product n :=
  pkg.accepted_and_components.product_exists_after_component_threshold hn

theorem log_exists_after_component_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedPublicConstructionPackage bounds)
    {n : ℕ}
    (hn : pkg.accepted_and_components.component_fields.threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.logRelation n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.logRelation n :=
  pkg.accepted_and_components.log_exists_after_component_threshold hn

theorem decomposition_exists_after_component_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedPublicConstructionPackage bounds)
    {n : ℕ}
    (hn : pkg.accepted_and_components.component_fields.threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.decomposition n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.decomposition n :=
  pkg.accepted_and_components.decomposition_exists_after_component_threshold hn

theorem threePow_exists_after_component_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedPublicConstructionPackage bounds)
    {n : ℕ}
    (hn : pkg.accepted_and_components.component_fields.threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.threePow n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.threePow n :=
  pkg.accepted_and_components.threePow_exists_after_component_threshold hn

theorem payload_exists_after_component_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedPublicConstructionPackage bounds)
    {n : ℕ}
    (hn : pkg.accepted_and_components.component_fields.threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.payload n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.payload n :=
  pkg.accepted_and_components.payload_exists_after_component_threshold hn

theorem system_eventual_from_component_fields
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedPublicConstructionPackage bounds) :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectSystemValidEventually
        bounds) :=
  pkg.accepted_and_components.component_fields.system_eventual_nonempty

theorem semantic_eventual_from_component_fields
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedPublicConstructionPackage bounds) :
    Nonempty SondowReflectionGraftSidecarS21SemanticNonemptyEventually :=
  pkg.accepted_and_components.semantic_eventual_nonempty

theorem construction_system_eventual
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedPublicConstructionPackage bounds) :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectSystemValidEventually
        bounds) :=
  pkg.construction_layer.system_eventual

theorem construction_semantic_eventual
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedPublicConstructionPackage bounds) :
    Nonempty SondowReflectionGraftSidecarS21SemanticNonemptyEventually :=
  pkg.construction_layer.semantic_eventual

theorem recognition_split
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedPublicConstructionPackage bounds) :
    Nonempty
      SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate :=
  pkg.construction_layer.recognition_split

theorem checked_code_witness
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedPublicConstructionPackage bounds) :
    Nonempty SondowReflectionGraftRootCheckedCodeConventionWitness :=
  pkg.construction_layer.checked_code_witness

end Month2SondowAcceptedPublicConstructionPackage

noncomputable def public_construction_package_of_accepted_component_fields_and_root_convention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAndComponentFields bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Month2SondowAcceptedPublicConstructionPackage bounds where
  accepted_and_components := pkg
  construction_layer :=
    construction_layer_of_component_fields_and_root_convention
      pkg.component_fields hroot

noncomputable def public_construction_package_of_reproof_payload_spec_source_compilers_rationality_and_root_convention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Month2SondowAcceptedPublicConstructionPackage bounds :=
  public_construction_package_of_accepted_component_fields_and_root_convention
    (accepted_and_component_fields_of_reproof_payload_spec_source_compilers_and_rationality
      hspec hver compilers h_rat)
    hroot

noncomputable def public_construction_package_of_reproof_bridge_package_source_compilers_rationality_and_root_convention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hbridge : _root_.SondowCollapseVerificationBridgePackage)
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Month2SondowAcceptedPublicConstructionPackage bounds :=
  public_construction_package_of_accepted_component_fields_and_root_convention
    (accepted_and_component_fields_of_reproof_bridge_package_source_compilers_and_rationality
      hbridge compilers h_rat)
    hroot

theorem semantic_eventual_of_rationality_project_proof_objects
    {ctx : BoundedArithmeticLab.GammaRationalityContext}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcerts :
      Nonempty
        (BoundedArithmeticLab.SondowRationalityToProjectProofObjectCertificates
          ctx bounds))
    (hgamma : BoundedArithmeticLab.GammaRationalityWitness ctx) :
    Nonempty SondowReflectionGraftSidecarS21SemanticNonemptyEventually :=
  sidecarS21SemanticNonemptyEventually_nonempty_of_rationalityProjectProofObjects
    hcerts hgamma

theorem semantic_eventual_upper_bound_of_main_eventual_compiler
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds) :
    SondowReflectionGraftSidecarS21SemanticEventualUpperBound bounds :=
  sidecarS21SemanticEventualUpperBound_of_mainEventualCompiler compiler

structure Month2SondowAcceptedCLineClosureLayer
    (bounds : BoundedArithmeticLab.SondowComponentBounds) : Prop where
  kernel :
    Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}
  checker :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
        bounds)
  root_convention :
    Nonempty SondowReflectionGraftRootProofLengthConvention

namespace Month2SondowAcceptedCLineClosureLayer

theorem minimal_closure
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (layer : Month2SondowAcceptedCLineClosureLayer.{u} bounds) :
    Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds) :=
  sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_rootConvention
    layer.kernel layer.checker layer.root_convention

theorem concrete_checked_code_certificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (layer : Month2SondowAcceptedCLineClosureLayer.{u} bounds) :
    Nonempty
      SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u} :=
  sondowCLineMinimalClosureCertificate_nonempty_to_concreteCheckedCodeCertificate_nonempty
    (layer.minimal_closure)

theorem verifier
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (layer : Month2SondowAcceptedCLineClosureLayer.{u} bounds) :
    Nonempty SondowProjectLocalReflectionGraftVerifier :=
  sondowCLineMinimalClosureCertificate_nonempty_to_verifier_nonempty
    (layer.minimal_closure)

theorem payload_truth
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (layer : Month2SondowAcceptedCLineClosureLayer.{u} bounds) :
    Nonempty _root_.PartialConsistencyPayloadTruth :=
  sondowCLinePayloadTruth_nonempty_of_minimalClosureCertificate
    (layer.minimal_closure)

theorem direct_trace_completion
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (layer : Month2SondowAcceptedCLineClosureLayer.{u} bounds) :
    Nonempty SondowProjectLocalDirectTraceCollapseCompletion := by
  rcases layer.minimal_closure with ⟨certificate⟩
  exact ⟨certificate.toDirectTraceCompletion⟩

theorem collapse_conclusion
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (layer : Month2SondowAcceptedCLineClosureLayer.{u} bounds) :
    SondowProjectLocalS21CollapseConclusion :=
  sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
    (layer.minimal_closure)

end Month2SondowAcceptedCLineClosureLayer

structure Month2SondowAcceptedVerifierClosurePackage
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  public_construction :
    Month2SondowAcceptedPublicConstructionPackage bounds
  c_line_closure :
    Month2SondowAcceptedCLineClosureLayer.{u} bounds

namespace Month2SondowAcceptedVerifierClosurePackage

theorem accepted_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedVerifierClosurePackage.{u} bounds)
    {n : ℕ}
    (hn :
      pkg.public_construction.accepted_and_components.accepted_threshold ≤
        n) :
    Month2SondowAccepted n :=
  pkg.public_construction.accepted_after hn

theorem root_accepted_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedVerifierClosurePackage.{u} bounds)
    {n : ℕ}
    (hn :
      pkg.public_construction.accepted_and_components.accepted_threshold ≤
        n) :
    _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  pkg.public_construction.root_accepted_after hn

theorem component_system_eventual
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedVerifierClosurePackage.{u} bounds) :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectSystemValidEventually
        bounds) :=
  pkg.public_construction.construction_system_eventual

theorem semantic_eventual
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedVerifierClosurePackage.{u} bounds) :
    Nonempty SondowReflectionGraftSidecarS21SemanticNonemptyEventually :=
  pkg.public_construction.construction_semantic_eventual

theorem checked_code_witness
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedVerifierClosurePackage.{u} bounds) :
    Nonempty SondowReflectionGraftRootCheckedCodeConventionWitness :=
  pkg.public_construction.checked_code_witness

theorem minimal_closure
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedVerifierClosurePackage.{u} bounds) :
    Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds) :=
  pkg.c_line_closure.minimal_closure

theorem concrete_checked_code_certificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedVerifierClosurePackage.{u} bounds) :
    Nonempty
      SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u} :=
  pkg.c_line_closure.concrete_checked_code_certificate

theorem verifier
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedVerifierClosurePackage.{u} bounds) :
    Nonempty SondowProjectLocalReflectionGraftVerifier :=
  pkg.c_line_closure.verifier

theorem payload_truth
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedVerifierClosurePackage.{u} bounds) :
    Nonempty _root_.PartialConsistencyPayloadTruth :=
  pkg.c_line_closure.payload_truth

theorem direct_trace_completion
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedVerifierClosurePackage.{u} bounds) :
    Nonempty SondowProjectLocalDirectTraceCollapseCompletion :=
  pkg.c_line_closure.direct_trace_completion

theorem collapse_conclusion
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedVerifierClosurePackage.{u} bounds) :
    SondowProjectLocalS21CollapseConclusion :=
  pkg.c_line_closure.collapse_conclusion

end Month2SondowAcceptedVerifierClosurePackage

def month2_c_line_closure_layer_of_kernel_checker_root_convention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Month2SondowAcceptedCLineClosureLayer.{u} bounds where
  kernel := hkernel
  checker := hchecker
  root_convention := hroot

def verifier_closure_package_of_public_construction_kernel_checker_root_convention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (publicPkg :
      Month2SondowAcceptedPublicConstructionPackage bounds)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Month2SondowAcceptedVerifierClosurePackage.{u} bounds where
  public_construction := publicPkg
  c_line_closure :=
    month2_c_line_closure_layer_of_kernel_checker_root_convention
      hkernel hchecker hroot

noncomputable def verifier_closure_package_of_reproof_payload_spec_source_compilers_rationality_kernel_checker_root_convention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Month2SondowAcceptedVerifierClosurePackage.{u} bounds :=
  verifier_closure_package_of_public_construction_kernel_checker_root_convention
    (public_construction_package_of_reproof_payload_spec_source_compilers_rationality_and_root_convention
      hspec hver compilers h_rat hroot)
    hkernel hchecker hroot

noncomputable def verifier_closure_package_of_reproof_bridge_package_source_compilers_rationality_kernel_checker_root_convention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hbridge : _root_.SondowCollapseVerificationBridgePackage)
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Month2SondowAcceptedVerifierClosurePackage.{u} bounds :=
  verifier_closure_package_of_public_construction_kernel_checker_root_convention
    (public_construction_package_of_reproof_bridge_package_source_compilers_rationality_and_root_convention
      hbridge compilers h_rat hroot)
    hkernel hchecker hroot

structure Month2SondowSourceCompilerInterface
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  compilers :
    MainSondowFullCertificateSourceComponentCompilers bounds

namespace Month2SondowSourceCompilerInterface

def toFullCertificateComponentProofCompiler
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (iface : Month2SondowSourceCompilerInterface bounds) :
    MainSondowFullCertificateComponentProofCompiler bounds :=
  iface.compilers.toFullCertificateComponentProofCompiler

def sourceCertificateSystems
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (iface : Month2SondowSourceCompilerInterface bounds) :
    MainSondowSourceComponentCertificateSystems bounds :=
  iface.compilers.toSourceCertificateSystems

def projectProofCodeCompilers
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (iface : Month2SondowSourceCompilerInterface bounds) :
    BoundedArithmeticLab.SondowProjectComponentProofCodeCompilers bounds :=
  iface.compilers.toProjectProofCodeCompilers

theorem source_certificates_valid
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (iface : Month2SondowSourceCompilerInterface bounds)
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    iface.sourceCertificateSystems.productSystem.valid n
        hsource.productLogCertificate ∧
      iface.sourceCertificateSystems.logSystem.valid n
        hsource.productLogCertificate ∧
      iface.sourceCertificateSystems.decompositionSystem.valid n
        hsource.decompositionCertificate ∧
      iface.sourceCertificateSystems.threePowSystem.valid n
        hsource.threePowCertificate ∧
      iface.sourceCertificateSystems.payloadSystem.valid n
        hsource.payloadCertificate :=
  iface.compilers.source_certificates_valid hsource

def projectProofCodeCertificateAtOfSource
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (iface : Month2SondowSourceCompilerInterface bounds)
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    BoundedArithmeticLab.SondowProjectProofCodeCertificateAt
      iface.projectProofCodeCompilers n :=
  iface.compilers.projectProofCodeCertificateAt hsource

def sourceComponentsOfFullCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (_iface : Month2SondowSourceCompilerInterface bounds)
    {q : ℚ} {n : ℕ}
    (hchecked : mainSondowFullCertificateChecks q n) :
    MainSondowFullCertificateSourceComponents q n :=
  (mainSondowFullCertificateChecks_iff_sourceComponents q n).1
    hchecked

def projectProofCodeCertificateAtOfFullCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (iface : Month2SondowSourceCompilerInterface bounds)
    {q : ℚ} {n : ℕ}
    (hchecked : mainSondowFullCertificateChecks q n) :
    BoundedArithmeticLab.SondowProjectProofCodeCertificateAt
      iface.projectProofCodeCompilers n :=
  iface.projectProofCodeCertificateAtOfSource
    (iface.sourceComponentsOfFullCertificate hchecked)

def componentCertificateOfSource
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (iface : Month2SondowSourceCompilerInterface bounds)
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    BoundedArithmeticLab.SondowComponentCertificate :=
  iface.compilers.componentCertificateOfSource hsource

theorem componentCertificateOfSource_valid
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (iface : Month2SondowSourceCompilerInterface bounds)
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
      BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
      (iface.componentCertificateOfSource hsource) :=
  iface.compilers.componentCertificateOfSource_valid hsource

def componentCertificateOfFullCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (iface : Month2SondowSourceCompilerInterface bounds)
    {q : ℚ} {n : ℕ}
    (hchecked : mainSondowFullCertificateChecks q n) :
    BoundedArithmeticLab.SondowComponentCertificate :=
  iface.compilers.componentCertificateOfFullCertificate hchecked

theorem componentCertificateOfFullCertificate_valid
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (iface : Month2SondowSourceCompilerInterface bounds)
    {q : ℚ} {n : ℕ}
    (hchecked : mainSondowFullCertificateChecks q n) :
    BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
      BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
      (iface.componentCertificateOfFullCertificate hchecked) :=
  iface.compilers.componentCertificateOfFullCertificate_valid hchecked

noncomputable def component_fields_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (iface : Month2SondowSourceCompilerInterface bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2SondowComponentCertificateFields bounds :=
  component_fields_of_source_component_compilers_and_rationality
    iface.compilers h_rat

noncomputable def public_construction_package_of_reproof_payload_spec_rationality_and_root_convention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (iface : Month2SondowSourceCompilerInterface bounds)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Month2SondowAcceptedPublicConstructionPackage bounds :=
  public_construction_package_of_reproof_payload_spec_source_compilers_rationality_and_root_convention
    hspec hver iface.compilers h_rat hroot

noncomputable def public_construction_package_of_reproof_bridge_package_rationality_and_root_convention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (iface : Month2SondowSourceCompilerInterface bounds)
    (hbridge : _root_.SondowCollapseVerificationBridgePackage)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Month2SondowAcceptedPublicConstructionPackage bounds :=
  public_construction_package_of_reproof_bridge_package_source_compilers_rationality_and_root_convention
    hbridge iface.compilers h_rat hroot

noncomputable def verifier_closure_package_of_reproof_payload_spec_rationality_kernel_checker_root_convention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (iface : Month2SondowSourceCompilerInterface bounds)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Month2SondowAcceptedVerifierClosurePackage.{u} bounds :=
  verifier_closure_package_of_reproof_payload_spec_source_compilers_rationality_kernel_checker_root_convention
    hspec hver iface.compilers h_rat hkernel hchecker hroot

noncomputable def verifier_closure_package_of_reproof_bridge_package_rationality_kernel_checker_root_convention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (iface : Month2SondowSourceCompilerInterface bounds)
    (hbridge : _root_.SondowCollapseVerificationBridgePackage)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Month2SondowAcceptedVerifierClosurePackage.{u} bounds :=
  verifier_closure_package_of_reproof_bridge_package_source_compilers_rationality_kernel_checker_root_convention
    hbridge iface.compilers h_rat hkernel hchecker hroot

end Month2SondowSourceCompilerInterface

structure Month2SondowAcceptedAuditorBoundary
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  payload_spec : _root_.PartialConsistencyPayloadSpec
  concrete_verification :
    _root_.ReflectionGraftConcreteVerificationPackage
  source_interface : Month2SondowSourceCompilerInterface bounds
  root_convention :
    Nonempty SondowReflectionGraftRootProofLengthConvention
  kernel :
    Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}
  checker :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
        bounds)

namespace Month2SondowAcceptedAuditorBoundary

def forward_reproof_boundary
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (_boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds) :
    Month2SondowAcceptedForwardReproofBoundary :=
  month2SondowAcceptedForwardReproofBoundary

theorem forward_inputs_closed_by_reproof
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds) :
    boundary.forward_reproof_boundary.forward_inputs =
      _root_.SondowForwardInputs.of_reproof :=
  rfl

theorem accepted_eventually_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  boundary.forward_reproof_boundary
    |>.reflection_graft_accepted_eventually_of_payload_spec
      boundary.payload_spec boundary.concrete_verification h_rat

theorem source_certificates_valid
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    boundary.source_interface.sourceCertificateSystems.productSystem.valid n
        hsource.productLogCertificate ∧
      boundary.source_interface.sourceCertificateSystems.logSystem.valid n
        hsource.productLogCertificate ∧
      boundary.source_interface.sourceCertificateSystems.decompositionSystem.valid n
        hsource.decompositionCertificate ∧
      boundary.source_interface.sourceCertificateSystems.threePowSystem.valid n
        hsource.threePowCertificate ∧
      boundary.source_interface.sourceCertificateSystems.payloadSystem.valid n
        hsource.payloadCertificate :=
  boundary.source_interface.source_certificates_valid hsource

def componentCertificateOfSource
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    BoundedArithmeticLab.SondowComponentCertificate :=
  boundary.source_interface.componentCertificateOfSource hsource

theorem componentCertificateOfSource_valid
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
      BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
      (boundary.componentCertificateOfSource hsource) :=
  boundary.source_interface.componentCertificateOfSource_valid hsource

def componentCertificateOfFullCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    {q : ℚ} {n : ℕ}
    (hchecked : mainSondowFullCertificateChecks q n) :
    BoundedArithmeticLab.SondowComponentCertificate :=
  boundary.source_interface.componentCertificateOfFullCertificate hchecked

theorem componentCertificateOfFullCertificate_valid
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    {q : ℚ} {n : ℕ}
    (hchecked : mainSondowFullCertificateChecks q n) :
    BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
      BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
      (boundary.componentCertificateOfFullCertificate hchecked) :=
  boundary.source_interface.componentCertificateOfFullCertificate_valid hchecked

def sourceComponentsOfFullCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    {q : ℚ} {n : ℕ}
    (hchecked : mainSondowFullCertificateChecks q n) :
    MainSondowFullCertificateSourceComponents q n :=
  boundary.source_interface.sourceComponentsOfFullCertificate hchecked

def projectProofCodeCertificateAtOfFullCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    {q : ℚ} {n : ℕ}
    (hchecked : mainSondowFullCertificateChecks q n) :
    BoundedArithmeticLab.SondowProjectProofCodeCertificateAt
      boundary.source_interface.projectProofCodeCompilers n :=
  boundary.source_interface.projectProofCodeCertificateAtOfFullCertificate
    hchecked

noncomputable def component_fields_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2SondowComponentCertificateFields bounds :=
  boundary.source_interface.component_fields_of_rationality h_rat

noncomputable def component_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) : ℕ :=
  (boundary.component_fields_of_rationality h_rat).threshold

theorem product_exists_after_component_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : boundary.component_threshold_of_rationality h_rat ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.product n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.product n :=
  (boundary.component_fields_of_rationality h_rat).product_exists_after hn

theorem log_exists_after_component_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : boundary.component_threshold_of_rationality h_rat ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.logRelation n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.logRelation n :=
  (boundary.component_fields_of_rationality h_rat).log_exists_after hn

theorem decomposition_exists_after_component_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : boundary.component_threshold_of_rationality h_rat ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.decomposition n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.decomposition n :=
  (boundary.component_fields_of_rationality h_rat).decomposition_exists_after hn

theorem threePow_exists_after_component_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : boundary.component_threshold_of_rationality h_rat ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.threePow n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.threePow n :=
  (boundary.component_fields_of_rationality h_rat).threePow_exists_after hn

theorem payload_exists_after_component_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : boundary.component_threshold_of_rationality h_rat ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.payload n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.payload n :=
  (boundary.component_fields_of_rationality h_rat).payload_exists_after hn

noncomputable def public_construction_package_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2SondowAcceptedPublicConstructionPackage bounds :=
  boundary.source_interface.public_construction_package_of_reproof_payload_spec_rationality_and_root_convention
    boundary.payload_spec boundary.concrete_verification h_rat
    boundary.root_convention

noncomputable def verifier_closure_package_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2SondowAcceptedVerifierClosurePackage.{u} bounds :=
  boundary.source_interface.verifier_closure_package_of_reproof_payload_spec_rationality_kernel_checker_root_convention
    boundary.payload_spec boundary.concrete_verification h_rat
    boundary.kernel boundary.checker boundary.root_convention

noncomputable def accepted_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) : ℕ :=
  let pkg := boundary.verifier_closure_package_of_rationality h_rat
  pkg.public_construction.accepted_and_components.accepted_threshold

theorem root_accepted_after_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : boundary.accepted_threshold_of_rationality h_rat ≤ n) :
    _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  (boundary.verifier_closure_package_of_rationality h_rat).root_accepted_after
    hn

noncomputable def audit_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) : ℕ :=
  max (boundary.accepted_threshold_of_rationality h_rat)
    (boundary.component_threshold_of_rationality h_rat)

theorem accepted_after_audit_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : boundary.audit_threshold_of_rationality h_rat ≤ n) :
    Month2SondowAccepted n :=
  (boundary.verifier_closure_package_of_rationality h_rat).accepted_after
    (Nat.le_trans (Nat.le_max_left _ _) hn)

theorem root_accepted_after_audit_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : boundary.audit_threshold_of_rationality h_rat ≤ n) :
    _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  boundary.root_accepted_after_of_rationality h_rat
    (Nat.le_trans (Nat.le_max_left _ _) hn)

theorem product_exists_after_audit_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : boundary.audit_threshold_of_rationality h_rat ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.product n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.product n :=
  boundary.product_exists_after_component_threshold_of_rationality h_rat
    (Nat.le_trans (Nat.le_max_right _ _) hn)

theorem log_exists_after_audit_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : boundary.audit_threshold_of_rationality h_rat ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.logRelation n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.logRelation n :=
  boundary.log_exists_after_component_threshold_of_rationality h_rat
    (Nat.le_trans (Nat.le_max_right _ _) hn)

theorem decomposition_exists_after_audit_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : boundary.audit_threshold_of_rationality h_rat ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.decomposition n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.decomposition n :=
  boundary.decomposition_exists_after_component_threshold_of_rationality h_rat
    (Nat.le_trans (Nat.le_max_right _ _) hn)

theorem threePow_exists_after_audit_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : boundary.audit_threshold_of_rationality h_rat ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.threePow n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.threePow n :=
  boundary.threePow_exists_after_component_threshold_of_rationality h_rat
    (Nat.le_trans (Nat.le_max_right _ _) hn)

theorem payload_exists_after_audit_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : boundary.audit_threshold_of_rationality h_rat ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.payload n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.payload n :=
  boundary.payload_exists_after_component_threshold_of_rationality h_rat
    (Nat.le_trans (Nat.le_max_right _ _) hn)

theorem collapse_conclusion_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    SondowProjectLocalS21CollapseConclusion :=
  (boundary.verifier_closure_package_of_rationality h_rat)
    |>.collapse_conclusion

end Month2SondowAcceptedAuditorBoundary

structure Month2SondowAcceptedAuditThresholdPackage
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  boundary : Month2SondowAcceptedAuditorBoundary.{u} bounds
  rationality : _root_.is_rational _root_.euler_mascheroni

namespace Month2SondowAcceptedAuditThresholdPackage

noncomputable def audit_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds) : ℕ :=
  pkg.boundary.audit_threshold_of_rationality pkg.rationality

theorem accepted_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds)
    {n : ℕ} (hn : pkg.audit_threshold ≤ n) :
    Month2SondowAccepted n :=
  pkg.boundary.accepted_after_audit_threshold_of_rationality
    pkg.rationality hn

theorem root_accepted_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds)
    {n : ℕ} (hn : pkg.audit_threshold ≤ n) :
    _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  pkg.boundary.root_accepted_after_audit_threshold_of_rationality
    pkg.rationality hn

theorem product_exists_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds)
    {n : ℕ} (hn : pkg.audit_threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.product n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.product n :=
  pkg.boundary.product_exists_after_audit_threshold_of_rationality
    pkg.rationality hn

theorem log_exists_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds)
    {n : ℕ} (hn : pkg.audit_threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.logRelation n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.logRelation n :=
  pkg.boundary.log_exists_after_audit_threshold_of_rationality
    pkg.rationality hn

theorem decomposition_exists_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds)
    {n : ℕ} (hn : pkg.audit_threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.decomposition n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.decomposition n :=
  pkg.boundary.decomposition_exists_after_audit_threshold_of_rationality
    pkg.rationality hn

theorem threePow_exists_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds)
    {n : ℕ} (hn : pkg.audit_threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.threePow n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.threePow n :=
  pkg.boundary.threePow_exists_after_audit_threshold_of_rationality
    pkg.rationality hn

theorem payload_exists_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds)
    {n : ℕ} (hn : pkg.audit_threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.payload n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.payload n :=
  pkg.boundary.payload_exists_after_audit_threshold_of_rationality
    pkg.rationality hn

theorem accepted_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  ⟨pkg.audit_threshold, fun _ hn => pkg.accepted_after hn⟩

theorem root_accepted_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  ⟨pkg.audit_threshold, fun _ hn => pkg.root_accepted_after hn⟩

noncomputable def component_eventual
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds) :
    SondowReflectionGraftSidecarComponentProofObjectExistsEventually
      bounds where
  threshold := pkg.audit_threshold
  product_exists := fun _ hn => pkg.product_exists_after hn
  log_exists := fun _ hn => pkg.log_exists_after hn
  decomposition_exists := fun _ hn => pkg.decomposition_exists_after hn
  threePow_exists := fun _ hn => pkg.threePow_exists_after hn
  payload_exists := fun _ hn => pkg.payload_exists_after hn

theorem component_eventual_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds) :
    Nonempty
      (SondowReflectionGraftSidecarComponentProofObjectExistsEventually
        bounds) :=
  ⟨pkg.component_eventual⟩

noncomputable def system_eventual
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds) :
    SondowReflectionGraftSidecarProofObjectSystemValidEventually
      bounds :=
  pkg.component_eventual.toSystemValidEventually

theorem system_eventual_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds) :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectSystemValidEventually
        bounds) :=
  ⟨pkg.system_eventual⟩

noncomputable def semantic_eventual
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds) :
    SondowReflectionGraftSidecarS21SemanticNonemptyEventually :=
  pkg.component_eventual.toSemanticNonemptyEventually

theorem semantic_eventual_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds) :
    Nonempty SondowReflectionGraftSidecarS21SemanticNonemptyEventually :=
  ⟨pkg.semantic_eventual⟩

theorem construction_layer
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds) :
    Month2SondowAcceptedCertificateConstructionLayer bounds where
  component_eventual := pkg.component_eventual_nonempty
  root_convention := pkg.boundary.root_convention

theorem sondow_accepted_of_root_accepted
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (_pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds)
    {n : ℕ}
    (hroot :
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)) :
    mainSondowAcceptedAt n :=
  _root_.accepted_sondow_certificate_of_reflection_graft hroot

theorem full_certificate_of_root_accepted
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds)
    {n : ℕ}
    (hroot :
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)) :
    ∃ q : ℚ, mainSondowFullCertificateChecks q n :=
  pkg.sondow_accepted_of_root_accepted hroot

theorem full_certificate_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds)
    {n : ℕ} (hn : pkg.audit_threshold ≤ n) :
    ∃ q : ℚ, mainSondowFullCertificateChecks q n :=
  pkg.full_certificate_of_root_accepted (pkg.root_accepted_after hn)

structure CompiledSourceCertificateAt
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds)
    (n : ℕ) where
  q : ℚ
  checked : mainSondowFullCertificateChecks q n
  certificate :
    BoundedArithmeticLab.SondowProjectProofCodeCertificateAt
      pkg.boundary.source_interface.projectProofCodeCompilers n

noncomputable def projectProofCodeCertificateAtAfter
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds)
    {n : ℕ} (hn : pkg.audit_threshold ≤ n) :
    CompiledSourceCertificateAt pkg n :=
  let hfull := pkg.full_certificate_after hn
  let q := Classical.choose hfull
  let hchecked := Classical.choose_spec hfull
  { q := q
    checked := hchecked
    certificate :=
      pkg.boundary.projectProofCodeCertificateAtOfFullCertificate
        hchecked }

theorem componentCertificateOfAcceptedAfter_valid
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds)
    {n : ℕ} (hn : pkg.audit_threshold ≤ n) :
    ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
      BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
        BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
        (pkg.boundary.componentCertificateOfFullCertificate hchecked) := by
  rcases pkg.full_certificate_after hn with ⟨q, hchecked⟩
  exact
    ⟨q, hchecked,
      pkg.boundary.componentCertificateOfFullCertificate_valid
        hchecked⟩

noncomputable def public_construction
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds) :
    Month2SondowAcceptedPublicConstructionPackage bounds :=
  pkg.boundary.public_construction_package_of_rationality pkg.rationality

noncomputable def verifier_closure
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds) :
    Month2SondowAcceptedVerifierClosurePackage.{u} bounds :=
  pkg.boundary.verifier_closure_package_of_rationality pkg.rationality

theorem collapse_conclusion
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (pkg : Month2SondowAcceptedAuditThresholdPackage.{u} bounds) :
    SondowProjectLocalS21CollapseConclusion :=
  pkg.boundary.collapse_conclusion_of_rationality pkg.rationality

end Month2SondowAcceptedAuditThresholdPackage

structure Month2SondowAcceptedExternalAnalyticInputs
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  rationality : _root_.is_rational _root_.euler_mascheroni
  payload_spec : _root_.PartialConsistencyPayloadSpec
  concrete_verification :
    _root_.ReflectionGraftConcreteVerificationPackage
  source_interface : Month2SondowSourceCompilerInterface bounds
  root_convention :
    Nonempty SondowReflectionGraftRootProofLengthConvention
  kernel :
    Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}
  checker :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
        bounds)

namespace Month2SondowAcceptedExternalAnalyticInputs

def boundary
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    Month2SondowAcceptedAuditorBoundary.{u} bounds where
  payload_spec := inputs.payload_spec
  concrete_verification := inputs.concrete_verification
  source_interface := inputs.source_interface
  root_convention := inputs.root_convention
  kernel := inputs.kernel
  checker := inputs.checker

def audit_package
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    Month2SondowAcceptedAuditThresholdPackage.{u} bounds where
  boundary := inputs.boundary
  rationality := inputs.rationality

theorem forward_inputs_closed_by_reproof
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    inputs.boundary.forward_reproof_boundary.forward_inputs =
      _root_.SondowForwardInputs.of_reproof :=
  inputs.boundary.forward_inputs_closed_by_reproof

theorem accepted_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  inputs.boundary.accepted_eventually_of_rationality
    inputs.rationality

noncomputable def component_fields
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    Month2SondowComponentCertificateFields bounds :=
  inputs.boundary.component_fields_of_rationality inputs.rationality

noncomputable def component_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    ℕ :=
  inputs.boundary.component_threshold_of_rationality inputs.rationality

noncomputable def audit_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    ℕ :=
  inputs.audit_package.audit_threshold

theorem accepted_after_audit_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds)
    {n : ℕ} (hn : inputs.audit_threshold ≤ n) :
    Month2SondowAccepted n :=
  inputs.audit_package.accepted_after hn

theorem root_accepted_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  inputs.audit_package.root_accepted_eventually

theorem full_certificate_checks_iff_source_components
    (_inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds)
    (q : ℚ) (n : ℕ) :
    mainSondowFullCertificateChecks q n ↔
      MainSondowFullCertificateSourceComponents q n :=
  mainSondowFullCertificateChecks_iff_sourceComponents q n

noncomputable def compiled_source_certificate_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds)
    {n : ℕ} (hn : inputs.audit_threshold ≤ n) :
    inputs.audit_package.CompiledSourceCertificateAt n :=
  inputs.audit_package.projectProofCodeCertificateAtAfter hn

theorem component_certificate_after_valid
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds)
    {n : ℕ} (hn : inputs.audit_threshold ≤ n) :
    ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
      BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
        BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
        (inputs.boundary.componentCertificateOfFullCertificate hchecked) :=
  inputs.audit_package.componentCertificateOfAcceptedAfter_valid hn

noncomputable def public_construction
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    Month2SondowAcceptedPublicConstructionPackage bounds :=
  inputs.audit_package.public_construction

noncomputable def verifier_closure
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    Month2SondowAcceptedVerifierClosurePackage.{u} bounds :=
  inputs.audit_package.verifier_closure

noncomputable def component_eventual
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    SondowReflectionGraftSidecarComponentProofObjectExistsEventually
      bounds :=
  inputs.audit_package.component_eventual

theorem component_eventual_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    Nonempty
      (SondowReflectionGraftSidecarComponentProofObjectExistsEventually
        bounds) :=
  inputs.audit_package.component_eventual_nonempty

theorem system_eventual_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectSystemValidEventually
        bounds) :=
  inputs.audit_package.system_eventual_nonempty

theorem semantic_eventual_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    Nonempty SondowReflectionGraftSidecarS21SemanticNonemptyEventually :=
  inputs.audit_package.semantic_eventual_nonempty

theorem collapse_conclusion
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    SondowProjectLocalS21CollapseConclusion :=
  inputs.audit_package.collapse_conclusion

end Month2SondowAcceptedExternalAnalyticInputs

structure Month2SondowAcceptedLeanClosedAnalyticSurface
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds
  audit_package : Month2SondowAcceptedAuditThresholdPackage.{u} bounds
  forward_inputs_closed_by_reproof :
    inputs.boundary.forward_reproof_boundary.forward_inputs =
      _root_.SondowForwardInputs.of_reproof
  accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n
  root_accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  component_eventual_nonempty :
    Nonempty
      (SondowReflectionGraftSidecarComponentProofObjectExistsEventually
        bounds)
  system_eventual_nonempty :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectSystemValidEventually
        bounds)
  semantic_eventual_nonempty :
    Nonempty SondowReflectionGraftSidecarS21SemanticNonemptyEventually
  public_construction :
    Month2SondowAcceptedPublicConstructionPackage bounds
  verifier_closure :
    Month2SondowAcceptedVerifierClosurePackage.{u} bounds
  collapse_conclusion :
    SondowProjectLocalS21CollapseConclusion

namespace Month2SondowAcceptedExternalAnalyticInputs

noncomputable def lean_closed_surface
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds where
  inputs := inputs
  audit_package := inputs.audit_package
  forward_inputs_closed_by_reproof :=
    inputs.forward_inputs_closed_by_reproof
  accepted_eventually := inputs.accepted_eventually
  root_accepted_eventually := inputs.root_accepted_eventually
  component_eventual_nonempty := inputs.component_eventual_nonempty
  system_eventual_nonempty := inputs.system_eventual_nonempty
  semantic_eventual_nonempty := inputs.semantic_eventual_nonempty
  public_construction := inputs.public_construction
  verifier_closure := inputs.verifier_closure
  collapse_conclusion := inputs.collapse_conclusion

end Month2SondowAcceptedExternalAnalyticInputs

namespace Month2SondowAcceptedLeanClosedAnalyticSurface

noncomputable def audit_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (surface : Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds) :
    ℕ :=
  surface.audit_package.audit_threshold

theorem accepted_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (surface : Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds)
    {n : ℕ} (hn : surface.audit_threshold ≤ n) :
    Month2SondowAccepted n :=
  surface.audit_package.accepted_after hn

theorem root_accepted_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (surface : Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds)
    {n : ℕ} (hn : surface.audit_threshold ≤ n) :
    _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  surface.audit_package.root_accepted_after hn

theorem full_certificate_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (surface : Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds)
    {n : ℕ} (hn : surface.audit_threshold ≤ n) :
    ∃ q : ℚ, mainSondowFullCertificateChecks q n :=
  surface.audit_package.full_certificate_after hn

noncomputable def compiled_source_certificate_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (surface : Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds)
    {n : ℕ} (hn : surface.audit_threshold ≤ n) :
    surface.audit_package.CompiledSourceCertificateAt n :=
  surface.audit_package.projectProofCodeCertificateAtAfter hn

theorem component_certificate_after_valid
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (surface : Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds)
    {n : ℕ} (hn : surface.audit_threshold ≤ n) :
    ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
      BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
        BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
        (surface.audit_package.boundary.componentCertificateOfFullCertificate
          hchecked) :=
  surface.audit_package.componentCertificateOfAcceptedAfter_valid hn

theorem product_exists_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (surface : Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds)
    {n : ℕ} (hn : surface.audit_threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.product n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.product n :=
  surface.audit_package.product_exists_after hn

theorem log_exists_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (surface : Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds)
    {n : ℕ} (hn : surface.audit_threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.logRelation n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.logRelation n :=
  surface.audit_package.log_exists_after hn

theorem decomposition_exists_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (surface : Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds)
    {n : ℕ} (hn : surface.audit_threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.decomposition n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.decomposition n :=
  surface.audit_package.decomposition_exists_after hn

theorem threePow_exists_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (surface : Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds)
    {n : ℕ} (hn : surface.audit_threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.threePow n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.threePow n :=
  surface.audit_package.threePow_exists_after hn

theorem payload_exists_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (surface : Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds)
    {n : ℕ} (hn : surface.audit_threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.payload n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.payload n :=
  surface.audit_package.payload_exists_after hn

theorem collapse_conclusion_from_audit
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (surface : Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds) :
    SondowProjectLocalS21CollapseConclusion :=
  surface.audit_package.collapse_conclusion

end Month2SondowAcceptedLeanClosedAnalyticSurface

structure Month2SondowAcceptedCompiledCertificateAt
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (surface : Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds)
    (n : ℕ) where
  accepted : Month2SondowAccepted n
  root_accepted :
    _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate :
    ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_source :
    surface.audit_package.CompiledSourceCertificateAt n
  component_certificate_valid :
    ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
      BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
        BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
        (surface.audit_package.boundary.componentCertificateOfFullCertificate
          hchecked)

namespace Month2SondowAcceptedCompiledCertificateAt

noncomputable def of_surface_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (surface : Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds)
    {n : ℕ} (hn : surface.audit_threshold ≤ n) :
    Month2SondowAcceptedCompiledCertificateAt surface n where
  accepted := surface.accepted_after hn
  root_accepted := surface.root_accepted_after hn
  full_certificate := surface.full_certificate_after hn
  compiled_source := surface.compiled_source_certificate_after hn
  component_certificate_valid :=
    surface.component_certificate_after_valid hn

end Month2SondowAcceptedCompiledCertificateAt

structure Month2SondowAcceptedPaperTheoremSurface
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  surface : Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds

namespace Month2SondowAcceptedPaperTheoremSurface

def inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (paper : Month2SondowAcceptedPaperTheoremSurface.{u} bounds) :
    Month2SondowAcceptedExternalAnalyticInputs.{u} bounds :=
  paper.surface.inputs

def audit_package
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (paper : Month2SondowAcceptedPaperTheoremSurface.{u} bounds) :
    Month2SondowAcceptedAuditThresholdPackage.{u} bounds :=
  paper.surface.audit_package

noncomputable def audit_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (paper : Month2SondowAcceptedPaperTheoremSurface.{u} bounds) :
    ℕ :=
  paper.surface.audit_threshold

theorem accepted_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (paper : Month2SondowAcceptedPaperTheoremSurface.{u} bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  paper.surface.accepted_eventually

theorem root_accepted_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (paper : Month2SondowAcceptedPaperTheoremSurface.{u} bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  paper.surface.root_accepted_eventually

theorem accepted_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (paper : Month2SondowAcceptedPaperTheoremSurface.{u} bounds)
    {n : ℕ} (hn : paper.audit_threshold ≤ n) :
    Month2SondowAccepted n :=
  paper.surface.accepted_after hn

theorem root_accepted_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (paper : Month2SondowAcceptedPaperTheoremSurface.{u} bounds)
    {n : ℕ} (hn : paper.audit_threshold ≤ n) :
    _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  paper.surface.root_accepted_after hn

theorem full_certificate_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (paper : Month2SondowAcceptedPaperTheoremSurface.{u} bounds)
    {n : ℕ} (hn : paper.audit_threshold ≤ n) :
    ∃ q : ℚ, mainSondowFullCertificateChecks q n :=
  paper.surface.full_certificate_after hn

noncomputable def compiled_certificate_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (paper : Month2SondowAcceptedPaperTheoremSurface.{u} bounds)
    {n : ℕ} (hn : paper.audit_threshold ≤ n) :
    Month2SondowAcceptedCompiledCertificateAt paper.surface n :=
  Month2SondowAcceptedCompiledCertificateAt.of_surface_after
    paper.surface hn

  theorem full_certificate_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (paper : Month2SondowAcceptedPaperTheoremSurface.{u} bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n :=
  ⟨paper.audit_threshold, fun _ hn => paper.full_certificate_after hn⟩

theorem compiled_certificate_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (paper : Month2SondowAcceptedPaperTheoremSurface.{u} bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty (Month2SondowAcceptedCompiledCertificateAt paper.surface n) :=
  ⟨paper.audit_threshold, fun _ hn =>
    ⟨paper.compiled_certificate_after hn⟩⟩

theorem full_certificate_checks_iff_source_components
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (paper : Month2SondowAcceptedPaperTheoremSurface.{u} bounds)
    (q : ℚ) (n : ℕ) :
    mainSondowFullCertificateChecks q n ↔
      MainSondowFullCertificateSourceComponents q n :=
  paper.inputs.full_certificate_checks_iff_source_components q n

theorem component_eventual_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (paper : Month2SondowAcceptedPaperTheoremSurface.{u} bounds) :
    Nonempty
      (SondowReflectionGraftSidecarComponentProofObjectExistsEventually
        bounds) :=
  paper.surface.component_eventual_nonempty

theorem system_eventual_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (paper : Month2SondowAcceptedPaperTheoremSurface.{u} bounds) :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectSystemValidEventually
        bounds) :=
  paper.surface.system_eventual_nonempty

theorem semantic_eventual_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (paper : Month2SondowAcceptedPaperTheoremSurface.{u} bounds) :
    Nonempty SondowReflectionGraftSidecarS21SemanticNonemptyEventually :=
  paper.surface.semantic_eventual_nonempty

theorem collapse_conclusion
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (paper : Month2SondowAcceptedPaperTheoremSurface.{u} bounds) :
    SondowProjectLocalS21CollapseConclusion :=
  paper.surface.collapse_conclusion

end Month2SondowAcceptedPaperTheoremSurface

namespace Month2SondowAcceptedExternalAnalyticInputs

noncomputable def paper_theorem_surface
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    Month2SondowAcceptedPaperTheoremSurface.{u} bounds where
  surface := inputs.lean_closed_surface

end Month2SondowAcceptedExternalAnalyticInputs

structure Month2SondowAcceptedProjectAuditChecklist
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds
  paper_surface : Month2SondowAcceptedPaperTheoremSurface.{u} bounds
  source_equivalence :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n
  root_accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  component_eventual_nonempty :
    Nonempty
      (SondowReflectionGraftSidecarComponentProofObjectExistsEventually
        bounds)
  system_eventual_nonempty :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectSystemValidEventually
        bounds)
  semantic_eventual_nonempty :
    Nonempty SondowReflectionGraftSidecarS21SemanticNonemptyEventually
  collapse_conclusion :
    SondowProjectLocalS21CollapseConclusion
  certificates_after :
    ∀ {n : ℕ}, paper_surface.audit_threshold ≤ n →
      Month2SondowAcceptedCompiledCertificateAt paper_surface.surface n

namespace Month2SondowAcceptedProjectAuditChecklist

noncomputable def of_external_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds) :
    Month2SondowAcceptedProjectAuditChecklist.{u} bounds where
  inputs := inputs
  paper_surface := inputs.paper_theorem_surface
  source_equivalence := fun q n =>
    inputs.full_certificate_checks_iff_source_components q n
  accepted_eventually := inputs.accepted_eventually
  root_accepted_eventually := inputs.root_accepted_eventually
  component_eventual_nonempty := inputs.component_eventual_nonempty
  system_eventual_nonempty := inputs.system_eventual_nonempty
  semantic_eventual_nonempty := inputs.semantic_eventual_nonempty
  collapse_conclusion := inputs.collapse_conclusion
  certificates_after := fun {_} hn =>
    inputs.paper_theorem_surface.compiled_certificate_after hn

noncomputable def audit_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (checklist : Month2SondowAcceptedProjectAuditChecklist.{u} bounds) :
    ℕ :=
  checklist.paper_surface.audit_threshold

theorem accepted_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (checklist : Month2SondowAcceptedProjectAuditChecklist.{u} bounds)
    {n : ℕ} (hn : checklist.audit_threshold ≤ n) :
    Month2SondowAccepted n :=
  (checklist.certificates_after hn).accepted

theorem root_accepted_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (checklist : Month2SondowAcceptedProjectAuditChecklist.{u} bounds)
    {n : ℕ} (hn : checklist.audit_threshold ≤ n) :
    _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  (checklist.certificates_after hn).root_accepted

theorem full_certificate_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (checklist : Month2SondowAcceptedProjectAuditChecklist.{u} bounds)
    {n : ℕ} (hn : checklist.audit_threshold ≤ n) :
    ∃ q : ℚ, mainSondowFullCertificateChecks q n :=
  (checklist.certificates_after hn).full_certificate

noncomputable def compiled_certificate_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (checklist : Month2SondowAcceptedProjectAuditChecklist.{u} bounds)
    {n : ℕ} (hn : checklist.audit_threshold ≤ n) :
    Month2SondowAcceptedCompiledCertificateAt
      checklist.paper_surface.surface n :=
  checklist.certificates_after hn

theorem full_certificate_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (checklist : Month2SondowAcceptedProjectAuditChecklist.{u} bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n :=
  ⟨checklist.audit_threshold, fun _ hn =>
    checklist.full_certificate_after hn⟩

theorem compiled_certificate_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (checklist : Month2SondowAcceptedProjectAuditChecklist.{u} bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          checklist.paper_surface.surface n) :=
  ⟨checklist.audit_threshold, fun _ hn =>
    ⟨checklist.compiled_certificate_after hn⟩⟩

theorem component_certificate_after_valid
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (checklist : Month2SondowAcceptedProjectAuditChecklist.{u} bounds)
    {n : ℕ} (hn : checklist.audit_threshold ≤ n) :
    ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
      BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
        BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
        (checklist.paper_surface.surface.audit_package.boundary
          |>.componentCertificateOfFullCertificate hchecked) :=
  (checklist.certificates_after hn).component_certificate_valid

end Month2SondowAcceptedProjectAuditChecklist

namespace Month2SondowAcceptedPublicRationalityTheorem

noncomputable def external_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (source_interface : Month2SondowSourceCompilerInterface bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds)) :
    Month2SondowAcceptedExternalAnalyticInputs.{u} bounds where
  rationality := h_rat
  payload_spec := hspec
  concrete_verification := hver
  source_interface := source_interface
  root_convention := hroot
  kernel := hkernel
  checker := hchecker

noncomputable def paper_surface
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (source_interface : Month2SondowSourceCompilerInterface bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds)) :
    Month2SondowAcceptedPaperTheoremSurface.{u} bounds :=
  (external_inputs h_rat hspec hver source_interface hroot hkernel hchecker)
    |>.paper_theorem_surface

noncomputable def audit_checklist
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (source_interface : Month2SondowSourceCompilerInterface bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds)) :
    Month2SondowAcceptedProjectAuditChecklist.{u} bounds :=
  Month2SondowAcceptedProjectAuditChecklist.of_external_inputs
    (external_inputs h_rat hspec hver source_interface hroot hkernel hchecker)

noncomputable def audit_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (source_interface : Month2SondowSourceCompilerInterface bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds)) :
    ℕ :=
  (audit_checklist h_rat hspec hver source_interface hroot hkernel hchecker)
    |>.audit_threshold

theorem accepted_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (source_interface : Month2SondowSourceCompilerInterface bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  (audit_checklist h_rat hspec hver source_interface hroot hkernel hchecker)
    |>.accepted_eventually

theorem root_accepted_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (source_interface : Month2SondowSourceCompilerInterface bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  (audit_checklist h_rat hspec hver source_interface hroot hkernel hchecker)
    |>.root_accepted_eventually

theorem source_equivalence
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (source_interface : Month2SondowSourceCompilerInterface bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (q : ℚ) (n : ℕ) :
    mainSondowFullCertificateChecks q n ↔
      MainSondowFullCertificateSourceComponents q n :=
  (audit_checklist h_rat hspec hver source_interface hroot hkernel hchecker)
    |>.source_equivalence q n

theorem accepted_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (source_interface : Month2SondowSourceCompilerInterface bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    {n : ℕ}
    (hn :
      audit_threshold h_rat hspec hver source_interface hroot hkernel
        hchecker ≤ n) :
    Month2SondowAccepted n :=
  (audit_checklist h_rat hspec hver source_interface hroot hkernel hchecker)
    |>.accepted_after hn

theorem full_certificate_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (source_interface : Month2SondowSourceCompilerInterface bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    {n : ℕ}
    (hn :
      audit_threshold h_rat hspec hver source_interface hroot hkernel
        hchecker ≤ n) :
    ∃ q : ℚ, mainSondowFullCertificateChecks q n :=
  (audit_checklist h_rat hspec hver source_interface hroot hkernel hchecker)
    |>.full_certificate_after hn

noncomputable def compiled_certificate_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (source_interface : Month2SondowSourceCompilerInterface bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    {n : ℕ}
    (hn :
      audit_threshold h_rat hspec hver source_interface hroot hkernel
        hchecker ≤ n) :
    Month2SondowAcceptedCompiledCertificateAt
      (paper_surface h_rat hspec hver source_interface hroot hkernel
        hchecker).surface n :=
  (audit_checklist h_rat hspec hver source_interface hroot hkernel hchecker)
    |>.compiled_certificate_after hn

theorem full_certificate_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (source_interface : Month2SondowSourceCompilerInterface bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n :=
  (audit_checklist h_rat hspec hver source_interface hroot hkernel hchecker)
    |>.full_certificate_eventually

theorem compiled_certificate_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (source_interface : Month2SondowSourceCompilerInterface bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          (paper_surface h_rat hspec hver source_interface hroot hkernel
            hchecker).surface n) :=
  (audit_checklist h_rat hspec hver source_interface hroot hkernel hchecker)
    |>.compiled_certificate_eventually

theorem component_certificate_after_valid
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (source_interface : Month2SondowSourceCompilerInterface bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    {n : ℕ}
    (hn :
      audit_threshold h_rat hspec hver source_interface hroot hkernel
        hchecker ≤ n) :
    ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
      BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
        BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
        ((paper_surface h_rat hspec hver source_interface hroot hkernel
          hchecker).surface.audit_package.boundary
          |>.componentCertificateOfFullCertificate hchecked) :=
  (audit_checklist h_rat hspec hver source_interface hroot hkernel hchecker)
    |>.component_certificate_after_valid hn

def source_interface_of_compilers
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compilers : MainSondowFullCertificateSourceComponentCompilers bounds) :
    Month2SondowSourceCompilerInterface bounds where
  compilers := compilers

noncomputable def audit_checklist_of_compilers
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (compilers : MainSondowFullCertificateSourceComponentCompilers bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds)) :
    Month2SondowAcceptedProjectAuditChecklist.{u} bounds :=
  audit_checklist h_rat hspec hver
    (source_interface_of_compilers compilers) hroot hkernel hchecker

noncomputable def audit_threshold_of_compilers
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (compilers : MainSondowFullCertificateSourceComponentCompilers bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds)) :
    ℕ :=
  (audit_checklist_of_compilers h_rat hspec hver compilers hroot hkernel
    hchecker).audit_threshold

theorem accepted_eventually_of_compilers
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (compilers : MainSondowFullCertificateSourceComponentCompilers bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  (audit_checklist_of_compilers h_rat hspec hver compilers hroot hkernel
    hchecker).accepted_eventually

theorem root_accepted_eventually_of_compilers
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (compilers : MainSondowFullCertificateSourceComponentCompilers bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  (audit_checklist_of_compilers h_rat hspec hver compilers hroot hkernel
    hchecker).root_accepted_eventually

theorem source_equivalence_of_compilers
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (compilers : MainSondowFullCertificateSourceComponentCompilers bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (q : ℚ) (n : ℕ) :
    mainSondowFullCertificateChecks q n ↔
      MainSondowFullCertificateSourceComponents q n :=
  (audit_checklist_of_compilers h_rat hspec hver compilers hroot hkernel
    hchecker).source_equivalence q n

theorem accepted_after_compiler_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (compilers : MainSondowFullCertificateSourceComponentCompilers bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    {n : ℕ}
    (hn :
      audit_threshold_of_compilers h_rat hspec hver compilers hroot hkernel
        hchecker ≤ n) :
    Month2SondowAccepted n :=
  (audit_checklist_of_compilers h_rat hspec hver compilers hroot hkernel
    hchecker).accepted_after hn

theorem root_accepted_after_compiler_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (compilers : MainSondowFullCertificateSourceComponentCompilers bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    {n : ℕ}
    (hn :
      audit_threshold_of_compilers h_rat hspec hver compilers hroot hkernel
        hchecker ≤ n) :
    _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  (audit_checklist_of_compilers h_rat hspec hver compilers hroot hkernel
    hchecker).root_accepted_after hn

theorem full_certificate_after_compiler_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (compilers : MainSondowFullCertificateSourceComponentCompilers bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    {n : ℕ}
    (hn :
      audit_threshold_of_compilers h_rat hspec hver compilers hroot hkernel
        hchecker ≤ n) :
    ∃ q : ℚ, mainSondowFullCertificateChecks q n :=
  (audit_checklist_of_compilers h_rat hspec hver compilers hroot hkernel
    hchecker).full_certificate_after hn

theorem full_certificate_eventually_of_compilers
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (compilers : MainSondowFullCertificateSourceComponentCompilers bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n :=
  (audit_checklist_of_compilers h_rat hspec hver compilers hroot hkernel
    hchecker).full_certificate_eventually

noncomputable def compiled_certificate_after_compiler_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (compilers : MainSondowFullCertificateSourceComponentCompilers bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    {n : ℕ}
    (hn :
      audit_threshold_of_compilers h_rat hspec hver compilers hroot hkernel
        hchecker ≤ n) :
    Month2SondowAcceptedCompiledCertificateAt
      ((paper_surface h_rat hspec hver
        (source_interface_of_compilers compilers) hroot hkernel hchecker)
        |>.surface)
      n :=
  (audit_checklist_of_compilers h_rat hspec hver compilers hroot hkernel
    hchecker).compiled_certificate_after hn

theorem compiled_certificate_eventually_of_compilers
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (compilers : MainSondowFullCertificateSourceComponentCompilers bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          ((paper_surface h_rat hspec hver
            (source_interface_of_compilers compilers) hroot hkernel hchecker)
            |>.surface)
          n) :=
  (audit_checklist_of_compilers h_rat hspec hver compilers hroot hkernel
    hchecker).compiled_certificate_eventually

theorem component_certificate_after_valid_compiler_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (hspec : _root_.PartialConsistencyPayloadSpec)
    (hver : _root_.ReflectionGraftConcreteVerificationPackage)
    (compilers : MainSondowFullCertificateSourceComponentCompilers bounds)
    (hroot : Nonempty SondowReflectionGraftRootProofLengthConvention)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    {n : ℕ}
    (hn :
      audit_threshold_of_compilers h_rat hspec hver compilers hroot hkernel
        hchecker ≤ n) :
    ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
      BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
        BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
        (((paper_surface h_rat hspec hver
          (source_interface_of_compilers compilers) hroot hkernel hchecker)
          |>.surface).audit_package.boundary
          |>.componentCertificateOfFullCertificate hchecked) :=
  (audit_checklist_of_compilers h_rat hspec hver compilers hroot hkernel
    hchecker).component_certificate_after_valid hn

structure PublicCompilerInputs
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  rationality : _root_.is_rational _root_.euler_mascheroni
  payload_spec : _root_.PartialConsistencyPayloadSpec
  concrete_verification :
    _root_.ReflectionGraftConcreteVerificationPackage
  compilers : MainSondowFullCertificateSourceComponentCompilers bounds
  root_convention :
    Nonempty SondowReflectionGraftRootProofLengthConvention
  kernel :
    Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}
  checker :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
        bounds)

namespace PublicCompilerInputs

def source_interface
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    Month2SondowSourceCompilerInterface bounds :=
  source_interface_of_compilers inputs.compilers

noncomputable def external_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    Month2SondowAcceptedExternalAnalyticInputs.{u} bounds :=
  Month2SondowAcceptedPublicRationalityTheorem.external_inputs
    inputs.rationality inputs.payload_spec inputs.concrete_verification
    inputs.source_interface inputs.root_convention inputs.kernel inputs.checker

noncomputable def paper_surface
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    Month2SondowAcceptedPaperTheoremSurface.{u} bounds :=
  inputs.external_inputs.paper_theorem_surface

noncomputable def audit_checklist
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    Month2SondowAcceptedProjectAuditChecklist.{u} bounds :=
  Month2SondowAcceptedProjectAuditChecklist.of_external_inputs
    inputs.external_inputs

theorem audit_checklist_eq_long_form
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    inputs.audit_checklist =
      audit_checklist_of_compilers
        inputs.rationality inputs.payload_spec inputs.concrete_verification
        inputs.compilers inputs.root_convention inputs.kernel
        inputs.checker :=
  rfl

noncomputable def audit_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    ℕ :=
  inputs.audit_checklist.audit_threshold

theorem audit_threshold_eq_long_form
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    inputs.audit_threshold =
      audit_threshold_of_compilers
        inputs.rationality inputs.payload_spec inputs.concrete_verification
        inputs.compilers inputs.root_convention inputs.kernel
        inputs.checker :=
  rfl

theorem accepted_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  inputs.audit_checklist.accepted_eventually

theorem root_accepted_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  inputs.audit_checklist.root_accepted_eventually

theorem source_equivalence
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds)
    (q : ℚ) (n : ℕ) :
    mainSondowFullCertificateChecks q n ↔
      MainSondowFullCertificateSourceComponents q n :=
  inputs.audit_checklist.source_equivalence q n

theorem accepted_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds)
    {n : ℕ} (hn : inputs.audit_threshold ≤ n) :
    Month2SondowAccepted n :=
  inputs.audit_checklist.accepted_after hn

theorem root_accepted_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds)
    {n : ℕ} (hn : inputs.audit_threshold ≤ n) :
    _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  inputs.audit_checklist.root_accepted_after hn

theorem full_certificate_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds)
    {n : ℕ} (hn : inputs.audit_threshold ≤ n) :
    ∃ q : ℚ, mainSondowFullCertificateChecks q n :=
  inputs.audit_checklist.full_certificate_after hn

noncomputable def compiled_certificate_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds)
    {n : ℕ} (hn : inputs.audit_threshold ≤ n) :
    Month2SondowAcceptedCompiledCertificateAt
      inputs.paper_surface.surface n :=
  inputs.audit_checklist.compiled_certificate_after hn

theorem full_certificate_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n :=
  inputs.audit_checklist.full_certificate_eventually

theorem compiled_certificate_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          inputs.paper_surface.surface n) :=
  inputs.audit_checklist.compiled_certificate_eventually

theorem component_certificate_after_valid
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds)
    {n : ℕ} (hn : inputs.audit_threshold ≤ n) :
    ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
      BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
        BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
        (inputs.paper_surface.surface.audit_package.boundary
          |>.componentCertificateOfFullCertificate hchecked) :=
  inputs.audit_checklist.component_certificate_after_valid hn

theorem collapse_conclusion
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    SondowProjectLocalS21CollapseConclusion :=
  inputs.paper_surface.collapse_conclusion

end PublicCompilerInputs

structure PaperReadyTheoremStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) : Prop where
  source_equivalence :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n
  root_accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          inputs.paper_surface.surface n)
  accepted_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n → Month2SondowAccepted n
  root_accepted_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          inputs.paper_surface.surface n)
  component_certificate_after_valid :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
        BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
          BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
          (inputs.paper_surface.surface.audit_package.boundary
            |>.componentCertificateOfFullCertificate hchecked)
  collapse_conclusion_nonempty :
    Nonempty SondowProjectLocalS21CollapseConclusion

structure PaperReadyTheoremPackage
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) where
  paper_surface : Month2SondowAcceptedPaperTheoremSurface.{u} bounds
  paper_surface_eq : paper_surface = inputs.paper_surface
  audit_checklist : Month2SondowAcceptedProjectAuditChecklist.{u} bounds
  audit_checklist_eq : audit_checklist = inputs.audit_checklist
  audit_threshold : ℕ
  audit_threshold_eq : audit_threshold = inputs.audit_threshold
  source_equivalence :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n
  root_accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          inputs.paper_surface.surface n)
  accepted_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n → Month2SondowAccepted n
  root_accepted_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      Month2SondowAcceptedCompiledCertificateAt
        inputs.paper_surface.surface n
  component_certificate_after_valid :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
        BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
          BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
          (inputs.paper_surface.surface.audit_package.boundary
            |>.componentCertificateOfFullCertificate hchecked)
  collapse_conclusion :
    SondowProjectLocalS21CollapseConclusion

namespace PaperReadyTheoremPackage

noncomputable def of_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    PaperReadyTheoremPackage inputs where
  paper_surface := inputs.paper_surface
  paper_surface_eq := rfl
  audit_checklist := inputs.audit_checklist
  audit_checklist_eq := rfl
  audit_threshold := inputs.audit_threshold
  audit_threshold_eq := rfl
  source_equivalence := inputs.source_equivalence
  accepted_eventually := inputs.accepted_eventually
  root_accepted_eventually := inputs.root_accepted_eventually
  full_certificate_eventually := inputs.full_certificate_eventually
  compiled_certificate_eventually := inputs.compiled_certificate_eventually
  accepted_after := fun hn => inputs.accepted_after hn
  root_accepted_after := fun hn => inputs.root_accepted_after hn
  full_certificate_after := fun hn => inputs.full_certificate_after hn
  compiled_certificate_after := fun hn => inputs.compiled_certificate_after hn
  component_certificate_after_valid := fun hn =>
    inputs.component_certificate_after_valid hn
  collapse_conclusion := inputs.collapse_conclusion

theorem audit_checklist_eq_long_form
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {inputs : PublicCompilerInputs.{u} bounds}
    (pkg : PaperReadyTheoremPackage inputs) :
    pkg.audit_checklist =
      audit_checklist_of_compilers
        inputs.rationality inputs.payload_spec inputs.concrete_verification
        inputs.compilers inputs.root_convention inputs.kernel
        inputs.checker :=
  calc
    pkg.audit_checklist = inputs.audit_checklist := pkg.audit_checklist_eq
    _ =
      audit_checklist_of_compilers
        inputs.rationality inputs.payload_spec inputs.concrete_verification
        inputs.compilers inputs.root_convention inputs.kernel
        inputs.checker := inputs.audit_checklist_eq_long_form

theorem audit_threshold_eq_long_form
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {inputs : PublicCompilerInputs.{u} bounds}
    (pkg : PaperReadyTheoremPackage inputs) :
    pkg.audit_threshold =
      audit_threshold_of_compilers
        inputs.rationality inputs.payload_spec inputs.concrete_verification
        inputs.compilers inputs.root_convention inputs.kernel
        inputs.checker :=
  calc
    pkg.audit_threshold = inputs.audit_threshold := pkg.audit_threshold_eq
    _ =
      audit_threshold_of_compilers
        inputs.rationality inputs.payload_spec inputs.concrete_verification
        inputs.compilers inputs.root_convention inputs.kernel
        inputs.checker := inputs.audit_threshold_eq_long_form

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    PaperReadyTheoremStatement inputs where
  source_equivalence := inputs.source_equivalence
  accepted_eventually := inputs.accepted_eventually
  root_accepted_eventually := inputs.root_accepted_eventually
  full_certificate_eventually := inputs.full_certificate_eventually
  compiled_certificate_eventually := inputs.compiled_certificate_eventually
  accepted_after := fun hn => inputs.accepted_after hn
  root_accepted_after := fun hn => inputs.root_accepted_after hn
  full_certificate_after := fun hn => inputs.full_certificate_after hn
  compiled_certificate_after := fun hn => ⟨inputs.compiled_certificate_after hn⟩
  component_certificate_after_valid := fun hn =>
    inputs.component_certificate_after_valid hn
  collapse_conclusion_nonempty := ⟨inputs.collapse_conclusion⟩

theorem statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    PaperReadyTheoremStatement inputs ↔
      Nonempty (PaperReadyTheoremPackage inputs) := by
  constructor
  · intro h
    classical
    rcases h.collapse_conclusion_nonempty with ⟨hcollapse⟩
    exact
      ⟨{ paper_surface := inputs.paper_surface
         paper_surface_eq := rfl
         audit_checklist := inputs.audit_checklist
         audit_checklist_eq := rfl
         audit_threshold := inputs.audit_threshold
         audit_threshold_eq := rfl
         source_equivalence := h.source_equivalence
         accepted_eventually := h.accepted_eventually
         root_accepted_eventually := h.root_accepted_eventually
         full_certificate_eventually := h.full_certificate_eventually
         compiled_certificate_eventually := h.compiled_certificate_eventually
         accepted_after := fun hn => h.accepted_after hn
         root_accepted_after := fun hn => h.root_accepted_after hn
         full_certificate_after := fun hn => h.full_certificate_after hn
         compiled_certificate_after := fun hn =>
           Classical.choice (h.compiled_certificate_after hn)
         component_certificate_after_valid := fun hn =>
           h.component_certificate_after_valid hn
         collapse_conclusion := hcollapse }⟩
  · rintro ⟨pkg⟩
    exact
      { source_equivalence := pkg.source_equivalence
        accepted_eventually := pkg.accepted_eventually
        root_accepted_eventually := pkg.root_accepted_eventually
        full_certificate_eventually := pkg.full_certificate_eventually
        compiled_certificate_eventually := pkg.compiled_certificate_eventually
        accepted_after := fun hn => pkg.accepted_after hn
        root_accepted_after := fun hn => pkg.root_accepted_after hn
        full_certificate_after := fun hn => pkg.full_certificate_after hn
        compiled_certificate_after := fun hn =>
          ⟨pkg.compiled_certificate_after hn⟩
        component_certificate_after_valid := fun hn =>
          pkg.component_certificate_after_valid hn
        collapse_conclusion_nonempty := ⟨pkg.collapse_conclusion⟩ }

theorem package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    Nonempty (PaperReadyTheoremPackage inputs) :=
  (statement_iff_package_nonempty inputs).1 (statement inputs)

end PaperReadyTheoremPackage

structure ExternalLeanClosedBoundaryStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) : Prop where
  external_inputs_eq_public :
    inputs.external_inputs =
      Month2SondowAcceptedPublicRationalityTheorem.external_inputs
        inputs.rationality inputs.payload_spec inputs.concrete_verification
        inputs.source_interface inputs.root_convention inputs.kernel
        inputs.checker
  forward_inputs_closed_by_reproof :
    inputs.external_inputs.boundary.forward_reproof_boundary.forward_inputs =
      _root_.SondowForwardInputs.of_reproof
  lean_closed_surface_eq_paper_surface :
    inputs.external_inputs.lean_closed_surface = inputs.paper_surface.surface
  paper_surface_eq_public :
    inputs.paper_surface = inputs.external_inputs.paper_theorem_surface
  audit_checklist_eq_public :
    inputs.audit_checklist =
      Month2SondowAcceptedProjectAuditChecklist.of_external_inputs
        inputs.external_inputs
  audit_threshold_eq_paper_surface :
    inputs.audit_threshold = inputs.paper_surface.audit_threshold
  paper_ready_statement :
    PaperReadyTheoremStatement inputs
  paper_ready_package_nonempty :
    Nonempty (PaperReadyTheoremPackage inputs)

structure ExternalLeanClosedBoundaryPackage
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) where
  external_inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds
  external_inputs_eq_public : external_inputs = inputs.external_inputs
  lean_closed_surface : Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds
  lean_closed_surface_eq_public :
    lean_closed_surface = inputs.external_inputs.lean_closed_surface
  paper_surface : Month2SondowAcceptedPaperTheoremSurface.{u} bounds
  paper_surface_eq_public : paper_surface = inputs.paper_surface
  audit_checklist : Month2SondowAcceptedProjectAuditChecklist.{u} bounds
  audit_checklist_eq_public : audit_checklist = inputs.audit_checklist
  audit_threshold : ℕ
  audit_threshold_eq_public : audit_threshold = inputs.audit_threshold
  paper_ready_package : PaperReadyTheoremPackage inputs
  statement_iff_paper_ready_package_nonempty :
    PaperReadyTheoremStatement inputs ↔
      Nonempty (PaperReadyTheoremPackage inputs)

namespace ExternalLeanClosedBoundaryPackage

noncomputable def of_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    ExternalLeanClosedBoundaryPackage inputs where
  external_inputs := inputs.external_inputs
  external_inputs_eq_public := rfl
  lean_closed_surface := inputs.external_inputs.lean_closed_surface
  lean_closed_surface_eq_public := rfl
  paper_surface := inputs.paper_surface
  paper_surface_eq_public := rfl
  audit_checklist := inputs.audit_checklist
  audit_checklist_eq_public := rfl
  audit_threshold := inputs.audit_threshold
  audit_threshold_eq_public := rfl
  paper_ready_package := PaperReadyTheoremPackage.of_inputs inputs
  statement_iff_paper_ready_package_nonempty :=
    PaperReadyTheoremPackage.statement_iff_package_nonempty inputs

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    ExternalLeanClosedBoundaryStatement inputs where
  external_inputs_eq_public := rfl
  forward_inputs_closed_by_reproof :=
    inputs.external_inputs.forward_inputs_closed_by_reproof
  lean_closed_surface_eq_paper_surface := rfl
  paper_surface_eq_public := rfl
  audit_checklist_eq_public := rfl
  audit_threshold_eq_paper_surface := rfl
  paper_ready_statement := PaperReadyTheoremPackage.statement inputs
  paper_ready_package_nonempty := PaperReadyTheoremPackage.package_nonempty inputs

theorem statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    ExternalLeanClosedBoundaryStatement inputs ↔
      Nonempty (ExternalLeanClosedBoundaryPackage inputs) := by
  constructor
  · intro _h
    exact ⟨of_inputs inputs⟩
  · intro _h
    exact statement inputs

theorem package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    Nonempty (ExternalLeanClosedBoundaryPackage inputs) :=
  (statement_iff_package_nonempty inputs).1 (statement inputs)

end ExternalLeanClosedBoundaryPackage

structure ExternalAnalyticAssumptionLedger
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  rationality : _root_.is_rational _root_.euler_mascheroni
  payload_spec : _root_.PartialConsistencyPayloadSpec
  concrete_verification :
    _root_.ReflectionGraftConcreteVerificationPackage
  compilers : MainSondowFullCertificateSourceComponentCompilers bounds
  root_convention :
    Nonempty SondowReflectionGraftRootProofLengthConvention
  kernel :
    Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}
  checker :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
        bounds)

namespace ExternalAnalyticAssumptionLedger

def to_public_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (ledger : ExternalAnalyticAssumptionLedger.{u} bounds) :
    PublicCompilerInputs.{u} bounds where
  rationality := ledger.rationality
  payload_spec := ledger.payload_spec
  concrete_verification := ledger.concrete_verification
  compilers := ledger.compilers
  root_convention := ledger.root_convention
  kernel := ledger.kernel
  checker := ledger.checker

end ExternalAnalyticAssumptionLedger

namespace PublicCompilerInputs

def assumption_ledger
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    ExternalAnalyticAssumptionLedger.{u} bounds where
  rationality := inputs.rationality
  payload_spec := inputs.payload_spec
  concrete_verification := inputs.concrete_verification
  compilers := inputs.compilers
  root_convention := inputs.root_convention
  kernel := inputs.kernel
  checker := inputs.checker

theorem assumption_ledger_to_public_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    inputs.assumption_ledger.to_public_inputs = inputs := by
  cases inputs
  rfl

end PublicCompilerInputs

structure NoHiddenAssumptionsStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) : Prop where
  assumption_ledger_roundtrip :
    inputs.assumption_ledger.to_public_inputs = inputs
  external_inputs_eq_from_ledger :
    (inputs.assumption_ledger.to_public_inputs).external_inputs =
      inputs.external_inputs
  audit_checklist_eq_long_form :
    inputs.audit_checklist =
      audit_checklist_of_compilers
        inputs.rationality inputs.payload_spec inputs.concrete_verification
        inputs.compilers inputs.root_convention inputs.kernel
        inputs.checker
  audit_threshold_eq_long_form :
    inputs.audit_threshold =
      audit_threshold_of_compilers
        inputs.rationality inputs.payload_spec inputs.concrete_verification
        inputs.compilers inputs.root_convention inputs.kernel
        inputs.checker
  same_lean_closed_surface :
    inputs.paper_surface.surface = inputs.external_inputs.lean_closed_surface
  same_audit_package :
    inputs.paper_surface.audit_package = inputs.external_inputs.audit_package
  boundary_statement :
    ExternalLeanClosedBoundaryStatement inputs
  paper_ready_statement :
    PaperReadyTheoremStatement inputs
  boundary_package_nonempty :
    Nonempty (ExternalLeanClosedBoundaryPackage inputs)
  paper_ready_package_nonempty :
    Nonempty (PaperReadyTheoremPackage inputs)

structure NoHiddenAssumptionsPackage
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) where
  ledger : ExternalAnalyticAssumptionLedger.{u} bounds
  ledger_eq_public : ledger = inputs.assumption_ledger
  public_inputs_eq : ledger.to_public_inputs = inputs
  boundary_package : ExternalLeanClosedBoundaryPackage inputs
  paper_ready_package : PaperReadyTheoremPackage inputs
  audit_checklist_eq_long_form :
    inputs.audit_checklist =
      audit_checklist_of_compilers
        inputs.rationality inputs.payload_spec inputs.concrete_verification
        inputs.compilers inputs.root_convention inputs.kernel
        inputs.checker
  audit_threshold_eq_long_form :
    inputs.audit_threshold =
      audit_threshold_of_compilers
        inputs.rationality inputs.payload_spec inputs.concrete_verification
        inputs.compilers inputs.root_convention inputs.kernel
        inputs.checker

namespace NoHiddenAssumptionsPackage

noncomputable def of_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    NoHiddenAssumptionsPackage inputs where
  ledger := inputs.assumption_ledger
  ledger_eq_public := rfl
  public_inputs_eq := inputs.assumption_ledger_to_public_inputs
  boundary_package := ExternalLeanClosedBoundaryPackage.of_inputs inputs
  paper_ready_package := PaperReadyTheoremPackage.of_inputs inputs
  audit_checklist_eq_long_form := inputs.audit_checklist_eq_long_form
  audit_threshold_eq_long_form := inputs.audit_threshold_eq_long_form

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    NoHiddenAssumptionsStatement inputs where
  assumption_ledger_roundtrip := inputs.assumption_ledger_to_public_inputs
  external_inputs_eq_from_ledger := by
    rw [inputs.assumption_ledger_to_public_inputs]
  audit_checklist_eq_long_form := inputs.audit_checklist_eq_long_form
  audit_threshold_eq_long_form := inputs.audit_threshold_eq_long_form
  same_lean_closed_surface := rfl
  same_audit_package := rfl
  boundary_statement := ExternalLeanClosedBoundaryPackage.statement inputs
  paper_ready_statement := PaperReadyTheoremPackage.statement inputs
  boundary_package_nonempty :=
    ExternalLeanClosedBoundaryPackage.package_nonempty inputs
  paper_ready_package_nonempty := PaperReadyTheoremPackage.package_nonempty inputs

theorem statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    NoHiddenAssumptionsStatement inputs ↔
      Nonempty (NoHiddenAssumptionsPackage inputs) := by
  constructor
  · intro _h
    exact ⟨of_inputs inputs⟩
  · intro _h
    exact statement inputs

theorem package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    Nonempty (NoHiddenAssumptionsPackage inputs) :=
  (statement_iff_package_nonempty inputs).1 (statement inputs)

end NoHiddenAssumptionsPackage

structure PublicInfrastructureKit
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  payload_spec : _root_.PartialConsistencyPayloadSpec
  concrete_verification :
    _root_.ReflectionGraftConcreteVerificationPackage
  compilers : MainSondowFullCertificateSourceComponentCompilers bounds
  root_convention :
    Nonempty SondowReflectionGraftRootProofLengthConvention
  kernel :
    Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}
  checker :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
        bounds)

namespace PublicInfrastructureKit

def with_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    PublicCompilerInputs.{u} bounds where
  rationality := h_rat
  payload_spec := kit.payload_spec
  concrete_verification := kit.concrete_verification
  compilers := kit.compilers
  root_convention := kit.root_convention
  kernel := kit.kernel
  checker := kit.checker

noncomputable def paper_ready_package_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    PaperReadyTheoremPackage (kit.with_rationality h_rat) :=
  PaperReadyTheoremPackage.of_inputs (kit.with_rationality h_rat)

theorem paper_ready_statement_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    PaperReadyTheoremStatement (kit.with_rationality h_rat) :=
  PaperReadyTheoremPackage.statement (kit.with_rationality h_rat)

theorem boundary_statement_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ExternalLeanClosedBoundaryStatement (kit.with_rationality h_rat) :=
  ExternalLeanClosedBoundaryPackage.statement (kit.with_rationality h_rat)

theorem no_hidden_assumptions_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    NoHiddenAssumptionsStatement (kit.with_rationality h_rat) :=
  NoHiddenAssumptionsPackage.statement (kit.with_rationality h_rat)

theorem no_hidden_assumptions_package_nonempty_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (NoHiddenAssumptionsPackage (kit.with_rationality h_rat)) :=
  NoHiddenAssumptionsPackage.package_nonempty (kit.with_rationality h_rat)

theorem source_equivalence_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (q : ℚ) (n : ℕ) :
    mainSondowFullCertificateChecks q n ↔
      MainSondowFullCertificateSourceComponents q n :=
  (kit.with_rationality h_rat).source_equivalence q n

theorem accepted_eventually_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  (kit.with_rationality h_rat).accepted_eventually

theorem root_accepted_eventually_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  (kit.with_rationality h_rat).root_accepted_eventually

theorem full_certificate_eventually_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n :=
  (kit.with_rationality h_rat).full_certificate_eventually

theorem compiled_certificate_eventually_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          (kit.with_rationality h_rat).paper_surface.surface n) :=
  (kit.with_rationality h_rat).compiled_certificate_eventually

theorem accepted_after_rationality_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    Month2SondowAccepted n :=
  (kit.with_rationality h_rat).accepted_after hn

theorem root_accepted_after_rationality_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  (kit.with_rationality h_rat).root_accepted_after hn

noncomputable def compiled_certificate_after_rationality_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    Month2SondowAcceptedCompiledCertificateAt
      (kit.with_rationality h_rat).paper_surface.surface n :=
  (kit.with_rationality h_rat).compiled_certificate_after hn

end PublicInfrastructureKit

structure ComponentConsumptionStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) : Prop where
  source_equivalence :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  full_certificate_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          inputs.paper_surface.surface n)
  component_certificate_after_valid :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
        BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
          BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
          (inputs.paper_surface.surface.audit_package.boundary
            |>.componentCertificateOfFullCertificate hchecked)
  component_eventual_nonempty :
    Nonempty
      (SondowReflectionGraftSidecarComponentProofObjectExistsEventually
        bounds)
  system_eventual_nonempty :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectSystemValidEventually
        bounds)
  semantic_eventual_nonempty :
    Nonempty SondowReflectionGraftSidecarS21SemanticNonemptyEventually
  audit_threshold_eq_paper_surface :
    inputs.audit_threshold = inputs.paper_surface.audit_threshold
  paper_ready_statement :
    PaperReadyTheoremStatement inputs
  no_hidden_assumptions_statement :
    NoHiddenAssumptionsStatement inputs

structure ComponentConsumptionPackage
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) where
  paper_ready_package : PaperReadyTheoremPackage inputs
  no_hidden_assumptions_package : NoHiddenAssumptionsPackage inputs
  source_equivalence :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  full_certificate_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      Month2SondowAcceptedCompiledCertificateAt
        inputs.paper_surface.surface n
  component_certificate_after_valid :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
        BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
          BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
          (inputs.paper_surface.surface.audit_package.boundary
            |>.componentCertificateOfFullCertificate hchecked)
  component_eventual_nonempty :
    Nonempty
      (SondowReflectionGraftSidecarComponentProofObjectExistsEventually
        bounds)
  system_eventual_nonempty :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectSystemValidEventually
        bounds)
  semantic_eventual_nonempty :
    Nonempty SondowReflectionGraftSidecarS21SemanticNonemptyEventually
  audit_threshold_eq_paper_surface :
    inputs.audit_threshold = inputs.paper_surface.audit_threshold

namespace ComponentConsumptionPackage

noncomputable def of_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    ComponentConsumptionPackage inputs where
  paper_ready_package := PaperReadyTheoremPackage.of_inputs inputs
  no_hidden_assumptions_package := NoHiddenAssumptionsPackage.of_inputs inputs
  source_equivalence := inputs.source_equivalence
  full_certificate_after := fun hn => inputs.full_certificate_after hn
  compiled_certificate_after := fun hn => inputs.compiled_certificate_after hn
  component_certificate_after_valid := fun hn =>
    inputs.component_certificate_after_valid hn
  component_eventual_nonempty :=
    inputs.audit_checklist.component_eventual_nonempty
  system_eventual_nonempty := inputs.audit_checklist.system_eventual_nonempty
  semantic_eventual_nonempty :=
    inputs.audit_checklist.semantic_eventual_nonempty
  audit_threshold_eq_paper_surface := rfl

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    ComponentConsumptionStatement inputs where
  source_equivalence := inputs.source_equivalence
  full_certificate_after := fun hn => inputs.full_certificate_after hn
  compiled_certificate_after := fun hn => ⟨inputs.compiled_certificate_after hn⟩
  component_certificate_after_valid := fun hn =>
    inputs.component_certificate_after_valid hn
  component_eventual_nonempty :=
    inputs.audit_checklist.component_eventual_nonempty
  system_eventual_nonempty := inputs.audit_checklist.system_eventual_nonempty
  semantic_eventual_nonempty :=
    inputs.audit_checklist.semantic_eventual_nonempty
  audit_threshold_eq_paper_surface := rfl
  paper_ready_statement := PaperReadyTheoremPackage.statement inputs
  no_hidden_assumptions_statement :=
    NoHiddenAssumptionsPackage.statement inputs

theorem statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    ComponentConsumptionStatement inputs ↔
      Nonempty (ComponentConsumptionPackage inputs) := by
  constructor
  · intro _h
    exact ⟨of_inputs inputs⟩
  · rintro ⟨pkg⟩
    exact
      { source_equivalence := pkg.source_equivalence
        full_certificate_after := fun hn => pkg.full_certificate_after hn
        compiled_certificate_after := fun hn =>
          ⟨pkg.compiled_certificate_after hn⟩
        component_certificate_after_valid := fun hn =>
          pkg.component_certificate_after_valid hn
        component_eventual_nonempty := pkg.component_eventual_nonempty
        system_eventual_nonempty := pkg.system_eventual_nonempty
        semantic_eventual_nonempty := pkg.semantic_eventual_nonempty
        audit_threshold_eq_paper_surface :=
          pkg.audit_threshold_eq_paper_surface
        paper_ready_statement :=
          PaperReadyTheoremPackage.statement inputs
        no_hidden_assumptions_statement :=
          NoHiddenAssumptionsPackage.statement inputs }

theorem package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    Nonempty (ComponentConsumptionPackage inputs) :=
  (statement_iff_package_nonempty inputs).1 (statement inputs)

end ComponentConsumptionPackage

namespace PublicInfrastructureKit

theorem component_consumption_statement_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ComponentConsumptionStatement (kit.with_rationality h_rat) :=
  ComponentConsumptionPackage.statement (kit.with_rationality h_rat)

theorem component_consumption_package_nonempty_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (ComponentConsumptionPackage (kit.with_rationality h_rat)) :=
  ComponentConsumptionPackage.package_nonempty (kit.with_rationality h_rat)

theorem component_certificate_after_valid_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
      BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
        BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
        ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
          |>.componentCertificateOfFullCertificate hchecked) :=
  (kit.with_rationality h_rat).component_certificate_after_valid hn

theorem component_eventual_nonempty_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty
      (SondowReflectionGraftSidecarComponentProofObjectExistsEventually
        bounds) :=
  (kit.with_rationality h_rat).audit_checklist.component_eventual_nonempty

end PublicInfrastructureKit

structure AnalyticBoundaryClassificationStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) : Prop where
  assumption_ledger_roundtrip :
    inputs.assumption_ledger.to_public_inputs = inputs
  external_inputs_from_ledger :
    (inputs.assumption_ledger.to_public_inputs).external_inputs =
      inputs.external_inputs
  external_forward_reproof_boundary :
    inputs.external_inputs.boundary.forward_reproof_boundary.forward_inputs =
      _root_.SondowForwardInputs.of_reproof
  external_to_lean_closed_surface :
    inputs.external_inputs.lean_closed_surface = inputs.paper_surface.surface
  accepted_eventually_lean_closed :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n
  root_accepted_eventually_lean_closed :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_eventually_lean_closed :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_eventually_lean_closed :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          inputs.paper_surface.surface n)
  component_eventual_nonempty_lean_closed :
    Nonempty
      (SondowReflectionGraftSidecarComponentProofObjectExistsEventually
        bounds)
  system_eventual_nonempty_lean_closed :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectSystemValidEventually
        bounds)
  semantic_eventual_nonempty_lean_closed :
    Nonempty SondowReflectionGraftSidecarS21SemanticNonemptyEventually
  component_consumption_statement :
    ComponentConsumptionStatement inputs
  no_hidden_assumptions_statement :
    NoHiddenAssumptionsStatement inputs
  paper_ready_statement :
    PaperReadyTheoremStatement inputs

structure AnalyticBoundaryClassificationPackage
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) where
  assumption_ledger : ExternalAnalyticAssumptionLedger.{u} bounds
  assumption_ledger_eq_public :
    assumption_ledger = inputs.assumption_ledger
  public_inputs_eq :
    assumption_ledger.to_public_inputs = inputs
  external_inputs : Month2SondowAcceptedExternalAnalyticInputs.{u} bounds
  external_inputs_eq_public : external_inputs = inputs.external_inputs
  lean_closed_surface : Month2SondowAcceptedLeanClosedAnalyticSurface.{u} bounds
  lean_closed_surface_eq_public :
    lean_closed_surface = inputs.paper_surface.surface
  component_consumption_package : ComponentConsumptionPackage inputs
  no_hidden_assumptions_package : NoHiddenAssumptionsPackage inputs
  paper_ready_package : PaperReadyTheoremPackage inputs
  accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n
  root_accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          inputs.paper_surface.surface n)

namespace AnalyticBoundaryClassificationPackage

noncomputable def of_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    AnalyticBoundaryClassificationPackage inputs where
  assumption_ledger := inputs.assumption_ledger
  assumption_ledger_eq_public := rfl
  public_inputs_eq := inputs.assumption_ledger_to_public_inputs
  external_inputs := inputs.external_inputs
  external_inputs_eq_public := rfl
  lean_closed_surface := inputs.paper_surface.surface
  lean_closed_surface_eq_public := rfl
  component_consumption_package :=
    ComponentConsumptionPackage.of_inputs inputs
  no_hidden_assumptions_package :=
    NoHiddenAssumptionsPackage.of_inputs inputs
  paper_ready_package := PaperReadyTheoremPackage.of_inputs inputs
  accepted_eventually := inputs.accepted_eventually
  root_accepted_eventually := inputs.root_accepted_eventually
  full_certificate_eventually := inputs.full_certificate_eventually
  compiled_certificate_eventually := inputs.compiled_certificate_eventually

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    AnalyticBoundaryClassificationStatement inputs where
  assumption_ledger_roundtrip := inputs.assumption_ledger_to_public_inputs
  external_inputs_from_ledger := by
    rw [inputs.assumption_ledger_to_public_inputs]
  external_forward_reproof_boundary :=
    inputs.external_inputs.forward_inputs_closed_by_reproof
  external_to_lean_closed_surface := rfl
  accepted_eventually_lean_closed := inputs.accepted_eventually
  root_accepted_eventually_lean_closed := inputs.root_accepted_eventually
  full_certificate_eventually_lean_closed := inputs.full_certificate_eventually
  compiled_certificate_eventually_lean_closed :=
    inputs.compiled_certificate_eventually
  component_eventual_nonempty_lean_closed :=
    inputs.audit_checklist.component_eventual_nonempty
  system_eventual_nonempty_lean_closed :=
    inputs.audit_checklist.system_eventual_nonempty
  semantic_eventual_nonempty_lean_closed :=
    inputs.audit_checklist.semantic_eventual_nonempty
  component_consumption_statement :=
    ComponentConsumptionPackage.statement inputs
  no_hidden_assumptions_statement :=
    NoHiddenAssumptionsPackage.statement inputs
  paper_ready_statement := PaperReadyTheoremPackage.statement inputs

theorem statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    AnalyticBoundaryClassificationStatement inputs ↔
      Nonempty (AnalyticBoundaryClassificationPackage inputs) := by
  constructor
  · intro _h
    exact ⟨of_inputs inputs⟩
  · intro _h
    exact statement inputs

theorem package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    Nonempty (AnalyticBoundaryClassificationPackage inputs) :=
  (statement_iff_package_nonempty inputs).1 (statement inputs)

end AnalyticBoundaryClassificationPackage

structure ComponentFamilyConsumptionStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) : Prop where
  audit_threshold_eq_paper_surface :
    inputs.audit_threshold = inputs.paper_surface.audit_threshold
  product_exists_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.product n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.product n
  log_exists_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.logRelation n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.logRelation n
  decomposition_exists_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.decomposition n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.decomposition n
  threePow_exists_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.threePow n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.threePow n
  payload_exists_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.payload n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.payload n
  component_consumption_statement :
    ComponentConsumptionStatement inputs
  analytic_boundary_classification_statement :
    AnalyticBoundaryClassificationStatement inputs

structure ComponentFamilyConsumptionPackage
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) where
  component_consumption_package : ComponentConsumptionPackage inputs
  analytic_boundary_classification_package :
    AnalyticBoundaryClassificationPackage inputs
  audit_threshold : ℕ
  audit_threshold_eq_public : audit_threshold = inputs.audit_threshold
  product_exists_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.product n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.product n
  log_exists_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.logRelation n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.logRelation n
  decomposition_exists_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.decomposition n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.decomposition n
  threePow_exists_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.threePow n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.threePow n
  payload_exists_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.payload n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.payload n

namespace ComponentFamilyConsumptionPackage

noncomputable def of_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    ComponentFamilyConsumptionPackage inputs where
  component_consumption_package :=
    ComponentConsumptionPackage.of_inputs inputs
  analytic_boundary_classification_package :=
    AnalyticBoundaryClassificationPackage.of_inputs inputs
  audit_threshold := inputs.audit_threshold
  audit_threshold_eq_public := rfl
  product_exists_after := fun hn =>
    inputs.paper_surface.surface.product_exists_after hn
  log_exists_after := fun hn =>
    inputs.paper_surface.surface.log_exists_after hn
  decomposition_exists_after := fun hn =>
    inputs.paper_surface.surface.decomposition_exists_after hn
  threePow_exists_after := fun hn =>
    inputs.paper_surface.surface.threePow_exists_after hn
  payload_exists_after := fun hn =>
    inputs.paper_surface.surface.payload_exists_after hn

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    ComponentFamilyConsumptionStatement inputs where
  audit_threshold_eq_paper_surface := rfl
  product_exists_after := fun hn =>
    inputs.paper_surface.surface.product_exists_after hn
  log_exists_after := fun hn =>
    inputs.paper_surface.surface.log_exists_after hn
  decomposition_exists_after := fun hn =>
    inputs.paper_surface.surface.decomposition_exists_after hn
  threePow_exists_after := fun hn =>
    inputs.paper_surface.surface.threePow_exists_after hn
  payload_exists_after := fun hn =>
    inputs.paper_surface.surface.payload_exists_after hn
  component_consumption_statement :=
    ComponentConsumptionPackage.statement inputs
  analytic_boundary_classification_statement :=
    AnalyticBoundaryClassificationPackage.statement inputs

theorem statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    ComponentFamilyConsumptionStatement inputs ↔
      Nonempty (ComponentFamilyConsumptionPackage inputs) := by
  constructor
  · intro _h
    exact ⟨of_inputs inputs⟩
  · rintro ⟨pkg⟩
    exact
      { audit_threshold_eq_paper_surface := rfl
        product_exists_after := fun hn => pkg.product_exists_after hn
        log_exists_after := fun hn => pkg.log_exists_after hn
        decomposition_exists_after := fun hn =>
          pkg.decomposition_exists_after hn
        threePow_exists_after := fun hn => pkg.threePow_exists_after hn
        payload_exists_after := fun hn => pkg.payload_exists_after hn
        component_consumption_statement :=
          ComponentConsumptionPackage.statement inputs
        analytic_boundary_classification_statement :=
          AnalyticBoundaryClassificationPackage.statement inputs }

theorem package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    Nonempty (ComponentFamilyConsumptionPackage inputs) :=
  (statement_iff_package_nonempty inputs).1 (statement inputs)

end ComponentFamilyConsumptionPackage

structure AcceptedCertificateCompilerSurfaceStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) : Prop where
  source_equivalence :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  accepted_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n → Month2SondowAccepted n
  root_accepted_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          inputs.paper_surface.surface n)
  component_certificate_after_valid :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
        BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
          BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
          (inputs.paper_surface.surface.audit_package.boundary
            |>.componentCertificateOfFullCertificate hchecked)
  component_family_consumption_statement :
    ComponentFamilyConsumptionStatement inputs
  component_consumption_statement :
    ComponentConsumptionStatement inputs
  paper_ready_statement :
    PaperReadyTheoremStatement inputs
  no_hidden_assumptions_statement :
    NoHiddenAssumptionsStatement inputs

structure AcceptedCertificateCompilerSurfacePackage
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) where
  paper_ready_package : PaperReadyTheoremPackage inputs
  component_consumption_package : ComponentConsumptionPackage inputs
  component_family_consumption_package :
    ComponentFamilyConsumptionPackage inputs
  no_hidden_assumptions_package : NoHiddenAssumptionsPackage inputs
  source_equivalence :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  accepted_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n → Month2SondowAccepted n
  root_accepted_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_after :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      Month2SondowAcceptedCompiledCertificateAt
        inputs.paper_surface.surface n
  component_certificate_after_valid :
    ∀ {n : ℕ}, inputs.audit_threshold ≤ n →
      ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
        BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
          BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
          (inputs.paper_surface.surface.audit_package.boundary
            |>.componentCertificateOfFullCertificate hchecked)

namespace AcceptedCertificateCompilerSurfacePackage

noncomputable def of_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    AcceptedCertificateCompilerSurfacePackage inputs where
  paper_ready_package := PaperReadyTheoremPackage.of_inputs inputs
  component_consumption_package :=
    ComponentConsumptionPackage.of_inputs inputs
  component_family_consumption_package :=
    ComponentFamilyConsumptionPackage.of_inputs inputs
  no_hidden_assumptions_package := NoHiddenAssumptionsPackage.of_inputs inputs
  source_equivalence := inputs.source_equivalence
  accepted_after := fun hn => inputs.accepted_after hn
  root_accepted_after := fun hn => inputs.root_accepted_after hn
  full_certificate_after := fun hn => inputs.full_certificate_after hn
  compiled_certificate_after := fun hn => inputs.compiled_certificate_after hn
  component_certificate_after_valid := fun hn =>
    inputs.component_certificate_after_valid hn

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    AcceptedCertificateCompilerSurfaceStatement inputs where
  source_equivalence := inputs.source_equivalence
  accepted_after := fun hn => inputs.accepted_after hn
  root_accepted_after := fun hn => inputs.root_accepted_after hn
  full_certificate_after := fun hn => inputs.full_certificate_after hn
  compiled_certificate_after := fun hn => ⟨inputs.compiled_certificate_after hn⟩
  component_certificate_after_valid := fun hn =>
    inputs.component_certificate_after_valid hn
  component_family_consumption_statement :=
    ComponentFamilyConsumptionPackage.statement inputs
  component_consumption_statement :=
    ComponentConsumptionPackage.statement inputs
  paper_ready_statement := PaperReadyTheoremPackage.statement inputs
  no_hidden_assumptions_statement :=
    NoHiddenAssumptionsPackage.statement inputs

theorem statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    AcceptedCertificateCompilerSurfaceStatement inputs ↔
      Nonempty (AcceptedCertificateCompilerSurfacePackage inputs) := by
  constructor
  · intro _h
    exact ⟨of_inputs inputs⟩
  · rintro ⟨pkg⟩
    exact
      { source_equivalence := pkg.source_equivalence
        accepted_after := fun hn => pkg.accepted_after hn
        root_accepted_after := fun hn => pkg.root_accepted_after hn
        full_certificate_after := fun hn => pkg.full_certificate_after hn
        compiled_certificate_after := fun hn =>
          ⟨pkg.compiled_certificate_after hn⟩
        component_certificate_after_valid := fun hn =>
          pkg.component_certificate_after_valid hn
        component_family_consumption_statement :=
          ComponentFamilyConsumptionPackage.statement inputs
        component_consumption_statement :=
          ComponentConsumptionPackage.statement inputs
        paper_ready_statement :=
          PaperReadyTheoremPackage.statement inputs
        no_hidden_assumptions_statement :=
          NoHiddenAssumptionsPackage.statement inputs }

theorem package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    Nonempty (AcceptedCertificateCompilerSurfacePackage inputs) :=
  (statement_iff_package_nonempty inputs).1 (statement inputs)

end AcceptedCertificateCompilerSurfacePackage

structure Month2PaperTheoremBundleStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) : Prop where
  audit_checklist_eq_long_form :
    inputs.audit_checklist =
      audit_checklist_of_compilers
        inputs.rationality inputs.payload_spec inputs.concrete_verification
        inputs.compilers inputs.root_convention inputs.kernel
        inputs.checker
  audit_threshold_eq_long_form :
    inputs.audit_threshold =
      audit_threshold_of_compilers
        inputs.rationality inputs.payload_spec inputs.concrete_verification
        inputs.compilers inputs.root_convention inputs.kernel
        inputs.checker
  source_equivalence :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n
  root_accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          inputs.paper_surface.surface n)
  no_hidden_assumptions_statement :
    NoHiddenAssumptionsStatement inputs
  analytic_boundary_classification_statement :
    AnalyticBoundaryClassificationStatement inputs
  component_consumption_statement :
    ComponentConsumptionStatement inputs
  component_family_consumption_statement :
    ComponentFamilyConsumptionStatement inputs
  accepted_certificate_compiler_surface_statement :
    AcceptedCertificateCompilerSurfaceStatement inputs
  paper_ready_statement :
    PaperReadyTheoremStatement inputs

structure Month2PaperTheoremBundlePackage
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) where
  no_hidden_assumptions_package : NoHiddenAssumptionsPackage inputs
  analytic_boundary_classification_package :
    AnalyticBoundaryClassificationPackage inputs
  component_consumption_package : ComponentConsumptionPackage inputs
  component_family_consumption_package :
    ComponentFamilyConsumptionPackage inputs
  accepted_certificate_compiler_surface_package :
    AcceptedCertificateCompilerSurfacePackage inputs
  paper_ready_package : PaperReadyTheoremPackage inputs
  audit_checklist_eq_long_form :
    inputs.audit_checklist =
      audit_checklist_of_compilers
        inputs.rationality inputs.payload_spec inputs.concrete_verification
        inputs.compilers inputs.root_convention inputs.kernel
        inputs.checker
  audit_threshold_eq_long_form :
    inputs.audit_threshold =
      audit_threshold_of_compilers
        inputs.rationality inputs.payload_spec inputs.concrete_verification
        inputs.compilers inputs.root_convention inputs.kernel
        inputs.checker
  source_equivalence :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n
  root_accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          inputs.paper_surface.surface n)

namespace Month2PaperTheoremBundlePackage

noncomputable def of_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    Month2PaperTheoremBundlePackage inputs where
  no_hidden_assumptions_package := NoHiddenAssumptionsPackage.of_inputs inputs
  analytic_boundary_classification_package :=
    AnalyticBoundaryClassificationPackage.of_inputs inputs
  component_consumption_package :=
    ComponentConsumptionPackage.of_inputs inputs
  component_family_consumption_package :=
    ComponentFamilyConsumptionPackage.of_inputs inputs
  accepted_certificate_compiler_surface_package :=
    AcceptedCertificateCompilerSurfacePackage.of_inputs inputs
  paper_ready_package := PaperReadyTheoremPackage.of_inputs inputs
  audit_checklist_eq_long_form := inputs.audit_checklist_eq_long_form
  audit_threshold_eq_long_form := inputs.audit_threshold_eq_long_form
  source_equivalence := inputs.source_equivalence
  accepted_eventually := inputs.accepted_eventually
  root_accepted_eventually := inputs.root_accepted_eventually
  full_certificate_eventually := inputs.full_certificate_eventually
  compiled_certificate_eventually := inputs.compiled_certificate_eventually

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    Month2PaperTheoremBundleStatement inputs where
  audit_checklist_eq_long_form := inputs.audit_checklist_eq_long_form
  audit_threshold_eq_long_form := inputs.audit_threshold_eq_long_form
  source_equivalence := inputs.source_equivalence
  accepted_eventually := inputs.accepted_eventually
  root_accepted_eventually := inputs.root_accepted_eventually
  full_certificate_eventually := inputs.full_certificate_eventually
  compiled_certificate_eventually := inputs.compiled_certificate_eventually
  no_hidden_assumptions_statement :=
    NoHiddenAssumptionsPackage.statement inputs
  analytic_boundary_classification_statement :=
    AnalyticBoundaryClassificationPackage.statement inputs
  component_consumption_statement :=
    ComponentConsumptionPackage.statement inputs
  component_family_consumption_statement :=
    ComponentFamilyConsumptionPackage.statement inputs
  accepted_certificate_compiler_surface_statement :=
    AcceptedCertificateCompilerSurfacePackage.statement inputs
  paper_ready_statement := PaperReadyTheoremPackage.statement inputs

theorem statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    Month2PaperTheoremBundleStatement inputs ↔
      Nonempty (Month2PaperTheoremBundlePackage inputs) := by
  constructor
  · intro _h
    exact ⟨of_inputs inputs⟩
  · rintro ⟨pkg⟩
    exact
      { audit_checklist_eq_long_form :=
          pkg.audit_checklist_eq_long_form
        audit_threshold_eq_long_form :=
          pkg.audit_threshold_eq_long_form
        source_equivalence := pkg.source_equivalence
        accepted_eventually := pkg.accepted_eventually
        root_accepted_eventually := pkg.root_accepted_eventually
        full_certificate_eventually := pkg.full_certificate_eventually
        compiled_certificate_eventually :=
          pkg.compiled_certificate_eventually
        no_hidden_assumptions_statement :=
          NoHiddenAssumptionsPackage.statement inputs
        analytic_boundary_classification_statement :=
          AnalyticBoundaryClassificationPackage.statement inputs
        component_consumption_statement :=
          ComponentConsumptionPackage.statement inputs
        component_family_consumption_statement :=
          ComponentFamilyConsumptionPackage.statement inputs
        accepted_certificate_compiler_surface_statement :=
          AcceptedCertificateCompilerSurfacePackage.statement inputs
        paper_ready_statement :=
          PaperReadyTheoremPackage.statement inputs }

theorem package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : PublicCompilerInputs.{u} bounds) :
    Nonempty (Month2PaperTheoremBundlePackage inputs) :=
  (statement_iff_package_nonempty inputs).1 (statement inputs)

end Month2PaperTheoremBundlePackage

structure Month2RationalityFinalPublicTheoremStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) : Prop where
  paper_bundle_statement :
    Month2PaperTheoremBundleStatement (kit.with_rationality h_rat)
  accepted_certificate_compiler_surface_statement :
    AcceptedCertificateCompilerSurfaceStatement (kit.with_rationality h_rat)
  component_family_consumption_statement :
    ComponentFamilyConsumptionStatement (kit.with_rationality h_rat)
  analytic_boundary_classification_statement :
    AnalyticBoundaryClassificationStatement (kit.with_rationality h_rat)
  no_hidden_assumptions_statement :
    NoHiddenAssumptionsStatement (kit.with_rationality h_rat)
  source_equivalence :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n
  root_accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          (kit.with_rationality h_rat).paper_surface.surface n)
  accepted_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      Month2SondowAccepted n
  root_accepted_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          (kit.with_rationality h_rat).paper_surface.surface n)
  component_certificate_after_valid_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
        BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
          BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
          ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
            |>.componentCertificateOfFullCertificate hchecked)

structure Month2RationalityFinalPublicTheoremPackage
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) where
  paper_bundle_package :
    Month2PaperTheoremBundlePackage (kit.with_rationality h_rat)
  accepted_certificate_compiler_surface_package :
    AcceptedCertificateCompilerSurfacePackage (kit.with_rationality h_rat)
  component_family_consumption_package :
    ComponentFamilyConsumptionPackage (kit.with_rationality h_rat)
  analytic_boundary_classification_package :
    AnalyticBoundaryClassificationPackage (kit.with_rationality h_rat)
  no_hidden_assumptions_package :
    NoHiddenAssumptionsPackage (kit.with_rationality h_rat)
  accepted_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      Month2SondowAccepted n
  root_accepted_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      Month2SondowAcceptedCompiledCertificateAt
        (kit.with_rationality h_rat).paper_surface.surface n
  component_certificate_after_valid_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
        BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
          BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
          ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
            |>.componentCertificateOfFullCertificate hchecked)

namespace Month2RationalityFinalPublicTheoremPackage

noncomputable def of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2RationalityFinalPublicTheoremPackage kit h_rat where
  paper_bundle_package :=
    Month2PaperTheoremBundlePackage.of_inputs (kit.with_rationality h_rat)
  accepted_certificate_compiler_surface_package :=
    AcceptedCertificateCompilerSurfacePackage.of_inputs
      (kit.with_rationality h_rat)
  component_family_consumption_package :=
    ComponentFamilyConsumptionPackage.of_inputs (kit.with_rationality h_rat)
  analytic_boundary_classification_package :=
    AnalyticBoundaryClassificationPackage.of_inputs
      (kit.with_rationality h_rat)
  no_hidden_assumptions_package :=
    NoHiddenAssumptionsPackage.of_inputs (kit.with_rationality h_rat)
  accepted_after_threshold := fun hn =>
    (kit.with_rationality h_rat).accepted_after hn
  root_accepted_after_threshold := fun hn =>
    (kit.with_rationality h_rat).root_accepted_after hn
  full_certificate_after_threshold := fun hn =>
    (kit.with_rationality h_rat).full_certificate_after hn
  compiled_certificate_after_threshold := fun hn =>
    (kit.with_rationality h_rat).compiled_certificate_after hn
  component_certificate_after_valid_threshold := fun hn =>
    (kit.with_rationality h_rat).component_certificate_after_valid hn

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2RationalityFinalPublicTheoremStatement kit h_rat where
  paper_bundle_statement :=
    Month2PaperTheoremBundlePackage.statement (kit.with_rationality h_rat)
  accepted_certificate_compiler_surface_statement :=
    AcceptedCertificateCompilerSurfacePackage.statement
      (kit.with_rationality h_rat)
  component_family_consumption_statement :=
    ComponentFamilyConsumptionPackage.statement (kit.with_rationality h_rat)
  analytic_boundary_classification_statement :=
    AnalyticBoundaryClassificationPackage.statement
      (kit.with_rationality h_rat)
  no_hidden_assumptions_statement :=
    NoHiddenAssumptionsPackage.statement (kit.with_rationality h_rat)
  source_equivalence :=
    (kit.with_rationality h_rat).source_equivalence
  accepted_eventually :=
    (kit.with_rationality h_rat).accepted_eventually
  root_accepted_eventually :=
    (kit.with_rationality h_rat).root_accepted_eventually
  full_certificate_eventually :=
    (kit.with_rationality h_rat).full_certificate_eventually
  compiled_certificate_eventually :=
    (kit.with_rationality h_rat).compiled_certificate_eventually
  accepted_after_threshold := fun hn =>
    (kit.with_rationality h_rat).accepted_after hn
  root_accepted_after_threshold := fun hn =>
    (kit.with_rationality h_rat).root_accepted_after hn
  full_certificate_after_threshold := fun hn =>
    (kit.with_rationality h_rat).full_certificate_after hn
  compiled_certificate_after_threshold := fun hn =>
    ⟨(kit.with_rationality h_rat).compiled_certificate_after hn⟩
  component_certificate_after_valid_threshold := fun hn =>
    (kit.with_rationality h_rat).component_certificate_after_valid hn

theorem statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2RationalityFinalPublicTheoremStatement kit h_rat ↔
      Nonempty (Month2RationalityFinalPublicTheoremPackage kit h_rat) := by
  constructor
  · intro _h
    exact ⟨of_rationality kit h_rat⟩
  · rintro ⟨pkg⟩
    exact
      { paper_bundle_statement :=
          Month2PaperTheoremBundlePackage.statement
            (kit.with_rationality h_rat)
        accepted_certificate_compiler_surface_statement :=
          AcceptedCertificateCompilerSurfacePackage.statement
            (kit.with_rationality h_rat)
        component_family_consumption_statement :=
          ComponentFamilyConsumptionPackage.statement
            (kit.with_rationality h_rat)
        analytic_boundary_classification_statement :=
          AnalyticBoundaryClassificationPackage.statement
            (kit.with_rationality h_rat)
        no_hidden_assumptions_statement :=
          NoHiddenAssumptionsPackage.statement
            (kit.with_rationality h_rat)
        source_equivalence :=
          (kit.with_rationality h_rat).source_equivalence
        accepted_eventually :=
          (kit.with_rationality h_rat).accepted_eventually
        root_accepted_eventually :=
          (kit.with_rationality h_rat).root_accepted_eventually
        full_certificate_eventually :=
          (kit.with_rationality h_rat).full_certificate_eventually
        compiled_certificate_eventually :=
          (kit.with_rationality h_rat).compiled_certificate_eventually
        accepted_after_threshold := fun hn =>
          pkg.accepted_after_threshold hn
        root_accepted_after_threshold := fun hn =>
          pkg.root_accepted_after_threshold hn
        full_certificate_after_threshold := fun hn =>
          pkg.full_certificate_after_threshold hn
        compiled_certificate_after_threshold := fun hn =>
          ⟨pkg.compiled_certificate_after_threshold hn⟩
        component_certificate_after_valid_threshold := fun hn =>
          pkg.component_certificate_after_valid_threshold hn }

theorem package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (Month2RationalityFinalPublicTheoremPackage kit h_rat) :=
  (statement_iff_package_nonempty kit h_rat).1 (statement kit h_rat)

end Month2RationalityFinalPublicTheoremPackage

structure Month2RationalityAuditorChecklistStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) : Prop where
  public_inputs_roundtrip :
    (kit.with_rationality h_rat).assumption_ledger.to_public_inputs =
      kit.with_rationality h_rat
  rationality_witness_eq :
    (kit.with_rationality h_rat).rationality = h_rat
  final_public_theorem_statement :
    Month2RationalityFinalPublicTheoremStatement kit h_rat
  final_public_theorem_package_nonempty :
    Nonempty (Month2RationalityFinalPublicTheoremPackage kit h_rat)
  final_statement_iff_package_nonempty :
    Month2RationalityFinalPublicTheoremStatement kit h_rat ↔
      Nonempty (Month2RationalityFinalPublicTheoremPackage kit h_rat)
  no_hidden_assumptions_statement :
    NoHiddenAssumptionsStatement (kit.with_rationality h_rat)
  accepted_certificate_compiler_surface_statement :
    AcceptedCertificateCompilerSurfaceStatement (kit.with_rationality h_rat)
  component_family_consumption_statement :
    ComponentFamilyConsumptionStatement (kit.with_rationality h_rat)
  paper_bundle_statement :
    Month2PaperTheoremBundleStatement (kit.with_rationality h_rat)
  source_equivalence_same_object :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  accepted_iff_root_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      Month2SondowAccepted n ∧
        _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  compiled_certificate_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          (kit.with_rationality h_rat).paper_surface.surface n)
  component_certificate_after_valid_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
        BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
          BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
          ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
            |>.componentCertificateOfFullCertificate hchecked)

structure Month2RationalityAuditorChecklistPackage
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) where
  public_inputs_roundtrip :
    (kit.with_rationality h_rat).assumption_ledger.to_public_inputs =
      kit.with_rationality h_rat
  rationality_witness_eq :
    (kit.with_rationality h_rat).rationality = h_rat
  final_public_theorem_package :
    Month2RationalityFinalPublicTheoremPackage kit h_rat
  no_hidden_assumptions_package :
    NoHiddenAssumptionsPackage (kit.with_rationality h_rat)
  accepted_certificate_compiler_surface_package :
    AcceptedCertificateCompilerSurfacePackage (kit.with_rationality h_rat)
  component_family_consumption_package :
    ComponentFamilyConsumptionPackage (kit.with_rationality h_rat)
  paper_bundle_package :
    Month2PaperTheoremBundlePackage (kit.with_rationality h_rat)

namespace Month2RationalityAuditorChecklistPackage

noncomputable def of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2RationalityAuditorChecklistPackage kit h_rat where
  public_inputs_roundtrip :=
    (kit.with_rationality h_rat).assumption_ledger_to_public_inputs
  rationality_witness_eq := rfl
  final_public_theorem_package :=
    Month2RationalityFinalPublicTheoremPackage.of_rationality kit h_rat
  no_hidden_assumptions_package :=
    NoHiddenAssumptionsPackage.of_inputs (kit.with_rationality h_rat)
  accepted_certificate_compiler_surface_package :=
    AcceptedCertificateCompilerSurfacePackage.of_inputs
      (kit.with_rationality h_rat)
  component_family_consumption_package :=
    ComponentFamilyConsumptionPackage.of_inputs (kit.with_rationality h_rat)
  paper_bundle_package :=
    Month2PaperTheoremBundlePackage.of_inputs (kit.with_rationality h_rat)

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2RationalityAuditorChecklistStatement kit h_rat where
  public_inputs_roundtrip :=
    (kit.with_rationality h_rat).assumption_ledger_to_public_inputs
  rationality_witness_eq := rfl
  final_public_theorem_statement :=
    Month2RationalityFinalPublicTheoremPackage.statement kit h_rat
  final_public_theorem_package_nonempty :=
    Month2RationalityFinalPublicTheoremPackage.package_nonempty kit h_rat
  final_statement_iff_package_nonempty :=
    Month2RationalityFinalPublicTheoremPackage.statement_iff_package_nonempty
      kit h_rat
  no_hidden_assumptions_statement :=
    NoHiddenAssumptionsPackage.statement (kit.with_rationality h_rat)
  accepted_certificate_compiler_surface_statement :=
    AcceptedCertificateCompilerSurfacePackage.statement
      (kit.with_rationality h_rat)
  component_family_consumption_statement :=
    ComponentFamilyConsumptionPackage.statement (kit.with_rationality h_rat)
  paper_bundle_statement :=
    Month2PaperTheoremBundlePackage.statement (kit.with_rationality h_rat)
  source_equivalence_same_object :=
    (kit.with_rationality h_rat).source_equivalence
  accepted_iff_root_after_threshold := fun hn =>
    ⟨(kit.with_rationality h_rat).accepted_after hn,
      (kit.with_rationality h_rat).root_accepted_after hn⟩
  compiled_certificate_after_threshold := fun hn =>
    ⟨(kit.with_rationality h_rat).compiled_certificate_after hn⟩
  component_certificate_after_valid_threshold := fun hn =>
    (kit.with_rationality h_rat).component_certificate_after_valid hn

theorem statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2RationalityAuditorChecklistStatement kit h_rat ↔
      Nonempty (Month2RationalityAuditorChecklistPackage kit h_rat) := by
  constructor
  · intro _h
    exact ⟨of_rationality kit h_rat⟩
  · intro _h
    exact statement kit h_rat

theorem package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (Month2RationalityAuditorChecklistPackage kit h_rat) :=
  (statement_iff_package_nonempty kit h_rat).1 (statement kit h_rat)

end Month2RationalityAuditorChecklistPackage

structure Month2PaperFacingAuditBoundaryStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) : Prop where
  public_inputs_roundtrip :
    (kit.with_rationality h_rat).assumption_ledger.to_public_inputs =
      kit.with_rationality h_rat
  audit_checklist_eq_long_form :
    (kit.with_rationality h_rat).audit_checklist =
      audit_checklist_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker
  audit_threshold_eq_long_form :
    (kit.with_rationality h_rat).audit_threshold =
      audit_threshold_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker
  same_lean_closed_surface :
    (kit.with_rationality h_rat).paper_surface.surface =
      (kit.with_rationality h_rat).external_inputs.lean_closed_surface
  same_audit_package :
    (kit.with_rationality h_rat).paper_surface.audit_package =
      (kit.with_rationality h_rat).external_inputs.audit_package
  paper_bundle_statement :
    Month2PaperTheoremBundleStatement (kit.with_rationality h_rat)
  paper_bundle_statement_iff_package_nonempty :
    Month2PaperTheoremBundleStatement (kit.with_rationality h_rat) ↔
      Nonempty
        (Month2PaperTheoremBundlePackage (kit.with_rationality h_rat))
  final_public_theorem_statement :
    Month2RationalityFinalPublicTheoremStatement kit h_rat
  final_public_theorem_statement_iff_package_nonempty :
    Month2RationalityFinalPublicTheoremStatement kit h_rat ↔
      Nonempty (Month2RationalityFinalPublicTheoremPackage kit h_rat)
  auditor_checklist_statement :
    Month2RationalityAuditorChecklistStatement kit h_rat
  auditor_checklist_statement_iff_package_nonempty :
    Month2RationalityAuditorChecklistStatement kit h_rat ↔
      Nonempty (Month2RationalityAuditorChecklistPackage kit h_rat)
  no_hidden_assumptions_statement :
    NoHiddenAssumptionsStatement (kit.with_rationality h_rat)
  accepted_root_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      Month2SondowAccepted n ∧
        _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  compiled_certificate_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          (kit.with_rationality h_rat).paper_surface.surface n)
  component_certificate_after_valid_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
        BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
          BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
          ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
            |>.componentCertificateOfFullCertificate hchecked)

structure Month2PaperFacingAuditBoundaryPackage
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) where
  public_inputs_roundtrip :
    (kit.with_rationality h_rat).assumption_ledger.to_public_inputs =
      kit.with_rationality h_rat
  audit_checklist_eq_long_form :
    (kit.with_rationality h_rat).audit_checklist =
      audit_checklist_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker
  audit_threshold_eq_long_form :
    (kit.with_rationality h_rat).audit_threshold =
      audit_threshold_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker
  paper_bundle_package :
    Month2PaperTheoremBundlePackage (kit.with_rationality h_rat)
  final_public_theorem_package :
    Month2RationalityFinalPublicTheoremPackage kit h_rat
  auditor_checklist_package :
    Month2RationalityAuditorChecklistPackage kit h_rat
  no_hidden_assumptions_package :
    NoHiddenAssumptionsPackage (kit.with_rationality h_rat)

namespace Month2PaperFacingAuditBoundaryPackage

noncomputable def of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2PaperFacingAuditBoundaryPackage kit h_rat where
  public_inputs_roundtrip :=
    (kit.with_rationality h_rat).assumption_ledger_to_public_inputs
  audit_checklist_eq_long_form :=
    (kit.with_rationality h_rat).audit_checklist_eq_long_form
  audit_threshold_eq_long_form :=
    (kit.with_rationality h_rat).audit_threshold_eq_long_form
  paper_bundle_package :=
    Month2PaperTheoremBundlePackage.of_inputs (kit.with_rationality h_rat)
  final_public_theorem_package :=
    Month2RationalityFinalPublicTheoremPackage.of_rationality kit h_rat
  auditor_checklist_package :=
    Month2RationalityAuditorChecklistPackage.of_rationality kit h_rat
  no_hidden_assumptions_package :=
    NoHiddenAssumptionsPackage.of_inputs (kit.with_rationality h_rat)

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2PaperFacingAuditBoundaryStatement kit h_rat where
  public_inputs_roundtrip :=
    (kit.with_rationality h_rat).assumption_ledger_to_public_inputs
  audit_checklist_eq_long_form :=
    (kit.with_rationality h_rat).audit_checklist_eq_long_form
  audit_threshold_eq_long_form :=
    (kit.with_rationality h_rat).audit_threshold_eq_long_form
  same_lean_closed_surface := rfl
  same_audit_package := rfl
  paper_bundle_statement :=
    Month2PaperTheoremBundlePackage.statement (kit.with_rationality h_rat)
  paper_bundle_statement_iff_package_nonempty :=
    Month2PaperTheoremBundlePackage.statement_iff_package_nonempty
      (kit.with_rationality h_rat)
  final_public_theorem_statement :=
    Month2RationalityFinalPublicTheoremPackage.statement kit h_rat
  final_public_theorem_statement_iff_package_nonempty :=
    Month2RationalityFinalPublicTheoremPackage.statement_iff_package_nonempty
      kit h_rat
  auditor_checklist_statement :=
    Month2RationalityAuditorChecklistPackage.statement kit h_rat
  auditor_checklist_statement_iff_package_nonempty :=
    Month2RationalityAuditorChecklistPackage.statement_iff_package_nonempty
      kit h_rat
  no_hidden_assumptions_statement :=
    NoHiddenAssumptionsPackage.statement (kit.with_rationality h_rat)
  accepted_root_after_threshold := fun hn =>
    ⟨(kit.with_rationality h_rat).accepted_after hn,
      (kit.with_rationality h_rat).root_accepted_after hn⟩
  compiled_certificate_after_threshold := fun hn =>
    ⟨(kit.with_rationality h_rat).compiled_certificate_after hn⟩
  component_certificate_after_valid_threshold := fun hn =>
    (kit.with_rationality h_rat).component_certificate_after_valid hn

theorem statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2PaperFacingAuditBoundaryStatement kit h_rat ↔
      Nonempty (Month2PaperFacingAuditBoundaryPackage kit h_rat) := by
  constructor
  · intro _h
    exact ⟨of_rationality kit h_rat⟩
  · rintro ⟨pkg⟩
    exact
      { public_inputs_roundtrip := pkg.public_inputs_roundtrip
        audit_checklist_eq_long_form := pkg.audit_checklist_eq_long_form
        audit_threshold_eq_long_form := pkg.audit_threshold_eq_long_form
        same_lean_closed_surface := rfl
        same_audit_package := rfl
        paper_bundle_statement :=
          Month2PaperTheoremBundlePackage.statement
            (kit.with_rationality h_rat)
        paper_bundle_statement_iff_package_nonempty :=
          Month2PaperTheoremBundlePackage.statement_iff_package_nonempty
            (kit.with_rationality h_rat)
        final_public_theorem_statement :=
          Month2RationalityFinalPublicTheoremPackage.statement kit h_rat
        final_public_theorem_statement_iff_package_nonempty :=
          Month2RationalityFinalPublicTheoremPackage.statement_iff_package_nonempty
            kit h_rat
        auditor_checklist_statement :=
          Month2RationalityAuditorChecklistPackage.statement kit h_rat
        auditor_checklist_statement_iff_package_nonempty :=
          Month2RationalityAuditorChecklistPackage.statement_iff_package_nonempty
            kit h_rat
        no_hidden_assumptions_statement :=
          NoHiddenAssumptionsPackage.statement (kit.with_rationality h_rat)
        accepted_root_after_threshold := fun hn =>
          ⟨(kit.with_rationality h_rat).accepted_after hn,
            (kit.with_rationality h_rat).root_accepted_after hn⟩
        compiled_certificate_after_threshold := fun hn =>
          ⟨(kit.with_rationality h_rat).compiled_certificate_after hn⟩
        component_certificate_after_valid_threshold := fun hn =>
          (kit.with_rationality h_rat).component_certificate_after_valid hn }

theorem audit_checklist_eq_long_form_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    (kit.with_rationality h_rat).audit_checklist =
      audit_checklist_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker :=
  (statement kit h_rat).audit_checklist_eq_long_form

theorem audit_threshold_eq_long_form_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    (kit.with_rationality h_rat).audit_threshold =
      audit_threshold_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker :=
  (statement kit h_rat).audit_threshold_eq_long_form

theorem paper_bundle_statement_iff_package_nonempty_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2PaperTheoremBundleStatement (kit.with_rationality h_rat) ↔
      Nonempty
        (Month2PaperTheoremBundlePackage (kit.with_rationality h_rat)) :=
  (statement kit h_rat).paper_bundle_statement_iff_package_nonempty

theorem final_public_theorem_statement_iff_package_nonempty_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2RationalityFinalPublicTheoremStatement kit h_rat ↔
      Nonempty (Month2RationalityFinalPublicTheoremPackage kit h_rat) :=
  (statement kit h_rat).final_public_theorem_statement_iff_package_nonempty

theorem auditor_checklist_statement_iff_package_nonempty_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2RationalityAuditorChecklistStatement kit h_rat ↔
      Nonempty (Month2RationalityAuditorChecklistPackage kit h_rat) :=
  (statement kit h_rat).auditor_checklist_statement_iff_package_nonempty

theorem package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (Month2PaperFacingAuditBoundaryPackage kit h_rat) :=
  (statement_iff_package_nonempty kit h_rat).1 (statement kit h_rat)

end Month2PaperFacingAuditBoundaryPackage

structure Month2CompilerConsumptionPaperSurfaceStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) : Prop where
  paper_facing_boundary_statement :
    Month2PaperFacingAuditBoundaryStatement kit h_rat
  paper_facing_boundary_statement_iff_package_nonempty :
    Month2PaperFacingAuditBoundaryStatement kit h_rat ↔
      Nonempty (Month2PaperFacingAuditBoundaryPackage kit h_rat)
  accepted_certificate_compiler_surface_statement :
    AcceptedCertificateCompilerSurfaceStatement (kit.with_rationality h_rat)
  accepted_certificate_compiler_surface_statement_iff_package_nonempty :
    AcceptedCertificateCompilerSurfaceStatement (kit.with_rationality h_rat) ↔
      Nonempty
        (AcceptedCertificateCompilerSurfacePackage
          (kit.with_rationality h_rat))
  source_equivalence_same_object :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  accepted_root_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      Month2SondowAccepted n ∧
        _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  source_components_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, MainSondowFullCertificateSourceComponents q n
  compiled_certificate_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          (kit.with_rationality h_rat).paper_surface.surface n)
  component_certificate_after_valid_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
        BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
          BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
          ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
            |>.componentCertificateOfFullCertificate hchecked)
  compiler_consumption_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
        (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
          Nonempty
            (Month2SondowAcceptedCompiledCertificateAt
              (kit.with_rationality h_rat).paper_surface.surface n) ∧
            ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
              BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
                BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
                ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
                  |>.componentCertificateOfFullCertificate hchecked)

structure Month2CompilerConsumptionPaperSurfacePackage
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) where
  paper_facing_boundary_package :
    Month2PaperFacingAuditBoundaryPackage kit h_rat
  accepted_certificate_compiler_surface_package :
    AcceptedCertificateCompilerSurfacePackage (kit.with_rationality h_rat)
  paper_facing_boundary_statement_iff_package_nonempty :
    Month2PaperFacingAuditBoundaryStatement kit h_rat ↔
      Nonempty (Month2PaperFacingAuditBoundaryPackage kit h_rat)
  accepted_certificate_compiler_surface_statement_iff_package_nonempty :
    AcceptedCertificateCompilerSurfaceStatement (kit.with_rationality h_rat) ↔
      Nonempty
        (AcceptedCertificateCompilerSurfacePackage
          (kit.with_rationality h_rat))
  source_equivalence_same_object :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  accepted_root_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      Month2SondowAccepted n ∧
        _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  source_components_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, MainSondowFullCertificateSourceComponents q n
  compiled_certificate_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      Month2SondowAcceptedCompiledCertificateAt
        (kit.with_rationality h_rat).paper_surface.surface n
  component_certificate_after_valid_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
        BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
          BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
          ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
            |>.componentCertificateOfFullCertificate hchecked)

namespace Month2CompilerConsumptionPaperSurfacePackage

noncomputable def of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2CompilerConsumptionPaperSurfacePackage kit h_rat where
  paper_facing_boundary_package :=
    Month2PaperFacingAuditBoundaryPackage.of_rationality kit h_rat
  accepted_certificate_compiler_surface_package :=
    AcceptedCertificateCompilerSurfacePackage.of_inputs
      (kit.with_rationality h_rat)
  paper_facing_boundary_statement_iff_package_nonempty :=
    Month2PaperFacingAuditBoundaryPackage.statement_iff_package_nonempty
      kit h_rat
  accepted_certificate_compiler_surface_statement_iff_package_nonempty :=
    AcceptedCertificateCompilerSurfacePackage.statement_iff_package_nonempty
      (kit.with_rationality h_rat)
  source_equivalence_same_object :=
    (kit.with_rationality h_rat).source_equivalence
  accepted_root_after_threshold := fun hn =>
    ⟨(kit.with_rationality h_rat).accepted_after hn,
      (kit.with_rationality h_rat).root_accepted_after hn⟩
  full_certificate_after_threshold := fun hn =>
    (kit.with_rationality h_rat).full_certificate_after hn
  source_components_after_threshold := fun {n} hn => by
    rcases (kit.with_rationality h_rat).full_certificate_after hn with
      ⟨q, hchecked⟩
    exact
      ⟨q, ((kit.with_rationality h_rat).source_equivalence q n).1
        hchecked⟩
  compiled_certificate_after_threshold := fun hn =>
    (kit.with_rationality h_rat).compiled_certificate_after hn
  component_certificate_after_valid_threshold := fun hn =>
    (kit.with_rationality h_rat).component_certificate_after_valid hn

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2CompilerConsumptionPaperSurfaceStatement kit h_rat where
  paper_facing_boundary_statement :=
    Month2PaperFacingAuditBoundaryPackage.statement kit h_rat
  paper_facing_boundary_statement_iff_package_nonempty :=
    Month2PaperFacingAuditBoundaryPackage.statement_iff_package_nonempty
      kit h_rat
  accepted_certificate_compiler_surface_statement :=
    AcceptedCertificateCompilerSurfacePackage.statement
      (kit.with_rationality h_rat)
  accepted_certificate_compiler_surface_statement_iff_package_nonempty :=
    AcceptedCertificateCompilerSurfacePackage.statement_iff_package_nonempty
      (kit.with_rationality h_rat)
  source_equivalence_same_object :=
    (kit.with_rationality h_rat).source_equivalence
  accepted_root_after_threshold := fun hn =>
    ⟨(kit.with_rationality h_rat).accepted_after hn,
      (kit.with_rationality h_rat).root_accepted_after hn⟩
  full_certificate_after_threshold := fun hn =>
    (kit.with_rationality h_rat).full_certificate_after hn
  source_components_after_threshold := fun {n} hn => by
    rcases (kit.with_rationality h_rat).full_certificate_after hn with
      ⟨q, hchecked⟩
    exact
      ⟨q, ((kit.with_rationality h_rat).source_equivalence q n).1
        hchecked⟩
  compiled_certificate_after_threshold := fun hn =>
    ⟨(kit.with_rationality h_rat).compiled_certificate_after hn⟩
  component_certificate_after_valid_threshold := fun hn =>
    (kit.with_rationality h_rat).component_certificate_after_valid hn
  compiler_consumption_after_threshold := fun {n} hn => by
    rcases (kit.with_rationality h_rat).full_certificate_after hn with
      ⟨q, hchecked⟩
    have hsource :
        MainSondowFullCertificateSourceComponents q n :=
      ((kit.with_rationality h_rat).source_equivalence q n).1 hchecked
    exact
      ⟨⟨q, hchecked⟩,
        ⟨⟨q, hsource⟩,
          ⟨⟨(kit.with_rationality h_rat).compiled_certificate_after hn⟩,
            (kit.with_rationality h_rat).component_certificate_after_valid hn⟩⟩⟩

theorem statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2CompilerConsumptionPaperSurfaceStatement kit h_rat ↔
      Nonempty (Month2CompilerConsumptionPaperSurfacePackage kit h_rat) := by
  constructor
  · intro h
    classical
    exact
      ⟨{ paper_facing_boundary_package :=
            Month2PaperFacingAuditBoundaryPackage.of_rationality kit h_rat
         accepted_certificate_compiler_surface_package :=
            AcceptedCertificateCompilerSurfacePackage.of_inputs
              (kit.with_rationality h_rat)
         paper_facing_boundary_statement_iff_package_nonempty :=
            h.paper_facing_boundary_statement_iff_package_nonempty
         accepted_certificate_compiler_surface_statement_iff_package_nonempty :=
            h.accepted_certificate_compiler_surface_statement_iff_package_nonempty
         source_equivalence_same_object :=
            h.source_equivalence_same_object
         accepted_root_after_threshold := fun hn =>
            h.accepted_root_after_threshold hn
         full_certificate_after_threshold := fun hn =>
            h.full_certificate_after_threshold hn
         source_components_after_threshold := fun hn =>
            h.source_components_after_threshold hn
         compiled_certificate_after_threshold := fun hn =>
            Classical.choice (h.compiled_certificate_after_threshold hn)
         component_certificate_after_valid_threshold := fun hn =>
            h.component_certificate_after_valid_threshold hn }⟩
  · rintro ⟨pkg⟩
    exact
      { paper_facing_boundary_statement :=
          Month2PaperFacingAuditBoundaryPackage.statement kit h_rat
        paper_facing_boundary_statement_iff_package_nonempty :=
          pkg.paper_facing_boundary_statement_iff_package_nonempty
        accepted_certificate_compiler_surface_statement :=
          AcceptedCertificateCompilerSurfacePackage.statement
            (kit.with_rationality h_rat)
        accepted_certificate_compiler_surface_statement_iff_package_nonempty :=
          pkg.accepted_certificate_compiler_surface_statement_iff_package_nonempty
        source_equivalence_same_object :=
          pkg.source_equivalence_same_object
        accepted_root_after_threshold := fun hn =>
          pkg.accepted_root_after_threshold hn
        full_certificate_after_threshold := fun hn =>
          pkg.full_certificate_after_threshold hn
        source_components_after_threshold := fun hn =>
          pkg.source_components_after_threshold hn
        compiled_certificate_after_threshold := fun hn =>
          ⟨pkg.compiled_certificate_after_threshold hn⟩
        component_certificate_after_valid_threshold := fun hn =>
          pkg.component_certificate_after_valid_threshold hn
        compiler_consumption_after_threshold := fun {n} hn => by
          rcases pkg.full_certificate_after_threshold hn with ⟨q, hchecked⟩
          rcases pkg.source_components_after_threshold hn with
            ⟨qsource, hsource⟩
          exact
            ⟨⟨q, hchecked⟩,
              ⟨⟨qsource, hsource⟩,
                ⟨⟨pkg.compiled_certificate_after_threshold hn⟩,
                  pkg.component_certificate_after_valid_threshold hn⟩⟩⟩ }

theorem package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (Month2CompilerConsumptionPaperSurfacePackage kit h_rat) :=
  (statement_iff_package_nonempty kit h_rat).1 (statement kit h_rat)

theorem source_components_after_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    ∃ q : ℚ, MainSondowFullCertificateSourceComponents q n :=
  (statement kit h_rat).source_components_after_threshold hn

noncomputable def compiled_certificate_after_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    Month2SondowAcceptedCompiledCertificateAt
      (kit.with_rationality h_rat).paper_surface.surface n :=
  (of_rationality kit h_rat).compiled_certificate_after_threshold hn

theorem component_certificate_after_valid_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
      BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
        BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
        ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
          |>.componentCertificateOfFullCertificate hchecked) :=
  (statement kit h_rat).component_certificate_after_valid_threshold hn

theorem compiler_consumption_after_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
      (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
        Nonempty
          (Month2SondowAcceptedCompiledCertificateAt
            (kit.with_rationality h_rat).paper_surface.surface n) ∧
          ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
            BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
              BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
              ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
                |>.componentCertificateOfFullCertificate hchecked) :=
  (statement kit h_rat).compiler_consumption_after_threshold hn

end Month2CompilerConsumptionPaperSurfacePackage

structure Month2AnalyticBoundaryPaperSurfaceStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) : Prop where
  external_lean_closed_boundary_statement :
    ExternalLeanClosedBoundaryStatement (kit.with_rationality h_rat)
  analytic_boundary_classification_statement :
    AnalyticBoundaryClassificationStatement (kit.with_rationality h_rat)
  no_hidden_assumptions_statement :
    NoHiddenAssumptionsStatement (kit.with_rationality h_rat)
  compiler_consumption_paper_surface_statement :
    Month2CompilerConsumptionPaperSurfaceStatement kit h_rat
  paper_facing_boundary_statement :
    Month2PaperFacingAuditBoundaryStatement kit h_rat
  external_boundary_statement_iff_package_nonempty :
    ExternalLeanClosedBoundaryStatement (kit.with_rationality h_rat) ↔
      Nonempty
        (ExternalLeanClosedBoundaryPackage (kit.with_rationality h_rat))
  analytic_boundary_statement_iff_package_nonempty :
    AnalyticBoundaryClassificationStatement (kit.with_rationality h_rat) ↔
      Nonempty
        (AnalyticBoundaryClassificationPackage (kit.with_rationality h_rat))
  no_hidden_assumptions_statement_iff_package_nonempty :
    NoHiddenAssumptionsStatement (kit.with_rationality h_rat) ↔
      Nonempty (NoHiddenAssumptionsPackage (kit.with_rationality h_rat))
  compiler_consumption_statement_iff_package_nonempty :
    Month2CompilerConsumptionPaperSurfaceStatement kit h_rat ↔
      Nonempty (Month2CompilerConsumptionPaperSurfacePackage kit h_rat)
  assumption_ledger_roundtrip :
    (kit.with_rationality h_rat).assumption_ledger.to_public_inputs =
      kit.with_rationality h_rat
  external_inputs_eq_public :
    (kit.with_rationality h_rat).external_inputs =
      Month2SondowAcceptedPublicRationalityTheorem.external_inputs
        h_rat kit.payload_spec kit.concrete_verification
        (kit.with_rationality h_rat).source_interface
        kit.root_convention kit.kernel kit.checker
  external_inputs_from_ledger :
    ((kit.with_rationality h_rat).assumption_ledger.to_public_inputs).external_inputs =
      (kit.with_rationality h_rat).external_inputs
  external_forward_reproof_boundary :
    (kit.with_rationality h_rat).external_inputs.boundary.forward_reproof_boundary.forward_inputs =
      _root_.SondowForwardInputs.of_reproof
  lean_closed_surface_eq_paper_surface :
    (kit.with_rationality h_rat).external_inputs.lean_closed_surface =
      (kit.with_rationality h_rat).paper_surface.surface
  paper_surface_eq_public :
    (kit.with_rationality h_rat).paper_surface =
      (kit.with_rationality h_rat).external_inputs.paper_theorem_surface
  audit_checklist_eq_public :
    (kit.with_rationality h_rat).audit_checklist =
      Month2SondowAcceptedProjectAuditChecklist.of_external_inputs
        (kit.with_rationality h_rat).external_inputs
  audit_threshold_eq_paper_surface :
    (kit.with_rationality h_rat).audit_threshold =
      (kit.with_rationality h_rat).paper_surface.audit_threshold
  accepted_eventually_lean_closed :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n
  root_accepted_eventually_lean_closed :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_eventually_lean_closed :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_eventually_lean_closed :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          (kit.with_rationality h_rat).paper_surface.surface n)
  component_eventual_nonempty_lean_closed :
    Nonempty
      (SondowReflectionGraftSidecarComponentProofObjectExistsEventually
        bounds)
  system_eventual_nonempty_lean_closed :
    Nonempty
      (SondowReflectionGraftSidecarProofObjectSystemValidEventually
        bounds)
  semantic_eventual_nonempty_lean_closed :
    Nonempty SondowReflectionGraftSidecarS21SemanticNonemptyEventually

structure Month2AnalyticBoundaryPaperSurfacePackage
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) where
  external_lean_closed_boundary_package :
    ExternalLeanClosedBoundaryPackage (kit.with_rationality h_rat)
  analytic_boundary_classification_package :
    AnalyticBoundaryClassificationPackage (kit.with_rationality h_rat)
  no_hidden_assumptions_package :
    NoHiddenAssumptionsPackage (kit.with_rationality h_rat)
  compiler_consumption_paper_surface_package :
    Month2CompilerConsumptionPaperSurfacePackage kit h_rat
  paper_facing_boundary_package :
    Month2PaperFacingAuditBoundaryPackage kit h_rat
  external_boundary_statement_iff_package_nonempty :
    ExternalLeanClosedBoundaryStatement (kit.with_rationality h_rat) ↔
      Nonempty
        (ExternalLeanClosedBoundaryPackage (kit.with_rationality h_rat))
  analytic_boundary_statement_iff_package_nonempty :
    AnalyticBoundaryClassificationStatement (kit.with_rationality h_rat) ↔
      Nonempty
        (AnalyticBoundaryClassificationPackage (kit.with_rationality h_rat))
  no_hidden_assumptions_statement_iff_package_nonempty :
    NoHiddenAssumptionsStatement (kit.with_rationality h_rat) ↔
      Nonempty (NoHiddenAssumptionsPackage (kit.with_rationality h_rat))

namespace Month2AnalyticBoundaryPaperSurfacePackage

noncomputable def of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2AnalyticBoundaryPaperSurfacePackage kit h_rat where
  external_lean_closed_boundary_package :=
    ExternalLeanClosedBoundaryPackage.of_inputs (kit.with_rationality h_rat)
  analytic_boundary_classification_package :=
    AnalyticBoundaryClassificationPackage.of_inputs (kit.with_rationality h_rat)
  no_hidden_assumptions_package :=
    NoHiddenAssumptionsPackage.of_inputs (kit.with_rationality h_rat)
  compiler_consumption_paper_surface_package :=
    Month2CompilerConsumptionPaperSurfacePackage.of_rationality kit h_rat
  paper_facing_boundary_package :=
    Month2PaperFacingAuditBoundaryPackage.of_rationality kit h_rat
  external_boundary_statement_iff_package_nonempty :=
    ExternalLeanClosedBoundaryPackage.statement_iff_package_nonempty
      (kit.with_rationality h_rat)
  analytic_boundary_statement_iff_package_nonempty :=
    AnalyticBoundaryClassificationPackage.statement_iff_package_nonempty
      (kit.with_rationality h_rat)
  no_hidden_assumptions_statement_iff_package_nonempty :=
    NoHiddenAssumptionsPackage.statement_iff_package_nonempty
      (kit.with_rationality h_rat)

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2AnalyticBoundaryPaperSurfaceStatement kit h_rat where
  external_lean_closed_boundary_statement :=
    ExternalLeanClosedBoundaryPackage.statement (kit.with_rationality h_rat)
  analytic_boundary_classification_statement :=
    AnalyticBoundaryClassificationPackage.statement
      (kit.with_rationality h_rat)
  no_hidden_assumptions_statement :=
    NoHiddenAssumptionsPackage.statement (kit.with_rationality h_rat)
  compiler_consumption_paper_surface_statement :=
    Month2CompilerConsumptionPaperSurfacePackage.statement kit h_rat
  paper_facing_boundary_statement :=
    Month2PaperFacingAuditBoundaryPackage.statement kit h_rat
  external_boundary_statement_iff_package_nonempty :=
    ExternalLeanClosedBoundaryPackage.statement_iff_package_nonempty
      (kit.with_rationality h_rat)
  analytic_boundary_statement_iff_package_nonempty :=
    AnalyticBoundaryClassificationPackage.statement_iff_package_nonempty
      (kit.with_rationality h_rat)
  no_hidden_assumptions_statement_iff_package_nonempty :=
    NoHiddenAssumptionsPackage.statement_iff_package_nonempty
      (kit.with_rationality h_rat)
  compiler_consumption_statement_iff_package_nonempty :=
    Month2CompilerConsumptionPaperSurfacePackage.statement_iff_package_nonempty
      kit h_rat
  assumption_ledger_roundtrip :=
    (kit.with_rationality h_rat).assumption_ledger_to_public_inputs
  external_inputs_eq_public := rfl
  external_inputs_from_ledger := by
    rw [(kit.with_rationality h_rat).assumption_ledger_to_public_inputs]
  external_forward_reproof_boundary :=
    (kit.with_rationality h_rat).external_inputs.forward_inputs_closed_by_reproof
  lean_closed_surface_eq_paper_surface := rfl
  paper_surface_eq_public := rfl
  audit_checklist_eq_public := rfl
  audit_threshold_eq_paper_surface := rfl
  accepted_eventually_lean_closed :=
    (kit.with_rationality h_rat).accepted_eventually
  root_accepted_eventually_lean_closed :=
    (kit.with_rationality h_rat).root_accepted_eventually
  full_certificate_eventually_lean_closed :=
    (kit.with_rationality h_rat).full_certificate_eventually
  compiled_certificate_eventually_lean_closed :=
    (kit.with_rationality h_rat).compiled_certificate_eventually
  component_eventual_nonempty_lean_closed :=
    (kit.with_rationality h_rat).audit_checklist.component_eventual_nonempty
  system_eventual_nonempty_lean_closed :=
    (kit.with_rationality h_rat).audit_checklist.system_eventual_nonempty
  semantic_eventual_nonempty_lean_closed :=
    (kit.with_rationality h_rat).audit_checklist.semantic_eventual_nonempty

theorem statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2AnalyticBoundaryPaperSurfaceStatement kit h_rat ↔
      Nonempty (Month2AnalyticBoundaryPaperSurfacePackage kit h_rat) := by
  constructor
  · intro _h
    exact ⟨of_rationality kit h_rat⟩
  · rintro ⟨pkg⟩
    exact
      { external_lean_closed_boundary_statement :=
          ExternalLeanClosedBoundaryPackage.statement
            (kit.with_rationality h_rat)
        analytic_boundary_classification_statement :=
          AnalyticBoundaryClassificationPackage.statement
            (kit.with_rationality h_rat)
        no_hidden_assumptions_statement :=
          NoHiddenAssumptionsPackage.statement (kit.with_rationality h_rat)
        compiler_consumption_paper_surface_statement :=
          Month2CompilerConsumptionPaperSurfacePackage.statement kit h_rat
        paper_facing_boundary_statement :=
          Month2PaperFacingAuditBoundaryPackage.statement kit h_rat
        external_boundary_statement_iff_package_nonempty :=
          pkg.external_boundary_statement_iff_package_nonempty
        analytic_boundary_statement_iff_package_nonempty :=
          pkg.analytic_boundary_statement_iff_package_nonempty
        no_hidden_assumptions_statement_iff_package_nonempty :=
          pkg.no_hidden_assumptions_statement_iff_package_nonempty
        compiler_consumption_statement_iff_package_nonempty :=
          Month2CompilerConsumptionPaperSurfacePackage.statement_iff_package_nonempty
            kit h_rat
        assumption_ledger_roundtrip :=
          (kit.with_rationality h_rat).assumption_ledger_to_public_inputs
        external_inputs_eq_public := rfl
        external_inputs_from_ledger := by
          rw [(kit.with_rationality h_rat).assumption_ledger_to_public_inputs]
        external_forward_reproof_boundary :=
          (kit.with_rationality h_rat).external_inputs.forward_inputs_closed_by_reproof
        lean_closed_surface_eq_paper_surface := rfl
        paper_surface_eq_public := rfl
        audit_checklist_eq_public := rfl
        audit_threshold_eq_paper_surface := rfl
        accepted_eventually_lean_closed :=
          (kit.with_rationality h_rat).accepted_eventually
        root_accepted_eventually_lean_closed :=
          (kit.with_rationality h_rat).root_accepted_eventually
        full_certificate_eventually_lean_closed :=
          (kit.with_rationality h_rat).full_certificate_eventually
        compiled_certificate_eventually_lean_closed :=
          (kit.with_rationality h_rat).compiled_certificate_eventually
        component_eventual_nonempty_lean_closed :=
          (kit.with_rationality h_rat).audit_checklist.component_eventual_nonempty
        system_eventual_nonempty_lean_closed :=
          (kit.with_rationality h_rat).audit_checklist.system_eventual_nonempty
        semantic_eventual_nonempty_lean_closed :=
          (kit.with_rationality h_rat).audit_checklist.semantic_eventual_nonempty }

theorem package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (Month2AnalyticBoundaryPaperSurfacePackage kit h_rat) :=
  (statement_iff_package_nonempty kit h_rat).1 (statement kit h_rat)

theorem lean_closed_surface_eq_paper_surface_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    (kit.with_rationality h_rat).external_inputs.lean_closed_surface =
      (kit.with_rationality h_rat).paper_surface.surface :=
  (statement kit h_rat).lean_closed_surface_eq_paper_surface

theorem external_forward_reproof_boundary_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    (kit.with_rationality h_rat).external_inputs.boundary.forward_reproof_boundary.forward_inputs =
      _root_.SondowForwardInputs.of_reproof :=
  (statement kit h_rat).external_forward_reproof_boundary

theorem compiled_certificate_eventually_lean_closed_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          (kit.with_rationality h_rat).paper_surface.surface n) :=
  (statement kit h_rat).compiled_certificate_eventually_lean_closed

end Month2AnalyticBoundaryPaperSurfacePackage

structure Month2AcceptedCertificateMasterTheoremStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) : Prop where
  final_public_theorem_statement :
    Month2RationalityFinalPublicTheoremStatement kit h_rat
  auditor_checklist_statement :
    Month2RationalityAuditorChecklistStatement kit h_rat
  paper_facing_audit_boundary_statement :
    Month2PaperFacingAuditBoundaryStatement kit h_rat
  compiler_consumption_paper_surface_statement :
    Month2CompilerConsumptionPaperSurfaceStatement kit h_rat
  analytic_boundary_paper_surface_statement :
    Month2AnalyticBoundaryPaperSurfaceStatement kit h_rat
  no_hidden_assumptions_statement :
    NoHiddenAssumptionsStatement (kit.with_rationality h_rat)
  final_public_theorem_statement_iff_package_nonempty :
    Month2RationalityFinalPublicTheoremStatement kit h_rat ↔
      Nonempty (Month2RationalityFinalPublicTheoremPackage kit h_rat)
  auditor_checklist_statement_iff_package_nonempty :
    Month2RationalityAuditorChecklistStatement kit h_rat ↔
      Nonempty (Month2RationalityAuditorChecklistPackage kit h_rat)
  paper_facing_audit_boundary_statement_iff_package_nonempty :
    Month2PaperFacingAuditBoundaryStatement kit h_rat ↔
      Nonempty (Month2PaperFacingAuditBoundaryPackage kit h_rat)
  compiler_consumption_paper_surface_statement_iff_package_nonempty :
    Month2CompilerConsumptionPaperSurfaceStatement kit h_rat ↔
      Nonempty (Month2CompilerConsumptionPaperSurfacePackage kit h_rat)
  analytic_boundary_paper_surface_statement_iff_package_nonempty :
    Month2AnalyticBoundaryPaperSurfaceStatement kit h_rat ↔
      Nonempty (Month2AnalyticBoundaryPaperSurfacePackage kit h_rat)
  source_equivalence_same_object :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  audit_checklist_eq_long_form :
    (kit.with_rationality h_rat).audit_checklist =
      audit_checklist_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker
  audit_threshold_eq_long_form :
    (kit.with_rationality h_rat).audit_threshold =
      audit_threshold_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker
  lean_closed_surface_eq_paper_surface :
    (kit.with_rationality h_rat).external_inputs.lean_closed_surface =
      (kit.with_rationality h_rat).paper_surface.surface
  external_forward_reproof_boundary :
    (kit.with_rationality h_rat).external_inputs.boundary.forward_reproof_boundary.forward_inputs =
      _root_.SondowForwardInputs.of_reproof
  accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n
  root_accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          (kit.with_rationality h_rat).paper_surface.surface n)
  accepted_root_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      Month2SondowAccepted n ∧
        _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  source_components_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, MainSondowFullCertificateSourceComponents q n
  compiled_certificate_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          (kit.with_rationality h_rat).paper_surface.surface n)
  component_certificate_after_valid_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
        BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
          BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
          ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
            |>.componentCertificateOfFullCertificate hchecked)
  compiler_consumption_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
        (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
          Nonempty
            (Month2SondowAcceptedCompiledCertificateAt
              (kit.with_rationality h_rat).paper_surface.surface n) ∧
            ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
              BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
                BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
                ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
                  |>.componentCertificateOfFullCertificate hchecked)

structure Month2AcceptedCertificateMasterTheoremPackage
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) where
  final_public_theorem_package :
    Month2RationalityFinalPublicTheoremPackage kit h_rat
  auditor_checklist_package :
    Month2RationalityAuditorChecklistPackage kit h_rat
  paper_facing_audit_boundary_package :
    Month2PaperFacingAuditBoundaryPackage kit h_rat
  compiler_consumption_paper_surface_package :
    Month2CompilerConsumptionPaperSurfacePackage kit h_rat
  analytic_boundary_paper_surface_package :
    Month2AnalyticBoundaryPaperSurfacePackage kit h_rat
  no_hidden_assumptions_package :
    NoHiddenAssumptionsPackage (kit.with_rationality h_rat)
  source_equivalence_same_object :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  audit_checklist_eq_long_form :
    (kit.with_rationality h_rat).audit_checklist =
      audit_checklist_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker
  audit_threshold_eq_long_form :
    (kit.with_rationality h_rat).audit_threshold =
      audit_threshold_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker
  lean_closed_surface_eq_paper_surface :
    (kit.with_rationality h_rat).external_inputs.lean_closed_surface =
      (kit.with_rationality h_rat).paper_surface.surface
  external_forward_reproof_boundary :
    (kit.with_rationality h_rat).external_inputs.boundary.forward_reproof_boundary.forward_inputs =
      _root_.SondowForwardInputs.of_reproof
  accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n
  root_accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          (kit.with_rationality h_rat).paper_surface.surface n)
  accepted_root_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      Month2SondowAccepted n ∧
        _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  source_components_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, MainSondowFullCertificateSourceComponents q n
  compiled_certificate_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      Month2SondowAcceptedCompiledCertificateAt
        (kit.with_rationality h_rat).paper_surface.surface n
  component_certificate_after_valid_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
        BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
          BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
          ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
            |>.componentCertificateOfFullCertificate hchecked)

namespace Month2AcceptedCertificateMasterTheoremPackage

noncomputable def of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2AcceptedCertificateMasterTheoremPackage kit h_rat where
  final_public_theorem_package :=
    Month2RationalityFinalPublicTheoremPackage.of_rationality kit h_rat
  auditor_checklist_package :=
    Month2RationalityAuditorChecklistPackage.of_rationality kit h_rat
  paper_facing_audit_boundary_package :=
    Month2PaperFacingAuditBoundaryPackage.of_rationality kit h_rat
  compiler_consumption_paper_surface_package :=
    Month2CompilerConsumptionPaperSurfacePackage.of_rationality kit h_rat
  analytic_boundary_paper_surface_package :=
    Month2AnalyticBoundaryPaperSurfacePackage.of_rationality kit h_rat
  no_hidden_assumptions_package :=
    NoHiddenAssumptionsPackage.of_inputs (kit.with_rationality h_rat)
  source_equivalence_same_object :=
    (kit.with_rationality h_rat).source_equivalence
  audit_checklist_eq_long_form :=
    (kit.with_rationality h_rat).audit_checklist_eq_long_form
  audit_threshold_eq_long_form :=
    (kit.with_rationality h_rat).audit_threshold_eq_long_form
  lean_closed_surface_eq_paper_surface := rfl
  external_forward_reproof_boundary :=
    (kit.with_rationality h_rat).external_inputs.forward_inputs_closed_by_reproof
  accepted_eventually :=
    (kit.with_rationality h_rat).accepted_eventually
  root_accepted_eventually :=
    (kit.with_rationality h_rat).root_accepted_eventually
  full_certificate_eventually :=
    (kit.with_rationality h_rat).full_certificate_eventually
  compiled_certificate_eventually :=
    (kit.with_rationality h_rat).compiled_certificate_eventually
  accepted_root_after_threshold := fun hn =>
    ⟨(kit.with_rationality h_rat).accepted_after hn,
      (kit.with_rationality h_rat).root_accepted_after hn⟩
  full_certificate_after_threshold := fun hn =>
    (kit.with_rationality h_rat).full_certificate_after hn
  source_components_after_threshold := fun {n} hn => by
    rcases (kit.with_rationality h_rat).full_certificate_after hn with
      ⟨q, hchecked⟩
    exact
      ⟨q, ((kit.with_rationality h_rat).source_equivalence q n).1
        hchecked⟩
  compiled_certificate_after_threshold := fun hn =>
    (kit.with_rationality h_rat).compiled_certificate_after hn
  component_certificate_after_valid_threshold := fun hn =>
    (kit.with_rationality h_rat).component_certificate_after_valid hn

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2AcceptedCertificateMasterTheoremStatement kit h_rat where
  final_public_theorem_statement :=
    Month2RationalityFinalPublicTheoremPackage.statement kit h_rat
  auditor_checklist_statement :=
    Month2RationalityAuditorChecklistPackage.statement kit h_rat
  paper_facing_audit_boundary_statement :=
    Month2PaperFacingAuditBoundaryPackage.statement kit h_rat
  compiler_consumption_paper_surface_statement :=
    Month2CompilerConsumptionPaperSurfacePackage.statement kit h_rat
  analytic_boundary_paper_surface_statement :=
    Month2AnalyticBoundaryPaperSurfacePackage.statement kit h_rat
  no_hidden_assumptions_statement :=
    NoHiddenAssumptionsPackage.statement (kit.with_rationality h_rat)
  final_public_theorem_statement_iff_package_nonempty :=
    Month2RationalityFinalPublicTheoremPackage.statement_iff_package_nonempty
      kit h_rat
  auditor_checklist_statement_iff_package_nonempty :=
    Month2RationalityAuditorChecklistPackage.statement_iff_package_nonempty
      kit h_rat
  paper_facing_audit_boundary_statement_iff_package_nonempty :=
    Month2PaperFacingAuditBoundaryPackage.statement_iff_package_nonempty
      kit h_rat
  compiler_consumption_paper_surface_statement_iff_package_nonempty :=
    Month2CompilerConsumptionPaperSurfacePackage.statement_iff_package_nonempty
      kit h_rat
  analytic_boundary_paper_surface_statement_iff_package_nonempty :=
    Month2AnalyticBoundaryPaperSurfacePackage.statement_iff_package_nonempty
      kit h_rat
  source_equivalence_same_object :=
    (kit.with_rationality h_rat).source_equivalence
  audit_checklist_eq_long_form :=
    (kit.with_rationality h_rat).audit_checklist_eq_long_form
  audit_threshold_eq_long_form :=
    (kit.with_rationality h_rat).audit_threshold_eq_long_form
  lean_closed_surface_eq_paper_surface := rfl
  external_forward_reproof_boundary :=
    (kit.with_rationality h_rat).external_inputs.forward_inputs_closed_by_reproof
  accepted_eventually :=
    (kit.with_rationality h_rat).accepted_eventually
  root_accepted_eventually :=
    (kit.with_rationality h_rat).root_accepted_eventually
  full_certificate_eventually :=
    (kit.with_rationality h_rat).full_certificate_eventually
  compiled_certificate_eventually :=
    (kit.with_rationality h_rat).compiled_certificate_eventually
  accepted_root_after_threshold := fun hn =>
    ⟨(kit.with_rationality h_rat).accepted_after hn,
      (kit.with_rationality h_rat).root_accepted_after hn⟩
  full_certificate_after_threshold := fun hn =>
    (kit.with_rationality h_rat).full_certificate_after hn
  source_components_after_threshold := fun {n} hn => by
    rcases (kit.with_rationality h_rat).full_certificate_after hn with
      ⟨q, hchecked⟩
    exact
      ⟨q, ((kit.with_rationality h_rat).source_equivalence q n).1
        hchecked⟩
  compiled_certificate_after_threshold := fun hn =>
    ⟨(kit.with_rationality h_rat).compiled_certificate_after hn⟩
  component_certificate_after_valid_threshold := fun hn =>
    (kit.with_rationality h_rat).component_certificate_after_valid hn
  compiler_consumption_after_threshold := fun hn =>
    Month2CompilerConsumptionPaperSurfacePackage.compiler_consumption_after_threshold_of_rationality
      kit h_rat hn

theorem statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2AcceptedCertificateMasterTheoremStatement kit h_rat ↔
      Nonempty (Month2AcceptedCertificateMasterTheoremPackage kit h_rat) := by
  constructor
  · intro _h
    exact ⟨of_rationality kit h_rat⟩
  · intro _h
    exact statement kit h_rat

theorem package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (Month2AcceptedCertificateMasterTheoremPackage kit h_rat) :=
  (statement_iff_package_nonempty kit h_rat).1 (statement kit h_rat)

theorem accepted_eventually_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  (statement kit h_rat).accepted_eventually

theorem root_accepted_eventually_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  (statement kit h_rat).root_accepted_eventually

noncomputable def compiled_certificate_after_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    Month2SondowAcceptedCompiledCertificateAt
      (kit.with_rationality h_rat).paper_surface.surface n :=
  (of_rationality kit h_rat).compiled_certificate_after_threshold hn

theorem compiler_consumption_after_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
      (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
        Nonempty
          (Month2SondowAcceptedCompiledCertificateAt
            (kit.with_rationality h_rat).paper_surface.surface n) ∧
          ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
            BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
              BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
              ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
                |>.componentCertificateOfFullCertificate hchecked) :=
  (statement kit h_rat).compiler_consumption_after_threshold hn

end Month2AcceptedCertificateMasterTheoremPackage

structure Month2OpenSourceReleaseSurfaceStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) : Prop where
  master_theorem_statement :
    Month2AcceptedCertificateMasterTheoremStatement kit h_rat
  master_theorem_statement_iff_package_nonempty :
    Month2AcceptedCertificateMasterTheoremStatement kit h_rat ↔
      Nonempty (Month2AcceptedCertificateMasterTheoremPackage kit h_rat)
  master_theorem_package_nonempty :
    Nonempty (Month2AcceptedCertificateMasterTheoremPackage kit h_rat)
  paper_ready_statement :
    PaperReadyTheoremStatement (kit.with_rationality h_rat)
  paper_ready_statement_iff_package_nonempty :
    PaperReadyTheoremStatement (kit.with_rationality h_rat) ↔
      Nonempty (PaperReadyTheoremPackage (kit.with_rationality h_rat))
  external_boundary_statement :
    ExternalLeanClosedBoundaryStatement (kit.with_rationality h_rat)
  external_boundary_statement_iff_package_nonempty :
    ExternalLeanClosedBoundaryStatement (kit.with_rationality h_rat) ↔
      Nonempty
        (ExternalLeanClosedBoundaryPackage (kit.with_rationality h_rat))
  no_hidden_assumptions_statement :
    NoHiddenAssumptionsStatement (kit.with_rationality h_rat)
  no_hidden_assumptions_statement_iff_package_nonempty :
    NoHiddenAssumptionsStatement (kit.with_rationality h_rat) ↔
      Nonempty (NoHiddenAssumptionsPackage (kit.with_rationality h_rat))
  accepted_certificate_compiler_surface_statement :
    AcceptedCertificateCompilerSurfaceStatement (kit.with_rationality h_rat)
  component_family_consumption_statement :
    ComponentFamilyConsumptionStatement (kit.with_rationality h_rat)
  source_equivalence_same_object :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  audit_checklist_eq_long_form :
    (kit.with_rationality h_rat).audit_checklist =
      audit_checklist_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker
  audit_threshold_eq_long_form :
    (kit.with_rationality h_rat).audit_threshold =
      audit_threshold_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker
  lean_closed_surface_eq_paper_surface :
    (kit.with_rationality h_rat).external_inputs.lean_closed_surface =
      (kit.with_rationality h_rat).paper_surface.surface
  external_forward_reproof_boundary :
    (kit.with_rationality h_rat).external_inputs.boundary.forward_reproof_boundary.forward_inputs =
      _root_.SondowForwardInputs.of_reproof
  accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n
  root_accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          (kit.with_rationality h_rat).paper_surface.surface n)
  compiler_consumption_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
        (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
          Nonempty
            (Month2SondowAcceptedCompiledCertificateAt
              (kit.with_rationality h_rat).paper_surface.surface n) ∧
            ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
              BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
                BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
                ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
                  |>.componentCertificateOfFullCertificate hchecked)

structure Month2OpenSourceReleaseSurfacePackage
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) where
  master_theorem_package :
    Month2AcceptedCertificateMasterTheoremPackage kit h_rat
  paper_ready_package :
    PaperReadyTheoremPackage (kit.with_rationality h_rat)
  external_boundary_package :
    ExternalLeanClosedBoundaryPackage (kit.with_rationality h_rat)
  no_hidden_assumptions_package :
    NoHiddenAssumptionsPackage (kit.with_rationality h_rat)
  accepted_certificate_compiler_surface_package :
    AcceptedCertificateCompilerSurfacePackage (kit.with_rationality h_rat)
  component_family_consumption_package :
    ComponentFamilyConsumptionPackage (kit.with_rationality h_rat)
  source_equivalence_same_object :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  audit_checklist_eq_long_form :
    (kit.with_rationality h_rat).audit_checklist =
      audit_checklist_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker
  audit_threshold_eq_long_form :
    (kit.with_rationality h_rat).audit_threshold =
      audit_threshold_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker
  lean_closed_surface_eq_paper_surface :
    (kit.with_rationality h_rat).external_inputs.lean_closed_surface =
      (kit.with_rationality h_rat).paper_surface.surface
  external_forward_reproof_boundary :
    (kit.with_rationality h_rat).external_inputs.boundary.forward_reproof_boundary.forward_inputs =
      _root_.SondowForwardInputs.of_reproof

namespace Month2OpenSourceReleaseSurfacePackage

noncomputable def of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2OpenSourceReleaseSurfacePackage kit h_rat where
  master_theorem_package :=
    Month2AcceptedCertificateMasterTheoremPackage.of_rationality kit h_rat
  paper_ready_package :=
    PaperReadyTheoremPackage.of_inputs (kit.with_rationality h_rat)
  external_boundary_package :=
    ExternalLeanClosedBoundaryPackage.of_inputs (kit.with_rationality h_rat)
  no_hidden_assumptions_package :=
    NoHiddenAssumptionsPackage.of_inputs (kit.with_rationality h_rat)
  accepted_certificate_compiler_surface_package :=
    AcceptedCertificateCompilerSurfacePackage.of_inputs
      (kit.with_rationality h_rat)
  component_family_consumption_package :=
    ComponentFamilyConsumptionPackage.of_inputs (kit.with_rationality h_rat)
  source_equivalence_same_object :=
    (kit.with_rationality h_rat).source_equivalence
  audit_checklist_eq_long_form :=
    (kit.with_rationality h_rat).audit_checklist_eq_long_form
  audit_threshold_eq_long_form :=
    (kit.with_rationality h_rat).audit_threshold_eq_long_form
  lean_closed_surface_eq_paper_surface := rfl
  external_forward_reproof_boundary :=
    (kit.with_rationality h_rat).external_inputs.forward_inputs_closed_by_reproof

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2OpenSourceReleaseSurfaceStatement kit h_rat where
  master_theorem_statement :=
    Month2AcceptedCertificateMasterTheoremPackage.statement kit h_rat
  master_theorem_statement_iff_package_nonempty :=
    Month2AcceptedCertificateMasterTheoremPackage.statement_iff_package_nonempty
      kit h_rat
  master_theorem_package_nonempty :=
    Month2AcceptedCertificateMasterTheoremPackage.package_nonempty kit h_rat
  paper_ready_statement :=
    PaperReadyTheoremPackage.statement (kit.with_rationality h_rat)
  paper_ready_statement_iff_package_nonempty :=
    PaperReadyTheoremPackage.statement_iff_package_nonempty
      (kit.with_rationality h_rat)
  external_boundary_statement :=
    ExternalLeanClosedBoundaryPackage.statement (kit.with_rationality h_rat)
  external_boundary_statement_iff_package_nonempty :=
    ExternalLeanClosedBoundaryPackage.statement_iff_package_nonempty
      (kit.with_rationality h_rat)
  no_hidden_assumptions_statement :=
    NoHiddenAssumptionsPackage.statement (kit.with_rationality h_rat)
  no_hidden_assumptions_statement_iff_package_nonempty :=
    NoHiddenAssumptionsPackage.statement_iff_package_nonempty
      (kit.with_rationality h_rat)
  accepted_certificate_compiler_surface_statement :=
    AcceptedCertificateCompilerSurfacePackage.statement
      (kit.with_rationality h_rat)
  component_family_consumption_statement :=
    ComponentFamilyConsumptionPackage.statement (kit.with_rationality h_rat)
  source_equivalence_same_object :=
    (kit.with_rationality h_rat).source_equivalence
  audit_checklist_eq_long_form :=
    (kit.with_rationality h_rat).audit_checklist_eq_long_form
  audit_threshold_eq_long_form :=
    (kit.with_rationality h_rat).audit_threshold_eq_long_form
  lean_closed_surface_eq_paper_surface := rfl
  external_forward_reproof_boundary :=
    (kit.with_rationality h_rat).external_inputs.forward_inputs_closed_by_reproof
  accepted_eventually :=
    (kit.with_rationality h_rat).accepted_eventually
  root_accepted_eventually :=
    (kit.with_rationality h_rat).root_accepted_eventually
  full_certificate_eventually :=
    (kit.with_rationality h_rat).full_certificate_eventually
  compiled_certificate_eventually :=
    (kit.with_rationality h_rat).compiled_certificate_eventually
  compiler_consumption_after_threshold := fun hn =>
    Month2AcceptedCertificateMasterTheoremPackage.compiler_consumption_after_threshold_of_rationality
      kit h_rat hn

theorem statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2OpenSourceReleaseSurfaceStatement kit h_rat ↔
      Nonempty (Month2OpenSourceReleaseSurfacePackage kit h_rat) := by
  constructor
  · intro _h
    exact ⟨of_rationality kit h_rat⟩
  · intro _h
    exact statement kit h_rat

theorem package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (Month2OpenSourceReleaseSurfacePackage kit h_rat) :=
  (statement_iff_package_nonempty kit h_rat).1 (statement kit h_rat)

theorem audit_threshold_eq_long_form_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    (kit.with_rationality h_rat).audit_threshold =
      audit_threshold_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker :=
  (statement kit h_rat).audit_threshold_eq_long_form

theorem accepted_eventually_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  (statement kit h_rat).accepted_eventually

theorem compiler_consumption_after_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
      (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
        Nonempty
          (Month2SondowAcceptedCompiledCertificateAt
            (kit.with_rationality h_rat).paper_surface.surface n) ∧
          ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
            BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
              BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
              ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
                |>.componentCertificateOfFullCertificate hchecked) :=
  (statement kit h_rat).compiler_consumption_after_threshold hn

end Month2OpenSourceReleaseSurfacePackage

structure Month2PublicCitationAuditChecklistStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) : Prop where
  open_source_release_surface_statement :
    Month2OpenSourceReleaseSurfaceStatement kit h_rat
  open_source_release_surface_statement_iff_package_nonempty :
    Month2OpenSourceReleaseSurfaceStatement kit h_rat ↔
      Nonempty (Month2OpenSourceReleaseSurfacePackage kit h_rat)
  open_source_release_surface_package_nonempty :
    Nonempty (Month2OpenSourceReleaseSurfacePackage kit h_rat)
  accepted_certificate_master_theorem_statement :
    Month2AcceptedCertificateMasterTheoremStatement kit h_rat
  accepted_certificate_master_theorem_statement_iff_package_nonempty :
    Month2AcceptedCertificateMasterTheoremStatement kit h_rat ↔
      Nonempty (Month2AcceptedCertificateMasterTheoremPackage kit h_rat)
  no_hidden_assumptions_statement :
    NoHiddenAssumptionsStatement (kit.with_rationality h_rat)
  no_hidden_assumptions_statement_iff_package_nonempty :
    NoHiddenAssumptionsStatement (kit.with_rationality h_rat) ↔
      Nonempty (NoHiddenAssumptionsPackage (kit.with_rationality h_rat))
  accepted_definition_exact :
    ∀ n : ℕ,
      Month2SondowAccepted n ↔
        _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  source_equivalence_same_object :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  audit_threshold_eq_long_form :
    (kit.with_rationality h_rat).audit_threshold =
      audit_threshold_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker
  audit_checklist_eq_long_form :
    (kit.with_rationality h_rat).audit_checklist =
      audit_checklist_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker
  lean_closed_surface_eq_paper_surface :
    (kit.with_rationality h_rat).external_inputs.lean_closed_surface =
      (kit.with_rationality h_rat).paper_surface.surface
  external_forward_reproof_boundary :
    (kit.with_rationality h_rat).external_inputs.boundary.forward_reproof_boundary.forward_inputs =
      _root_.SondowForwardInputs.of_reproof
  accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n
  root_accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  full_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℚ, mainSondowFullCertificateChecks q n
  compiled_certificate_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          (kit.with_rationality h_rat).paper_surface.surface n)
  compiler_consumption_after_threshold :
    ∀ {n : ℕ}, (kit.with_rationality h_rat).audit_threshold ≤ n →
      (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
        (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
          Nonempty
            (Month2SondowAcceptedCompiledCertificateAt
              (kit.with_rationality h_rat).paper_surface.surface n) ∧
            ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
              BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
                BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
                ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
                  |>.componentCertificateOfFullCertificate hchecked)

structure Month2PublicCitationAuditChecklistPackage
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) where
  open_source_release_surface_package :
    Month2OpenSourceReleaseSurfacePackage kit h_rat
  accepted_certificate_master_theorem_package :
    Month2AcceptedCertificateMasterTheoremPackage kit h_rat
  no_hidden_assumptions_package :
    NoHiddenAssumptionsPackage (kit.with_rationality h_rat)
  accepted_definition_exact :
    ∀ n : ℕ,
      Month2SondowAccepted n ↔
        _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  source_equivalence_same_object :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  audit_threshold_eq_long_form :
    (kit.with_rationality h_rat).audit_threshold =
      audit_threshold_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker
  audit_checklist_eq_long_form :
    (kit.with_rationality h_rat).audit_checklist =
      audit_checklist_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker
  lean_closed_surface_eq_paper_surface :
    (kit.with_rationality h_rat).external_inputs.lean_closed_surface =
      (kit.with_rationality h_rat).paper_surface.surface
  external_forward_reproof_boundary :
    (kit.with_rationality h_rat).external_inputs.boundary.forward_reproof_boundary.forward_inputs =
      _root_.SondowForwardInputs.of_reproof

namespace Month2PublicCitationAuditChecklistPackage

noncomputable def of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2PublicCitationAuditChecklistPackage kit h_rat where
  open_source_release_surface_package :=
    Month2OpenSourceReleaseSurfacePackage.of_rationality kit h_rat
  accepted_certificate_master_theorem_package :=
    Month2AcceptedCertificateMasterTheoremPackage.of_rationality kit h_rat
  no_hidden_assumptions_package :=
    NoHiddenAssumptionsPackage.of_inputs (kit.with_rationality h_rat)
  accepted_definition_exact :=
    month2SondowAccepted_iff_root_accepted
  source_equivalence_same_object :=
    (kit.with_rationality h_rat).source_equivalence
  audit_threshold_eq_long_form :=
    (kit.with_rationality h_rat).audit_threshold_eq_long_form
  audit_checklist_eq_long_form :=
    (kit.with_rationality h_rat).audit_checklist_eq_long_form
  lean_closed_surface_eq_paper_surface := rfl
  external_forward_reproof_boundary :=
    (kit.with_rationality h_rat).external_inputs.forward_inputs_closed_by_reproof

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2PublicCitationAuditChecklistStatement kit h_rat where
  open_source_release_surface_statement :=
    Month2OpenSourceReleaseSurfacePackage.statement kit h_rat
  open_source_release_surface_statement_iff_package_nonempty :=
    Month2OpenSourceReleaseSurfacePackage.statement_iff_package_nonempty
      kit h_rat
  open_source_release_surface_package_nonempty :=
    Month2OpenSourceReleaseSurfacePackage.package_nonempty kit h_rat
  accepted_certificate_master_theorem_statement :=
    Month2AcceptedCertificateMasterTheoremPackage.statement kit h_rat
  accepted_certificate_master_theorem_statement_iff_package_nonempty :=
    Month2AcceptedCertificateMasterTheoremPackage.statement_iff_package_nonempty
      kit h_rat
  no_hidden_assumptions_statement :=
    NoHiddenAssumptionsPackage.statement (kit.with_rationality h_rat)
  no_hidden_assumptions_statement_iff_package_nonempty :=
    NoHiddenAssumptionsPackage.statement_iff_package_nonempty
      (kit.with_rationality h_rat)
  accepted_definition_exact :=
    month2SondowAccepted_iff_root_accepted
  source_equivalence_same_object :=
    (kit.with_rationality h_rat).source_equivalence
  audit_threshold_eq_long_form :=
    (kit.with_rationality h_rat).audit_threshold_eq_long_form
  audit_checklist_eq_long_form :=
    (kit.with_rationality h_rat).audit_checklist_eq_long_form
  lean_closed_surface_eq_paper_surface := rfl
  external_forward_reproof_boundary :=
    (kit.with_rationality h_rat).external_inputs.forward_inputs_closed_by_reproof
  accepted_eventually :=
    (kit.with_rationality h_rat).accepted_eventually
  root_accepted_eventually :=
    (kit.with_rationality h_rat).root_accepted_eventually
  full_certificate_eventually :=
    (kit.with_rationality h_rat).full_certificate_eventually
  compiled_certificate_eventually :=
    (kit.with_rationality h_rat).compiled_certificate_eventually
  compiler_consumption_after_threshold := fun hn =>
    Month2OpenSourceReleaseSurfacePackage.compiler_consumption_after_threshold_of_rationality
      kit h_rat hn

theorem statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2PublicCitationAuditChecklistStatement kit h_rat ↔
      Nonempty (Month2PublicCitationAuditChecklistPackage kit h_rat) := by
  constructor
  · intro _h
    exact ⟨of_rationality kit h_rat⟩
  · intro _h
    exact statement kit h_rat

theorem package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (Month2PublicCitationAuditChecklistPackage kit h_rat) :=
  (statement_iff_package_nonempty kit h_rat).1 (statement kit h_rat)

theorem accepted_definition_exact_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (_kit : PublicInfrastructureKit.{u} bounds)
    (_h_rat : _root_.is_rational _root_.euler_mascheroni)
    (n : ℕ) :
    Month2SondowAccepted n ↔
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  (statement _kit _h_rat).accepted_definition_exact n

theorem release_surface_statement_iff_package_nonempty_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2OpenSourceReleaseSurfaceStatement kit h_rat ↔
      Nonempty (Month2OpenSourceReleaseSurfacePackage kit h_rat) :=
  (statement kit h_rat).open_source_release_surface_statement_iff_package_nonempty

theorem compiler_consumption_after_threshold_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
      (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
        Nonempty
          (Month2SondowAcceptedCompiledCertificateAt
            (kit.with_rationality h_rat).paper_surface.surface n) ∧
          ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
            BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
              BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
              ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
                |>.componentCertificateOfFullCertificate hchecked) :=
  (statement kit h_rat).compiler_consumption_after_threshold hn

end Month2PublicCitationAuditChecklistPackage

structure Month2VerifiedPublicReleaseInputs
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  kit : PublicInfrastructureKit.{u} bounds
  rationality : _root_.is_rational _root_.euler_mascheroni

namespace Month2VerifiedPublicReleaseInputs

abbrev public_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    PublicCompilerInputs.{u} bounds :=
  inputs.kit.with_rationality inputs.rationality

abbrev citation_statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) : Prop :=
  Month2PublicCitationAuditChecklistStatement
    inputs.kit inputs.rationality

abbrev release_surface_statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) : Prop :=
  Month2OpenSourceReleaseSurfaceStatement inputs.kit inputs.rationality

noncomputable def citation_package
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    Month2PublicCitationAuditChecklistPackage
      inputs.kit inputs.rationality :=
  Month2PublicCitationAuditChecklistPackage.of_rationality
    inputs.kit inputs.rationality

noncomputable def release_surface_package
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    Month2OpenSourceReleaseSurfacePackage inputs.kit inputs.rationality :=
  Month2OpenSourceReleaseSurfacePackage.of_rationality
    inputs.kit inputs.rationality

theorem citation_statement_of_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    inputs.citation_statement :=
  Month2PublicCitationAuditChecklistPackage.statement
    inputs.kit inputs.rationality

theorem citation_statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    inputs.citation_statement ↔
      Nonempty
        (Month2PublicCitationAuditChecklistPackage
          inputs.kit inputs.rationality) :=
  Month2PublicCitationAuditChecklistPackage.statement_iff_package_nonempty
    inputs.kit inputs.rationality

theorem citation_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    Nonempty
      (Month2PublicCitationAuditChecklistPackage
        inputs.kit inputs.rationality) :=
  Month2PublicCitationAuditChecklistPackage.package_nonempty
    inputs.kit inputs.rationality

theorem release_surface_statement_of_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    inputs.release_surface_statement :=
  Month2OpenSourceReleaseSurfacePackage.statement
    inputs.kit inputs.rationality

theorem release_surface_statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    inputs.release_surface_statement ↔
      Nonempty
        (Month2OpenSourceReleaseSurfacePackage
          inputs.kit inputs.rationality) :=
  Month2OpenSourceReleaseSurfacePackage.statement_iff_package_nonempty
    inputs.kit inputs.rationality

theorem accepted_definition_exact
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (_inputs : Month2VerifiedPublicReleaseInputs.{u} bounds)
    (n : ℕ) :
    Month2SondowAccepted n ↔
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  month2SondowAccepted_iff_root_accepted n

theorem accepted_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  (inputs.citation_statement_of_inputs).accepted_eventually

theorem root_accepted_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  (inputs.citation_statement_of_inputs).root_accepted_eventually

theorem no_hidden_assumptions
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    NoHiddenAssumptionsStatement inputs.public_inputs :=
  (inputs.citation_statement_of_inputs).no_hidden_assumptions_statement

theorem compiler_consumption_after_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds)
    {n : ℕ}
    (hn : inputs.public_inputs.audit_threshold ≤ n) :
    (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
      (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
        Nonempty
          (Month2SondowAcceptedCompiledCertificateAt
            inputs.public_inputs.paper_surface.surface n) ∧
          ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
            BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
              BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
              (inputs.public_inputs.paper_surface.surface.audit_package.boundary
                |>.componentCertificateOfFullCertificate hchecked) :=
  (inputs.citation_statement_of_inputs).compiler_consumption_after_threshold
    hn

end Month2VerifiedPublicReleaseInputs

structure Month2VerifiedPublicReleaseTheoremStatement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) : Prop where
  public_inputs_eq :
    inputs.public_inputs = inputs.kit.with_rationality inputs.rationality
  citation_statement :
    inputs.citation_statement
  citation_statement_iff_package_nonempty :
    inputs.citation_statement ↔
      Nonempty
        (Month2PublicCitationAuditChecklistPackage
          inputs.kit inputs.rationality)
  citation_package_nonempty :
    Nonempty
      (Month2PublicCitationAuditChecklistPackage
        inputs.kit inputs.rationality)
  release_surface_statement :
    inputs.release_surface_statement
  release_surface_statement_iff_package_nonempty :
    inputs.release_surface_statement ↔
      Nonempty
        (Month2OpenSourceReleaseSurfacePackage
          inputs.kit inputs.rationality)
  release_surface_package_nonempty :
    Nonempty
      (Month2OpenSourceReleaseSurfacePackage
        inputs.kit inputs.rationality)
  no_hidden_assumptions_statement :
    NoHiddenAssumptionsStatement inputs.public_inputs
  accepted_definition_exact :
    ∀ n : ℕ,
      Month2SondowAccepted n ↔
        _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  source_equivalence_same_object :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n
  root_accepted_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  compiler_consumption_after_threshold :
    ∀ {n : ℕ}, inputs.public_inputs.audit_threshold ≤ n →
      (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
        (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
          Nonempty
            (Month2SondowAcceptedCompiledCertificateAt
              inputs.public_inputs.paper_surface.surface n) ∧
            ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
              BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
                BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
                (inputs.public_inputs.paper_surface.surface.audit_package.boundary
                  |>.componentCertificateOfFullCertificate hchecked)

structure Month2VerifiedPublicReleaseTheoremPackage
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) where
  public_inputs_eq :
    inputs.public_inputs = inputs.kit.with_rationality inputs.rationality
  citation_package :
    Month2PublicCitationAuditChecklistPackage
      inputs.kit inputs.rationality
  release_surface_package :
    Month2OpenSourceReleaseSurfacePackage inputs.kit inputs.rationality
  no_hidden_assumptions_package :
    NoHiddenAssumptionsPackage inputs.public_inputs
  accepted_definition_exact :
    ∀ n : ℕ,
      Month2SondowAccepted n ↔
        _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  source_equivalence_same_object :
    ∀ q : ℚ, ∀ n : ℕ,
      mainSondowFullCertificateChecks q n ↔
        MainSondowFullCertificateSourceComponents q n
  compiler_consumption_after_threshold :
    ∀ {n : ℕ}, inputs.public_inputs.audit_threshold ≤ n →
      (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
        (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
          Nonempty
            (Month2SondowAcceptedCompiledCertificateAt
              inputs.public_inputs.paper_surface.surface n) ∧
            ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
              BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
                BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
                (inputs.public_inputs.paper_surface.surface.audit_package.boundary
                  |>.componentCertificateOfFullCertificate hchecked)

namespace Month2VerifiedPublicReleaseTheoremPackage

noncomputable def of_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    Month2VerifiedPublicReleaseTheoremPackage inputs where
  public_inputs_eq := rfl
  citation_package := inputs.citation_package
  release_surface_package := inputs.release_surface_package
  no_hidden_assumptions_package :=
    NoHiddenAssumptionsPackage.of_inputs inputs.public_inputs
  accepted_definition_exact :=
    Month2VerifiedPublicReleaseInputs.accepted_definition_exact inputs
  source_equivalence_same_object :=
    (inputs.citation_statement_of_inputs).source_equivalence_same_object
  compiler_consumption_after_threshold := fun hn =>
    Month2VerifiedPublicReleaseInputs.compiler_consumption_after_threshold
      inputs hn

theorem statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    Month2VerifiedPublicReleaseTheoremStatement inputs where
  public_inputs_eq := rfl
  citation_statement := inputs.citation_statement_of_inputs
  citation_statement_iff_package_nonempty :=
    inputs.citation_statement_iff_package_nonempty
  citation_package_nonempty := inputs.citation_package_nonempty
  release_surface_statement :=
    inputs.release_surface_statement_of_inputs
  release_surface_statement_iff_package_nonempty :=
    inputs.release_surface_statement_iff_package_nonempty
  release_surface_package_nonempty :=
    Month2OpenSourceReleaseSurfacePackage.package_nonempty
      inputs.kit inputs.rationality
  no_hidden_assumptions_statement := inputs.no_hidden_assumptions
  accepted_definition_exact :=
    Month2VerifiedPublicReleaseInputs.accepted_definition_exact inputs
  source_equivalence_same_object :=
    (inputs.citation_statement_of_inputs).source_equivalence_same_object
  accepted_eventually := inputs.accepted_eventually
  root_accepted_eventually := inputs.root_accepted_eventually
  compiler_consumption_after_threshold := fun hn =>
    Month2VerifiedPublicReleaseInputs.compiler_consumption_after_threshold
      inputs hn

theorem statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    Month2VerifiedPublicReleaseTheoremStatement inputs ↔
      Nonempty (Month2VerifiedPublicReleaseTheoremPackage inputs) := by
  constructor
  · intro _h
    exact ⟨of_inputs inputs⟩
  · intro _h
    exact statement inputs

theorem package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    Nonempty (Month2VerifiedPublicReleaseTheoremPackage inputs) :=
  (statement_iff_package_nonempty inputs).1 (statement inputs)

theorem accepted_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  (statement inputs).accepted_eventually

theorem compiler_consumption_after_threshold_of_statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds)
    {n : ℕ}
    (hn : inputs.public_inputs.audit_threshold ≤ n) :
    (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
      (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
        Nonempty
          (Month2SondowAcceptedCompiledCertificateAt
            inputs.public_inputs.paper_surface.surface n) ∧
          ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
            BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
              BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
              (inputs.public_inputs.paper_surface.surface.audit_package.boundary
                |>.componentCertificateOfFullCertificate hchecked) :=
  (statement inputs).compiler_consumption_after_threshold hn

end Month2VerifiedPublicReleaseTheoremPackage

namespace Month2VerifiedPublicReleaseInputs

theorem verified_public_release_theorem_statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    Month2VerifiedPublicReleaseTheoremStatement inputs :=
  Month2VerifiedPublicReleaseTheoremPackage.statement inputs

theorem verified_public_release_theorem_statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    Month2VerifiedPublicReleaseTheoremStatement inputs ↔
      Nonempty (Month2VerifiedPublicReleaseTheoremPackage inputs) :=
  Month2VerifiedPublicReleaseTheoremPackage.statement_iff_package_nonempty
    inputs

theorem verified_public_release_theorem_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (inputs : Month2VerifiedPublicReleaseInputs.{u} bounds) :
    Nonempty (Month2VerifiedPublicReleaseTheoremPackage inputs) :=
  Month2VerifiedPublicReleaseTheoremPackage.package_nonempty inputs

end Month2VerifiedPublicReleaseInputs

namespace PublicInfrastructureKit

noncomputable def verified_public_release_inputs
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2VerifiedPublicReleaseInputs.{u} bounds where
  kit := kit
  rationality := h_rat

theorem month2_verified_public_release_theorem_statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2VerifiedPublicReleaseTheoremStatement
      (kit.verified_public_release_inputs h_rat) :=
  Month2VerifiedPublicReleaseTheoremPackage.statement
    (kit.verified_public_release_inputs h_rat)

theorem month2_verified_public_release_theorem_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty
      (Month2VerifiedPublicReleaseTheoremPackage
        (kit.verified_public_release_inputs h_rat)) :=
  Month2VerifiedPublicReleaseTheoremPackage.package_nonempty
    (kit.verified_public_release_inputs h_rat)

theorem month2_verified_public_release_theorem_statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2VerifiedPublicReleaseTheoremStatement
        (kit.verified_public_release_inputs h_rat) ↔
      Nonempty
        (Month2VerifiedPublicReleaseTheoremPackage
          (kit.verified_public_release_inputs h_rat)) :=
  Month2VerifiedPublicReleaseTheoremPackage.statement_iff_package_nonempty
    (kit.verified_public_release_inputs h_rat)

theorem verified_public_release_accepted_definition_exact
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (n : ℕ) :
    Month2SondowAccepted n ↔
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  (kit.month2_verified_public_release_theorem_statement h_rat)
    |>.accepted_definition_exact n

theorem verified_public_release_source_equivalence_same_object
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (q : ℚ) (n : ℕ) :
    mainSondowFullCertificateChecks q n ↔
      MainSondowFullCertificateSourceComponents q n :=
  (kit.month2_verified_public_release_theorem_statement h_rat)
    |>.source_equivalence_same_object q n

theorem verified_public_release_accepted_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  (kit.month2_verified_public_release_theorem_statement h_rat)
    |>.accepted_eventually

theorem verified_public_release_root_accepted_eventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  (kit.month2_verified_public_release_theorem_statement h_rat)
    |>.root_accepted_eventually

theorem verified_public_release_compiler_consumption_after_rationality_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
      (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
        Nonempty
          (Month2SondowAcceptedCompiledCertificateAt
            (kit.with_rationality h_rat).paper_surface.surface n) ∧
          ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
            BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
              BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
              ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
                |>.componentCertificateOfFullCertificate hchecked) :=
  (kit.month2_verified_public_release_theorem_statement h_rat)
    |>.compiler_consumption_after_threshold hn

theorem analytic_boundary_classification_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    AnalyticBoundaryClassificationStatement (kit.with_rationality h_rat) :=
  AnalyticBoundaryClassificationPackage.statement
    (kit.with_rationality h_rat)

theorem analytic_boundary_classification_package_nonempty_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty
      (AnalyticBoundaryClassificationPackage (kit.with_rationality h_rat)) :=
  AnalyticBoundaryClassificationPackage.package_nonempty
    (kit.with_rationality h_rat)

theorem component_family_consumption_statement_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ComponentFamilyConsumptionStatement (kit.with_rationality h_rat) :=
  ComponentFamilyConsumptionPackage.statement (kit.with_rationality h_rat)

theorem component_family_consumption_package_nonempty_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty
      (ComponentFamilyConsumptionPackage (kit.with_rationality h_rat)) :=
  ComponentFamilyConsumptionPackage.package_nonempty
    (kit.with_rationality h_rat)

theorem accepted_certificate_compiler_surface_statement_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    AcceptedCertificateCompilerSurfaceStatement (kit.with_rationality h_rat) :=
  AcceptedCertificateCompilerSurfacePackage.statement
    (kit.with_rationality h_rat)

theorem accepted_certificate_compiler_surface_package_nonempty_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty
      (AcceptedCertificateCompilerSurfacePackage
        (kit.with_rationality h_rat)) :=
  AcceptedCertificateCompilerSurfacePackage.package_nonempty
    (kit.with_rationality h_rat)

theorem month2_paper_theorem_bundle_statement_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2PaperTheoremBundleStatement (kit.with_rationality h_rat) :=
  Month2PaperTheoremBundlePackage.statement
    (kit.with_rationality h_rat)

theorem month2_paper_theorem_bundle_package_nonempty_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty
      (Month2PaperTheoremBundlePackage (kit.with_rationality h_rat)) :=
  Month2PaperTheoremBundlePackage.package_nonempty
    (kit.with_rationality h_rat)

theorem month2_rationality_final_public_theorem_statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2RationalityFinalPublicTheoremStatement kit h_rat :=
  Month2RationalityFinalPublicTheoremPackage.statement kit h_rat

theorem month2_rationality_final_public_theorem_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (Month2RationalityFinalPublicTheoremPackage kit h_rat) :=
  Month2RationalityFinalPublicTheoremPackage.package_nonempty kit h_rat

theorem month2_rationality_auditor_checklist_statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2RationalityAuditorChecklistStatement kit h_rat :=
  Month2RationalityAuditorChecklistPackage.statement kit h_rat

theorem month2_rationality_auditor_checklist_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (Month2RationalityAuditorChecklistPackage kit h_rat) :=
  Month2RationalityAuditorChecklistPackage.package_nonempty kit h_rat

theorem month2_paper_facing_audit_boundary_statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2PaperFacingAuditBoundaryStatement kit h_rat :=
  Month2PaperFacingAuditBoundaryPackage.statement kit h_rat

theorem month2_paper_facing_audit_boundary_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (Month2PaperFacingAuditBoundaryPackage kit h_rat) :=
  Month2PaperFacingAuditBoundaryPackage.package_nonempty kit h_rat

theorem month2_compiler_consumption_paper_surface_statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2CompilerConsumptionPaperSurfaceStatement kit h_rat :=
  Month2CompilerConsumptionPaperSurfacePackage.statement kit h_rat

theorem month2_compiler_consumption_paper_surface_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (Month2CompilerConsumptionPaperSurfacePackage kit h_rat) :=
  Month2CompilerConsumptionPaperSurfacePackage.package_nonempty kit h_rat

theorem compiler_consumption_source_components_after_rationality_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    ∃ q : ℚ, MainSondowFullCertificateSourceComponents q n :=
  Month2CompilerConsumptionPaperSurfacePackage.source_components_after_threshold_of_rationality
    kit h_rat hn

noncomputable def compiler_consumption_compiled_certificate_after_rationality_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    Month2SondowAcceptedCompiledCertificateAt
      (kit.with_rationality h_rat).paper_surface.surface n :=
  Month2CompilerConsumptionPaperSurfacePackage.compiled_certificate_after_threshold_of_rationality
    kit h_rat hn

theorem compiler_consumption_after_rationality_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
      (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
        Nonempty
          (Month2SondowAcceptedCompiledCertificateAt
            (kit.with_rationality h_rat).paper_surface.surface n) ∧
          ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
            BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
              BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
              ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
                |>.componentCertificateOfFullCertificate hchecked) :=
  Month2CompilerConsumptionPaperSurfacePackage.compiler_consumption_after_threshold_of_rationality
    kit h_rat hn

theorem month2_analytic_boundary_paper_surface_statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2AnalyticBoundaryPaperSurfaceStatement kit h_rat :=
  Month2AnalyticBoundaryPaperSurfacePackage.statement kit h_rat

theorem month2_analytic_boundary_paper_surface_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (Month2AnalyticBoundaryPaperSurfacePackage kit h_rat) :=
  Month2AnalyticBoundaryPaperSurfacePackage.package_nonempty kit h_rat

theorem analytic_boundary_lean_closed_surface_eq_paper_surface
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    (kit.with_rationality h_rat).external_inputs.lean_closed_surface =
      (kit.with_rationality h_rat).paper_surface.surface :=
  Month2AnalyticBoundaryPaperSurfacePackage.lean_closed_surface_eq_paper_surface_of_rationality
    kit h_rat

theorem analytic_boundary_external_forward_reproof_boundary
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    (kit.with_rationality h_rat).external_inputs.boundary.forward_reproof_boundary.forward_inputs =
      _root_.SondowForwardInputs.of_reproof :=
  Month2AnalyticBoundaryPaperSurfacePackage.external_forward_reproof_boundary_of_rationality
    kit h_rat

theorem analytic_boundary_compiled_certificate_eventually_lean_closed
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (Month2SondowAcceptedCompiledCertificateAt
          (kit.with_rationality h_rat).paper_surface.surface n) :=
  Month2AnalyticBoundaryPaperSurfacePackage.compiled_certificate_eventually_lean_closed_of_rationality
    kit h_rat

theorem month2_accepted_certificate_master_theorem_statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2AcceptedCertificateMasterTheoremStatement kit h_rat :=
  Month2AcceptedCertificateMasterTheoremPackage.statement kit h_rat

theorem month2_accepted_certificate_master_theorem_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (Month2AcceptedCertificateMasterTheoremPackage kit h_rat) :=
  Month2AcceptedCertificateMasterTheoremPackage.package_nonempty kit h_rat

theorem accepted_certificate_master_accepted_eventually_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  Month2AcceptedCertificateMasterTheoremPackage.accepted_eventually_of_rationality
    kit h_rat

theorem accepted_certificate_master_root_accepted_eventually_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  Month2AcceptedCertificateMasterTheoremPackage.root_accepted_eventually_of_rationality
    kit h_rat

noncomputable def accepted_certificate_master_compiled_certificate_after_rationality_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    Month2SondowAcceptedCompiledCertificateAt
      (kit.with_rationality h_rat).paper_surface.surface n :=
  Month2AcceptedCertificateMasterTheoremPackage.compiled_certificate_after_threshold_of_rationality
    kit h_rat hn

theorem accepted_certificate_master_compiler_consumption_after_rationality_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
      (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
        Nonempty
          (Month2SondowAcceptedCompiledCertificateAt
            (kit.with_rationality h_rat).paper_surface.surface n) ∧
          ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
            BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
              BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
              ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
                |>.componentCertificateOfFullCertificate hchecked) :=
  Month2AcceptedCertificateMasterTheoremPackage.compiler_consumption_after_threshold_of_rationality
    kit h_rat hn

theorem month2_open_source_release_surface_statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2OpenSourceReleaseSurfaceStatement kit h_rat :=
  Month2OpenSourceReleaseSurfacePackage.statement kit h_rat

theorem month2_open_source_release_surface_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (Month2OpenSourceReleaseSurfacePackage kit h_rat) :=
  Month2OpenSourceReleaseSurfacePackage.package_nonempty kit h_rat

theorem open_source_release_audit_threshold_eq_long_form
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    (kit.with_rationality h_rat).audit_threshold =
      audit_threshold_of_compilers
        h_rat kit.payload_spec kit.concrete_verification kit.compilers
        kit.root_convention kit.kernel kit.checker :=
  Month2OpenSourceReleaseSurfacePackage.audit_threshold_eq_long_form_of_rationality
    kit h_rat

theorem open_source_release_accepted_eventually_of_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Month2SondowAccepted n :=
  Month2OpenSourceReleaseSurfacePackage.accepted_eventually_of_rationality
    kit h_rat

theorem open_source_release_compiler_consumption_after_rationality_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
      (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
        Nonempty
          (Month2SondowAcceptedCompiledCertificateAt
            (kit.with_rationality h_rat).paper_surface.surface n) ∧
          ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
            BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
              BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
              ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
                |>.componentCertificateOfFullCertificate hchecked) :=
  Month2OpenSourceReleaseSurfacePackage.compiler_consumption_after_threshold_of_rationality
    kit h_rat hn

theorem month2_public_citation_audit_checklist_statement
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2PublicCitationAuditChecklistStatement kit h_rat :=
  Month2PublicCitationAuditChecklistPackage.statement kit h_rat

theorem month2_public_citation_audit_checklist_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty (Month2PublicCitationAuditChecklistPackage kit h_rat) :=
  Month2PublicCitationAuditChecklistPackage.package_nonempty kit h_rat

theorem public_citation_accepted_definition_exact
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    (n : ℕ) :
    Month2SondowAccepted n ↔
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
  Month2PublicCitationAuditChecklistPackage.accepted_definition_exact_of_rationality
    kit h_rat n

theorem public_citation_release_surface_statement_iff_package_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Month2OpenSourceReleaseSurfaceStatement kit h_rat ↔
      Nonempty (Month2OpenSourceReleaseSurfacePackage kit h_rat) :=
  Month2PublicCitationAuditChecklistPackage.release_surface_statement_iff_package_nonempty_of_rationality
    kit h_rat

theorem public_citation_compiler_consumption_after_rationality_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    (∃ q : ℚ, mainSondowFullCertificateChecks q n) ∧
      (∃ q : ℚ, MainSondowFullCertificateSourceComponents q n) ∧
        Nonempty
          (Month2SondowAcceptedCompiledCertificateAt
            (kit.with_rationality h_rat).paper_surface.surface n) ∧
          ∃ q : ℚ, ∃ hchecked : mainSondowFullCertificateChecks q n,
            BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
              BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
              ((kit.with_rationality h_rat).paper_surface.surface.audit_package.boundary
                |>.componentCertificateOfFullCertificate hchecked) :=
  Month2PublicCitationAuditChecklistPackage.compiler_consumption_after_threshold_of_rationality
    kit h_rat hn

theorem full_certificate_after_rationality_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    ∃ q : ℚ, mainSondowFullCertificateChecks q n :=
  (kit.with_rationality h_rat).full_certificate_after hn

theorem product_exists_after_rationality_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.product n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.product n :=
  (kit.with_rationality h_rat).paper_surface.surface.product_exists_after hn

theorem log_exists_after_rationality_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.logRelation n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.logRelation n :=
  (kit.with_rationality h_rat).paper_surface.surface.log_exists_after hn

theorem decomposition_exists_after_rationality_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.decomposition n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.decomposition n :=
  (kit.with_rationality h_rat).paper_surface.surface.decomposition_exists_after
    hn

theorem threePow_exists_after_rationality_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.threePow n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.threePow n :=
  (kit.with_rationality h_rat).paper_surface.surface.threePow_exists_after hn

theorem payload_exists_after_rationality_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kit : PublicInfrastructureKit.{u} bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni)
    {n : ℕ}
    (hn : (kit.with_rationality h_rat).audit_threshold ≤ n) :
    ∃ proof :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          BoundedArithmeticLab.sondowProjectComponentFormulas.payload n ∧
        (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.payload n :=
  (kit.with_rationality h_rat).paper_surface.surface.payload_exists_after hn

end PublicInfrastructureKit

end Month2SondowAcceptedPublicRationalityTheorem

/-!
Intentional Month 2 public surface probes.
-/

#check Month2SondowAcceptedCertificateConstructionLayer
#check Month2SondowAccepted
#check month2SondowAccepted_iff_root_accepted
#check month2SondowAccepted_eventually_of_reflection_graft_collapse_inputs
#check Month2SondowComponentCertificateFields
#check Month2SondowComponentCertificateFields.product_exists_after
#check Month2SondowComponentCertificateFields.log_exists_after
#check Month2SondowComponentCertificateFields.decomposition_exists_after
#check Month2SondowComponentCertificateFields.threePow_exists_after
#check Month2SondowComponentCertificateFields.payload_exists_after
#check Month2SondowComponentCertificateFields.system_eventual_nonempty
#check Month2SondowComponentCertificateFields.semantic_eventual_nonempty
#check component_fields_of_rationality_project_proof_objects
#check component_fields_of_main_eventual_compiler_and_rationality
#check component_fields_of_main_full_compiler_and_rationality
#check component_fields_of_source_component_compilers_and_rationality
#check Month2SondowAcceptedAndComponentFields
#check Month2SondowAcceptedAndComponentFields.product_exists_after_component_threshold
#check Month2SondowAcceptedAndComponentFields.log_exists_after_component_threshold
#check Month2SondowAcceptedAndComponentFields.decomposition_exists_after_component_threshold
#check Month2SondowAcceptedAndComponentFields.threePow_exists_after_component_threshold
#check Month2SondowAcceptedAndComponentFields.payload_exists_after_component_threshold
#check Month2SondowAcceptedAndComponentFields.semantic_eventual_nonempty
#check accepted_and_component_fields_of_collapse_compiler_and_rationality
#check accepted_and_component_fields_of_collapse_full_compiler_and_rationality
#check accepted_and_component_fields_of_collapse_source_compilers_and_rationality
#check Month2SondowAcceptedForwardReproofBoundary
#check month2SondowAcceptedForwardReproofBoundary
#check month2SondowAcceptedForwardReproofBoundary_forward_inputs_eq
#check Month2SondowAcceptedForwardReproofBoundary.reflection_graft_accepted_eventually_of_payload_spec
#check Month2SondowAcceptedForwardReproofBoundary.reflection_graft_accepted_eventually_of_bridge_package
#check accepted_and_component_fields_of_reproof_payload_spec_source_compilers_and_rationality
#check accepted_and_component_fields_of_reproof_bridge_package_source_compilers_and_rationality
#check Month2SondowAcceptedCertificateConstructionLayer.system_eventual
#check Month2SondowAcceptedCertificateConstructionLayer.semantic_eventual
#check Month2SondowAcceptedCertificateConstructionLayer.recognition_split
#check Month2SondowAcceptedCertificateConstructionLayer.checked_code_witness
#check component_eventual_of_rationality_project_proof_objects
#check construction_layer_of_component_fields_and_root_convention
#check construction_layer_of_main_eventual_compiler_rationality_and_root_convention
#check construction_layer_of_main_full_compiler_rationality_and_root_convention
#check construction_layer_of_source_component_compilers_rationality_and_root_convention
#check Month2SondowAcceptedPublicConstructionPackage
#check Month2SondowAcceptedPublicConstructionPackage.accepted_after
#check Month2SondowAcceptedPublicConstructionPackage.root_accepted_after
#check Month2SondowAcceptedPublicConstructionPackage.product_exists_after_component_threshold
#check Month2SondowAcceptedPublicConstructionPackage.log_exists_after_component_threshold
#check Month2SondowAcceptedPublicConstructionPackage.decomposition_exists_after_component_threshold
#check Month2SondowAcceptedPublicConstructionPackage.threePow_exists_after_component_threshold
#check Month2SondowAcceptedPublicConstructionPackage.payload_exists_after_component_threshold
#check Month2SondowAcceptedPublicConstructionPackage.system_eventual_from_component_fields
#check Month2SondowAcceptedPublicConstructionPackage.semantic_eventual_from_component_fields
#check Month2SondowAcceptedPublicConstructionPackage.construction_system_eventual
#check Month2SondowAcceptedPublicConstructionPackage.construction_semantic_eventual
#check Month2SondowAcceptedPublicConstructionPackage.recognition_split
#check Month2SondowAcceptedPublicConstructionPackage.checked_code_witness
#check public_construction_package_of_accepted_component_fields_and_root_convention
#check public_construction_package_of_reproof_payload_spec_source_compilers_rationality_and_root_convention
#check public_construction_package_of_reproof_bridge_package_source_compilers_rationality_and_root_convention
#check semantic_eventual_of_rationality_project_proof_objects
#check semantic_eventual_upper_bound_of_main_eventual_compiler
#check Month2SondowAcceptedCLineClosureLayer
#check Month2SondowAcceptedCLineClosureLayer.minimal_closure
#check Month2SondowAcceptedCLineClosureLayer.concrete_checked_code_certificate
#check Month2SondowAcceptedCLineClosureLayer.verifier
#check Month2SondowAcceptedCLineClosureLayer.payload_truth
#check Month2SondowAcceptedCLineClosureLayer.direct_trace_completion
#check Month2SondowAcceptedCLineClosureLayer.collapse_conclusion
#check Month2SondowAcceptedVerifierClosurePackage
#check Month2SondowAcceptedVerifierClosurePackage.accepted_after
#check Month2SondowAcceptedVerifierClosurePackage.root_accepted_after
#check Month2SondowAcceptedVerifierClosurePackage.component_system_eventual
#check Month2SondowAcceptedVerifierClosurePackage.semantic_eventual
#check Month2SondowAcceptedVerifierClosurePackage.checked_code_witness
#check Month2SondowAcceptedVerifierClosurePackage.minimal_closure
#check Month2SondowAcceptedVerifierClosurePackage.concrete_checked_code_certificate
#check Month2SondowAcceptedVerifierClosurePackage.verifier
#check Month2SondowAcceptedVerifierClosurePackage.payload_truth
#check Month2SondowAcceptedVerifierClosurePackage.direct_trace_completion
#check Month2SondowAcceptedVerifierClosurePackage.collapse_conclusion
#check month2_c_line_closure_layer_of_kernel_checker_root_convention
#check verifier_closure_package_of_public_construction_kernel_checker_root_convention
#check verifier_closure_package_of_reproof_payload_spec_source_compilers_rationality_kernel_checker_root_convention
#check verifier_closure_package_of_reproof_bridge_package_source_compilers_rationality_kernel_checker_root_convention
#check Month2SondowSourceCompilerInterface
#check Month2SondowSourceCompilerInterface.toFullCertificateComponentProofCompiler
#check Month2SondowSourceCompilerInterface.sourceCertificateSystems
#check Month2SondowSourceCompilerInterface.projectProofCodeCompilers
#check Month2SondowSourceCompilerInterface.source_certificates_valid
#check Month2SondowSourceCompilerInterface.projectProofCodeCertificateAtOfSource
#check Month2SondowSourceCompilerInterface.sourceComponentsOfFullCertificate
#check Month2SondowSourceCompilerInterface.projectProofCodeCertificateAtOfFullCertificate
#check Month2SondowSourceCompilerInterface.componentCertificateOfSource
#check Month2SondowSourceCompilerInterface.componentCertificateOfSource_valid
#check Month2SondowSourceCompilerInterface.componentCertificateOfFullCertificate
#check Month2SondowSourceCompilerInterface.componentCertificateOfFullCertificate_valid
#check Month2SondowSourceCompilerInterface.component_fields_of_rationality
#check Month2SondowSourceCompilerInterface.public_construction_package_of_reproof_payload_spec_rationality_and_root_convention
#check Month2SondowSourceCompilerInterface.public_construction_package_of_reproof_bridge_package_rationality_and_root_convention
#check Month2SondowSourceCompilerInterface.verifier_closure_package_of_reproof_payload_spec_rationality_kernel_checker_root_convention
#check Month2SondowSourceCompilerInterface.verifier_closure_package_of_reproof_bridge_package_rationality_kernel_checker_root_convention
#check Month2SondowAcceptedAuditorBoundary
#check Month2SondowAcceptedAuditorBoundary.forward_reproof_boundary
#check Month2SondowAcceptedAuditorBoundary.forward_inputs_closed_by_reproof
#check Month2SondowAcceptedAuditorBoundary.accepted_eventually_of_rationality
#check Month2SondowAcceptedAuditorBoundary.source_certificates_valid
#check Month2SondowAcceptedAuditorBoundary.componentCertificateOfSource
#check Month2SondowAcceptedAuditorBoundary.componentCertificateOfSource_valid
#check Month2SondowAcceptedAuditorBoundary.componentCertificateOfFullCertificate
#check Month2SondowAcceptedAuditorBoundary.componentCertificateOfFullCertificate_valid
#check Month2SondowAcceptedAuditorBoundary.sourceComponentsOfFullCertificate
#check Month2SondowAcceptedAuditorBoundary.projectProofCodeCertificateAtOfFullCertificate
#check Month2SondowAcceptedAuditorBoundary.component_fields_of_rationality
#check Month2SondowAcceptedAuditorBoundary.component_threshold_of_rationality
#check Month2SondowAcceptedAuditorBoundary.product_exists_after_component_threshold_of_rationality
#check Month2SondowAcceptedAuditorBoundary.log_exists_after_component_threshold_of_rationality
#check Month2SondowAcceptedAuditorBoundary.decomposition_exists_after_component_threshold_of_rationality
#check Month2SondowAcceptedAuditorBoundary.threePow_exists_after_component_threshold_of_rationality
#check Month2SondowAcceptedAuditorBoundary.payload_exists_after_component_threshold_of_rationality
#check Month2SondowAcceptedAuditorBoundary.audit_threshold_of_rationality
#check Month2SondowAcceptedAuditorBoundary.accepted_after_audit_threshold_of_rationality
#check Month2SondowAcceptedAuditorBoundary.root_accepted_after_audit_threshold_of_rationality
#check Month2SondowAcceptedAuditorBoundary.product_exists_after_audit_threshold_of_rationality
#check Month2SondowAcceptedAuditorBoundary.log_exists_after_audit_threshold_of_rationality
#check Month2SondowAcceptedAuditorBoundary.decomposition_exists_after_audit_threshold_of_rationality
#check Month2SondowAcceptedAuditorBoundary.threePow_exists_after_audit_threshold_of_rationality
#check Month2SondowAcceptedAuditorBoundary.payload_exists_after_audit_threshold_of_rationality
#check Month2SondowAcceptedAuditorBoundary.public_construction_package_of_rationality
#check Month2SondowAcceptedAuditorBoundary.verifier_closure_package_of_rationality
#check Month2SondowAcceptedAuditorBoundary.accepted_threshold_of_rationality
#check Month2SondowAcceptedAuditorBoundary.root_accepted_after_of_rationality
#check Month2SondowAcceptedAuditorBoundary.collapse_conclusion_of_rationality
#check Month2SondowAcceptedAuditThresholdPackage
#check Month2SondowAcceptedAuditThresholdPackage.audit_threshold
#check Month2SondowAcceptedAuditThresholdPackage.accepted_after
#check Month2SondowAcceptedAuditThresholdPackage.root_accepted_after
#check Month2SondowAcceptedAuditThresholdPackage.product_exists_after
#check Month2SondowAcceptedAuditThresholdPackage.log_exists_after
#check Month2SondowAcceptedAuditThresholdPackage.decomposition_exists_after
#check Month2SondowAcceptedAuditThresholdPackage.threePow_exists_after
#check Month2SondowAcceptedAuditThresholdPackage.payload_exists_after
#check Month2SondowAcceptedAuditThresholdPackage.accepted_eventually
#check Month2SondowAcceptedAuditThresholdPackage.root_accepted_eventually
#check Month2SondowAcceptedAuditThresholdPackage.component_eventual
#check Month2SondowAcceptedAuditThresholdPackage.component_eventual_nonempty
#check Month2SondowAcceptedAuditThresholdPackage.system_eventual
#check Month2SondowAcceptedAuditThresholdPackage.system_eventual_nonempty
#check Month2SondowAcceptedAuditThresholdPackage.semantic_eventual
#check Month2SondowAcceptedAuditThresholdPackage.semantic_eventual_nonempty
#check Month2SondowAcceptedAuditThresholdPackage.construction_layer
#check Month2SondowAcceptedAuditThresholdPackage.sondow_accepted_of_root_accepted
#check Month2SondowAcceptedAuditThresholdPackage.full_certificate_of_root_accepted
#check Month2SondowAcceptedAuditThresholdPackage.full_certificate_after
#check Month2SondowAcceptedAuditThresholdPackage.CompiledSourceCertificateAt
#check Month2SondowAcceptedAuditThresholdPackage.projectProofCodeCertificateAtAfter
#check Month2SondowAcceptedAuditThresholdPackage.componentCertificateOfAcceptedAfter_valid
#check Month2SondowAcceptedAuditThresholdPackage.public_construction
#check Month2SondowAcceptedAuditThresholdPackage.verifier_closure
#check Month2SondowAcceptedAuditThresholdPackage.collapse_conclusion
#check Month2SondowAcceptedExternalAnalyticInputs
#check Month2SondowAcceptedExternalAnalyticInputs.boundary
#check Month2SondowAcceptedExternalAnalyticInputs.audit_package
#check Month2SondowAcceptedExternalAnalyticInputs.forward_inputs_closed_by_reproof
#check Month2SondowAcceptedExternalAnalyticInputs.accepted_eventually
#check Month2SondowAcceptedExternalAnalyticInputs.component_fields
#check Month2SondowAcceptedExternalAnalyticInputs.audit_threshold
#check Month2SondowAcceptedExternalAnalyticInputs.accepted_after_audit_threshold
#check Month2SondowAcceptedExternalAnalyticInputs.root_accepted_eventually
#check Month2SondowAcceptedExternalAnalyticInputs.full_certificate_checks_iff_source_components
#check Month2SondowAcceptedExternalAnalyticInputs.compiled_source_certificate_after
#check Month2SondowAcceptedExternalAnalyticInputs.component_certificate_after_valid
#check Month2SondowAcceptedExternalAnalyticInputs.public_construction
#check Month2SondowAcceptedExternalAnalyticInputs.verifier_closure
#check Month2SondowAcceptedExternalAnalyticInputs.component_eventual
#check Month2SondowAcceptedExternalAnalyticInputs.component_eventual_nonempty
#check Month2SondowAcceptedExternalAnalyticInputs.system_eventual_nonempty
#check Month2SondowAcceptedExternalAnalyticInputs.semantic_eventual_nonempty
#check Month2SondowAcceptedExternalAnalyticInputs.collapse_conclusion
#check Month2SondowAcceptedLeanClosedAnalyticSurface
#check Month2SondowAcceptedExternalAnalyticInputs.lean_closed_surface
#check Month2SondowAcceptedLeanClosedAnalyticSurface.audit_threshold
#check Month2SondowAcceptedLeanClosedAnalyticSurface.accepted_after
#check Month2SondowAcceptedLeanClosedAnalyticSurface.root_accepted_after
#check Month2SondowAcceptedLeanClosedAnalyticSurface.full_certificate_after
#check Month2SondowAcceptedLeanClosedAnalyticSurface.compiled_source_certificate_after
#check Month2SondowAcceptedLeanClosedAnalyticSurface.component_certificate_after_valid
#check Month2SondowAcceptedLeanClosedAnalyticSurface.product_exists_after
#check Month2SondowAcceptedLeanClosedAnalyticSurface.log_exists_after
#check Month2SondowAcceptedLeanClosedAnalyticSurface.decomposition_exists_after
#check Month2SondowAcceptedLeanClosedAnalyticSurface.threePow_exists_after
#check Month2SondowAcceptedLeanClosedAnalyticSurface.payload_exists_after
#check Month2SondowAcceptedLeanClosedAnalyticSurface.collapse_conclusion
#check Month2SondowAcceptedLeanClosedAnalyticSurface.collapse_conclusion_from_audit
#check Month2SondowAcceptedCompiledCertificateAt
#check Month2SondowAcceptedCompiledCertificateAt.of_surface_after
#check Month2SondowAcceptedPaperTheoremSurface
#check Month2SondowAcceptedPaperTheoremSurface.inputs
#check Month2SondowAcceptedPaperTheoremSurface.audit_package
#check Month2SondowAcceptedPaperTheoremSurface.audit_threshold
#check Month2SondowAcceptedPaperTheoremSurface.accepted_eventually
#check Month2SondowAcceptedPaperTheoremSurface.root_accepted_eventually
#check Month2SondowAcceptedPaperTheoremSurface.accepted_after
#check Month2SondowAcceptedPaperTheoremSurface.root_accepted_after
#check Month2SondowAcceptedPaperTheoremSurface.full_certificate_after
#check Month2SondowAcceptedPaperTheoremSurface.compiled_certificate_after
#check Month2SondowAcceptedPaperTheoremSurface.full_certificate_eventually
#check Month2SondowAcceptedPaperTheoremSurface.compiled_certificate_eventually
#check Month2SondowAcceptedPaperTheoremSurface.full_certificate_checks_iff_source_components
#check Month2SondowAcceptedPaperTheoremSurface.component_eventual_nonempty
#check Month2SondowAcceptedPaperTheoremSurface.system_eventual_nonempty
#check Month2SondowAcceptedPaperTheoremSurface.semantic_eventual_nonempty
#check Month2SondowAcceptedPaperTheoremSurface.collapse_conclusion
#check Month2SondowAcceptedExternalAnalyticInputs.paper_theorem_surface
#check Month2SondowAcceptedProjectAuditChecklist
#check Month2SondowAcceptedProjectAuditChecklist.of_external_inputs
#check Month2SondowAcceptedProjectAuditChecklist.audit_threshold
#check Month2SondowAcceptedProjectAuditChecklist.accepted_after
#check Month2SondowAcceptedProjectAuditChecklist.root_accepted_after
#check Month2SondowAcceptedProjectAuditChecklist.full_certificate_after
#check Month2SondowAcceptedProjectAuditChecklist.compiled_certificate_after
#check Month2SondowAcceptedProjectAuditChecklist.full_certificate_eventually
#check Month2SondowAcceptedProjectAuditChecklist.compiled_certificate_eventually
#check Month2SondowAcceptedProjectAuditChecklist.component_certificate_after_valid
#check Month2SondowAcceptedPublicRationalityTheorem.external_inputs
#check Month2SondowAcceptedPublicRationalityTheorem.paper_surface
#check Month2SondowAcceptedPublicRationalityTheorem.audit_checklist
#check Month2SondowAcceptedPublicRationalityTheorem.audit_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.accepted_eventually
#check Month2SondowAcceptedPublicRationalityTheorem.root_accepted_eventually
#check Month2SondowAcceptedPublicRationalityTheorem.source_equivalence
#check Month2SondowAcceptedPublicRationalityTheorem.accepted_after
#check Month2SondowAcceptedPublicRationalityTheorem.full_certificate_after
#check Month2SondowAcceptedPublicRationalityTheorem.compiled_certificate_after
#check Month2SondowAcceptedPublicRationalityTheorem.full_certificate_eventually
#check Month2SondowAcceptedPublicRationalityTheorem.compiled_certificate_eventually
#check Month2SondowAcceptedPublicRationalityTheorem.component_certificate_after_valid
#check Month2SondowAcceptedPublicRationalityTheorem.source_interface_of_compilers
#check Month2SondowAcceptedPublicRationalityTheorem.audit_checklist_of_compilers
#check Month2SondowAcceptedPublicRationalityTheorem.audit_threshold_of_compilers
#check Month2SondowAcceptedPublicRationalityTheorem.accepted_eventually_of_compilers
#check Month2SondowAcceptedPublicRationalityTheorem.root_accepted_eventually_of_compilers
#check Month2SondowAcceptedPublicRationalityTheorem.source_equivalence_of_compilers
#check Month2SondowAcceptedPublicRationalityTheorem.accepted_after_compiler_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.root_accepted_after_compiler_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.full_certificate_after_compiler_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.full_certificate_eventually_of_compilers
#check Month2SondowAcceptedPublicRationalityTheorem.compiled_certificate_after_compiler_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.compiled_certificate_eventually_of_compilers
#check Month2SondowAcceptedPublicRationalityTheorem.component_certificate_after_valid_compiler_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.source_interface
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.external_inputs
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.paper_surface
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.audit_checklist
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.audit_checklist_eq_long_form
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.audit_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.audit_threshold_eq_long_form
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.accepted_eventually
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.root_accepted_eventually
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.source_equivalence
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.accepted_after
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.root_accepted_after
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.full_certificate_after
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.compiled_certificate_after
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.full_certificate_eventually
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.compiled_certificate_eventually
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.component_certificate_after_valid
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.collapse_conclusion
#check Month2SondowAcceptedPublicRationalityTheorem.PaperReadyTheoremStatement
#check Month2SondowAcceptedPublicRationalityTheorem.PaperReadyTheoremPackage
#check Month2SondowAcceptedPublicRationalityTheorem.PaperReadyTheoremPackage.of_inputs
#check Month2SondowAcceptedPublicRationalityTheorem.PaperReadyTheoremPackage.audit_checklist_eq_long_form
#check Month2SondowAcceptedPublicRationalityTheorem.PaperReadyTheoremPackage.audit_threshold_eq_long_form
#check Month2SondowAcceptedPublicRationalityTheorem.PaperReadyTheoremPackage.statement
#check Month2SondowAcceptedPublicRationalityTheorem.PaperReadyTheoremPackage.statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PaperReadyTheoremPackage.package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.ExternalLeanClosedBoundaryStatement
#check Month2SondowAcceptedPublicRationalityTheorem.ExternalLeanClosedBoundaryPackage
#check Month2SondowAcceptedPublicRationalityTheorem.ExternalLeanClosedBoundaryPackage.of_inputs
#check Month2SondowAcceptedPublicRationalityTheorem.ExternalLeanClosedBoundaryPackage.statement
#check Month2SondowAcceptedPublicRationalityTheorem.ExternalLeanClosedBoundaryPackage.statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.ExternalLeanClosedBoundaryPackage.package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.ExternalAnalyticAssumptionLedger
#check Month2SondowAcceptedPublicRationalityTheorem.ExternalAnalyticAssumptionLedger.to_public_inputs
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.assumption_ledger
#check Month2SondowAcceptedPublicRationalityTheorem.PublicCompilerInputs.assumption_ledger_to_public_inputs
#check Month2SondowAcceptedPublicRationalityTheorem.NoHiddenAssumptionsStatement
#check Month2SondowAcceptedPublicRationalityTheorem.NoHiddenAssumptionsPackage
#check Month2SondowAcceptedPublicRationalityTheorem.NoHiddenAssumptionsPackage.of_inputs
#check Month2SondowAcceptedPublicRationalityTheorem.NoHiddenAssumptionsPackage.statement
#check Month2SondowAcceptedPublicRationalityTheorem.NoHiddenAssumptionsPackage.statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.NoHiddenAssumptionsPackage.package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.with_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.paper_ready_package_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.paper_ready_statement_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.boundary_statement_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.no_hidden_assumptions_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.no_hidden_assumptions_package_nonempty_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.source_equivalence_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.accepted_eventually_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.root_accepted_eventually_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.full_certificate_eventually_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.compiled_certificate_eventually_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.accepted_after_rationality_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.root_accepted_after_rationality_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.compiled_certificate_after_rationality_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.ComponentConsumptionStatement
#check Month2SondowAcceptedPublicRationalityTheorem.ComponentConsumptionPackage
#check Month2SondowAcceptedPublicRationalityTheorem.ComponentConsumptionPackage.of_inputs
#check Month2SondowAcceptedPublicRationalityTheorem.ComponentConsumptionPackage.statement
#check Month2SondowAcceptedPublicRationalityTheorem.ComponentConsumptionPackage.statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.ComponentConsumptionPackage.package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.component_consumption_statement_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.component_consumption_package_nonempty_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.component_certificate_after_valid_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.component_eventual_nonempty_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.AnalyticBoundaryClassificationStatement
#check Month2SondowAcceptedPublicRationalityTheorem.AnalyticBoundaryClassificationPackage
#check Month2SondowAcceptedPublicRationalityTheorem.AnalyticBoundaryClassificationPackage.of_inputs
#check Month2SondowAcceptedPublicRationalityTheorem.AnalyticBoundaryClassificationPackage.statement
#check Month2SondowAcceptedPublicRationalityTheorem.AnalyticBoundaryClassificationPackage.statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.AnalyticBoundaryClassificationPackage.package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.analytic_boundary_classification_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.analytic_boundary_classification_package_nonempty_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.ComponentFamilyConsumptionStatement
#check Month2SondowAcceptedPublicRationalityTheorem.ComponentFamilyConsumptionPackage
#check Month2SondowAcceptedPublicRationalityTheorem.ComponentFamilyConsumptionPackage.of_inputs
#check Month2SondowAcceptedPublicRationalityTheorem.ComponentFamilyConsumptionPackage.statement
#check Month2SondowAcceptedPublicRationalityTheorem.ComponentFamilyConsumptionPackage.statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.ComponentFamilyConsumptionPackage.package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.component_family_consumption_statement_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.component_family_consumption_package_nonempty_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.product_exists_after_rationality_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.log_exists_after_rationality_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.decomposition_exists_after_rationality_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.threePow_exists_after_rationality_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.payload_exists_after_rationality_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.AcceptedCertificateCompilerSurfaceStatement
#check Month2SondowAcceptedPublicRationalityTheorem.AcceptedCertificateCompilerSurfacePackage
#check Month2SondowAcceptedPublicRationalityTheorem.AcceptedCertificateCompilerSurfacePackage.of_inputs
#check Month2SondowAcceptedPublicRationalityTheorem.AcceptedCertificateCompilerSurfacePackage.statement
#check Month2SondowAcceptedPublicRationalityTheorem.AcceptedCertificateCompilerSurfacePackage.statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.AcceptedCertificateCompilerSurfacePackage.package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.accepted_certificate_compiler_surface_statement_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.accepted_certificate_compiler_surface_package_nonempty_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.full_certificate_after_rationality_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PaperTheoremBundleStatement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PaperTheoremBundlePackage
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PaperTheoremBundlePackage.of_inputs
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PaperTheoremBundlePackage.statement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PaperTheoremBundlePackage.statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PaperTheoremBundlePackage.package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_paper_theorem_bundle_statement_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_paper_theorem_bundle_package_nonempty_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2RationalityFinalPublicTheoremStatement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2RationalityFinalPublicTheoremPackage
#check Month2SondowAcceptedPublicRationalityTheorem.Month2RationalityFinalPublicTheoremPackage.of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2RationalityFinalPublicTheoremPackage.statement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2RationalityFinalPublicTheoremPackage.statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2RationalityFinalPublicTheoremPackage.package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_rationality_final_public_theorem_statement
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_rationality_final_public_theorem_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2RationalityAuditorChecklistStatement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2RationalityAuditorChecklistPackage
#check Month2SondowAcceptedPublicRationalityTheorem.Month2RationalityAuditorChecklistPackage.of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2RationalityAuditorChecklistPackage.statement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2RationalityAuditorChecklistPackage.statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2RationalityAuditorChecklistPackage.package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_rationality_auditor_checklist_statement
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_rationality_auditor_checklist_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PaperFacingAuditBoundaryStatement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PaperFacingAuditBoundaryPackage
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PaperFacingAuditBoundaryPackage.of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PaperFacingAuditBoundaryPackage.statement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PaperFacingAuditBoundaryPackage.statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PaperFacingAuditBoundaryPackage.audit_checklist_eq_long_form_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PaperFacingAuditBoundaryPackage.audit_threshold_eq_long_form_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PaperFacingAuditBoundaryPackage.paper_bundle_statement_iff_package_nonempty_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PaperFacingAuditBoundaryPackage.final_public_theorem_statement_iff_package_nonempty_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PaperFacingAuditBoundaryPackage.auditor_checklist_statement_iff_package_nonempty_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PaperFacingAuditBoundaryPackage.package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_paper_facing_audit_boundary_statement
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_paper_facing_audit_boundary_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2CompilerConsumptionPaperSurfaceStatement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2CompilerConsumptionPaperSurfacePackage
#check Month2SondowAcceptedPublicRationalityTheorem.Month2CompilerConsumptionPaperSurfacePackage.of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2CompilerConsumptionPaperSurfacePackage.statement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2CompilerConsumptionPaperSurfacePackage.statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2CompilerConsumptionPaperSurfacePackage.package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2CompilerConsumptionPaperSurfacePackage.source_components_after_threshold_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2CompilerConsumptionPaperSurfacePackage.compiled_certificate_after_threshold_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2CompilerConsumptionPaperSurfacePackage.component_certificate_after_valid_threshold_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2CompilerConsumptionPaperSurfacePackage.compiler_consumption_after_threshold_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_compiler_consumption_paper_surface_statement
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_compiler_consumption_paper_surface_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.compiler_consumption_source_components_after_rationality_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.compiler_consumption_compiled_certificate_after_rationality_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.compiler_consumption_after_rationality_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AnalyticBoundaryPaperSurfaceStatement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AnalyticBoundaryPaperSurfacePackage
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AnalyticBoundaryPaperSurfacePackage.of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AnalyticBoundaryPaperSurfacePackage.statement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AnalyticBoundaryPaperSurfacePackage.statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AnalyticBoundaryPaperSurfacePackage.package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AnalyticBoundaryPaperSurfacePackage.lean_closed_surface_eq_paper_surface_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AnalyticBoundaryPaperSurfacePackage.external_forward_reproof_boundary_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AnalyticBoundaryPaperSurfacePackage.compiled_certificate_eventually_lean_closed_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_analytic_boundary_paper_surface_statement
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_analytic_boundary_paper_surface_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.analytic_boundary_lean_closed_surface_eq_paper_surface
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.analytic_boundary_external_forward_reproof_boundary
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.analytic_boundary_compiled_certificate_eventually_lean_closed
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AcceptedCertificateMasterTheoremStatement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AcceptedCertificateMasterTheoremPackage
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AcceptedCertificateMasterTheoremPackage.of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AcceptedCertificateMasterTheoremPackage.statement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AcceptedCertificateMasterTheoremPackage.statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AcceptedCertificateMasterTheoremPackage.package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AcceptedCertificateMasterTheoremPackage.accepted_eventually_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AcceptedCertificateMasterTheoremPackage.root_accepted_eventually_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AcceptedCertificateMasterTheoremPackage.compiled_certificate_after_threshold_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2AcceptedCertificateMasterTheoremPackage.compiler_consumption_after_threshold_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_accepted_certificate_master_theorem_statement
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_accepted_certificate_master_theorem_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.accepted_certificate_master_accepted_eventually_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.accepted_certificate_master_root_accepted_eventually_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.accepted_certificate_master_compiled_certificate_after_rationality_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.accepted_certificate_master_compiler_consumption_after_rationality_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.Month2OpenSourceReleaseSurfaceStatement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2OpenSourceReleaseSurfacePackage
#check Month2SondowAcceptedPublicRationalityTheorem.Month2OpenSourceReleaseSurfacePackage.of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2OpenSourceReleaseSurfacePackage.statement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2OpenSourceReleaseSurfacePackage.statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2OpenSourceReleaseSurfacePackage.package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2OpenSourceReleaseSurfacePackage.audit_threshold_eq_long_form_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2OpenSourceReleaseSurfacePackage.accepted_eventually_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2OpenSourceReleaseSurfacePackage.compiler_consumption_after_threshold_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_open_source_release_surface_statement
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_open_source_release_surface_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.open_source_release_audit_threshold_eq_long_form
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.open_source_release_accepted_eventually_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.open_source_release_compiler_consumption_after_rationality_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PublicCitationAuditChecklistStatement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PublicCitationAuditChecklistPackage
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PublicCitationAuditChecklistPackage.of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PublicCitationAuditChecklistPackage.statement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PublicCitationAuditChecklistPackage.statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PublicCitationAuditChecklistPackage.package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PublicCitationAuditChecklistPackage.accepted_definition_exact_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PublicCitationAuditChecklistPackage.release_surface_statement_iff_package_nonempty_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.Month2PublicCitationAuditChecklistPackage.compiler_consumption_after_threshold_of_rationality
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_public_citation_audit_checklist_statement
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_public_citation_audit_checklist_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.public_citation_accepted_definition_exact
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.public_citation_release_surface_statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.public_citation_compiler_consumption_after_rationality_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.public_inputs
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.citation_statement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.release_surface_statement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.citation_package
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.release_surface_package
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.citation_statement_of_inputs
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.citation_statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.citation_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.release_surface_statement_of_inputs
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.release_surface_statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.accepted_definition_exact
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.accepted_eventually
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.root_accepted_eventually
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.no_hidden_assumptions
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.compiler_consumption_after_threshold
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseTheoremStatement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseTheoremPackage
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseTheoremPackage.of_inputs
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseTheoremPackage.statement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseTheoremPackage.statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseTheoremPackage.package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseTheoremPackage.accepted_eventually
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseTheoremPackage.compiler_consumption_after_threshold_of_statement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.verified_public_release_theorem_statement
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.verified_public_release_theorem_statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.Month2VerifiedPublicReleaseInputs.verified_public_release_theorem_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.verified_public_release_inputs
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_verified_public_release_theorem_statement
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_verified_public_release_theorem_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.month2_verified_public_release_theorem_statement_iff_package_nonempty
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.verified_public_release_accepted_definition_exact
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.verified_public_release_source_equivalence_same_object
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.verified_public_release_accepted_eventually
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.verified_public_release_root_accepted_eventually
#check Month2SondowAcceptedPublicRationalityTheorem.PublicInfrastructureKit.verified_public_release_compiler_consumption_after_rationality_threshold

end SondowProjectMonth2SondowAcceptedCertificateSurface
end SondowMainCheckedCodeBridge
