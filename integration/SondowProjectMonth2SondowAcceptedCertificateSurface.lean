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
#check Month2SondowAcceptedAuditThresholdPackage.public_construction
#check Month2SondowAcceptedAuditThresholdPackage.verifier_closure
#check Month2SondowAcceptedAuditThresholdPackage.collapse_conclusion

end SondowProjectMonth2SondowAcceptedCertificateSurface
end SondowMainCheckedCodeBridge
