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

theorem collapse_conclusion
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (layer : Month2SondowAcceptedCLineClosureLayer.{u} bounds) :
    SondowProjectLocalS21CollapseConclusion :=
  sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
    (layer.minimal_closure)

end Month2SondowAcceptedCLineClosureLayer

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
#check Month2SondowAcceptedCertificateConstructionLayer.system_eventual
#check Month2SondowAcceptedCertificateConstructionLayer.semantic_eventual
#check Month2SondowAcceptedCertificateConstructionLayer.recognition_split
#check Month2SondowAcceptedCertificateConstructionLayer.checked_code_witness
#check component_eventual_of_rationality_project_proof_objects
#check construction_layer_of_component_fields_and_root_convention
#check construction_layer_of_main_eventual_compiler_rationality_and_root_convention
#check construction_layer_of_main_full_compiler_rationality_and_root_convention
#check construction_layer_of_source_component_compilers_rationality_and_root_convention
#check semantic_eventual_of_rationality_project_proof_objects
#check semantic_eventual_upper_bound_of_main_eventual_compiler
#check Month2SondowAcceptedCLineClosureLayer
#check Month2SondowAcceptedCLineClosureLayer.minimal_closure
#check Month2SondowAcceptedCLineClosureLayer.concrete_checked_code_certificate
#check Month2SondowAcceptedCLineClosureLayer.verifier
#check Month2SondowAcceptedCLineClosureLayer.payload_truth
#check Month2SondowAcceptedCLineClosureLayer.collapse_conclusion

end SondowProjectMonth2SondowAcceptedCertificateSurface
end SondowMainCheckedCodeBridge
