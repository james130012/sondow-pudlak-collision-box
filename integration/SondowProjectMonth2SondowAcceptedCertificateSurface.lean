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
#check Month2SondowAcceptedCertificateConstructionLayer.system_eventual
#check Month2SondowAcceptedCertificateConstructionLayer.semantic_eventual
#check Month2SondowAcceptedCertificateConstructionLayer.recognition_split
#check Month2SondowAcceptedCertificateConstructionLayer.checked_code_witness
#check component_eventual_of_rationality_project_proof_objects
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
