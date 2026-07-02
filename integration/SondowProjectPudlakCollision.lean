/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectS21Kernel
import EulerLimit.PudlakFormulaCode

/-!
# Project-local S21 upper bound to Pudlak collision

This module keeps the final collision step narrow.  The upper side is the
project-local S21 collapse conclusion:

`is_rational euler_mascheroni -> eventual polynomial PA short proofs for
  sondowReflectionGraftCode`.

The lower side is the Pudlak finite-consistency lower bound after transfer to
the same reflection-graft family.  No truth payload is silently converted into a
short proof here; the only bridge used is the explicit project-local upper
bound.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge

/-- The shared proof-length box for the project-local upper route and the
Pudlak lower route. -/
abbrev sondowProjectLocalPudlakCollisionBox (n : ℕ) : ℝ :=
  _root_.proof_length _root_.ProofSystem.PA
    _root_.ProofLengthMeasure.symbolSize
    (_root_.sondowReflectionGraftCode n)

/-- Audited inputs for the final project-local collision.  The upper route is
already the direct `SondowProjectLocalS21CollapseConclusion`; the lower route is
still the external Pudlak finite-consistency theorem plus an explicit transfer
from the partial-consistency family to the graft family. -/
structure SondowProjectLocalPudlakCollisionInputs where
  project_upper : SondowProjectLocalS21CollapseConclusion
  pudlak_lower_bound : _root_.PudlakFiniteConsistencyLowerBoundPackage
  transfer_to_graft : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer

namespace SondowProjectLocalPudlakCollisionInputs

/-- The Pudlak lower bound, moved to the same graft family as the project-local
upper bound. -/
def graftLowerBound
    (h : SondowProjectLocalPudlakCollisionInputs) :
    _root_.EventualLowerBound _root_.ProofSystem.PA
      _root_.ProofLengthMeasure.symbolSize _root_.sondowReflectionGraftCode :=
  h.pudlak_lower_bound.eventualReflectionGraftLowerBound_of_transfer
    h.transfer_to_graft

/-- Final collision: the project-local upper bound and the transferred Pudlak
lower bound cannot both hold under rationality of `gamma`. -/
theorem not_rational
    (h : SondowProjectLocalPudlakCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  intro hrat
  rcases h.project_upper hrat with ⟨f, hf_poly, N, hupper⟩
  rcases h.graftLowerBound.lower_bound f hf_poly N with
    ⟨n, hn_ge, hlower⟩
  rcases hupper n hn_ge with ⟨_haccepted, hle⟩
  linarith

/-- Build collision inputs from a projection instead of a lower-bound transfer.
This is the common conjunction-elimination route: a short proof of the graft
family would project to a short proof of the partial-consistency family. -/
def ofProjection
    (hupper : SondowProjectLocalS21CollapseConclusion)
    (hpudlak : _root_.PudlakFiniteConsistencyLowerBoundPackage)
    (hprojection : _root_.PartialConsistencyToReflectionGraftProjection) :
    SondowProjectLocalPudlakCollisionInputs where
  project_upper := hupper
  pudlak_lower_bound := hpudlak
  transfer_to_graft :=
    _root_.partial_consistency_to_reflection_graft_transfer hprojection

end SondowProjectLocalPudlakCollisionInputs

theorem irrational_of_project_local_collapse_conclusion_and_pudlak_transfer
    (hupper : SondowProjectLocalS21CollapseConclusion)
    (hpudlak : _root_.PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  ({ project_upper := hupper
     pudlak_lower_bound := hpudlak
     transfer_to_graft := htransfer } :
    SondowProjectLocalPudlakCollisionInputs).not_rational

theorem irrational_of_project_local_collapse_conclusion_and_pudlak_projection
    (hupper : SondowProjectLocalS21CollapseConclusion)
    (hpudlak : _root_.PudlakFiniteConsistencyLowerBoundPackage)
    (hprojection : _root_.PartialConsistencyToReflectionGraftProjection) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  (SondowProjectLocalPudlakCollisionInputs.ofProjection
    hupper hpudlak hprojection).not_rational

theorem irrational_of_project_local_collapse_conclusion_and_pudlak_projection_principle
    (hupper : SondowProjectLocalS21CollapseConclusion)
    (hpudlak : _root_.PudlakFiniteConsistencyLowerBoundPackage)
    (hprinciple : _root_.PAProofLengthProjectionPrinciple) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  irrational_of_project_local_collapse_conclusion_and_pudlak_projection
    hupper hpudlak
    (_root_.partial_consistency_to_reflection_graft_projection_of_principle
      hprinciple)

theorem irrational_of_project_local_verifier_payload_truth_and_pudlak_transfer
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak : _root_.PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  irrational_of_project_local_collapse_conclusion_and_pudlak_transfer
    (verifier.toCollapseConclusion htruth) hpudlak htransfer

theorem irrational_of_project_local_verifier_payload_truth_and_pudlak_projection
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hpudlak : _root_.PudlakFiniteConsistencyLowerBoundPackage)
    (hprojection : _root_.PartialConsistencyToReflectionGraftProjection) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  irrational_of_project_local_collapse_conclusion_and_pudlak_projection
    (verifier.toCollapseConclusion htruth) hpudlak hprojection

theorem verifierAndPayloadTruth_nonempty_to_projectLocalPudlakCollision
    (hupper :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth)
    (hpudlak : _root_.PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases hupper with ⟨⟨verifier⟩, ⟨htruth⟩⟩
  exact irrational_of_project_local_verifier_payload_truth_and_pudlak_transfer
    verifier htruth hpudlak htransfer

theorem directTraceCompletion_to_projectLocalPudlakCollision
    (hcompletion : SondowProjectLocalDirectTraceCollapseCompletion)
    (hpudlak : _root_.PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  irrational_of_project_local_collapse_conclusion_and_pudlak_transfer
    hcompletion.toCollapseConclusion hpudlak htransfer

theorem traceCompletion_to_projectLocalPudlakCollision
    (hcompletion : SondowProjectLocalS21TraceCollapseCompletion)
    (hpudlak : _root_.PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  irrational_of_project_local_collapse_conclusion_and_pudlak_transfer
    hcompletion.toCollapseConclusion hpudlak htransfer

/-- Tail-collision endpoint for the current upper-bound route.  Compared with
`irrational_of_project_local_collapse_conclusion_and_pudlak_transfer`, this
does not require an all-index PA short-proof upper package: the upper side is
assembled from the local S²₁ kernel, the eventual Sondow component compiler,
and the root proof-length convention. -/
theorem irrational_of_project_tailCompiler_rootConvention_kernel_pudlak_transfer
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcollapse :
      _root_.EventualCertificateCollapseInputs
        _root_.sondowReflectionGraftCode)
    (kernel : SondowProjectLocalS21Kernel)
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (hroot : SondowReflectionGraftRootProofLengthConvention)
    (hpudlak : _root_.PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  irrational_of_sondowReflectionGraft_mainEventualCompiler_rootConvention_kernel_tailLowerBound
    hcollapse kernel compiler hroot
    (hpudlak.eventualReflectionGraftLowerBound_of_transfer htransfer)

theorem irrational_of_project_tailCompiler_rootConvention_kernel_pudlak_projection
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcollapse :
      _root_.EventualCertificateCollapseInputs
        _root_.sondowReflectionGraftCode)
    (kernel : SondowProjectLocalS21Kernel)
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (hroot : SondowReflectionGraftRootProofLengthConvention)
    (hpudlak : _root_.PudlakFiniteConsistencyLowerBoundPackage)
    (hprojection : _root_.PartialConsistencyToReflectionGraftProjection) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  irrational_of_project_tailCompiler_rootConvention_kernel_pudlak_transfer
    hcollapse kernel compiler hroot hpudlak
    (_root_.partial_consistency_to_reflection_graft_transfer hprojection)

theorem irrational_of_project_tailCompiler_checkedCodeConventionWitness_kernel_pudlak_transfer
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcollapse :
      _root_.EventualCertificateCollapseInputs
        _root_.sondowReflectionGraftCode)
    (kernel : SondowProjectLocalS21Kernel)
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (hwitness : SondowReflectionGraftRootCheckedCodeConventionWitness)
    (hpudlak : _root_.PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  irrational_of_project_tailCompiler_rootConvention_kernel_pudlak_transfer
    hcollapse kernel compiler hwitness.toRootProofLengthConvention
    hpudlak htransfer

theorem irrational_of_project_tailCompiler_checkedCodeConventionWitness_kernel_pudlak_projection
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcollapse :
      _root_.EventualCertificateCollapseInputs
        _root_.sondowReflectionGraftCode)
    (kernel : SondowProjectLocalS21Kernel)
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (hwitness : SondowReflectionGraftRootCheckedCodeConventionWitness)
    (hpudlak : _root_.PudlakFiniteConsistencyLowerBoundPackage)
    (hprojection : _root_.PartialConsistencyToReflectionGraftProjection) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  irrational_of_project_tailCompiler_checkedCodeConventionWitness_kernel_pudlak_transfer
    hcollapse kernel compiler hwitness hpudlak
    (_root_.partial_consistency_to_reflection_graft_transfer hprojection)

theorem irrational_of_project_tailCompiler_splitRootCalibrations_kernel_pudlak_transfer
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcollapse :
      _root_.EventualCertificateCollapseInputs
        _root_.sondowReflectionGraftCode)
    (kernel : SondowProjectLocalS21Kernel)
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (hs21root : SondowReflectionGraftRootS21ProofLengthCalibration)
    (hparoot : SondowReflectionGraftRootPAProofLengthCalibration)
    (hpudlak : _root_.PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  irrational_of_project_tailCompiler_rootConvention_kernel_pudlak_transfer
    hcollapse kernel compiler
    (SondowReflectionGraftRootProofLengthConvention.ofSplitCalibrations
      hs21root hparoot)
    hpudlak htransfer

end SondowMainCheckedCodeBridge

end
