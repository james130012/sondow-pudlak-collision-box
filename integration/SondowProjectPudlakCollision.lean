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

/-- Proof-length-free arithmetic collision core: an eventual strict gap
`U n < L n` and an eventual upper bound `L n ≤ U n` cannot hold for the same
measured function `L`.  The project-specific proof-length box is introduced
only when this generic core is instantiated below. -/
theorem genericCollisionCore_from_lower_upper_gap
    {U L : ℕ → ℝ}
    (hgap : _root_.EventualStrictGap U L)
    (N : ℕ)
    (hupper : ∀ n : ℕ, N ≤ n → L n ≤ U n) :
    False := by
  rcases hgap.gap_after N with ⟨n, hn_ge, hlt⟩
  exact (not_lt_of_ge (hupper n hn_ge)) hlt

/-- Proof-length-free rationality collision interface.  The measured function
`L` is abstract: the core theorem only needs rationality to give an eventual
polynomial upper bound for `L`, and the lower side to give a strict eventual
gap against every polynomial upper function on the same `L`. -/
structure GenericRationalCollisionInputs where
  measured : ℕ → ℝ
  upper_under_rationality :
    _root_.is_rational _root_.euler_mascheroni →
      ∃ U : ℕ → ℝ, _root_.is_polynomial_bound U ∧
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → measured n ≤ U n
  gap_for_polynomial_upper :
    ∀ U : ℕ → ℝ, _root_.is_polynomial_bound U →
      _root_.EventualStrictGap U measured

namespace GenericRationalCollisionInputs

/-- Proof-length-free collision theorem.  No PA proof-length box appears in the
statement; project-specific proof-length assumptions enter only when a concrete
`measured` function is instantiated. -/
theorem not_rational
    (h : GenericRationalCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  intro hrat
  rcases h.upper_under_rationality hrat with ⟨U, hU, N, hupper⟩
  exact
    genericCollisionCore_from_lower_upper_gap
      (h.gap_for_polynomial_upper U hU) N hupper

theorem audited_collision_core
    (h : GenericRationalCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.not_rational

theorem contradiction
    (h : GenericRationalCollisionInputs)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.not_rational hrat

end GenericRationalCollisionInputs

/-- The shared proof-length box for the project-local upper route and the
Pudlak lower route. -/
abbrev sondowProjectLocalPudlakCollisionBox (n : ℕ) : ℝ :=
  _root_.proof_length _root_.ProofSystem.PA
    _root_.ProofLengthMeasure.symbolSize
    (_root_.sondowReflectionGraftCode n)

/-- Audit name for the shared measurement box: both the Sondow upper route and
the Pudlak gap route measure the same PA symbol-size proof length. -/
theorem sondowProjectLocalPudlakCollisionBox_eq_proofLength (n : ℕ) :
    sondowProjectLocalPudlakCollisionBox n =
      _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.sondowReflectionGraftCode n) :=
  rfl

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

/-- Audit-facing gap certificate for the shared graft family.  Given the
Sondow-side polynomial upper function, the transferred Pudlak lower bound
returns an explicit eventual strict gap against the same PA symbol-size proof
length. -/
def graftGapCertificate
    (h : SondowProjectLocalPudlakCollisionInputs)
    (U : ℕ → ℝ) (hU : _root_.is_polynomial_bound U) :
    _root_.EventualStrictGap U
      (fun n : ℕ =>
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowReflectionGraftCode n)) :=
  h.pudlak_lower_bound.reflectionGraftGap_of_transfer
    h.transfer_to_graft U hU

/-- Audit-facing upper certificate source.  Under rationality, the project-local
Sondow/S²₁ route produces the polynomial upper function that is fed into the
Pudlak gap certificate. -/
theorem upperBoundUnderRationality
    (h : SondowProjectLocalPudlakCollisionInputs)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ U : ℕ → ℝ, _root_.is_polynomial_bound U ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowReflectionGraftCode n) ≤ U n := by
  rcases h.project_upper hrat with ⟨U, hU_poly, N, hupper⟩
  exact
    ⟨U, hU_poly, N, fun n hn_ge => by
      rcases hupper n hn_ge with ⟨_haccepted, hle⟩
      exact hle⟩

/-- Short audit-facing alias for the Sondow upper side.  This theorem makes
explicit that the upper certificate is conditional on rationality. -/
theorem audited_upper_core
    (h : SondowProjectLocalPudlakCollisionInputs)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ U : ℕ → ℝ, _root_.is_polynomial_bound U ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowReflectionGraftCode n) ≤ U n :=
  h.upperBoundUnderRationality hrat

/-- Audit-facing final Pudlak gap certificate for the project-local collision
box. -/
theorem finalPudlakGapCertificate
    (h : SondowProjectLocalPudlakCollisionInputs)
    (U : ℕ → ℝ) (hU : _root_.is_polynomial_bound U) :
    _root_.EventualStrictGap U
      (fun n : ℕ => sondowProjectLocalPudlakCollisionBox n) :=
  h.graftGapCertificate U hU

/-- Short audit-facing alias for the Pudlak gap side of the shared collision
box. -/
theorem audited_gap_core
    (h : SondowProjectLocalPudlakCollisionInputs)
    (U : ℕ → ℝ) (hU : _root_.is_polynomial_bound U) :
    _root_.EventualStrictGap U
      (fun n : ℕ => sondowProjectLocalPudlakCollisionBox n) :=
  h.finalPudlakGapCertificate U hU

/-- Instantiate the proof-length-free rationality collision skeleton with the
project-local PA symbol-size proof-length box. -/
def toGenericRationalCollisionInputs
    (h : SondowProjectLocalPudlakCollisionInputs) :
    GenericRationalCollisionInputs where
  measured := sondowProjectLocalPudlakCollisionBox
  upper_under_rationality := h.upperBoundUnderRationality
  gap_for_polynomial_upper := h.finalPudlakGapCertificate

/-- Final collision, factored through the explicit gap certificate.  This is
definitionally the same route as `not_rational`, but it exposes the exact
`U n < proof_length ...` witness used to contradict the Sondow upper bound. -/
theorem not_rational_via_gap_certificate
    (h : SondowProjectLocalPudlakCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toGenericRationalCollisionInputs.not_rational

/-- Final collision: the project-local upper bound and the transferred Pudlak
lower bound cannot both hold under rationality of `gamma`. -/
theorem not_rational
    (h : SondowProjectLocalPudlakCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.not_rational_via_gap_certificate

/-- Four-certificate audit entry: Sondow upper, Pudlak gap, shared proof-length
box calibration, and the collision core close the contradiction. -/
theorem not_rational_from_audited_upper_gap_box_collisionCore
    (h : SondowProjectLocalPudlakCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.not_rational_via_gap_certificate

/-- Short audit-facing alias for the final collision core. -/
theorem audited_collision_core
    (h : SondowProjectLocalPudlakCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.not_rational_from_audited_upper_gap_box_collisionCore

/-- Boundary audit: the project-local final theorem is definitionally the
proof-length-free generic collision skeleton after project proof-length
instantiation. -/
theorem not_rational_eq_generic_collision_skeleton
    (h : SondowProjectLocalPudlakCollisionInputs) :
    h.not_rational =
      h.toGenericRationalCollisionInputs.not_rational :=
  rfl

/-- Boundary audit for the named audited endpoint. -/
theorem audited_collision_core_eq_generic_collision_skeleton
    (h : SondowProjectLocalPudlakCollisionInputs) :
    h.audited_collision_core =
      h.toGenericRationalCollisionInputs.not_rational :=
  rfl

/-- Contradiction form of the audited collision core.  This is useful for
auditors who want to see the rationality assumption discharged explicitly. -/
theorem audited_collision_contradiction
    (h : SondowProjectLocalPudlakCollisionInputs)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.audited_collision_core hrat

/-- Curried contradiction form: the audited collision core refutes the
rationality assumption directly. -/
theorem audited_collision_refutes_rationality
    (h : SondowProjectLocalPudlakCollisionInputs) :
    _root_.is_rational _root_.euler_mascheroni → False :=
  fun hrat => h.audited_collision_contradiction hrat

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
