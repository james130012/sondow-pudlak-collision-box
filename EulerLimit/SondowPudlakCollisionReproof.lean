/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.SondowShortProofReproof
import EulerLimit.PudlakFormulaCode

/-!
# Sondow reproof to Pudlak collision adapters

This module fixes the common proof-length box for the reproved Sondow forward
route and the Pudlak lower-bound route:

`proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
  (sondowReflectionGraftCode n)`.

It does not discharge the bounded-arithmetic verification package, the Pudlak
lower-bound package, or the proof-length transfer/projection package.  Its role
is to make the shared Lean statement explicit and reusable.
-/

noncomputable section

/-- The common reflection-graft proof-length box used by both the short-proof
upper bound and the Pudlak lower bound. -/
abbrev reflectionGraftPudlakBox (n : ℕ) : ℝ :=
  proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
    (sondowReflectionGraftCode n)

/-- After the Sondow forward reproof, a collapse verification package gives the
short-proof side exactly on the reflection-graft Pudlak box. -/
def SondowCollapseVerificationBridgePackage.toReflectionGraftShortVerificationOfReproof
    (h : SondowCollapseVerificationBridgePackage) :
    EventualShortVerificationBridge ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  (h.toReflectionGraftCollapseInputsOfReproof).toEventualShortVerificationBridge

/-- Box-level short-proof statement exposed without reintroducing the Sondow
forward package as an assumption. -/
theorem SondowCollapseVerificationBridgePackage.shortProofBoxOfReproof
    (h : SondowCollapseVerificationBridgePackage) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (sondowReflectionGraftCode n) →
        reflectionGraftPudlakBox n ≤ f n :=
  h.toReflectionGraftShortVerificationOfReproof.short_proofs_of_accepted_certificates

/-- The Pudlak finite-consistency package gives the lower-bound side on the
same reflection-graft box once the partial-consistency lower bound is
transferred to the graft formula family. -/
theorem PudlakFiniteConsistencyLowerBoundPackage.reflectionGraftLowerBoundBox_of_transfer
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  h.eventualReflectionGraftLowerBound_of_transfer htransfer

/-- Projection is the zero-overhead special case of the transfer route. -/
theorem PudlakFiniteConsistencyLowerBoundPackage.reflectionGraftLowerBoundBox_of_projection
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hprojection : PartialConsistencyToReflectionGraftProjection) :
    EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  h.eventualReflectionGraftLowerBound_of_projection hprojection

/-- Inputs for the audited reflection-graft collision after the Sondow forward
package has been internally reproved.  Every field is a remaining external
proof-complexity input, while the formula family, system, and measure are fixed
by the target statement. -/
structure ReflectionGraftPudlakCollisionInputsOfReproof where
  collapse_verification : SondowCollapseVerificationBridgePackage
  pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage
  transfer_to_graft : PartialConsistencyToReflectionGraftLowerBoundTransfer

/-- The boxed model inputs: both sides talk about
`proof_length PA symbolSize (sondowReflectionGraftCode n)`. -/
def ReflectionGraftPudlakCollisionInputsOfReproof.toEventualReflectionGraftModelInputs
    (h : ReflectionGraftPudlakCollisionInputsOfReproof) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode where
  certificate_collapse :=
    h.collapse_verification.toReflectionGraftCollapseInputsOfReproof
  short_verification :=
    h.collapse_verification.toReflectionGraftShortVerificationOfReproof
  graft_lower_bound :=
    h.pudlak_lower_bound.reflectionGraftLowerBoundBox_of_transfer
      h.transfer_to_graft

/-- Collision endpoint with the Sondow forward package closed by reproof and
the remaining lower-bound movement supplied as a transfer. -/
theorem irrational_of_reproof_verified_collapse_pudlak_package_and_transfer
    (hverify : SondowCollapseVerificationBridgePackage)
    (hpudlak : PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_eventual_reflection_graft_model_inputs
    (({ collapse_verification := hverify
        pudlak_lower_bound := hpudlak
        transfer_to_graft := htransfer } :
      ReflectionGraftPudlakCollisionInputsOfReproof)
        |>.toEventualReflectionGraftModelInputs)

/-- Collision endpoint for the common projection route. -/
theorem irrational_of_reproof_verified_collapse_pudlak_package_and_projection
    (hverify : SondowCollapseVerificationBridgePackage)
    (hpudlak : PudlakFiniteConsistencyLowerBoundPackage)
    (hprojection : PartialConsistencyToReflectionGraftProjection) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_reproof_verified_collapse_pudlak_package_and_transfer
    hverify hpudlak
    (partial_consistency_to_reflection_graft_transfer hprojection)

/-- Collision endpoint when the projection is supplied by the general
proof-length projection principle. -/
theorem irrational_of_reproof_verified_collapse_pudlak_package_and_projection_principle
    (hverify : SondowCollapseVerificationBridgePackage)
    (hpudlak : PudlakFiniteConsistencyLowerBoundPackage)
    (hprinciple : PAProofLengthProjectionPrinciple) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_reproof_verified_collapse_pudlak_package_and_projection
    hverify hpudlak
    (partial_consistency_to_reflection_graft_projection_of_principle hprinciple)

end
