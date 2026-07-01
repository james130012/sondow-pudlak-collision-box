/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.FormalProofSystem
import BoundedArithmeticLab.VerifierTrace

/-!
# Proof-object simulations

This is the proof-object version of `S21 proof → PA proof with controlled
length`.  It is stronger than a pure proof-length transport: it maps concrete
source proofs to concrete target proofs and proves the mapped proof remains
linearly bounded.
-/

namespace BoundedArithmeticLab

universe u v

structure LinearProofObjectSimulation
    {source target : AbstractProofLengthBox}
    (sourceModel : ProofSystemBoxModel.{u} source)
    (targetModel : ProofSystemBoxModel.{v} target) where
  same_formula : ∀ n : ℕ, source.formula n = target.formula n
  C : ℝ
  D : ℝ
  C_nonneg : 0 ≤ C
  D_nonneg : 0 ≤ D
  mapProof : sourceModel.Proof → targetModel.Proof
  map_proves :
    ∀ {n : ℕ} {p : sourceModel.Proof},
      sourceModel.proves p n → targetModel.proves (mapProof p) n
  map_size_le :
    ∀ p : sourceModel.Proof,
      (targetModel.size (mapProof p) : ℝ) ≤
        C * (sourceModel.size p : ℝ) + D

def LinearProofObjectSimulation.mapBound
    {source target : AbstractProofLengthBox}
    {sourceModel : ProofSystemBoxModel.{u} source}
    {targetModel : ProofSystemBoxModel.{v} target}
    (h : LinearProofObjectSimulation sourceModel targetModel)
    (f : ℕ → ℝ) : ℕ → ℝ :=
  fun n => h.C * f n + h.D

theorem LinearProofObjectSimulation.mapBound_poly
    {source target : AbstractProofLengthBox}
    {sourceModel : ProofSystemBoxModel.{u} source}
    {targetModel : ProofSystemBoxModel.{v} target}
    (h : LinearProofObjectSimulation sourceModel targetModel)
    {f : ℕ → ℝ} (hf : IsPolynomialBound f) :
    IsPolynomialBound (h.mapBound f) :=
  hf.linear_rescale h.C_nonneg h.D_nonneg

def LinearProofObjectSimulation.transportAcceptedProofFamily
    {source target : AbstractProofLengthBox}
    {sourceModel : ProofSystemBoxModel.{u} source}
    {targetModel : ProofSystemBoxModel.{v} target}
    {accepted : ℕ → Prop}
    (h : LinearProofObjectSimulation sourceModel targetModel)
    (hfamily : AcceptedProofFamily sourceModel accepted) :
    AcceptedProofFamily targetModel accepted where
  bound := h.mapBound hfamily.bound
  bound_poly := h.mapBound_poly hfamily.bound_poly
  proof_of_accepted := by
    intro n hn
    rcases hfamily.proof_of_accepted n hn with ⟨p, hp, hsize⟩
    refine ⟨h.mapProof p, h.map_proves hp, ?_⟩
    have hmap := h.map_size_le p
    have hmul :
        h.C * (sourceModel.size p : ℝ) ≤ h.C * hfamily.bound n :=
      mul_le_mul_of_nonneg_left hsize h.C_nonneg
    dsimp [LinearProofObjectSimulation.mapBound]
    linarith

def paShortProofsOfS21TraceRealizationAndObjectSimulation
    {s21Box paBox : AbstractProofLengthBox}
    {s21Model : ProofSystemBoxModel.{u} s21Box}
    {paModel : ProofSystemBoxModel.{v} paBox}
    {accepted : ℕ → Prop}
    (htrace : S21VerifierTraceRealization accepted s21Model)
    (hsim : LinearProofObjectSimulation s21Model paModel) :
    EventualShortProofUpperBound paBox accepted :=
  (hsim.transportAcceptedProofFamily htrace.toAcceptedProofFamily)
    |>.toShortProofUpperBound

abbrev S21ToPAFormalProofObjectSimulation
    (s21 : S21ProofSystemFormalization.{u})
    (pa : PAProofSystemFormalization.{v}) :=
  LinearProofObjectSimulation s21.toBoxModel pa.toBoxModel

def paShortProofsOfFormalS21TraceAndPASimulation
    {s21 : S21ProofSystemFormalization.{u}}
    {pa : PAProofSystemFormalization.{v}}
    {accepted : ℕ → Prop}
    (htrace : S21VerifierTraceRealization accepted s21.toBoxModel)
    (hsim : S21ToPAFormalProofObjectSimulation s21 pa) :
    EventualShortProofUpperBound pa.box accepted :=
  paShortProofsOfS21TraceRealizationAndObjectSimulation htrace hsim

structure ObjectSimulatedCollisionInputs
    {s21Box paBox : AbstractProofLengthBox}
    (s21Model : ProofSystemBoxModel.{u} s21Box)
    (paModel : ProofSystemBoxModel.{v} paBox)
    (accepted : ℕ → Prop) where
  acceptance : EventualAcceptanceUnderRationality accepted
  trace_realization : S21VerifierTraceRealization accepted s21Model
  s21_to_pa : LinearProofObjectSimulation s21Model paModel
  pa_lower : EventualLowerBound paBox

theorem collision_of_s21_trace_object_simulation_and_pa_lower
    {s21Box paBox : AbstractProofLengthBox}
    {s21Model : ProofSystemBoxModel.{u} s21Box}
    {paModel : ProofSystemBoxModel.{v} paBox}
    {accepted : ℕ → Prop}
    (h : ObjectSimulatedCollisionInputs s21Model paModel accepted) :
    False :=
  eventualCollision h.acceptance
    (paShortProofsOfS21TraceRealizationAndObjectSimulation
      h.trace_realization h.s21_to_pa)
    h.pa_lower

end BoundedArithmeticLab
