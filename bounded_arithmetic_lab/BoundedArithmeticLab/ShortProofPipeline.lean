/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.ProofObjectSimulation
import BoundedArithmeticLab.BussPudlakSource

/-!
# Short-proof pipeline to the Pudlak lower bound

This file assembles the narrow route requested for the collision:

1. verifier trace accepted → `S21` proof object,
2. `S21` proof object → PA proof object with controlled length,
3. PA short proof → collision with a Pudlák-style PA lower bound.
-/

namespace BoundedArithmeticLab

universe u v

structure BussPudlakObjectSimulatedCollisionInputs
    {s21Box paBox : AbstractProofLengthBox}
    (s21Model : ProofSystemBoxModel.{u} s21Box)
    (paModel : ProofSystemBoxModel.{v} paBox)
    (accepted : ℕ → Prop) where
  lower_source : BussPudlakTheorem5PALowerBoundSource
  lower_source_to_pa : LowerBoundTransfer lower_source.box paBox
  acceptance : EventualAcceptanceUnderRationality accepted
  trace_realization : S21VerifierTraceRealization accepted s21Model
  s21_to_pa : LinearProofObjectSimulation s21Model paModel

def BussPudlakObjectSimulatedCollisionInputs.paShortUpper
    {s21Box paBox : AbstractProofLengthBox}
    {s21Model : ProofSystemBoxModel.{u} s21Box}
    {paModel : ProofSystemBoxModel.{v} paBox}
    {accepted : ℕ → Prop}
    (h : BussPudlakObjectSimulatedCollisionInputs s21Model paModel accepted) :
    EventualShortProofUpperBound paBox accepted :=
  paShortProofsOfS21TraceRealizationAndObjectSimulation
    h.trace_realization h.s21_to_pa

def BussPudlakObjectSimulatedCollisionInputs.paLower
    {s21Box paBox : AbstractProofLengthBox}
    {s21Model : ProofSystemBoxModel.{u} s21Box}
    {paModel : ProofSystemBoxModel.{v} paBox}
    {accepted : ℕ → Prop}
    (h : BussPudlakObjectSimulatedCollisionInputs s21Model paModel accepted) :
    EventualLowerBound paBox :=
  h.lower_source.transferToTarget h.lower_source_to_pa

theorem collision_of_buss_pudlak_source_and_object_simulated_short_proof
    {s21Box paBox : AbstractProofLengthBox}
    {s21Model : ProofSystemBoxModel.{u} s21Box}
    {paModel : ProofSystemBoxModel.{v} paBox}
    {accepted : ℕ → Prop}
    (h : BussPudlakObjectSimulatedCollisionInputs s21Model paModel accepted) :
    False :=
  eventualCollision h.acceptance h.paShortUpper h.paLower

structure FormalS21PABussPudlakCollisionInputs
    (s21 : S21ProofSystemFormalization.{u})
    (pa : PAProofSystemFormalization.{v})
    (accepted : ℕ → Prop) where
  lower_source : BussPudlakTheorem5PALowerBoundSource
  lower_source_to_pa : LowerBoundTransfer lower_source.box pa.box
  acceptance : EventualAcceptanceUnderRationality accepted
  trace_realization : S21VerifierTraceRealization accepted s21.toBoxModel
  s21_to_pa : S21ToPAFormalProofObjectSimulation s21 pa

def FormalS21PABussPudlakCollisionInputs.paShortUpper
    {s21 : S21ProofSystemFormalization.{u}}
    {pa : PAProofSystemFormalization.{v}}
    {accepted : ℕ → Prop}
    (h : FormalS21PABussPudlakCollisionInputs s21 pa accepted) :
    EventualShortProofUpperBound pa.box accepted :=
  paShortProofsOfFormalS21TraceAndPASimulation
    h.trace_realization h.s21_to_pa

def FormalS21PABussPudlakCollisionInputs.paLower
    {s21 : S21ProofSystemFormalization.{u}}
    {pa : PAProofSystemFormalization.{v}}
    {accepted : ℕ → Prop}
    (h : FormalS21PABussPudlakCollisionInputs s21 pa accepted) :
    EventualLowerBound pa.box :=
  h.lower_source.transferToTarget h.lower_source_to_pa

theorem collision_of_formal_s21_pa_buss_pudlak_pipeline
    {s21 : S21ProofSystemFormalization.{u}}
    {pa : PAProofSystemFormalization.{v}}
    {accepted : ℕ → Prop}
    (h : FormalS21PABussPudlakCollisionInputs s21 pa accepted) :
    False :=
  eventualCollision h.acceptance h.paShortUpper h.paLower

end BoundedArithmeticLab
