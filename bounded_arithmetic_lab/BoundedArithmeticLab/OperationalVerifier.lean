/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.ConcretePudlakPipeline

/-!
# Operational verifier traces

This module narrows `accepted` from an arbitrary predicate to the existence of
an accepting run of a verifier machine.  A separate compiler certificate then
turns each accepting run into an S21 derivation.
-/

namespace BoundedArithmeticLab

universe u

structure VerifierMachine where
  State : Type u
  initial : ℕ → State
  step : State → State → Prop
  accepting : State → Prop
  stateSize : State → ℕ

namespace VerifierMachine

inductive Reaches (M : VerifierMachine.{u}) :
    M.State → M.State → ℕ → Prop where
  | refl (s : M.State) : Reaches M s s 0
  | cons {s t u : M.State} {k : ℕ} :
      M.step s t → Reaches M t u k → Reaches M s u (k + 1)

structure AcceptedTrace (M : VerifierMachine.{u}) (n : ℕ) where
  final : M.State
  steps : ℕ
  reaches : Reaches M (M.initial n) final steps
  accepts : M.accepting final

def AcceptedTrace.size {M : VerifierMachine.{u}} {n : ℕ}
    (tr : AcceptedTrace M n) : ℕ :=
  tr.steps + 1

def acceptsInput (M : VerifierMachine.{u}) (n : ℕ) : Prop :=
  Nonempty (AcceptedTrace M n)

structure OperationalS21Compiler
    (M : VerifierMachine.{u}) (target : ℕ → BAFormula) where
  trace_bound : ℕ → ℝ
  trace_bound_poly : IsPolynomialBound trace_bound
  trace_size_le :
    ∀ n : ℕ, ∀ tr : AcceptedTrace M n,
      (tr.size : ℝ) ≤ trace_bound n
  compileTrace :
    ∀ n : ℕ, AcceptedTrace M n → BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n : ℕ, ∀ tr : AcceptedTrace M n,
      (compileTrace n tr).conclusion = target n
  compile_size_le_trace_size :
    ∀ n : ℕ, ∀ tr : AcceptedTrace M n,
      ((compileTrace n tr).size : ℝ) ≤ tr.size

def OperationalS21Compiler.toConcreteTraceSystem
    {M : VerifierMachine.{u}} {target : ℕ → BAFormula}
    (compiler : OperationalS21Compiler M target) :
    ConcreteVerifierTraceSystem target M.acceptsInput where
  Trace := Σ n : ℕ, AcceptedTrace M n
  index := fun tr => tr.1
  traceAccepted := fun _ => True
  accepted_has_trace := by
    intro n hn
    rcases hn with ⟨tr⟩
    exact ⟨⟨n, tr⟩, rfl, trivial⟩
  trace_bound := compiler.trace_bound
  trace_bound_poly := compiler.trace_bound_poly
  trace_size := fun tr => tr.2.size
  trace_size_le := by
    intro tr _htr
    exact compiler.trace_size_le tr.1 tr.2
  compileTrace := by
    intro tr _htr
    exact compiler.compileTrace tr.1 tr.2
  compile_conclusion := by
    intro tr _htr
    exact compiler.compile_conclusion tr.1 tr.2
  compile_size_le_trace_size := by
    intro tr _htr
    exact compiler.compile_size_le_trace_size tr.1 tr.2

theorem collision_of_operational_verifier_exact_pa_pudlak
    {M : VerifierMachine.{u}} {target : ℕ → BAFormula}
    {code : BAFormula → FormulaCode}
    (haccept : EventualAcceptanceUnderRationality M.acceptsInput)
    (compiler : OperationalS21Compiler M target)
    (lower : ConcreteBussPudlakExactLowerForPA target code) :
    False :=
  collision_of_concrete_trace_system_exact_pa_pudlak
    { acceptance := haccept
      trace_system := compiler.toConcreteTraceSystem
      exact_lower := lower }

end VerifierMachine

end BoundedArithmeticLab
