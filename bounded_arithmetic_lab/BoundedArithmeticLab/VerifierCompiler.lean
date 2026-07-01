/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.ConcreteProofSystems

/-!
# Concrete verifier compiler interface

The compiler is the concrete replacement for a bare verifier-trace assumption:
it must output an actual S21 derivation of the target formula and a polynomial
bound on the produced derivation size.
-/

namespace BoundedArithmeticLab

universe u

structure ConcreteVerifierTraceSystem
    (target : ℕ → BAFormula) (accepted : ℕ → Prop) where
  Trace : Type u
  index : Trace → ℕ
  traceAccepted : Trace → Prop
  accepted_has_trace :
    ∀ n : ℕ, accepted n →
      ∃ tr : Trace, index tr = n ∧ traceAccepted tr
  trace_bound : ℕ → ℝ
  trace_bound_poly : IsPolynomialBound trace_bound
  trace_size : Trace → ℕ
  trace_size_le :
    ∀ tr : Trace, traceAccepted tr →
      (trace_size tr : ℝ) ≤ trace_bound (index tr)
  compileTrace : ∀ tr : Trace, traceAccepted tr → BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ tr : Trace, ∀ htr : traceAccepted tr,
      (compileTrace tr htr).conclusion = target (index tr)
  compile_size_le_trace_size :
    ∀ tr : Trace, ∀ htr : traceAccepted tr,
      ((compileTrace tr htr).size : ℝ) ≤ trace_size tr

structure ConcreteS21VerifierCompiler
    (target : ℕ → BAFormula) (accepted : ℕ → Prop) where
  trace_bound : ℕ → ℝ
  trace_bound_poly : IsPolynomialBound trace_bound
  compile : ∀ n : ℕ, accepted n → BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n : ℕ, ∀ h : accepted n, (compile n h).conclusion = target n
  compile_size_le :
    ∀ n : ℕ, ∀ h : accepted n,
      ((compile n h).size : ℝ) ≤ trace_bound n

noncomputable def ConcreteVerifierTraceSystem.toCompiler
    {target : ℕ → BAFormula} {accepted : ℕ → Prop}
    (traceSystem : ConcreteVerifierTraceSystem.{u} target accepted) :
    ConcreteS21VerifierCompiler target accepted where
  trace_bound := traceSystem.trace_bound
  trace_bound_poly := traceSystem.trace_bound_poly
  compile := by
    intro n hn
    classical
    let tr := Classical.choose (traceSystem.accepted_has_trace n hn)
    have htr := Classical.choose_spec (traceSystem.accepted_has_trace n hn)
    exact traceSystem.compileTrace tr htr.2
  compile_conclusion := by
    intro n hn
    classical
    let tr := Classical.choose (traceSystem.accepted_has_trace n hn)
    have htr := Classical.choose_spec (traceSystem.accepted_has_trace n hn)
    have hidx : traceSystem.index tr = n := htr.1
    have hacc : traceSystem.traceAccepted tr := htr.2
    dsimp
    simpa [tr, hidx] using traceSystem.compile_conclusion tr hacc
  compile_size_le := by
    intro n hn
    classical
    let tr := Classical.choose (traceSystem.accepted_has_trace n hn)
    have htr := Classical.choose_spec (traceSystem.accepted_has_trace n hn)
    have hidx : traceSystem.index tr = n := htr.1
    have hacc : traceSystem.traceAccepted tr := htr.2
    have hcompile := traceSystem.compile_size_le_trace_size tr hacc
    have htrace := traceSystem.trace_size_le tr hacc
    dsimp
    simpa [tr, hidx] using hcompile.trans htrace

noncomputable def ConcreteS21VerifierCompiler.toTraceRealization
    {target : ℕ → BAFormula} {code : BAFormula → FormulaCode}
    {accepted : ℕ → Prop}
    (compiler : ConcreteS21VerifierCompiler target accepted) :
    S21VerifierTraceRealization accepted
      (concreteS21Formalization target code).toBoxModel where
  trace_bound := compiler.trace_bound
  trace_bound_poly := compiler.trace_bound_poly
  proof_of_accepted := by
    intro n hn
    refine ⟨compiler.compile n hn, ?_, compiler.compile_size_le n hn⟩
    exact compiler.compile_conclusion n hn

noncomputable def ConcreteS21VerifierCompiler.toPAShortProofUpper
    {target : ℕ → BAFormula} {code : BAFormula → FormulaCode}
    {accepted : ℕ → Prop}
    (compiler : ConcreteS21VerifierCompiler target accepted) :
    EventualShortProofUpperBound
      (concretePAFormalization target code).box accepted :=
  paShortProofsOfFormalS21TraceAndPASimulation
    compiler.toTraceRealization
    (concreteS21ToPALinearObjectSimulation target code)

end BoundedArithmeticLab
