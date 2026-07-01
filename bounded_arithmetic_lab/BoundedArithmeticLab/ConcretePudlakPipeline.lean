/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.VerifierCompiler
import BoundedArithmeticLab.BussPudlakSource

/-!
# Concrete short-proof/Pudlak collision pipeline

This module ties the concrete S21 compiler and concrete PA proof system to the
abstract Buss/Pudlak lower-bound source.  The lower-bound theorem itself remains
an explicit input, but its target PA box is no longer implicit.
-/

namespace BoundedArithmeticLab

universe u

structure ConcreteBussPudlakLowerForPA
    (target : ℕ → BAFormula) (code : BAFormula → FormulaCode) where
  lower_source : BussPudlakTheorem5PALowerBoundSource
  source_to_concrete_pa :
    LowerBoundTransfer lower_source.box
      (concretePAFormalization target code).box

def ConcreteBussPudlakLowerForPA.toLowerBound
    {target : ℕ → BAFormula} {code : BAFormula → FormulaCode}
    (h : ConcreteBussPudlakLowerForPA target code) :
    EventualLowerBound (concretePAFormalization target code).box :=
  h.lower_source.transferToTarget h.source_to_concrete_pa

structure ConcreteBussPudlakExactLowerForPA
    (target : ℕ → BAFormula) (code : BAFormula → FormulaCode) where
  lower_source : BussPudlakTheorem5PALowerBoundSource
  source_eq_concrete_pa :
    ProofLengthBoxEquiv lower_source.box
      (concretePAFormalization target code).box

structure ConcreteBussPudlakBoxCalibration
    (target : ℕ → BAFormula) (code : BAFormula → FormulaCode) where
  lower_source : BussPudlakTheorem5PALowerBoundSource
  formula_eq :
    ∀ n : ℕ, lower_source.box.formula n =
      (concretePAFormalization target code).box.formula n
  length_eq :
    ∀ n : ℕ, lower_source.box.length n =
      (concretePAFormalization target code).box.length n

def ConcreteBussPudlakBoxCalibration.toBoxEquiv
    {target : ℕ → BAFormula} {code : BAFormula → FormulaCode}
    (h : ConcreteBussPudlakBoxCalibration target code) :
    ProofLengthBoxEquiv h.lower_source.box
      (concretePAFormalization target code).box where
  system_eq := rfl
  measure_eq := rfl
  formula_eq := h.formula_eq
  length_eq := h.length_eq

def ConcreteBussPudlakBoxCalibration.toExactLower
    {target : ℕ → BAFormula} {code : BAFormula → FormulaCode}
    (h : ConcreteBussPudlakBoxCalibration target code) :
    ConcreteBussPudlakExactLowerForPA target code where
  lower_source := h.lower_source
  source_eq_concrete_pa := h.toBoxEquiv

structure ConcreteBussPudlakFormulaLengthCalibration
    (target : ℕ → BAFormula) (code : BAFormula → FormulaCode) where
  lower_source : BussPudlakTheorem5PALowerBoundSource
  formula_code_eq :
    ∀ n : ℕ,
      rescaledExternalPudlakCode
        lower_source.conditions.scale_data.scale n =
        code (target n)
  length_eq :
    ∀ n : ℕ,
      lower_source.pa_length n =
        semanticBAProofLength PAAxiom target n

def ConcreteBussPudlakFormulaLengthCalibration.toBoxCalibration
    {target : ℕ → BAFormula} {code : BAFormula → FormulaCode}
    (h : ConcreteBussPudlakFormulaLengthCalibration target code) :
    ConcreteBussPudlakBoxCalibration target code where
  lower_source := h.lower_source
  formula_eq := by
    intro n
    change rescaledExternalPudlakCode
        h.lower_source.conditions.scale_data.scale n = code (target n)
    exact h.formula_code_eq n
  length_eq := by
    intro n
    change h.lower_source.pa_length n = semanticBAProofLength PAAxiom target n
    exact h.length_eq n

def ConcreteBussPudlakExactLowerForPA.toLowerForPA
    {target : ℕ → BAFormula} {code : BAFormula → FormulaCode}
    (h : ConcreteBussPudlakExactLowerForPA target code) :
    ConcreteBussPudlakLowerForPA target code where
  lower_source := h.lower_source
  source_to_concrete_pa := h.source_eq_concrete_pa.toLowerBoundTransfer

def ConcreteBussPudlakExactLowerForPA.toLowerBound
    {target : ℕ → BAFormula} {code : BAFormula → FormulaCode}
    (h : ConcreteBussPudlakExactLowerForPA target code) :
    EventualLowerBound (concretePAFormalization target code).box :=
  h.toLowerForPA.toLowerBound

structure ConcreteS21PABussPudlakCollisionInputs
    (target : ℕ → BAFormula) (code : BAFormula → FormulaCode)
    (accepted : ℕ → Prop) where
  acceptance : EventualAcceptanceUnderRationality accepted
  compiler : ConcreteS21VerifierCompiler target accepted
  lower : ConcreteBussPudlakLowerForPA target code

theorem collision_of_concrete_s21_compiler_pa_pudlak
    {target : ℕ → BAFormula} {code : BAFormula → FormulaCode}
    {accepted : ℕ → Prop}
    (h : ConcreteS21PABussPudlakCollisionInputs target code accepted) :
    False :=
  eventualCollision h.acceptance
    h.compiler.toPAShortProofUpper
    h.lower.toLowerBound

structure ConcreteS21PABussPudlakExactCollisionInputs
    (target : ℕ → BAFormula) (code : BAFormula → FormulaCode)
    (accepted : ℕ → Prop) where
  acceptance : EventualAcceptanceUnderRationality accepted
  trace_system : ConcreteVerifierTraceSystem.{u} target accepted
  exact_lower : ConcreteBussPudlakExactLowerForPA target code

theorem collision_of_concrete_trace_system_exact_pa_pudlak
    {target : ℕ → BAFormula} {code : BAFormula → FormulaCode}
    {accepted : ℕ → Prop}
    (h : ConcreteS21PABussPudlakExactCollisionInputs target code accepted) :
    False :=
  eventualCollision h.acceptance
    h.trace_system.toCompiler.toPAShortProofUpper
    h.exact_lower.toLowerBound

end BoundedArithmeticLab
