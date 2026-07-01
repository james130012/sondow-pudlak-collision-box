/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.SystemComparison

/-!
# Buss/Pudlák lower-bound source interface

The source being audited is Buss's 1994 Theorem 5 route, which packages the
Friedman/Pudlák partial-consistency proof-length lower bound with a
time-constructible rescaling.  This file does not prove that theorem; it fixes
the exact PA/symbol-size lower-bound shape that such a formalization must
eventually provide.
-/

namespace BoundedArithmeticLab

/-- Conditions on the arithmetic theory in Buss's Theorem 5 extraction.  The
current sidecar keeps the statements abstract; a full formalization must replace
these placeholders with concrete PA syntax, axiom recognition, proof coding, and
sound arithmetization theorems. -/
structure BussPudlakTheoryConditions where
  system : ProofSystem
  measure : ProofLengthMeasure
  system_eq_pa : system = ProofSystem.PA
  measure_eq_symbolSize : measure = ProofLengthMeasure.symbolSize
  consistent_statement : Prop
  consistent : consistent_statement
  axiomatizable_statement : Prop
  axiomatizable : axiomatizable_statement
  axioms_polytime_recognizable_statement : Prop
  axioms_polytime_recognizable : axioms_polytime_recognizable_statement
  contains_bounded_arithmetic_statement : Prop
  contains_bounded_arithmetic : contains_bounded_arithmetic_statement
  efficient_metamathematics_statement : Prop
  efficient_metamathematics : efficient_metamathematics_statement
  efficient_proof_coding_statement : Prop
  efficient_proof_coding : efficient_proof_coding_statement
  binary_numerals_log_size_statement : Prop
  binary_numerals_log_size : binary_numerals_log_size_statement

structure TimeConstructibleScale where
  scale : ℕ → ℕ
  time_constructible_statement : Prop
  time_constructible : time_constructible_statement
  eventually_reads_input_statement : Prop
  eventually_reads_input : eventually_reads_input_statement
  eventually_defined_statement : Prop
  eventually_defined : eventually_defined_statement
  dominates_input_length_statement : Prop
  dominates_input_length : dominates_input_length_statement

structure BussPudlakTheorem5Conditions where
  theory : BussPudlakTheoryConditions
  scale_data : TimeConstructibleScale
  exponent_c : ℕ
  exponent_c_pos : 0 < exponent_c
  epsilon : ℝ
  epsilon_pos : 0 < epsilon

def rescaledExternalPudlakCode (ρ : ℕ → ℕ) (n : ℕ) : FormulaCode :=
  externalPudlakCode (ρ n)

def bussPudlakTheorem5PABox
    (ρ : ℕ → ℕ) (length : ℕ → ℝ) : AbstractProofLengthBox :=
  paSymbolBox (rescaledExternalPudlakCode ρ) length

/-- Audit-facing statement extracted from Buss/Pudlák/Friedman Theorem 5:
after a time-constructible rescaling, the finite-consistency family has no
eventual polynomial PA proofs measured by symbol size. -/
structure BussPudlakTheorem5PALowerBoundSource where
  conditions : BussPudlakTheorem5Conditions
  pa_length : ℕ → ℝ
  lower_bound :
    EventualLowerBound
      (bussPudlakTheorem5PABox conditions.scale_data.scale pa_length)

def BussPudlakTheorem5PALowerBoundSource.box
    (h : BussPudlakTheorem5PALowerBoundSource) :
    AbstractProofLengthBox :=
  bussPudlakTheorem5PABox h.conditions.scale_data.scale h.pa_length

theorem BussPudlakTheorem5PALowerBoundSource.toLowerBound
    (h : BussPudlakTheorem5PALowerBoundSource) :
    EventualLowerBound h.box :=
  h.lower_bound

/-- If the literature lower-bound family is calibrated to the project target
family, it supplies the target lower bound used in the collision. -/
def BussPudlakTheorem5PALowerBoundSource.transferToTarget
    (h : BussPudlakTheorem5PALowerBoundSource)
    {target : AbstractProofLengthBox}
    (htransfer : LowerBoundTransfer h.box target) :
    EventualLowerBound target :=
  htransfer.transfer (fun _ : ℕ => 0) (IsPolynomialBound.const 0)
    h.toLowerBound

structure BussPudlakTransportedCollisionInputs
    (shortBox targetBox : AbstractProofLengthBox)
    (accepted : ℕ → Prop) where
  lower_source : BussPudlakTheorem5PALowerBoundSource
  source_to_target : LowerBoundTransfer lower_source.box targetBox
  acceptance : EventualAcceptanceUnderRationality accepted
  short_upper : EventualShortProofUpperBound shortBox accepted
  short_to_target : ShortProofSystemTransport shortBox targetBox

theorem collision_of_buss_pudlak_source_and_short_proof_transport
    {shortBox targetBox : AbstractProofLengthBox} {accepted : ℕ → Prop}
    (h : BussPudlakTransportedCollisionInputs shortBox targetBox accepted) :
    False :=
  collision_of_transported_short_proof
    { acceptance := h.acceptance
      source_short := h.short_upper
      transport_to_target := h.short_to_target
      target_lower :=
        h.lower_source.transferToTarget h.source_to_target }

end BoundedArithmeticLab
