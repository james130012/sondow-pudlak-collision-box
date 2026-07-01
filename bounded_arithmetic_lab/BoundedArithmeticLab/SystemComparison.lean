/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.PudlakInterface

/-!
# Transporting short proofs between systems

The collision must happen in one proof-length box.  If short proofs are first
constructed in a weaker bounded-arithmetic system, this module records the
simulation needed to transport the upper bound to the lower-bound system.
-/

namespace BoundedArithmeticLab

def proofLengthBox
    (system : ProofSystem) (measure : ProofLengthMeasure)
    (formula : ℕ → FormulaCode) (length : ℕ → ℝ) :
    AbstractProofLengthBox where
  system := system
  measure := measure
  formula := formula
  length := length

def s21SymbolBox (formula : ℕ → FormulaCode) (length : ℕ → ℝ) :
    AbstractProofLengthBox :=
  proofLengthBox ProofSystem.S21 ProofLengthMeasure.symbolSize formula length

def paSymbolBox (formula : ℕ → FormulaCode) (length : ℕ → ℝ) :
    AbstractProofLengthBox :=
  proofLengthBox ProofSystem.PA ProofLengthMeasure.symbolSize formula length

/-- A system-transport certificate for upper bounds.  The important audit field
is `same_formula`: the simulation is only useful if it preserves the formula
family being proved. -/
structure ShortProofSystemTransport
    (source target : AbstractProofLengthBox) where
  same_formula : ∀ n : ℕ, source.formula n = target.formula n
  mapBound : (ℕ → ℝ) → ℕ → ℝ
  mapBound_poly :
    ∀ f : ℕ → ℝ, IsPolynomialBound f → IsPolynomialBound (mapBound f)
  target_le_mapped_bound :
    ∀ f : ℕ → ℝ, ∀ n : ℕ,
      source.length n ≤ f n → target.length n ≤ mapBound f n

structure ProofLengthBoxEquiv
    (source target : AbstractProofLengthBox) where
  system_eq : source.system = target.system
  measure_eq : source.measure = target.measure
  formula_eq : ∀ n : ℕ, source.formula n = target.formula n
  length_eq : ∀ n : ℕ, source.length n = target.length n

def ProofLengthBoxEquiv.refl (box : AbstractProofLengthBox) :
    ProofLengthBoxEquiv box box where
  system_eq := rfl
  measure_eq := rfl
  formula_eq := by intro n; rfl
  length_eq := by intro n; rfl

def ProofLengthBoxEquiv.symm
    {source target : AbstractProofLengthBox}
    (h : ProofLengthBoxEquiv source target) :
    ProofLengthBoxEquiv target source where
  system_eq := h.system_eq.symm
  measure_eq := h.measure_eq.symm
  formula_eq := by intro n; exact (h.formula_eq n).symm
  length_eq := by intro n; exact (h.length_eq n).symm

def ProofLengthBoxEquiv.toLowerBoundTransfer
    {source target : AbstractProofLengthBox}
    (h : ProofLengthBoxEquiv source target) :
    LowerBoundTransfer source target where
  transfer := by
    intro _f _hf hlower
    refine ⟨?_⟩
    intro g hg N
    rcases hlower.lower_bound g hg N with ⟨n, hn, hgt⟩
    refine ⟨n, hn, ?_⟩
    simpa [h.length_eq n] using hgt

structure LinearProofLengthSimulation
    (source target : AbstractProofLengthBox) where
  same_formula : ∀ n : ℕ, source.formula n = target.formula n
  C : ℝ
  D : ℝ
  C_nonneg : 0 ≤ C
  D_nonneg : 0 ≤ D
  target_le_linear_source :
    ∀ n : ℕ, target.length n ≤ C * source.length n + D

def LinearProofLengthSimulation.toShortProofSystemTransport
    {source target : AbstractProofLengthBox}
    (h : LinearProofLengthSimulation source target) :
    ShortProofSystemTransport source target where
  same_formula := h.same_formula
  mapBound := fun f n => h.C * f n + h.D
  mapBound_poly := by
    intro f hf
    exact hf.linear_rescale h.C_nonneg h.D_nonneg
  target_le_mapped_bound := by
    intro f n hsource
    have htarget := h.target_le_linear_source n
    have hmul : h.C * source.length n ≤ h.C * f n :=
      mul_le_mul_of_nonneg_left hsource h.C_nonneg
    linarith

def EventualShortProofUpperBound.transport
    {source target : AbstractProofLengthBox} {accepted : ℕ → Prop}
    (hshort : EventualShortProofUpperBound source accepted)
    (htransport : ShortProofSystemTransport source target) :
    EventualShortProofUpperBound target accepted where
  bound := htransport.mapBound hshort.bound
  bound_poly := htransport.mapBound_poly hshort.bound hshort.bound_poly
  short_of_accepted := by
    intro n hn
    exact htransport.target_le_mapped_bound hshort.bound
      n (hshort.short_of_accepted n hn)

/-- The common S²₁-to-PA shape: the same formula family is proved first in S²₁
and then simulated inside PA with polynomial overhead. -/
abbrev S21ToPATransport
    (formula : ℕ → FormulaCode)
    (s21Length paLength : ℕ → ℝ) :=
  ShortProofSystemTransport
    (s21SymbolBox formula s21Length)
    (paSymbolBox formula paLength)

abbrev S21ToPALinearSimulation
    (formula : ℕ → FormulaCode)
    (s21Length paLength : ℕ → ℝ) :=
  LinearProofLengthSimulation
    (s21SymbolBox formula s21Length)
    (paSymbolBox formula paLength)

structure TransportedCollisionInputs
    (source target : AbstractProofLengthBox) (accepted : ℕ → Prop) where
  acceptance : EventualAcceptanceUnderRationality accepted
  source_short : EventualShortProofUpperBound source accepted
  transport_to_target : ShortProofSystemTransport source target
  target_lower : EventualLowerBound target

theorem collision_of_transported_short_proof
    {source target : AbstractProofLengthBox} {accepted : ℕ → Prop}
    (h : TransportedCollisionInputs source target accepted) :
    False :=
  eventualCollision h.acceptance
    (h.source_short.transport h.transport_to_target)
    h.target_lower

end BoundedArithmeticLab
