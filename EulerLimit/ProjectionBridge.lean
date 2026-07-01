/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.MainRoutes
import EulerLimit.MiniHilbert
/-!
# Gödel-Sondow Coupling Hypothesis Formalization
This module formalizes the Euler-Mascheroni constant limit definition,
proof-complexity and projection-bridge layers.
-/

open Filter
structure ReflectionGraftConjunctionProjectionBridge : Prop where
  graft_syntax : ReflectionGraftConjunctionSyntax
  projection : PartialConsistencyToReflectionGraftProjection


-- Concrete proof-calculus choices for the projection bridge.  The project keeps
-- PA as the object theory, but the proof-length claim still needs a fixed proof
-- presentation.  For a Hilbert system, right-conjunction elimination is
-- obtained by appending the axiom instance `(A ∧ B) -> B` and one modus ponens
-- step.  For Frege/sequent presentations it is the corresponding standard
-- right-projection rule.
inductive PAProofCalculus
  | hilbert
  | frege
  | sequent

structure RightConjunctionEliminationCost
    (T : ProofSystem) (measure : ProofLengthMeasure)
    (source target : ℕ → FormulaCode) where
  calculus : PAProofCalculus
  linear_overhead :
    ProofLengthProjection T measure source target

structure RightConjunctionEliminationTransferCost
    (T : ProofSystem) (measure : ProofLengthMeasure)
    (source target : ℕ → FormulaCode) where
  calculus : PAProofCalculus
  linear_overhead :
    LinearProofLengthProjection T measure source target

abbrev PAConjunctionEliminationCost :=
  RightConjunctionEliminationCost
    ProofSystem.PA ProofLengthMeasure.symbolSize
    partialConsistencyCode sondowReflectionGraftCode

abbrev PAConjunctionEliminationTransferCost :=
  RightConjunctionEliminationTransferCost
    ProofSystem.PA ProofLengthMeasure.symbolSize
    partialConsistencyCode sondowReflectionGraftCode

abbrev PAConjunctionEliminationConstantCost :=
  ConstantProofLengthProjection
    ProofSystem.PA ProofLengthMeasure.symbolSize
    partialConsistencyCode sondowReflectionGraftCode

abbrev HilbertRightConjunctionLinearOverhead : Prop :=
  ∃ C D : ℝ,
    0 < C ∧ 0 ≤ D ∧
      ∀ n : ℕ,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) ≤
        C * proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) + D

abbrev HilbertRightConjunctionConstantOverhead : Prop :=
  ∃ D : ℝ,
    0 ≤ D ∧
      ∀ n : ℕ,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) ≤
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) + D

abbrev HilbertRightConjunctionTwoStepOverhead : Prop :=
  ∀ n : ℕ,
    proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
      (partialConsistencyCode n) ≤
    proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
      (sondowReflectionGraftCode n) + 2

structure HilbertTwoStepProofLengthRealization : Prop where
  graft_syntax : ReflectionGraftConjunctionSyntax
  graft_syntax_true : graft_syntax = reflection_graft_conjunction_syntax_true
  realizes_right_conj_elim :
    ∀ n : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode n) ≤
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode n) + 2

structure HilbertProofLengthSoundnessBridge : Prop where
  realizes_right_conj_elim :
    ∀ n : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode n) ≤
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode n) + 2

structure SemanticHilbertProofLengthSoundnessBridge
    (length : FormulaCode → ℕ) : Prop where
  realizes_right_conj_elim :
    ∀ n : ℕ,
      length (partialConsistencyCode n) ≤
        length (sondowReflectionGraftCode n) + 2

structure SemanticConstantProofLengthProjection
    (length : FormulaCode → ℕ)
    (source target : ℕ → FormulaCode) where
  D : ℕ
  source_le_target_add :
    ∀ n : ℕ, length (source n) ≤ length (target n) + D

structure SemanticStrongLowerBoundTransfer
    (length : FormulaCode → ℕ)
    (source target : ℕ → FormulaCode) : Prop where
  transfer :
    ∀ f : ℕ → ℝ, is_polynomial_bound f →
      ∃ g : ℕ → ℝ, is_polynomial_bound g ∧
        ((∃ᶠ n in atTop, (length (source n) : ℝ) > g n) →
          ∃ᶠ n in atTop, (length (target n) : ℝ) > f n)

structure SemanticStrongProofLengthLowerBound
    (length : FormulaCode → ℕ) (φ : ℕ → FormulaCode) : Prop where
  frequently_beats_every_polynomial :
    ∀ f : ℕ → ℝ, is_polynomial_bound f →
      ∃ᶠ n in atTop, (length (φ n) : ℝ) > f n

structure SemanticStrongNatLowerBound (sourceLength : ℕ → ℕ) : Prop where
  frequently_beats_every_polynomial :
    ∀ f : ℕ → ℝ, is_polynomial_bound f →
      ∃ᶠ n in atTop, (sourceLength n : ℝ) > f n

theorem SemanticStrongNatLowerBound.toFormulaCodeLowerBound
    {sourceLength : ℕ → ℕ} {length : FormulaCode → ℕ}
    {φ : ℕ → FormulaCode}
    (hsource : SemanticStrongNatLowerBound sourceLength)
    (hexact : ∀ n : ℕ, length (φ n) = sourceLength n) :
    SemanticStrongProofLengthLowerBound length φ where
  frequently_beats_every_polynomial := by
    intro f hf
    exact (hsource.frequently_beats_every_polynomial f hf).mono fun n hn => by
      simpa [hexact n] using hn

theorem SemanticStrongNatLowerBound.of_polynomial_cofinal_rescaling
    {sourceLength : ℕ → ℕ} {ρ : ℕ → ℕ}
    (hscale : PolynomialCofinalScale ρ)
    (hlower : SemanticStrongNatLowerBound (fun n : ℕ => sourceLength (ρ n))) :
    SemanticStrongNatLowerBound sourceLength where
  frequently_beats_every_polynomial := by
    intro f hf
    exact frequently_atTop_of_frequently_scale hscale
      (hlower.frequently_beats_every_polynomial
        (fun n : ℕ => f (ρ n)) (hscale.polynomial_substitution f hf))

structure SemanticEventualLowerBound
    (length : FormulaCode → ℕ) (φ : ℕ → FormulaCode) : Prop where
  lower_bound :
    ∀ f : ℕ → ℝ, is_polynomial_bound f →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (length (φ n) : ℝ) > f n

theorem SemanticEventualLowerBound.of_frequently
    {length : FormulaCode → ℕ} {φ : ℕ → FormulaCode}
    (hfreq :
      ∀ f : ℕ → ℝ, is_polynomial_bound f →
        ∃ᶠ n in atTop, (length (φ n) : ℝ) > f n) :
    SemanticEventualLowerBound length φ where
  lower_bound := by
    intro f hf N
    exact (Filter.frequently_atTop.mp (hfreq f hf)) N

theorem SemanticStrongProofLengthLowerBound.toSemanticEventualLowerBound
    {length : FormulaCode → ℕ} {φ : ℕ → FormulaCode}
    (h : SemanticStrongProofLengthLowerBound length φ) :
    SemanticEventualLowerBound length φ :=
  SemanticEventualLowerBound.of_frequently h.frequently_beats_every_polynomial

theorem SemanticEventualLowerBound.toEventualSemanticLowerBound
    {length : FormulaCode → ℕ} {φ : ℕ → FormulaCode}
    (h : SemanticEventualLowerBound length φ) :
    EventualSemanticLowerBound length φ where
  lower_bound := h.lower_bound

theorem SemanticStrongProofLengthLowerBound.toEventualSemanticLowerBound
    {length : FormulaCode → ℕ} {φ : ℕ → FormulaCode}
    (h : SemanticStrongProofLengthLowerBound length φ) :
    EventualSemanticLowerBound length φ :=
  h.toSemanticEventualLowerBound.toEventualSemanticLowerBound

theorem SemanticStrongProofLengthLowerBound.transfer
    {length : FormulaCode → ℕ}
    {source target : ℕ → FormulaCode}
    (hsource : SemanticStrongProofLengthLowerBound length source)
    (htransfer : SemanticStrongLowerBoundTransfer length source target) :
    SemanticStrongProofLengthLowerBound length target where
  frequently_beats_every_polynomial := by
    intro f hf
    rcases htransfer.transfer f hf with ⟨g, hg, htransfer_g⟩
    exact htransfer_g (hsource.frequently_beats_every_polynomial g hg)

theorem SemanticStrongProofLengthLowerBound.toStrongProofLengthLowerBound
    {length : FormulaCode → ℕ}
    {φ : ℕ → FormulaCode}
    {relevant : FormulaCode → Prop}
    (h : SemanticStrongProofLengthLowerBound length φ)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize length relevant)
    (hφ : ∀ n : ℕ, relevant (φ n)) :
    StrongProofLengthLowerBound
      ProofSystem.PA ProofLengthMeasure.symbolSize φ where
  frequently_beats_every_polynomial := by
    intro f hf
    exact (h.frequently_beats_every_polynomial f hf).mono fun n hn => by
      simpa [hsem.proof_length_eq (φ n) (hφ n)] using hn

theorem SemanticEventualLowerBound.toEventualLowerBound
    {length : FormulaCode → ℕ}
    {φ : ℕ → FormulaCode}
    {relevant : FormulaCode → Prop}
    (h : SemanticEventualLowerBound length φ)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize length relevant)
    (hφ : ∀ n : ℕ, relevant (φ n)) :
    EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize φ where
  lower_bound := by
    intro f hf N
    rcases h.lower_bound f hf N with ⟨n, hn, hgt⟩
    refine ⟨n, hn, ?_⟩
    simpa [hsem.proof_length_eq (φ n) (hφ n)] using hgt

theorem SemanticStrongLowerBoundTransfer.toStrongLowerBoundTransfer
    {length : FormulaCode → ℕ}
    {source target : ℕ → FormulaCode}
    {relevant : FormulaCode → Prop}
    (h : SemanticStrongLowerBoundTransfer length source target)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize length relevant)
    (hsource : ∀ n : ℕ, relevant (source n))
    (htarget : ∀ n : ℕ, relevant (target n)) :
    StrongLowerBoundTransfer
      ProofSystem.PA ProofLengthMeasure.symbolSize source target where
  transfer := by
    intro f hf
    rcases h.transfer f hf with ⟨g, hg, htransfer⟩
    refine ⟨g, hg, ?_⟩
    intro hfreq
    have hfreq_source :
        ∃ᶠ n in atTop, (length (source n) : ℝ) > g n :=
      hfreq.mono fun n hn => by
        simpa [hsem.proof_length_eq (source n) (hsource n)] using hn
    exact (htransfer hfreq_source).mono fun n hn => by
      simpa [hsem.proof_length_eq (target n) (htarget n)] using hn

theorem SemanticConstantProofLengthProjection.toSemanticStrongLowerBoundTransfer
    {length : FormulaCode → ℕ}
    {source target : ℕ → FormulaCode}
    (h : SemanticConstantProofLengthProjection length source target) :
    SemanticStrongLowerBoundTransfer length source target where
  transfer := by
    intro f hf
    refine ⟨fun n => (1 : ℝ) * f n + h.D,
      hf.linear_rescale (by norm_num) (by exact_mod_cast Nat.zero_le h.D), ?_⟩
    intro hfreq
    exact hfreq.mono fun n hn => by
      have hle := h.source_le_target_add n
      have hleR :
          (length (source n) : ℝ) ≤ (length (target n) : ℝ) + h.D := by
        exact_mod_cast hle
      nlinarith

noncomputable def SemanticConstantProofLengthProjection.toConstantProofLengthProjection
    {length : FormulaCode → ℕ}
    {source target : ℕ → FormulaCode}
    {relevant : FormulaCode → Prop}
    (h : SemanticConstantProofLengthProjection length source target)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize length relevant)
    (hsource : ∀ n : ℕ, relevant (source n))
    (htarget : ∀ n : ℕ, relevant (target n)) :
    ConstantProofLengthProjection
      ProofSystem.PA ProofLengthMeasure.symbolSize source target where
  D := h.D
  D_nonneg := by exact_mod_cast Nat.zero_le h.D
  source_le_target_add := by
    intro n
    rw [hsem.proof_length_eq (source n) (hsource n),
      hsem.proof_length_eq (target n) (htarget n)]
    exact_mod_cast h.source_le_target_add n

def SemanticHilbertProofLengthSoundnessBridge.toSemanticConstantProjection
    {length : FormulaCode → ℕ}
    (h : SemanticHilbertProofLengthSoundnessBridge length) :
    SemanticConstantProofLengthProjection
      length partialConsistencyCode sondowReflectionGraftCode where
  D := 2
  source_le_target_add := h.realizes_right_conj_elim

-- The syntactic part of the project-level projection bridge.  This is the
-- part that can be checked without assigning a concrete global meaning to
-- `proof_length`: the source family is the partial-consistency payload, the
-- target family is the reflection-graft conjunction, and both use the same
-- numerical index.
structure HilbertProjectionCodeAlignment : Prop where
  graft_syntax : ReflectionGraftConjunctionSyntax
  graft_syntax_true : graft_syntax = reflection_graft_conjunction_syntax_true
  payload_reading : PartialConsistencyPayloadIntendedReading
  source_family :
    ∀ n : ℕ, (partialConsistencyCode n).family = FormulaFamily.partialConsistency
  source_index :
    ∀ n : ℕ, (partialConsistencyCode n).index = n
  target_family :
    ∀ n : ℕ, (sondowReflectionGraftCode n).family =
      FormulaFamily.sondowReflectionGraft
  target_index :
    ∀ n : ℕ, (sondowReflectionGraftCode n).index = n

theorem hilbert_projection_code_alignment_true :
    HilbertProjectionCodeAlignment where
  graft_syntax := reflection_graft_conjunction_syntax_true
  graft_syntax_true := rfl
  payload_reading := partial_consistency_payload_intended_reading_true
  source_family := by
    intro n
    rfl
  source_index := by
    intro n
    rfl
  target_family := by
    intro n
    rfl
  target_index := by
    intro n
    rfl

-- The remaining semantic/soundness part of the project-level bridge: once the
-- formula-code alignment above is fixed, the chosen global `proof_length`
-- convention must count the standard Hilbert right-conjunction elimination as
-- at most one axiom instance plus one modus-ponens step.
structure HilbertProofLengthSoundnessForAlignedCoding
    (halign : HilbertProjectionCodeAlignment) : Prop where
  realizes_aligned_right_conj_elim :
    ∀ n : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode n) ≤
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode n) + 2

-- A stronger, lower-level way to discharge the previous field.  It says that,
-- for the two formula families used by the projection bridge, the global
-- `proof_length` agrees with a concrete Nat-valued Hilbert length model, and
-- that the concrete model has the right-conjunction projection with `+2`
-- overhead.  This is deliberately stronger than the bridge: it is the shape
-- expected from a real shortest-proof-length semantics.
structure HilbertProofLengthExactProjectionRealization
    (halign : HilbertProjectionCodeAlignment) where
  sourceLength : ℕ → ℕ
  targetLength : ℕ → ℕ
  source_exact :
    ∀ n : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode n) = sourceLength n
  target_exact :
    ∀ n : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode n) = targetLength n
  source_le_target_add_two :
    ∀ n : ℕ, sourceLength n ≤ targetLength n + 2

theorem HilbertProofLengthExactProjectionRealization.toAlignedSoundness
    {halign : HilbertProjectionCodeAlignment}
    (h : HilbertProofLengthExactProjectionRealization halign) :
    HilbertProofLengthSoundnessForAlignedCoding halign where
  realizes_aligned_right_conj_elim := by
    intro n
    rw [h.source_exact n, h.target_exact n]
    exact_mod_cast h.source_le_target_add_two n

theorem HilbertProofLengthExactProjectionRealization.toBridge
    {halign : HilbertProjectionCodeAlignment}
    (h : HilbertProofLengthExactProjectionRealization halign) :
    HilbertProofLengthSoundnessBridge where
  realizes_right_conj_elim := by
    let hs := HilbertProofLengthExactProjectionRealization.toAlignedSoundness h
    exact hs.realizes_aligned_right_conj_elim

theorem HilbertProofLengthExactProjectionRealization.toTwoStepOverhead
    {halign : HilbertProjectionCodeAlignment}
    (h : HilbertProofLengthExactProjectionRealization halign) :
    HilbertRightConjunctionTwoStepOverhead :=
  h.toBridge.realizes_right_conj_elim

-- It is often more convenient to prove exactness only for the target family,
-- plus a direct upper bound for the source family obtained by transforming a
-- target proof.  This is still strong enough to recover the project-level
-- bridge and avoids requiring an exact shortest-proof characterization for the
-- projected formula.
structure HilbertProofLengthTargetExactProjectionRealization
    (halign : HilbertProjectionCodeAlignment) where
  targetLength : ℕ → ℕ
  target_exact :
    ∀ n : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode n) = targetLength n
  source_le_targetLength_add_two :
    ∀ n : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode n) ≤ targetLength n + 2

theorem HilbertProofLengthTargetExactProjectionRealization.toAlignedSoundness
    {halign : HilbertProjectionCodeAlignment}
    (h : HilbertProofLengthTargetExactProjectionRealization halign) :
    HilbertProofLengthSoundnessForAlignedCoding halign where
  realizes_aligned_right_conj_elim := by
    intro n
    rw [h.target_exact n]
    exact h.source_le_targetLength_add_two n

theorem HilbertProofLengthTargetExactProjectionRealization.toBridge
    {halign : HilbertProjectionCodeAlignment}
    (h : HilbertProofLengthTargetExactProjectionRealization halign) :
    HilbertProofLengthSoundnessBridge where
  realizes_right_conj_elim := by
    let hs := HilbertProofLengthTargetExactProjectionRealization.toAlignedSoundness h
    exact hs.realizes_aligned_right_conj_elim

theorem HilbertProofLengthTargetExactProjectionRealization.toTwoStepOverhead
    {halign : HilbertProjectionCodeAlignment}
    (h : HilbertProofLengthTargetExactProjectionRealization halign) :
    HilbertRightConjunctionTwoStepOverhead :=
  h.toBridge.realizes_right_conj_elim

namespace MiniHilbert

open FirstOrder
open FirstOrder.Language

universe u v w

variable {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}

-- Project-level interpretation of a `FormulaCode` family by a concrete
-- MiniHilbert formula family and its shortest Hilbert proof length.  This is
-- the precise local shape needed before replacing the abstract `proof_length`
-- by a real shortest-proof-length semantics.
structure FormulaCodeMinLengthRealization
    (Ax : L.BoundedFormula α n → Prop)
    (code : ℕ → L.BoundedFormula α n)
    (φ : ℕ → FormulaCode) where
  proofFamily : ConcreteProofFamily Ax code
  proof_length_exact :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize (φ m) =
        proofFamily.minLength m

-- A one-sided version of `FormulaCodeMinLengthRealization`.  This is the
-- project-level shape produced by an explicit proof transformation: the global
-- `proof_length` is bounded above by the shortest concrete Hilbert proof length
-- of the transformed formula family, without claiming exact agreement.
structure FormulaCodeUpperLengthRealization
    (Ax : L.BoundedFormula α n → Prop)
    (code : ℕ → L.BoundedFormula α n)
    (φ : ℕ → FormulaCode) where
  proofFamily : ConcreteProofFamily Ax code
  proof_length_le :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize (φ m) ≤
        proofFamily.minLength m

def FormulaCodeMinLengthRealization.toUpperLengthRealization
    {Ax : L.BoundedFormula α n → Prop}
    {code : ℕ → L.BoundedFormula α n}
    {φ : ℕ → FormulaCode}
    (h : FormulaCodeMinLengthRealization Ax code φ) :
    FormulaCodeUpperLengthRealization Ax code φ where
  proofFamily := h.proofFamily
  proof_length_le := by
    intro m
    rw [h.proof_length_exact m]

theorem FormulaCodeMinLengthRealization.source_le_target_add_two_of_rightConjElim
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (target :
      FormulaCodeMinLengthRealization Ax (fun m => A m ⊓ B m)
        sondowReflectionGraftCode)
    (source :
      FormulaCodeMinLengthRealization Ax B partialConsistencyCode)
    (hsource :
      ∀ m : ℕ, source.proofFamily.minLength m =
        target.proofFamily.rightConjElim.minLength m) :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode m) ≤
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode m) + 2 := by
  intro m
  rw [source.proof_length_exact m, target.proof_length_exact m, hsource m]
  exact_mod_cast target.proofFamily.minLength_rightConjElim_le m

theorem FormulaCodeMinLengthRealization.source_le_target_add_two_of_rightConjElim_upper
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (target :
      FormulaCodeMinLengthRealization Ax (fun m => A m ⊓ B m)
        sondowReflectionGraftCode)
    (hsource_upper :
      ∀ m : ℕ,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode m) ≤
          target.proofFamily.rightConjElim.minLength m) :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode m) ≤
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode m) + 2 := by
  intro m
  rw [target.proof_length_exact m]
  exact le_trans (hsource_upper m)
    (by exact_mod_cast target.proofFamily.minLength_rightConjElim_le m)

theorem FormulaCodeUpperLengthRealization.source_upper_of_rightConjElim
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (target :
      FormulaCodeMinLengthRealization Ax (fun m => A m ⊓ B m)
        sondowReflectionGraftCode)
    (source :
      FormulaCodeUpperLengthRealization Ax B partialConsistencyCode)
    (hsource :
      ∀ m : ℕ, source.proofFamily.minLength m =
        target.proofFamily.rightConjElim.minLength m) :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode m) ≤
        target.proofFamily.rightConjElim.minLength m := by
  intro m
  rw [← hsource m]
  exact source.proof_length_le m

theorem FormulaCodeUpperLengthRealization.source_le_target_add_two_of_rightConjElim
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (target :
      FormulaCodeMinLengthRealization Ax (fun m => A m ⊓ B m)
        sondowReflectionGraftCode)
    (source :
      FormulaCodeUpperLengthRealization Ax B partialConsistencyCode)
    (hsource :
      ∀ m : ℕ, source.proofFamily.minLength m =
        target.proofFamily.rightConjElim.minLength m) :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode m) ≤
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode m) + 2 :=
  FormulaCodeMinLengthRealization.source_le_target_add_two_of_rightConjElim_upper
    target
    (FormulaCodeUpperLengthRealization.source_upper_of_rightConjElim
      target source hsource)

noncomputable def FormulaCodeMinLengthRealization.toExactProjectionRealization
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (target :
      FormulaCodeMinLengthRealization Ax (fun m => A m ⊓ B m)
        sondowReflectionGraftCode)
    (source :
      FormulaCodeMinLengthRealization Ax B partialConsistencyCode)
    (hsource :
      ∀ m : ℕ, source.proofFamily.minLength m =
        target.proofFamily.rightConjElim.minLength m) :
    HilbertProofLengthExactProjectionRealization halign where
  sourceLength := source.proofFamily.minLength
  targetLength := target.proofFamily.minLength
  source_exact := source.proof_length_exact
  target_exact := target.proof_length_exact
  source_le_target_add_two := by
    intro m
    rw [hsource m]
    exact target.proofFamily.minLength_rightConjElim_le m

theorem FormulaCodeMinLengthRealization.toHilbertBridge
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (target :
      FormulaCodeMinLengthRealization Ax (fun m => A m ⊓ B m)
        sondowReflectionGraftCode)
    (source :
      FormulaCodeMinLengthRealization Ax B partialConsistencyCode)
    (hsource :
      ∀ m : ℕ, source.proofFamily.minLength m =
        target.proofFamily.rightConjElim.minLength m) :
    HilbertProofLengthSoundnessBridge :=
  (FormulaCodeMinLengthRealization.toExactProjectionRealization
    (halign := halign) target source hsource).toBridge

noncomputable def FormulaCodeMinLengthRealization.toTargetExactProjectionRealization
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (target :
      FormulaCodeMinLengthRealization Ax (fun m => A m ⊓ B m)
        sondowReflectionGraftCode)
    (hsource_upper :
      ∀ m : ℕ,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode m) ≤
          target.proofFamily.rightConjElim.minLength m) :
    HilbertProofLengthTargetExactProjectionRealization halign where
  targetLength := target.proofFamily.minLength
  target_exact := target.proof_length_exact
  source_le_targetLength_add_two := by
    intro m
    rw [← target.proof_length_exact m]
    exact FormulaCodeMinLengthRealization.source_le_target_add_two_of_rightConjElim_upper
      target hsource_upper m

theorem FormulaCodeMinLengthRealization.toHilbertBridge_of_source_upper
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (target :
      FormulaCodeMinLengthRealization Ax (fun m => A m ⊓ B m)
        sondowReflectionGraftCode)
    (hsource_upper :
      ∀ m : ℕ,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode m) ≤
          target.proofFamily.rightConjElim.minLength m) :
    HilbertProofLengthSoundnessBridge :=
  (FormulaCodeMinLengthRealization.toTargetExactProjectionRealization
    (halign := halign) target hsource_upper).toBridge

noncomputable def FormulaCodeUpperLengthRealization.toTargetExactProjectionRealization
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (target :
      FormulaCodeMinLengthRealization Ax (fun m => A m ⊓ B m)
        sondowReflectionGraftCode)
    (source :
      FormulaCodeUpperLengthRealization Ax B partialConsistencyCode)
    (hsource :
      ∀ m : ℕ, source.proofFamily.minLength m =
        target.proofFamily.rightConjElim.minLength m) :
    HilbertProofLengthTargetExactProjectionRealization halign :=
  FormulaCodeMinLengthRealization.toTargetExactProjectionRealization
    (halign := halign) target
    (FormulaCodeUpperLengthRealization.source_upper_of_rightConjElim
      target source hsource)

theorem FormulaCodeUpperLengthRealization.toHilbertBridge
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (target :
      FormulaCodeMinLengthRealization Ax (fun m => A m ⊓ B m)
        sondowReflectionGraftCode)
    (source :
      FormulaCodeUpperLengthRealization Ax B partialConsistencyCode)
    (hsource :
      ∀ m : ℕ, source.proofFamily.minLength m =
        target.proofFamily.rightConjElim.minLength m) :
    HilbertProofLengthSoundnessBridge :=
  (FormulaCodeUpperLengthRealization.toTargetExactProjectionRealization
    (halign := halign) target source hsource).toBridge

noncomputable def FormulaCodeMinLengthRealization.rightConjElimUpperLengthRealization
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (target :
      FormulaCodeMinLengthRealization Ax (fun m => A m ⊓ B m)
        sondowReflectionGraftCode)
    (hsource_upper :
      ∀ m : ℕ,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode m) ≤
          target.proofFamily.rightConjElim.minLength m) :
    FormulaCodeUpperLengthRealization Ax B partialConsistencyCode where
  proofFamily := target.proofFamily.rightConjElim
  proof_length_le := hsource_upper

theorem FormulaCodeMinLengthRealization.toHilbertBridge_of_rightConjElimUpper
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (target :
      FormulaCodeMinLengthRealization Ax (fun m => A m ⊓ B m)
        sondowReflectionGraftCode)
    (hsource_upper :
      ∀ m : ℕ,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode m) ≤
          target.proofFamily.rightConjElim.minLength m) :
    HilbertProofLengthSoundnessBridge :=
  FormulaCodeUpperLengthRealization.toHilbertBridge
    (halign := halign)
    target
    (target.rightConjElimUpperLengthRealization hsource_upper)
    (by intro m; rfl)

def localFormulaCodeHilbertInterpretation
    (A B : ℕ → L.BoundedFormula α n) (code : FormulaCode) :
    L.BoundedFormula α n :=
  match code.family with
  | FormulaFamily.partialConsistency => B code.index
  | FormulaFamily.sondowReflectionGraft => A code.index ⊓ B code.index
  | _ => B code.index

theorem localFormulaCodeHilbertInterpretation_partialConsistency
    (A B : ℕ → L.BoundedFormula α n) (m : ℕ) :
    localFormulaCodeHilbertInterpretation A B (partialConsistencyCode m) =
      B m := by
  rfl

theorem localFormulaCodeHilbertInterpretation_reflectionGraft
    (A B : ℕ → L.BoundedFormula α n) (m : ℕ) :
    localFormulaCodeHilbertInterpretation A B (sondowReflectionGraftCode m) =
      A m ⊓ B m := by
  rfl

structure LocalFormulaCodeHilbertInterpretation
    (A B : ℕ → L.BoundedFormula α n) where
  interpret : FormulaCode → L.BoundedFormula α n
  interprets_partial_consistency :
    ∀ m : ℕ, interpret (partialConsistencyCode m) = B m
  interprets_reflection_graft :
    ∀ m : ℕ, interpret (sondowReflectionGraftCode m) = A m ⊓ B m

def LocalFormulaCodeHilbertInterpretation.default
    (A B : ℕ → L.BoundedFormula α n) :
    LocalFormulaCodeHilbertInterpretation A B where
  interpret := localFormulaCodeHilbertInterpretation A B
  interprets_partial_consistency :=
    localFormulaCodeHilbertInterpretation_partialConsistency A B
  interprets_reflection_graft :=
    localFormulaCodeHilbertInterpretation_reflectionGraft A B

structure HilbertRightConjElimFormulaCodeRealization
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  target :
    FormulaCodeMinLengthRealization Ax (fun m => A m ⊓ B m)
      sondowReflectionGraftCode
  source_upper :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode m) ≤
        target.proofFamily.rightConjElim.minLength m

-- The syntactic/interpretation half of the formula-code bridge.  This does not
-- assign semantics to the global `proof_length`; it only records that the
-- reflection-graft code is interpreted by a concrete MiniHilbert conjunction
-- family and that the project-level `FormulaCode` alignment has already been
-- discharged.
structure FormulaCodeHilbertInterpretation
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  local_interpretation : LocalFormulaCodeHilbertInterpretation A B
  target_proof_family : ConcreteProofFamily Ax (fun m => A m ⊓ B m)
  code_alignment : halign = hilbert_projection_code_alignment_true

-- The remaining semantic calibration.  This is exactly where the external
-- global proof-length convention must be connected to the concrete MiniHilbert
-- model; unlike the interpretation above, this cannot be proved while
-- `proof_length` remains an abstract axiom.
structure FormulaCodeProofLengthCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  target_exact :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode m) =
        interp.target_proof_family.minLength m
  source_upper :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode m) ≤
        interp.target_proof_family.rightConjElim.minLength m

-- A standard semantics source for the calibration above: on the two formula
-- families used by the projection bridge, the global project-level
-- `proof_length` is the minimum length in the concrete MiniHilbert model.
-- This is stronger than `FormulaCodeProofLengthCalibration` because it fixes
-- the source side by equality rather than only by an upper bound.
structure StandardFormulaCodeProofLengthSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  target_minLength :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode m) =
        interp.target_proof_family.minLength m
  source_minLength :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode m) =
        interp.target_proof_family.rightConjElim.minLength m

theorem StandardFormulaCodeProofLengthSemantics.toCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hsem : StandardFormulaCodeProofLengthSemantics interp) :
    FormulaCodeProofLengthCalibration interp where
  target_exact := hsem.target_minLength
  source_upper := by
    intro m
    rw [hsem.source_minLength m]

noncomputable def StandardFormulaCodeProofLengthSemantics.toTargetMinLengthRealization
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hsem : StandardFormulaCodeProofLengthSemantics interp) :
    FormulaCodeMinLengthRealization Ax (fun m => A m ⊓ B m)
      sondowReflectionGraftCode where
  proofFamily := interp.target_proof_family
  proof_length_exact := hsem.target_minLength

noncomputable def StandardFormulaCodeProofLengthSemantics.toSourceMinLengthRealization
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hsem : StandardFormulaCodeProofLengthSemantics interp) :
    FormulaCodeMinLengthRealization Ax B partialConsistencyCode where
  proofFamily := interp.target_proof_family.rightConjElim
  proof_length_exact := hsem.source_minLength

theorem StandardFormulaCodeProofLengthSemantics.source_minLength_matches_rightConjElim
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hsem : StandardFormulaCodeProofLengthSemantics interp) (m : ℕ) :
    (hsem.toSourceMinLengthRealization.proofFamily.minLength m) =
      (hsem.toTargetMinLengthRealization.proofFamily.rightConjElim.minLength m) := by
  rfl

noncomputable def StandardFormulaCodeProofLengthSemantics.toExactProjectionRealization
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hsem : StandardFormulaCodeProofLengthSemantics interp) :
    HilbertProofLengthExactProjectionRealization halign :=
  FormulaCodeMinLengthRealization.toExactProjectionRealization
    (halign := halign)
    hsem.toTargetMinLengthRealization
    hsem.toSourceMinLengthRealization
    hsem.source_minLength_matches_rightConjElim

noncomputable def StandardFormulaCodeProofLengthSemantics.toTargetExactProjectionRealization
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hsem : StandardFormulaCodeProofLengthSemantics interp) :
    HilbertProofLengthTargetExactProjectionRealization halign :=
  FormulaCodeMinLengthRealization.toTargetExactProjectionRealization
    (halign := halign)
    hsem.toTargetMinLengthRealization
    (by
      intro m
      rw [hsem.source_minLength m]
      exact le_rfl)

-- Conversely, an exact projection realization yields the standard local
-- minLength semantics once its abstract Nat-valued lengths are identified with
-- the concrete MiniHilbert source/target minLength functions.  This keeps the
-- remaining proof-length debt in a checkable, non-ad-hoc shape.
structure ExactProjectionRealizationMatchesFormulaCodeInterpretation
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hexact : HilbertProofLengthExactProjectionRealization halign) where
  targetLength_eq_minLength :
    ∀ m : ℕ, hexact.targetLength m = interp.target_proof_family.minLength m
  sourceLength_eq_minLength :
    ∀ m : ℕ,
      hexact.sourceLength m = interp.target_proof_family.rightConjElim.minLength m

theorem ExactProjectionRealizationMatchesFormulaCodeInterpretation.toStandardSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    {hexact : HilbertProofLengthExactProjectionRealization halign}
    (hmatch :
      ExactProjectionRealizationMatchesFormulaCodeInterpretation interp hexact) :
    StandardFormulaCodeProofLengthSemantics interp where
  target_minLength := by
    intro m
    rw [hexact.target_exact m, hmatch.targetLength_eq_minLength m]
  source_minLength := by
    intro m
    rw [hexact.source_exact m, hmatch.sourceLength_eq_minLength m]

theorem StandardFormulaCodeProofLengthSemantics.exactProjectionRealizationMatches
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hsem : StandardFormulaCodeProofLengthSemantics interp) :
    ExactProjectionRealizationMatchesFormulaCodeInterpretation
      interp hsem.toExactProjectionRealization where
  targetLength_eq_minLength := by
    intro m
    rfl
  sourceLength_eq_minLength := by
    intro m
    rfl

theorem StandardFormulaCodeProofLengthSemantics.toStandardSemantics_roundtrip
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hsem : StandardFormulaCodeProofLengthSemantics interp) :
    ExactProjectionRealizationMatchesFormulaCodeInterpretation.toStandardSemantics
      hsem.exactProjectionRealizationMatches = hsem := by
  cases hsem
  rfl

-- A fully local proof-length model for the two formula families used in the
-- projection bridge.  This does not mention the global project-level
-- `proof_length`; it is the concrete MiniHilbert minLength model that a later
-- project-level semantics can choose to calibrate against.
noncomputable def FormulaCodeHilbertInterpretation.localProofLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (code : FormulaCode) : ℕ :=
  match code.family with
  | FormulaFamily.partialConsistency =>
      interp.target_proof_family.rightConjElim.minLength code.index
  | FormulaFamily.sondowReflectionGraft =>
      interp.target_proof_family.minLength code.index
  | _ => interp.target_proof_family.minLength code.index

theorem FormulaCodeHilbertInterpretation.localProofLength_partialConsistency
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.localProofLength (partialConsistencyCode m) =
      interp.target_proof_family.rightConjElim.minLength m := by
  rfl

theorem FormulaCodeHilbertInterpretation.localProofLength_reflectionGraft
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.localProofLength (sondowReflectionGraftCode m) =
      interp.target_proof_family.minLength m := by
  rfl

theorem FormulaCodeHilbertInterpretation.localProofLength_rightConjElim_le_add_two
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.localProofLength (partialConsistencyCode m) ≤
      interp.localProofLength (sondowReflectionGraftCode m) + 2 := by
  rw [interp.localProofLength_partialConsistency m,
    interp.localProofLength_reflectionGraft m]
  exact interp.target_proof_family.minLength_rightConjElim_le m

noncomputable def FormulaCodeHilbertInterpretation.localCodeSizeProofLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (code : FormulaCode) : ℕ :=
  match code.family with
  | FormulaFamily.partialConsistency =>
      interp.target_proof_family.rightConjElim.minCodeSize code.index
  | FormulaFamily.sondowReflectionGraft =>
      interp.target_proof_family.minCodeSize code.index
  | _ => interp.target_proof_family.minCodeSize code.index

theorem FormulaCodeHilbertInterpretation.localCodeSizeProofLength_partialConsistency
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.localCodeSizeProofLength (partialConsistencyCode m) =
      interp.target_proof_family.rightConjElim.minCodeSize m := by
  rfl

theorem FormulaCodeHilbertInterpretation.localCodeSizeProofLength_reflectionGraft
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.localCodeSizeProofLength (sondowReflectionGraftCode m) =
      interp.target_proof_family.minCodeSize m := by
  rfl

theorem FormulaCodeHilbertInterpretation.localCodeSizeProofLength_eq_localProofLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (code : FormulaCode) :
    interp.localCodeSizeProofLength code = interp.localProofLength code := by
  cases code with
  | mk family index =>
      cases family <;> simp [FormulaCodeHilbertInterpretation.localCodeSizeProofLength,
        FormulaCodeHilbertInterpretation.localProofLength,
        ConcreteProofFamily.minCodeSize_eq_minLength]

theorem FormulaCodeHilbertInterpretation.localCodeSizeProofLength_rightConjElim_le_add_two
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.localCodeSizeProofLength (partialConsistencyCode m) ≤
      interp.localCodeSizeProofLength (sondowReflectionGraftCode m) + 2 := by
  rw [interp.localCodeSizeProofLength_eq_localProofLength (partialConsistencyCode m),
    interp.localCodeSizeProofLength_eq_localProofLength (sondowReflectionGraftCode m)]
  exact interp.localProofLength_rightConjElim_le_add_two m

noncomputable def FormulaCodeHilbertInterpretation.localCheckedCodeProofLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (code : FormulaCode) : ℕ :=
  match code.family with
  | FormulaFamily.partialConsistency =>
      interp.target_proof_family.rightConjElim.minCheckedCodeSize code.index
  | FormulaFamily.sondowReflectionGraft =>
      interp.target_proof_family.minCheckedCodeSize code.index
  | _ => interp.target_proof_family.minCheckedCodeSize code.index

noncomputable def FormulaCodeHilbertInterpretation.canonicalMinCheckedLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (code : FormulaCode) : ℕ :=
  interp.localCheckedCodeProofLength code

theorem FormulaCodeHilbertInterpretation.canonicalMinCheckedLength_eq_localChecked
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (code : FormulaCode) :
    interp.canonicalMinCheckedLength code =
      interp.localCheckedCodeProofLength code := by
  rfl

theorem FormulaCodeHilbertInterpretation.localCheckedCodeProofLength_partialConsistency
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.localCheckedCodeProofLength (partialConsistencyCode m) =
      interp.target_proof_family.rightConjElim.minCheckedCodeSize m := by
  rfl

theorem FormulaCodeHilbertInterpretation.canonicalMinCheckedLength_partialConsistency
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.canonicalMinCheckedLength (partialConsistencyCode m) =
      interp.target_proof_family.rightConjElim.minCheckedCodeSize m := by
  rfl

theorem FormulaCodeHilbertInterpretation.localCheckedCodeProofLength_reflectionGraft
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.localCheckedCodeProofLength (sondowReflectionGraftCode m) =
      interp.target_proof_family.minCheckedCodeSize m := by
  rfl

theorem FormulaCodeHilbertInterpretation.canonicalMinCheckedLength_reflectionGraft
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.canonicalMinCheckedLength (sondowReflectionGraftCode m) =
      interp.target_proof_family.minCheckedCodeSize m := by
  rfl

noncomputable def FormulaCodeHilbertInterpretation.projectCheckedProofLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (code : FormulaCode) : ℝ :=
  interp.localCheckedCodeProofLength code

theorem FormulaCodeHilbertInterpretation.projectCheckedProofLength_eq_localChecked
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (code : FormulaCode) :
    interp.projectCheckedProofLength code =
      interp.localCheckedCodeProofLength code := by
  rfl

theorem FormulaCodeHilbertInterpretation.projectCheckedProofLength_partialConsistency
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.projectCheckedProofLength (partialConsistencyCode m) =
      interp.target_proof_family.rightConjElim.minCheckedCodeSize m := by
  rw [FormulaCodeHilbertInterpretation.projectCheckedProofLength]
  exact_mod_cast interp.localCheckedCodeProofLength_partialConsistency m

theorem FormulaCodeHilbertInterpretation.projectCheckedProofLength_reflectionGraft
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.projectCheckedProofLength (sondowReflectionGraftCode m) =
      interp.target_proof_family.minCheckedCodeSize m := by
  rw [FormulaCodeHilbertInterpretation.projectCheckedProofLength]
  exact_mod_cast interp.localCheckedCodeProofLength_reflectionGraft m

theorem FormulaCodeHilbertInterpretation.localCheckedCodeProofLength_eq_localCodeSizeProofLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (code : FormulaCode) :
    interp.localCheckedCodeProofLength code = interp.localCodeSizeProofLength code := by
  cases code with
  | mk family index =>
      cases family <;> simp [FormulaCodeHilbertInterpretation.localCheckedCodeProofLength,
        FormulaCodeHilbertInterpretation.localCodeSizeProofLength,
        ConcreteProofFamily.minCheckedCodeSize_eq_minCodeSize]

theorem FormulaCodeHilbertInterpretation.localCheckedCodeProofLength_eq_localProofLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (code : FormulaCode) :
    interp.localCheckedCodeProofLength code = interp.localProofLength code := by
  rw [interp.localCheckedCodeProofLength_eq_localCodeSizeProofLength code,
    interp.localCodeSizeProofLength_eq_localProofLength code]

theorem FormulaCodeHilbertInterpretation.localCheckedCodeProofLength_rightConjElim_le_add_two
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.localCheckedCodeProofLength (partialConsistencyCode m) ≤
      interp.localCheckedCodeProofLength (sondowReflectionGraftCode m) + 2 := by
  rw [interp.localCheckedCodeProofLength_eq_localProofLength (partialConsistencyCode m),
    interp.localCheckedCodeProofLength_eq_localProofLength (sondowReflectionGraftCode m)]
  exact interp.localProofLength_rightConjElim_le_add_two m

theorem FormulaCodeHilbertInterpretation.semanticBridge_of_localCheckedCodeProofLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    SemanticHilbertProofLengthSoundnessBridge
      interp.localCheckedCodeProofLength where
  realizes_right_conj_elim :=
    interp.localCheckedCodeProofLength_rightConjElim_le_add_two

noncomputable def
    FormulaCodeHilbertInterpretation.semanticConstantProjection_of_localCheckedCodeProofLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    SemanticConstantProofLengthProjection
      interp.localCheckedCodeProofLength
      partialConsistencyCode sondowReflectionGraftCode :=
  interp.semanticBridge_of_localCheckedCodeProofLength.toSemanticConstantProjection

noncomputable def
    FormulaCodeHilbertInterpretation.semanticStrongTransfer_of_localCheckedCodeProofLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    SemanticStrongLowerBoundTransfer
      interp.localCheckedCodeProofLength
      partialConsistencyCode sondowReflectionGraftCode :=
  SemanticConstantProofLengthProjection.toSemanticStrongLowerBoundTransfer
    interp.semanticConstantProjection_of_localCheckedCodeProofLength

noncomputable def
    FormulaCodeHilbertInterpretation.semanticReflectionGraftLowerBound_of_localCheckedSource
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource :
      SemanticStrongProofLengthLowerBound
        interp.localCheckedCodeProofLength partialConsistencyCode) :
    SemanticStrongProofLengthLowerBound
      interp.localCheckedCodeProofLength sondowReflectionGraftCode :=
  hsource.transfer interp.semanticStrongTransfer_of_localCheckedCodeProofLength

noncomputable def
    FormulaCodeHilbertInterpretation.semanticReflectionGraftEventualLowerBound_of_localCheckedSource
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource :
      SemanticStrongProofLengthLowerBound
        interp.localCheckedCodeProofLength partialConsistencyCode) :
    SemanticEventualLowerBound
      interp.localCheckedCodeProofLength sondowReflectionGraftCode :=
  SemanticStrongProofLengthLowerBound.toSemanticEventualLowerBound
    (interp.semanticReflectionGraftLowerBound_of_localCheckedSource hsource)

theorem FormulaCodeHilbertInterpretation.localCheckedPartialConsistencyLowerBound_of_sourceLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource :
      SemanticStrongNatLowerBound
        interp.target_proof_family.rightConjElim.minCheckedCodeSize) :
    SemanticStrongProofLengthLowerBound
      interp.localCheckedCodeProofLength partialConsistencyCode :=
  hsource.toFormulaCodeLowerBound
    interp.localCheckedCodeProofLength_partialConsistency

structure PartialConsistencySourceMinCheckedCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) : Prop where
  proof_length_eq_source_minChecked :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode m) =
        interp.target_proof_family.rightConjElim.minCheckedCodeSize m

theorem PartialConsistencySourceMinCheckedCalibration.toSemanticStrongNatLowerBound
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcal : PartialConsistencySourceMinCheckedCalibration interp)
    (hlower : StrongPartialConsistencyLowerBound) :
    SemanticStrongNatLowerBound
      interp.target_proof_family.rightConjElim.minCheckedCodeSize where
  frequently_beats_every_polynomial := by
    intro f hf
    exact (hlower.frequently_beats_every_polynomial f hf).mono fun m hm => by
      simpa [hcal.proof_length_eq_source_minChecked m] using hm

theorem PartialConsistencySourceMinCheckedCalibration.semanticStrongNatLowerBound_of_rescaling
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcal : PartialConsistencySourceMinCheckedCalibration interp)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem) :
    SemanticStrongNatLowerBound
      interp.target_proof_family.rightConjElim.minCheckedCodeSize :=
  hcal.toSemanticStrongNatLowerBound
    hrescale.toStrongPartialConsistencyLowerBound

structure LocalFormulaCodeProjectionLengthModel
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  length : FormulaCode → ℕ
  source_exact :
    ∀ m : ℕ, length (partialConsistencyCode m) =
      interp.target_proof_family.rightConjElim.minLength m
  target_exact :
    ∀ m : ℕ, length (sondowReflectionGraftCode m) =
      interp.target_proof_family.minLength m
  source_le_target_add_two :
    ∀ m : ℕ,
      length (partialConsistencyCode m) ≤
        length (sondowReflectionGraftCode m) + 2

noncomputable def FormulaCodeHilbertInterpretation.localProjectionLengthModel
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    LocalFormulaCodeProjectionLengthModel interp where
  length := interp.localProofLength
  source_exact := interp.localProofLength_partialConsistency
  target_exact := interp.localProofLength_reflectionGraft
  source_le_target_add_two :=
    interp.localProofLength_rightConjElim_le_add_two

structure LocalFormulaCodeProjectionCheckedCodeModel
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  length : FormulaCode → ℕ
  source_exact :
    ∀ m : ℕ, length (partialConsistencyCode m) =
      interp.target_proof_family.rightConjElim.minCheckedCodeSize m
  target_exact :
    ∀ m : ℕ, length (sondowReflectionGraftCode m) =
      interp.target_proof_family.minCheckedCodeSize m
  source_le_target_add_two :
    ∀ m : ℕ,
      length (partialConsistencyCode m) ≤
        length (sondowReflectionGraftCode m) + 2

noncomputable def FormulaCodeHilbertInterpretation.localProjectionCheckedCodeModel
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    LocalFormulaCodeProjectionCheckedCodeModel interp where
  length := interp.localCheckedCodeProofLength
  source_exact := interp.localCheckedCodeProofLength_partialConsistency
  target_exact := interp.localCheckedCodeProofLength_reflectionGraft
  source_le_target_add_two :=
    interp.localCheckedCodeProofLength_rightConjElim_le_add_two

def FormulaCodeHilbertRelevantCode (code : FormulaCode) : Prop :=
  (∃ m : ℕ, code = partialConsistencyCode m) ∨
    ∃ m : ℕ, code = sondowReflectionGraftCode m

theorem SemanticHilbertProofLengthSoundnessBridge.toBridge
    {length : FormulaCode → ℕ}
    (hsemantic : SemanticHilbertProofLengthSoundnessBridge length)
    (hproof_length :
      ∀ code : FormulaCode, FormulaCodeHilbertRelevantCode code →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          length code) :
    HilbertProofLengthSoundnessBridge where
  realizes_right_conj_elim := by
    intro n
    rw [hproof_length (partialConsistencyCode n) (Or.inl ⟨n, rfl⟩),
      hproof_length (sondowReflectionGraftCode n) (Or.inr ⟨n, rfl⟩)]
    exact_mod_cast hsemantic.realizes_right_conj_elim n

theorem SemanticHilbertProofLengthSoundnessBridge.toBridge_of_projectSemantics
    {length : FormulaCode → ℕ}
    (hsemantic : SemanticHilbertProofLengthSoundnessBridge length)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        length FormulaCodeHilbertRelevantCode) :
    HilbertProofLengthSoundnessBridge :=
  SemanticHilbertProofLengthSoundnessBridge.toBridge
    hsemantic hsem.proof_length_eq

noncomputable def FormulaCodeHilbertInterpretation.localProofCodeSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProofCodeSemantics FormulaCodeHilbertRelevantCode where
  Code := FormulaCode
  checks := fun c code => c = code
  size := interp.localCheckedCodeProofLength
  complete := by
    intro code _hcode
    exact ⟨code, rfl⟩

theorem FormulaCodeHilbertInterpretation.localProofCodeSemantics_minProofCodeSize_eq
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (code : FormulaCode) (hcode : FormulaCodeHilbertRelevantCode code) :
    (interp.localProofCodeSemantics.minProofCodeSize code hcode) =
      interp.localCheckedCodeProofLength code := by
  apply Nat.le_antisymm
  · exact interp.localProofCodeSemantics.minProofCodeSize_le_of_hasProofCodeOfSize
      hcode ⟨code, rfl, le_rfl⟩
  · rcases interp.localProofCodeSemantics.hasProofCodeOfSize_minProofCodeSize
      hcode with ⟨c, hc, hsize⟩
    dsimp [FormulaCodeHilbertInterpretation.localProofCodeSemantics] at hc hsize
    rw [hc] at hsize
    exact hsize

theorem FormulaCodeHilbertInterpretation.localProofCode_projectLength_eq_projectChecked
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ)
    (code : FormulaCode) (hcode : FormulaCodeHilbertRelevantCode code) :
    interp.localProofCodeSemantics.projectLength fallback code =
      interp.projectCheckedProofLength code := by
  rw [interp.localProofCodeSemantics.projectLength_eq_minProofCodeSize fallback hcode,
    interp.localProofCodeSemantics_minProofCodeSize_eq code hcode,
    interp.projectCheckedProofLength_eq_localChecked code]

theorem FormulaCodeHilbertInterpretation.projectCheckedCodeSemantics_of_localProofCodeSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hproof_length :
      ∀ code : FormulaCode, ∀ hcode : FormulaCodeHilbertRelevantCode code,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          interp.localProofCodeSemantics.minProofCodeSize code hcode) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode :=
  interp.localProofCodeSemantics.toProjectProofLengthSemantics
    ProofSystem.PA ProofLengthMeasure.symbolSize
    interp.localCheckedCodeProofLength
    (by
      intro code hcode
      exact (interp.localProofCodeSemantics_minProofCodeSize_eq code hcode).symm)
    hproof_length

inductive LocalHilbertProofCode
    {Ax : L.BoundedFormula α n → Prop}
    (A B : ℕ → L.BoundedFormula α n) :
    Type (max u v w) where
  | source (m : ℕ) : TheoryProof.Code Ax (B m) → LocalHilbertProofCode A B
  | target (m : ℕ) : TheoryProof.Code Ax (A m ⊓ B m) → LocalHilbertProofCode A B

def LocalHilbertProofCode.checks
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (c : LocalHilbertProofCode (Ax := Ax) A B) (code : FormulaCode) : Prop :=
  match c with
  | LocalHilbertProofCode.source m _ => code = partialConsistencyCode m
  | LocalHilbertProofCode.target m _ => code = sondowReflectionGraftCode m

def LocalHilbertProofCode.size
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (c : LocalHilbertProofCode (Ax := Ax) A B) : ℕ :=
  match c with
  | LocalHilbertProofCode.source _ proofCode => proofCode.size
  | LocalHilbertProofCode.target _ proofCode => proofCode.size

noncomputable def FormulaCodeHilbertInterpretation.localHilbertProofCodeSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProofCodeSemantics FormulaCodeHilbertRelevantCode where
  Code := LocalHilbertProofCode (Ax := Ax) A B
  checks := LocalHilbertProofCode.checks
  size := LocalHilbertProofCode.size
  complete := by
    intro code hcode
    rcases hcode with ⟨m, hcode⟩ | ⟨m, hcode⟩
    · refine ⟨LocalHilbertProofCode.source m
        (TheoryProof.Code.ofProof (interp.target_proof_family.rightConjElim.proof m)), ?_⟩
      exact hcode
    · refine ⟨LocalHilbertProofCode.target m
        (TheoryProof.Code.ofProof (interp.target_proof_family.proof m)), ?_⟩
      exact hcode

theorem FormulaCodeHilbertInterpretation.localHilbertProofCodeSemantics_source_min_eq
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.localHilbertProofCodeSemantics.minProofCodeSize
        (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩) =
      interp.target_proof_family.rightConjElim.minCheckedCodeSize m := by
  apply Nat.le_antisymm
  · rcases TheoryProof.hasCheckedCodeOfSize_minCheckedCodeSize
      (interp.target_proof_family.rightConjElim.provable m) with ⟨c, hc⟩
    exact interp.localHilbertProofCodeSemantics.minProofCodeSize_le_of_hasProofCodeOfSize
      (Or.inl ⟨m, rfl⟩)
      ⟨LocalHilbertProofCode.source m c, rfl, hc⟩
  · rcases interp.localHilbertProofCodeSemantics.hasProofCodeOfSize_minProofCodeSize
      (Or.inl ⟨m, rfl⟩) with ⟨c, hchecks, hsize⟩
    cases c with
    | source m' proofCode =>
        have hm : m = m' := by
          simpa [partialConsistencyCode] using congrArg FormulaCode.index hchecks
        cases hm
        exact TheoryProof.minCheckedCodeSize_le_of_hasCheckedCodeOfSize
          (interp.target_proof_family.rightConjElim.provable m)
          ⟨proofCode, hsize⟩
    | target m' proofCode =>
        have hfam := congrArg FormulaCode.family hchecks
        simp [partialConsistencyCode, sondowReflectionGraftCode] at hfam

theorem FormulaCodeHilbertInterpretation.localHilbertProofCodeSemantics_target_min_eq
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.localHilbertProofCodeSemantics.minProofCodeSize
        (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩) =
      interp.target_proof_family.minCheckedCodeSize m := by
  apply Nat.le_antisymm
  · rcases TheoryProof.hasCheckedCodeOfSize_minCheckedCodeSize
      (interp.target_proof_family.provable m) with ⟨c, hc⟩
    exact interp.localHilbertProofCodeSemantics.minProofCodeSize_le_of_hasProofCodeOfSize
      (Or.inr ⟨m, rfl⟩)
      ⟨LocalHilbertProofCode.target m c, rfl, hc⟩
  · rcases interp.localHilbertProofCodeSemantics.hasProofCodeOfSize_minProofCodeSize
      (Or.inr ⟨m, rfl⟩) with ⟨c, hchecks, hsize⟩
    cases c with
    | source m' proofCode =>
        have hfam := congrArg FormulaCode.family hchecks
        simp [partialConsistencyCode, sondowReflectionGraftCode] at hfam
    | target m' proofCode =>
        have hm : m = m' := by
          simpa [sondowReflectionGraftCode] using congrArg FormulaCode.index hchecks
        cases hm
        exact TheoryProof.minCheckedCodeSize_le_of_hasCheckedCodeOfSize
          (interp.target_proof_family.provable m)
          ⟨proofCode, hsize⟩

theorem FormulaCodeHilbertInterpretation.localHilbertProofCodeSemantics_rightConjElim_le_add_two
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.localHilbertProofCodeSemantics.minProofCodeSize
        (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩) ≤
      interp.localHilbertProofCodeSemantics.minProofCodeSize
        (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩) + 2 := by
  rw [interp.localHilbertProofCodeSemantics_source_min_eq m,
    interp.localHilbertProofCodeSemantics_target_min_eq m]
  exact interp.target_proof_family.minCheckedCodeSize_rightConjElim_le m

-- Concrete checker exactness for the local Hilbert proof-code semantics.  This
-- part is internal: the minimum proof-code size computed by the checker is
-- definitionally the same checked-code length model used by the projection
-- bridge on the relevant formula-code fragment.
structure PAHilbertLocalCheckerExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) : Prop where
  minProofCodeSize_eq_localChecked :
    ∀ code : FormulaCode, ∀ hcode : FormulaCodeHilbertRelevantCode code,
      interp.localHilbertProofCodeSemantics.minProofCodeSize code hcode =
        interp.localCheckedCodeProofLength code

theorem FormulaCodeHilbertInterpretation.localHilbertProofCodeSemantics_min_eq_localChecked
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (code : FormulaCode) (hcode : FormulaCodeHilbertRelevantCode code) :
    interp.localHilbertProofCodeSemantics.minProofCodeSize code hcode =
      interp.localCheckedCodeProofLength code := by
  rcases hcode with ⟨m, hcode_eq⟩ | ⟨m, hcode_eq⟩
  · subst hcode_eq
    rw [interp.localHilbertProofCodeSemantics_source_min_eq m,
      interp.localCheckedCodeProofLength_partialConsistency m]
  · subst hcode_eq
    rw [interp.localHilbertProofCodeSemantics_target_min_eq m,
      interp.localCheckedCodeProofLength_reflectionGraft m]

theorem FormulaCodeHilbertInterpretation.localHilbertCheckerExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertLocalCheckerExactness interp where
  minProofCodeSize_eq_localChecked :=
    interp.localHilbertProofCodeSemantics_min_eq_localChecked

structure PartialConsistencyHilbertAcceptedSoundness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) : Prop where
  source_checked_sound :
    ∀ n : ℕ, ∀ c : interp.localHilbertProofCodeSemantics.Code,
      interp.localHilbertProofCodeSemantics.checks c
        (partialConsistencyCode n) →
        accepted_certificate (partialConsistencyCode n)

theorem PartialConsistencyHilbertAcceptedSoundness.of_payload_spec
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hspec : PartialConsistencyPayloadSpec) :
    PartialConsistencyHilbertAcceptedSoundness interp where
  source_checked_sound := by
    intro n _c _hchecks
    have hpayload : partial_consistency_payload n :=
      hspec.payload_truth.true_all n
    rw [← hspec.code_family_eq]
    exact (hspec.accepted_iff_payload n).2 hpayload

noncomputable def FormulaCodeHilbertInterpretation.toPartialConsistencyAcceptedCodeSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsound : PartialConsistencyHilbertAcceptedSoundness interp) :
    AcceptedCertificateCodeSemantics partialConsistencyCode where
  relevant := FormulaCodeHilbertRelevantCode
  proof_code_semantics := interp.localHilbertProofCodeSemantics
  relevant_family := by
    intro m
    exact Or.inl ⟨m, rfl⟩
  checks_sound := by
    intro c m hchecks
    exact hsound.source_checked_sound m c hchecks
  checks_complete := by
    intro m _hacc
    exact interp.localHilbertProofCodeSemantics.complete
      (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)

noncomputable def
    FormulaCodeHilbertInterpretation.toPartialConsistencyAcceptedCodeSemanticsOfPayloadSpec
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec) :
    AcceptedCertificateCodeSemantics partialConsistencyCode :=
  interp.toPartialConsistencyAcceptedCodeSemantics
    (PartialConsistencyHilbertAcceptedSoundness.of_payload_spec hspec)

structure PartialConsistencyHilbertS21TraceSoundness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) : Prop where
  source_checked_short_s21 :
    ∀ n : ℕ, ∀ c : interp.localHilbertProofCodeSemantics.Code,
      interp.localHilbertProofCodeSemantics.checks c
        (partialConsistencyCode n) →
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) ≤
          proof_predicate_formula_size partialConsistencyCode n

theorem PartialConsistencyHilbertS21TraceSoundness.of_verifier_trace_soundness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (haccepted : PartialConsistencyHilbertAcceptedSoundness interp)
    (hsound : S21VerifierTraceSoundness partialConsistencyCode) :
    PartialConsistencyHilbertS21TraceSoundness interp where
  source_checked_short_s21 := by
    intro m c hchecks
    exact hsound.short_proof_from_accepting_trace m
      (haccepted.source_checked_sound m c hchecks)

theorem PartialConsistencyHilbertS21TraceSoundness.of_payload_spec_and_verifier_trace
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hspec : PartialConsistencyPayloadSpec)
    (hsound : S21VerifierTraceSoundness partialConsistencyCode) :
    PartialConsistencyHilbertS21TraceSoundness interp :=
  PartialConsistencyHilbertS21TraceSoundness.of_verifier_trace_soundness
    (PartialConsistencyHilbertAcceptedSoundness.of_payload_spec hspec) hsound

noncomputable def
    FormulaCodeHilbertInterpretation.toPartialConsistencyAcceptedS21TraceRealization
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (haccepted : PartialConsistencyHilbertAcceptedSoundness interp)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp) :
    AcceptedCertificateS21TraceRealization partialConsistencyCode where
  accepted_code_semantics :=
    interp.toPartialConsistencyAcceptedCodeSemantics haccepted
  checked_code_has_short_s21_proof := by
    intro m c hchecks
    exact htrace.source_checked_short_s21 m c hchecks

noncomputable def
    FormulaCodeHilbertInterpretation.toPartialConsistencyAcceptedS21TraceRealizationOfPayloadSpec
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp) :
    AcceptedCertificateS21TraceRealization partialConsistencyCode :=
  interp.toPartialConsistencyAcceptedS21TraceRealization
    (PartialConsistencyHilbertAcceptedSoundness.of_payload_spec hspec) htrace

noncomputable def
    FormulaCodeHilbertInterpretation.toPartialConsistencyConcreteVerificationPackage
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (haccepted : PartialConsistencyHilbertAcceptedSoundness interp)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyConcreteVerificationPackage :=
  partial_consistency_concrete_verification_package_of_trace_realization
    (interp.toPartialConsistencyAcceptedS21TraceRealization haccepted htrace)
    hembed

noncomputable def
    FormulaCodeHilbertInterpretation.toPartialConsistencyConcreteVerificationPackageOfPayloadSpec
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyConcreteVerificationPackage :=
  interp.toPartialConsistencyConcreteVerificationPackage
    (PartialConsistencyHilbertAcceptedSoundness.of_payload_spec hspec)
    htrace hembed

theorem FormulaCodeHilbertInterpretation.irrational_of_partialConsistencyHilbertTrace
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencySpecExternalPackage)
    (haccepted : PartialConsistencyHilbertAcceptedSoundness interp)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_partial_consistency_spec_package hspec
    (interp.toPartialConsistencyConcreteVerificationPackage
      haccepted htrace hembed)

theorem
    FormulaCodeHilbertInterpretation.irrational_of_partialConsistencyHilbertTraceOfPayloadSpec
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencySpecExternalPackage)
    (hpayload : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  interp.irrational_of_partialConsistencyHilbertTrace hspec
    (PartialConsistencyHilbertAcceptedSoundness.of_payload_spec hpayload)
    htrace hembed

theorem FormulaCodeHilbertInterpretation.irrational_of_partialConsistencyVerifierTrace
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencySpecExternalPackage)
    (haccepted : PartialConsistencyHilbertAcceptedSoundness interp)
    (hsound : S21VerifierTraceSoundness partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  interp.irrational_of_partialConsistencyHilbertTrace hspec haccepted
    (PartialConsistencyHilbertS21TraceSoundness.of_verifier_trace_soundness
      haccepted hsound)
    hembed

theorem FormulaCodeHilbertInterpretation.irrational_of_payloadSpecAndVerifierTrace
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencySpecExternalPackage)
    (hpayload : PartialConsistencyPayloadSpec)
    (hsound : S21VerifierTraceSoundness partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  interp.irrational_of_partialConsistencyVerifierTrace hspec
    (PartialConsistencyHilbertAcceptedSoundness.of_payload_spec hpayload)
    hsound hembed

structure LocalHilbertProofCodeProjectionModel
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  source_exact :
    ∀ m : ℕ,
      interp.localHilbertProofCodeSemantics.minProofCodeSize
        (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩) =
        interp.target_proof_family.rightConjElim.minCheckedCodeSize m
  target_exact :
    ∀ m : ℕ,
      interp.localHilbertProofCodeSemantics.minProofCodeSize
        (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩) =
        interp.target_proof_family.minCheckedCodeSize m
  source_le_target_add_two :
    ∀ m : ℕ,
      interp.localHilbertProofCodeSemantics.minProofCodeSize
          (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩) ≤
        interp.localHilbertProofCodeSemantics.minProofCodeSize
          (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩) + 2

noncomputable def FormulaCodeHilbertInterpretation.localHilbertProofCodeProjectionModel
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    LocalHilbertProofCodeProjectionModel interp where
  source_exact := interp.localHilbertProofCodeSemantics_source_min_eq
  target_exact := interp.localHilbertProofCodeSemantics_target_min_eq
  source_le_target_add_two :=
    interp.localHilbertProofCodeSemantics_rightConjElim_le_add_two

noncomputable def FormulaCodeHilbertInterpretation.localHilbertSemanticProofLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ) : FormulaCode → ℕ :=
  interp.localHilbertProofCodeSemantics.semanticProofLength fallback

noncomputable def FormulaCodeHilbertInterpretation.localHilbertProofLengthCodeSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ) :
    ProofLengthCodeSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize FormulaCodeHilbertRelevantCode where
  proof_code_semantics := interp.localHilbertProofCodeSemantics
  fallback_length := fallback

theorem FormulaCodeHilbertInterpretation.localHilbertProofLengthCodeSemantics_length
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ) :
    (interp.localHilbertProofLengthCodeSemantics fallback).length =
      interp.localHilbertSemanticProofLength fallback := by
  rfl

theorem FormulaCodeHilbertInterpretation.localHilbertSemanticProofLength_partialConsistency
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ) (m : ℕ) :
    interp.localHilbertSemanticProofLength fallback (partialConsistencyCode m) =
      interp.target_proof_family.rightConjElim.minCheckedCodeSize m := by
  rw [FormulaCodeHilbertInterpretation.localHilbertSemanticProofLength]
  rw [interp.localHilbertProofCodeSemantics.semanticProofLength_eq_minProofCodeSize
    fallback (Or.inl ⟨m, rfl⟩)]
  exact interp.localHilbertProofCodeSemantics_source_min_eq m

theorem FormulaCodeHilbertInterpretation.localHilbertSemanticProofLength_reflectionGraft
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ) (m : ℕ) :
    interp.localHilbertSemanticProofLength fallback (sondowReflectionGraftCode m) =
      interp.target_proof_family.minCheckedCodeSize m := by
  rw [FormulaCodeHilbertInterpretation.localHilbertSemanticProofLength]
  rw [interp.localHilbertProofCodeSemantics.semanticProofLength_eq_minProofCodeSize
    fallback (Or.inr ⟨m, rfl⟩)]
  exact interp.localHilbertProofCodeSemantics_target_min_eq m

theorem FormulaCodeHilbertInterpretation.localHilbertSemanticProofLength_rightConjElim_le_add_two
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ) (m : ℕ) :
    interp.localHilbertSemanticProofLength fallback (partialConsistencyCode m) ≤
      interp.localHilbertSemanticProofLength fallback (sondowReflectionGraftCode m) + 2 := by
  rw [interp.localHilbertSemanticProofLength_partialConsistency fallback m,
    interp.localHilbertSemanticProofLength_reflectionGraft fallback m]
  exact interp.target_proof_family.minCheckedCodeSize_rightConjElim_le m

theorem FormulaCodeHilbertInterpretation.semanticBridge_of_localHilbertSemanticProofLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ) :
    SemanticHilbertProofLengthSoundnessBridge
      (interp.localHilbertSemanticProofLength fallback) where
  realizes_right_conj_elim :=
    interp.localHilbertSemanticProofLength_rightConjElim_le_add_two fallback

noncomputable def
    FormulaCodeHilbertInterpretation.toExactProjectionRealization_of_semanticProofLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ)
    (hproof_length :
      ∀ code : FormulaCode, FormulaCodeHilbertRelevantCode code →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          interp.localHilbertSemanticProofLength fallback code) :
    HilbertProofLengthExactProjectionRealization halign where
  sourceLength := fun m => interp.localHilbertSemanticProofLength fallback
    (partialConsistencyCode m)
  targetLength := fun m => interp.localHilbertSemanticProofLength fallback
    (sondowReflectionGraftCode m)
  source_exact := by
    intro m
    exact hproof_length (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)
  target_exact := by
    intro m
    exact hproof_length (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)
  source_le_target_add_two :=
    interp.localHilbertSemanticProofLength_rightConjElim_le_add_two fallback

theorem FormulaCodeHilbertInterpretation.toBridge_of_semanticProofLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ)
    (hproof_length :
      ∀ code : FormulaCode, FormulaCodeHilbertRelevantCode code →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          interp.localHilbertSemanticProofLength fallback code) :
    HilbertProofLengthSoundnessBridge :=
  SemanticHilbertProofLengthSoundnessBridge.toBridge
    (interp.semanticBridge_of_localHilbertSemanticProofLength fallback)
    hproof_length

theorem FormulaCodeHilbertInterpretation.projectSemantics_of_semanticProofLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ)
    (hproof_length :
      ∀ code : FormulaCode, FormulaCodeHilbertRelevantCode code →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          interp.localHilbertSemanticProofLength fallback code) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      (interp.localHilbertSemanticProofLength fallback)
      FormulaCodeHilbertRelevantCode where
  proof_length_eq := hproof_length

theorem FormulaCodeHilbertInterpretation.projectSemantics_of_localHilbertCodeCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ)
    (hcal :
      (interp.localHilbertProofLengthCodeSemantics fallback).Calibration) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      (interp.localHilbertSemanticProofLength fallback)
      FormulaCodeHilbertRelevantCode := by
  rw [← interp.localHilbertProofLengthCodeSemantics_length fallback]
  exact hcal.toProjectProofLengthSemantics

structure PAHilbertLocalProofCodeRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  proof_length_eq_minProofCodeSize :
    ∀ code : FormulaCode, ∀ hcode : FormulaCodeHilbertRelevantCode code,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
        interp.localHilbertProofCodeSemantics.minProofCodeSize code hcode

theorem PAHilbertLocalProofCodeRecognition.toProofLengthCodeCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAHilbertLocalProofCodeRecognition interp)
    (fallback : FormulaCode → ℕ) :
    (interp.localHilbertProofLengthCodeSemantics fallback).Calibration where
  proof_length_eq_length := by
    intro code hcode
    rw [hrec.proof_length_eq_minProofCodeSize code hcode]
    rw [ProofLengthCodeSemantics.length]
    exact_mod_cast (ProofCodeSemantics.semanticProofLength_eq_minProofCodeSize
      interp.localHilbertProofCodeSemantics fallback hcode).symm

theorem PAHilbertLocalProofCodeRecognition.ofProofLengthCodeCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (fallback : FormulaCode → ℕ)
    (hcal : (interp.localHilbertProofLengthCodeSemantics fallback).Calibration) :
    PAHilbertLocalProofCodeRecognition interp where
  proof_length_eq_minProofCodeSize := by
    intro code hcode
    rw [hcal.proof_length_eq_length code hcode]
    rw [ProofLengthCodeSemantics.length]
    exact_mod_cast ProofCodeSemantics.semanticProofLength_eq_minProofCodeSize
      interp.localHilbertProofCodeSemantics fallback hcode

theorem FormulaCodeHilbertInterpretation.localProofCodeRecognition_iff_proofLengthCodeCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ) :
    PAHilbertLocalProofCodeRecognition interp ↔
      (interp.localHilbertProofLengthCodeSemantics fallback).Calibration :=
  ⟨fun hrec => hrec.toProofLengthCodeCalibration fallback,
    PAHilbertLocalProofCodeRecognition.ofProofLengthCodeCalibration fallback⟩

structure PAHilbertProofLengthCodeSemanticsForProjection
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  fallback_length : FormulaCode → ℕ
  code_model :
    ProofLengthCodeSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize FormulaCodeHilbertRelevantCode
  code_model_eq :
    code_model = interp.localHilbertProofLengthCodeSemantics fallback_length
  semantic_bridge :
    SemanticHilbertProofLengthSoundnessBridge code_model.length

noncomputable def
    FormulaCodeHilbertInterpretation.localPAHilbertProofLengthCodeSemanticsForProjection
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ) :
    PAHilbertProofLengthCodeSemanticsForProjection interp where
  fallback_length := fallback
  code_model := interp.localHilbertProofLengthCodeSemantics fallback
  code_model_eq := rfl
  semantic_bridge := by
    rw [interp.localHilbertProofLengthCodeSemantics_length fallback]
    exact interp.semanticBridge_of_localHilbertSemanticProofLength fallback

theorem PAHilbertLocalProofCodeRecognition.toLocalPAHilbertCodeCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAHilbertLocalProofCodeRecognition interp)
    (fallback : FormulaCode → ℕ) :
    (let model := interp.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.Calibration) := by
  dsimp [FormulaCodeHilbertInterpretation.localPAHilbertProofLengthCodeSemanticsForProjection]
  exact hrec.toProofLengthCodeCalibration fallback

theorem PAHilbertLocalProofCodeRecognition.ofLocalPAHilbertCodeCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (fallback : FormulaCode → ℕ)
    (hcal :
      (let model := interp.localPAHilbertProofLengthCodeSemanticsForProjection fallback
       model.code_model.Calibration)) :
    PAHilbertLocalProofCodeRecognition interp := by
  dsimp [
    FormulaCodeHilbertInterpretation.localPAHilbertProofLengthCodeSemanticsForProjection
  ] at hcal
  exact PAHilbertLocalProofCodeRecognition.ofProofLengthCodeCalibration fallback hcal

theorem FormulaCodeHilbertInterpretation.localProofCodeRecognition_iff_localPAHilbertCodeCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ) :
    PAHilbertLocalProofCodeRecognition interp ↔
      (let model := interp.localPAHilbertProofLengthCodeSemanticsForProjection fallback
       model.code_model.Calibration) :=
  ⟨fun hrec => hrec.toLocalPAHilbertCodeCalibration fallback,
    PAHilbertLocalProofCodeRecognition.ofLocalPAHilbertCodeCalibration fallback⟩

theorem PAHilbertProofLengthCodeSemanticsForProjection.toProjectProofLengthSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (model : PAHilbertProofLengthCodeSemanticsForProjection interp)
    (hcal : model.code_model.Calibration) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      model.code_model.length FormulaCodeHilbertRelevantCode :=
  hcal.toProjectProofLengthSemantics

theorem PAHilbertProofLengthCodeSemanticsForProjection.toBridge
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (model : PAHilbertProofLengthCodeSemanticsForProjection interp)
    (hcal : model.code_model.Calibration) :
    HilbertProofLengthSoundnessBridge :=
  SemanticHilbertProofLengthSoundnessBridge.toBridge_of_projectSemantics
    model.semantic_bridge hcal.toProjectProofLengthSemantics

theorem PAHilbertProofLengthCodeSemanticsForProjection.calibration_of_family_exact
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (model : PAHilbertProofLengthCodeSemanticsForProjection interp)
    (hsource :
      ∀ m : ℕ,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode m) =
          model.code_model.length (partialConsistencyCode m))
    (htarget :
      ∀ m : ℕ,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode m) =
          model.code_model.length (sondowReflectionGraftCode m)) :
    model.code_model.Calibration where
  proof_length_eq_length := by
    intro code hcode
    rcases hcode with ⟨m, hcode_eq⟩ | ⟨m, hcode_eq⟩
    · subst hcode_eq
      exact hsource m
    · subst hcode_eq
      exact htarget m

theorem PAHilbertProofLengthCodeSemanticsForProjection.source_exact_of_calibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (model : PAHilbertProofLengthCodeSemanticsForProjection interp)
    (hcal : model.code_model.Calibration) :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode m) =
        model.code_model.length (partialConsistencyCode m) := by
  intro m
  exact hcal.proof_length_eq_length
    (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)

theorem PAHilbertProofLengthCodeSemanticsForProjection.target_exact_of_calibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (model : PAHilbertProofLengthCodeSemanticsForProjection interp)
    (hcal : model.code_model.Calibration) :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode m) =
        model.code_model.length (sondowReflectionGraftCode m) := by
  intro m
  exact hcal.proof_length_eq_length
    (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)

theorem PAHilbertProofLengthCodeSemanticsForProjection.calibration_iff_family_exact
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (model : PAHilbertProofLengthCodeSemanticsForProjection interp) :
    model.code_model.Calibration ↔
      (∀ m : ℕ,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode m) =
          model.code_model.length (partialConsistencyCode m)) ∧
      (∀ m : ℕ,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode m) =
          model.code_model.length (sondowReflectionGraftCode m)) := by
  constructor
  · intro hcal
    exact ⟨model.source_exact_of_calibration hcal,
      model.target_exact_of_calibration hcal⟩
  · intro hfamilies
    exact model.calibration_of_family_exact hfamilies.1 hfamilies.2

theorem FormulaCodeHilbertInterpretation.localPAHilbert_codeModel_length_partialConsistency
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ) (m : ℕ) :
    (let model := interp.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.length (partialConsistencyCode m)) =
      interp.target_proof_family.rightConjElim.minCheckedCodeSize m := by
  dsimp [FormulaCodeHilbertInterpretation.localPAHilbertProofLengthCodeSemanticsForProjection]
  exact interp.localHilbertSemanticProofLength_partialConsistency fallback m

theorem FormulaCodeHilbertInterpretation.localPAHilbert_codeModel_length_reflectionGraft
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ) (m : ℕ) :
    (let model := interp.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.length (sondowReflectionGraftCode m)) =
      interp.target_proof_family.minCheckedCodeSize m := by
  dsimp [FormulaCodeHilbertInterpretation.localPAHilbertProofLengthCodeSemanticsForProjection]
  exact interp.localHilbertSemanticProofLength_reflectionGraft fallback m

theorem FormulaCodeHilbertInterpretation.localPAHilbert_calibration_iff_minChecked_exact
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ) :
    (let model := interp.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.Calibration) ↔
      (∀ m : ℕ,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode m) =
          interp.target_proof_family.rightConjElim.minCheckedCodeSize m) ∧
      (∀ m : ℕ,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode m) =
          interp.target_proof_family.minCheckedCodeSize m) := by
  let model := interp.localPAHilbertProofLengthCodeSemanticsForProjection fallback
  rw [model.calibration_iff_family_exact]
  constructor
  · intro hfamilies
    constructor
    · intro m
      rw [hfamilies.1 m]
      exact_mod_cast
        interp.localPAHilbert_codeModel_length_partialConsistency fallback m
    · intro m
      rw [hfamilies.2 m]
      exact_mod_cast
        interp.localPAHilbert_codeModel_length_reflectionGraft fallback m
  · intro hfamilies
    constructor
    · intro m
      rw [hfamilies.1 m]
      exact_mod_cast
        (interp.localPAHilbert_codeModel_length_partialConsistency fallback m).symm
    · intro m
      rw [hfamilies.2 m]
      exact_mod_cast
        (interp.localPAHilbert_codeModel_length_reflectionGraft fallback m).symm

theorem FormulaCodeHilbertInterpretation.localPAHilbert_calibration_iff_standardSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ) :
    (let model := interp.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.Calibration) ↔
      StandardFormulaCodeProofLengthSemantics interp := by
  rw [interp.localPAHilbert_calibration_iff_minChecked_exact fallback]
  constructor
  · intro hfamilies
    refine ⟨?_, ?_⟩
    · intro m
      rw [hfamilies.2 m]
      exact_mod_cast interp.target_proof_family.minCheckedCodeSize_eq_minLength m
    · intro m
      rw [hfamilies.1 m]
      exact_mod_cast
        interp.target_proof_family.rightConjElim.minCheckedCodeSize_eq_minLength m
  · intro hsem
    constructor
    · intro m
      rw [hsem.source_minLength m]
      exact_mod_cast
        (interp.target_proof_family.rightConjElim.minCheckedCodeSize_eq_minLength m).symm
    · intro m
      rw [hsem.target_minLength m]
      exact_mod_cast
        (interp.target_proof_family.minCheckedCodeSize_eq_minLength m).symm

theorem StandardFormulaCodeProofLengthSemantics.toLocalPAHilbertCodeCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hsem : StandardFormulaCodeProofLengthSemantics interp)
    (fallback : FormulaCode → ℕ) :
    (let model := interp.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.Calibration) :=
  (interp.localPAHilbert_calibration_iff_standardSemantics fallback).2 hsem

theorem PAHilbertProofLengthCodeSemanticsForProjection.toStandardFormulaCodeSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (fallback : FormulaCode → ℕ)
    (hcal :
      (let model := interp.localPAHilbertProofLengthCodeSemanticsForProjection fallback
       model.code_model.Calibration)) :
    StandardFormulaCodeProofLengthSemantics interp :=
  (interp.localPAHilbert_calibration_iff_standardSemantics fallback).1 hcal

-- The lowest remaining project-level proof-length convention for the
-- projection bridge: exactly the two families used by the bridge agree with
-- the already-checked MiniHilbert code-size minima.  This is deliberately
-- narrower than a calibration over all relevant codes.
structure PAHilbertProjectionFamilyExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  partialConsistency_exact :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode m) =
        interp.target_proof_family.rightConjElim.minCheckedCodeSize m
  reflectionGraft_exact :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode m) =
        interp.target_proof_family.minCheckedCodeSize m

structure PAHilbertPartialConsistencyMinCheckedExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  partialConsistency_exact :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode m) =
        interp.target_proof_family.rightConjElim.minCheckedCodeSize m

structure PAHilbertReflectionGraftMinCheckedExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  reflectionGraft_exact :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode m) =
        interp.target_proof_family.minCheckedCodeSize m

structure PAHilbertPartialConsistencyCanonicalMinCheckedConvention
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) : Prop where
  proof_length_eq_canonical :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode m) =
        interp.canonicalMinCheckedLength (partialConsistencyCode m)

structure PAHilbertReflectionGraftCanonicalMinCheckedConvention
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) : Prop where
  proof_length_eq_canonical :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode m) =
        interp.canonicalMinCheckedLength (sondowReflectionGraftCode m)

structure PAHilbertSplitCanonicalMinCheckedConvention
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) : Prop where
  partial_convention :
    PAHilbertPartialConsistencyCanonicalMinCheckedConvention interp
  reflection_convention :
    PAHilbertReflectionGraftCanonicalMinCheckedConvention interp

structure PAPartialConsistencyProofLengthConvention where
  length : ℕ → ℕ
  proof_length_eq_length :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode m) = length m

structure PAReflectionGraftProofLengthConvention where
  length : ℕ → ℕ
  proof_length_eq_length :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode m) = length m

structure PAPartialConsistencyCheckedCodeExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hconv : PAPartialConsistencyProofLengthConvention) : Prop where
  length_eq_checked :
    ∀ m : ℕ, hconv.length m =
      interp.localCheckedCodeProofLength (partialConsistencyCode m)

structure PAReflectionGraftCheckedCodeExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hconv : PAReflectionGraftProofLengthConvention) : Prop where
  length_eq_checked :
    ∀ m : ℕ, hconv.length m =
      interp.localCheckedCodeProofLength (sondowReflectionGraftCode m)

structure PAPartialConsistencyCanonicalConventionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  convention : PAPartialConsistencyProofLengthConvention
  encoder_exactness :
    PAPartialConsistencyCheckedCodeExactness interp convention

structure PAReflectionGraftCanonicalConventionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  convention : PAReflectionGraftProofLengthConvention
  encoder_exactness :
    PAReflectionGraftCheckedCodeExactness interp convention

structure PASplitCanonicalConventionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  partial_certificate :
    PAPartialConsistencyCanonicalConventionCertificate interp
  reflection_certificate :
    PAReflectionGraftCanonicalConventionCertificate interp

structure PAPartialConsistencyLocalCheckedRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) : Prop where
  proof_length_eq_localChecked :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode m) =
        interp.localCheckedCodeProofLength (partialConsistencyCode m)

noncomputable def PAPartialConsistencyLocalCheckedRecognition.toProofLengthConvention
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAPartialConsistencyLocalCheckedRecognition interp) :
    PAPartialConsistencyProofLengthConvention where
  length := fun m => interp.localCheckedCodeProofLength (partialConsistencyCode m)
  proof_length_eq_length := hrec.proof_length_eq_localChecked

theorem PAPartialConsistencyLocalCheckedRecognition.toCheckedCodeExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAPartialConsistencyLocalCheckedRecognition interp) :
    PAPartialConsistencyCheckedCodeExactness
      interp hrec.toProofLengthConvention where
  length_eq_checked := by
    intro _m
    rfl

noncomputable def
    PAPartialConsistencyLocalCheckedRecognition.toConventionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAPartialConsistencyLocalCheckedRecognition interp) :
    PAPartialConsistencyCanonicalConventionCertificate interp where
  convention := hrec.toProofLengthConvention
  encoder_exactness := hrec.toCheckedCodeExactness

structure PAReflectionGraftLocalCheckedRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) : Prop where
  proof_length_eq_localChecked :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode m) =
        interp.localCheckedCodeProofLength (sondowReflectionGraftCode m)

noncomputable def PAReflectionGraftLocalCheckedRecognition.toProofLengthConvention
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAReflectionGraftLocalCheckedRecognition interp) :
    PAReflectionGraftProofLengthConvention where
  length := fun m => interp.localCheckedCodeProofLength (sondowReflectionGraftCode m)
  proof_length_eq_length := hrec.proof_length_eq_localChecked

theorem PAReflectionGraftLocalCheckedRecognition.toCheckedCodeExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAReflectionGraftLocalCheckedRecognition interp) :
    PAReflectionGraftCheckedCodeExactness
      interp hrec.toProofLengthConvention where
  length_eq_checked := by
    intro _m
    rfl

noncomputable def
    PAReflectionGraftLocalCheckedRecognition.toConventionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAReflectionGraftLocalCheckedRecognition interp) :
    PAReflectionGraftCanonicalConventionCertificate interp where
  convention := hrec.toProofLengthConvention
  encoder_exactness := hrec.toCheckedCodeExactness

structure PASplitLocalCheckedRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) : Prop where
  partial_recognition :
    PAPartialConsistencyLocalCheckedRecognition interp
  reflection_recognition :
    PAReflectionGraftLocalCheckedRecognition interp

noncomputable def PASplitLocalCheckedRecognition.toConventionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PASplitLocalCheckedRecognition interp) :
    PASplitCanonicalConventionCertificate interp where
  partial_certificate := hrec.partial_recognition.toConventionCertificate
  reflection_certificate := hrec.reflection_recognition.toConventionCertificate

theorem PAPartialConsistencyCanonicalConventionCertificate.toCanonicalConvention
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcert : PAPartialConsistencyCanonicalConventionCertificate interp) :
    PAHilbertPartialConsistencyCanonicalMinCheckedConvention interp where
  proof_length_eq_canonical := by
    intro m
    rw [hcert.convention.proof_length_eq_length m]
    have hlen :
        hcert.convention.length m =
          interp.canonicalMinCheckedLength (partialConsistencyCode m) := by
      rw [hcert.encoder_exactness.length_eq_checked m]
      exact
        (interp.canonicalMinCheckedLength_eq_localChecked
          (partialConsistencyCode m)).symm
    exact_mod_cast hlen

theorem PAReflectionGraftCanonicalConventionCertificate.toCanonicalConvention
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcert : PAReflectionGraftCanonicalConventionCertificate interp) :
    PAHilbertReflectionGraftCanonicalMinCheckedConvention interp where
  proof_length_eq_canonical := by
    intro m
    rw [hcert.convention.proof_length_eq_length m]
    have hlen :
        hcert.convention.length m =
          interp.canonicalMinCheckedLength (sondowReflectionGraftCode m) := by
      rw [hcert.encoder_exactness.length_eq_checked m]
      exact
        (interp.canonicalMinCheckedLength_eq_localChecked
          (sondowReflectionGraftCode m)).symm
    exact_mod_cast hlen

theorem PASplitCanonicalConventionCertificate.toCanonicalConvention
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcert : PASplitCanonicalConventionCertificate interp) :
    PAHilbertSplitCanonicalMinCheckedConvention interp where
  partial_convention := hcert.partial_certificate.toCanonicalConvention
  reflection_convention := hcert.reflection_certificate.toCanonicalConvention

noncomputable def PAPartialConsistencyCanonicalConventionCertificate.ofCanonical
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hconv : PAHilbertPartialConsistencyCanonicalMinCheckedConvention interp) :
    PAPartialConsistencyCanonicalConventionCertificate interp where
  convention := {
    length := fun m =>
      interp.canonicalMinCheckedLength (partialConsistencyCode m)
    proof_length_eq_length := hconv.proof_length_eq_canonical
  }
  encoder_exactness := {
    length_eq_checked := by
      intro m
      exact
        interp.canonicalMinCheckedLength_eq_localChecked
          (partialConsistencyCode m)
  }

noncomputable def PAReflectionGraftCanonicalConventionCertificate.ofCanonical
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hconv : PAHilbertReflectionGraftCanonicalMinCheckedConvention interp) :
    PAReflectionGraftCanonicalConventionCertificate interp where
  convention := {
    length := fun m =>
      interp.canonicalMinCheckedLength (sondowReflectionGraftCode m)
    proof_length_eq_length := hconv.proof_length_eq_canonical
  }
  encoder_exactness := {
    length_eq_checked := by
      intro m
      exact
        interp.canonicalMinCheckedLength_eq_localChecked
          (sondowReflectionGraftCode m)
  }

noncomputable def PASplitCanonicalConventionCertificate.ofCanonical
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hconv : PAHilbertSplitCanonicalMinCheckedConvention interp) :
    PASplitCanonicalConventionCertificate interp where
  partial_certificate :=
    PAPartialConsistencyCanonicalConventionCertificate.ofCanonical
      hconv.partial_convention
  reflection_certificate :=
    PAReflectionGraftCanonicalConventionCertificate.ofCanonical
      hconv.reflection_convention

theorem FormulaCodeHilbertInterpretation.partialCanonicalConvention_iff_certificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertPartialConsistencyCanonicalMinCheckedConvention interp ↔
      Nonempty (PAPartialConsistencyCanonicalConventionCertificate interp) := by
  constructor
  · intro hconv
    exact
      ⟨PAPartialConsistencyCanonicalConventionCertificate.ofCanonical
        hconv⟩
  · intro hcert
    rcases hcert with ⟨hcert⟩
    exact hcert.toCanonicalConvention

theorem PAPartialConsistencyCanonicalConventionCertificate.toLocalCheckedRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcert : PAPartialConsistencyCanonicalConventionCertificate interp) :
    PAPartialConsistencyLocalCheckedRecognition interp where
  proof_length_eq_localChecked := by
    intro m
    rw [hcert.convention.proof_length_eq_length m]
    exact_mod_cast hcert.encoder_exactness.length_eq_checked m

theorem FormulaCodeHilbertInterpretation.partialLocalCheckedRecognition_iff_certificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAPartialConsistencyLocalCheckedRecognition interp ↔
      Nonempty (PAPartialConsistencyCanonicalConventionCertificate interp) := by
  constructor
  · intro hrec
    exact ⟨hrec.toConventionCertificate⟩
  · intro hcert
    rcases hcert with ⟨hcert⟩
    exact hcert.toLocalCheckedRecognition

theorem FormulaCodeHilbertInterpretation.reflectionCanonicalConvention_iff_certificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertReflectionGraftCanonicalMinCheckedConvention interp ↔
      Nonempty (PAReflectionGraftCanonicalConventionCertificate interp) := by
  constructor
  · intro hconv
    exact
      ⟨PAReflectionGraftCanonicalConventionCertificate.ofCanonical
        hconv⟩
  · intro hcert
    rcases hcert with ⟨hcert⟩
    exact hcert.toCanonicalConvention

theorem PAReflectionGraftCanonicalConventionCertificate.toLocalCheckedRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcert : PAReflectionGraftCanonicalConventionCertificate interp) :
    PAReflectionGraftLocalCheckedRecognition interp where
  proof_length_eq_localChecked := by
    intro m
    rw [hcert.convention.proof_length_eq_length m]
    exact_mod_cast hcert.encoder_exactness.length_eq_checked m

theorem FormulaCodeHilbertInterpretation.reflectionLocalCheckedRecognition_iff_certificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAReflectionGraftLocalCheckedRecognition interp ↔
      Nonempty (PAReflectionGraftCanonicalConventionCertificate interp) := by
  constructor
  · intro hrec
    exact ⟨hrec.toConventionCertificate⟩
  · intro hcert
    rcases hcert with ⟨hcert⟩
    exact hcert.toLocalCheckedRecognition

theorem FormulaCodeHilbertInterpretation.splitCanonicalConvention_iff_certificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertSplitCanonicalMinCheckedConvention interp ↔
      Nonempty (PASplitCanonicalConventionCertificate interp) := by
  constructor
  · intro hconv
    exact ⟨PASplitCanonicalConventionCertificate.ofCanonical hconv⟩
  · intro hcert
    rcases hcert with ⟨hcert⟩
    exact hcert.toCanonicalConvention

theorem PASplitCanonicalConventionCertificate.toLocalCheckedRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcert : PASplitCanonicalConventionCertificate interp) :
    PASplitLocalCheckedRecognition interp where
  partial_recognition :=
    hcert.partial_certificate.toLocalCheckedRecognition
  reflection_recognition :=
    hcert.reflection_certificate.toLocalCheckedRecognition

theorem FormulaCodeHilbertInterpretation.splitLocalCheckedRecognition_iff_certificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PASplitLocalCheckedRecognition interp ↔
      Nonempty (PASplitCanonicalConventionCertificate interp) := by
  constructor
  · intro hrec
    exact ⟨hrec.toConventionCertificate⟩
  · intro hcert
    rcases hcert with ⟨hcert⟩
    exact hcert.toLocalCheckedRecognition

theorem PAHilbertPartialConsistencyCanonicalMinCheckedConvention.toSourceMinCheckedCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hconv : PAHilbertPartialConsistencyCanonicalMinCheckedConvention interp) :
    PartialConsistencySourceMinCheckedCalibration interp where
  proof_length_eq_source_minChecked := by
    intro m
    rw [hconv.proof_length_eq_canonical m]
    exact_mod_cast interp.canonicalMinCheckedLength_partialConsistency m

theorem PAPartialConsistencyCanonicalConventionCertificate.toSourceCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcert : PAPartialConsistencyCanonicalConventionCertificate interp) :
    PartialConsistencySourceMinCheckedCalibration interp :=
  hcert.toCanonicalConvention.toSourceMinCheckedCalibration

theorem PAPartialConsistencyCanonicalConventionCertificate.toSemanticStrongNatLowerBound
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcert : PAPartialConsistencyCanonicalConventionCertificate interp)
    (hlower : StrongPartialConsistencyLowerBound) :
    SemanticStrongNatLowerBound
      interp.target_proof_family.rightConjElim.minCheckedCodeSize :=
  hcert.toSourceCalibration.toSemanticStrongNatLowerBound hlower

theorem PAHilbertPartialConsistencyMinCheckedExactness.toSourceMinCheckedCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hpartial : PAHilbertPartialConsistencyMinCheckedExactness interp) :
    PartialConsistencySourceMinCheckedCalibration interp where
  proof_length_eq_source_minChecked := hpartial.partialConsistency_exact

theorem PartialConsistencySourceMinCheckedCalibration.toPartialConsistencyMinCheckedExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hsource : PartialConsistencySourceMinCheckedCalibration interp) :
    PAHilbertPartialConsistencyMinCheckedExactness interp where
  partialConsistency_exact := hsource.proof_length_eq_source_minChecked

theorem PartialConsistencySourceMinCheckedCalibration.toCanonicalMinCheckedConvention
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hsource : PartialConsistencySourceMinCheckedCalibration interp) :
    PAHilbertPartialConsistencyCanonicalMinCheckedConvention interp where
  proof_length_eq_canonical := by
    intro m
    rw [hsource.proof_length_eq_source_minChecked m]
    exact_mod_cast (interp.canonicalMinCheckedLength_partialConsistency m).symm

theorem FormulaCodeHilbertInterpretation.partialMinCheckedExactness_iff_sourceCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertPartialConsistencyMinCheckedExactness interp ↔
      PartialConsistencySourceMinCheckedCalibration interp :=
  ⟨PAHilbertPartialConsistencyMinCheckedExactness.toSourceMinCheckedCalibration,
    PartialConsistencySourceMinCheckedCalibration.toPartialConsistencyMinCheckedExactness⟩

theorem FormulaCodeHilbertInterpretation.partialCanonicalConvention_iff_sourceCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertPartialConsistencyCanonicalMinCheckedConvention interp ↔
      PartialConsistencySourceMinCheckedCalibration interp :=
  ⟨PAHilbertPartialConsistencyCanonicalMinCheckedConvention.toSourceMinCheckedCalibration,
    PartialConsistencySourceMinCheckedCalibration.toCanonicalMinCheckedConvention⟩

theorem PAPartialConsistencyLocalCheckedRecognition.toSourceMinCheckedCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAPartialConsistencyLocalCheckedRecognition interp) :
    PartialConsistencySourceMinCheckedCalibration interp where
  proof_length_eq_source_minChecked := by
    intro m
    rw [hrec.proof_length_eq_localChecked m]
    exact_mod_cast interp.localCheckedCodeProofLength_partialConsistency m

theorem PartialConsistencySourceMinCheckedCalibration.toLocalCheckedRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hsource : PartialConsistencySourceMinCheckedCalibration interp) :
    PAPartialConsistencyLocalCheckedRecognition interp where
  proof_length_eq_localChecked := by
    intro m
    rw [hsource.proof_length_eq_source_minChecked m]
    exact_mod_cast
      (interp.localCheckedCodeProofLength_partialConsistency m).symm

theorem FormulaCodeHilbertInterpretation.partialLocalCheckedRecognition_iff_sourceCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAPartialConsistencyLocalCheckedRecognition interp ↔
      PartialConsistencySourceMinCheckedCalibration interp :=
  ⟨PAPartialConsistencyLocalCheckedRecognition.toSourceMinCheckedCalibration,
    PartialConsistencySourceMinCheckedCalibration.toLocalCheckedRecognition⟩

theorem PAHilbertReflectionGraftCanonicalMinCheckedConvention.toReflectionGraftMinCheckedExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hconv : PAHilbertReflectionGraftCanonicalMinCheckedConvention interp) :
    PAHilbertReflectionGraftMinCheckedExactness interp where
  reflectionGraft_exact := by
    intro m
    rw [hconv.proof_length_eq_canonical m]
    exact_mod_cast interp.canonicalMinCheckedLength_reflectionGraft m

theorem PAHilbertReflectionGraftMinCheckedExactness.toReflectionGraftCanonicalMinCheckedConvention
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertReflectionGraftMinCheckedExactness interp) :
    PAHilbertReflectionGraftCanonicalMinCheckedConvention interp where
  proof_length_eq_canonical := by
    intro m
    rw [hexact.reflectionGraft_exact m]
    exact_mod_cast (interp.canonicalMinCheckedLength_reflectionGraft m).symm

theorem FormulaCodeHilbertInterpretation.reflectionGraftCanonicalConvention_iff_minCheckedExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertReflectionGraftCanonicalMinCheckedConvention interp ↔
      PAHilbertReflectionGraftMinCheckedExactness interp :=
  ⟨PAHilbertReflectionGraftCanonicalMinCheckedConvention.toReflectionGraftMinCheckedExactness,
    PAHilbertReflectionGraftMinCheckedExactness.toReflectionGraftCanonicalMinCheckedConvention⟩

theorem PAReflectionGraftLocalCheckedRecognition.toReflectionGraftMinCheckedExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAReflectionGraftLocalCheckedRecognition interp) :
    PAHilbertReflectionGraftMinCheckedExactness interp where
  reflectionGraft_exact := by
    intro m
    rw [hrec.proof_length_eq_localChecked m]
    exact_mod_cast interp.localCheckedCodeProofLength_reflectionGraft m

theorem PAHilbertReflectionGraftMinCheckedExactness.toLocalCheckedRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertReflectionGraftMinCheckedExactness interp) :
    PAReflectionGraftLocalCheckedRecognition interp where
  proof_length_eq_localChecked := by
    intro m
    rw [hexact.reflectionGraft_exact m]
    exact_mod_cast
      (interp.localCheckedCodeProofLength_reflectionGraft m).symm

theorem FormulaCodeHilbertInterpretation.reflectionLocalCheckedRecognition_iff_minCheckedExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAReflectionGraftLocalCheckedRecognition interp ↔
      PAHilbertReflectionGraftMinCheckedExactness interp :=
  ⟨PAReflectionGraftLocalCheckedRecognition.toReflectionGraftMinCheckedExactness,
    PAHilbertReflectionGraftMinCheckedExactness.toLocalCheckedRecognition⟩

theorem PAHilbertSplitCanonicalMinCheckedConvention.toSourceCalibrationAndReflectionExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hconv : PAHilbertSplitCanonicalMinCheckedConvention interp) :
      PartialConsistencySourceMinCheckedCalibration interp ∧
      PAHilbertReflectionGraftMinCheckedExactness interp :=
  ⟨hconv.partial_convention.toSourceMinCheckedCalibration,
    hconv.reflection_convention.toReflectionGraftMinCheckedExactness⟩

theorem PAHilbertSplitCanonicalMinCheckedConvention.toFamilyExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hconv : PAHilbertSplitCanonicalMinCheckedConvention interp) :
    PAHilbertProjectionFamilyExactness interp where
  partialConsistency_exact :=
    hconv.partial_convention.toSourceMinCheckedCalibration
      |>.toPartialConsistencyMinCheckedExactness
      |>.partialConsistency_exact
  reflectionGraft_exact :=
    hconv.reflection_convention.toReflectionGraftMinCheckedExactness
      |>.reflectionGraft_exact

theorem FormulaCodeHilbertInterpretation.splitCanonicalConvention_iff_sourceReflectionExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertSplitCanonicalMinCheckedConvention interp ↔
      PartialConsistencySourceMinCheckedCalibration interp ∧
        PAHilbertReflectionGraftMinCheckedExactness interp := by
  constructor
  · intro hconv
    exact hconv.toSourceCalibrationAndReflectionExactness
  · intro hpair
    exact
      { partial_convention :=
          hpair.1.toCanonicalMinCheckedConvention
        reflection_convention :=
          hpair.2.toReflectionGraftCanonicalMinCheckedConvention }

theorem PAHilbertPartialConsistencyMinCheckedExactness.toSemanticStrongNatLowerBound
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hpartial : PAHilbertPartialConsistencyMinCheckedExactness interp)
    (hlower : StrongPartialConsistencyLowerBound) :
    SemanticStrongNatLowerBound
      interp.target_proof_family.rightConjElim.minCheckedCodeSize :=
  hpartial.toSourceMinCheckedCalibration.toSemanticStrongNatLowerBound hlower

theorem
    PAHilbertPartialConsistencyMinCheckedExactness.semanticStrongNatLowerBound_of_rescaling
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hpartial : PAHilbertPartialConsistencyMinCheckedExactness interp)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem) :
    SemanticStrongNatLowerBound
      interp.target_proof_family.rightConjElim.minCheckedCodeSize :=
  hpartial.toSourceMinCheckedCalibration.semanticStrongNatLowerBound_of_rescaling
    hrescale

theorem PAHilbertPartialConsistencyMinCheckedExactness.toLocalCheckedLowerBound
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hpartial : PAHilbertPartialConsistencyMinCheckedExactness interp)
    (hlower : StrongPartialConsistencyLowerBound) :
    SemanticStrongProofLengthLowerBound
      interp.localCheckedCodeProofLength partialConsistencyCode :=
  interp.localCheckedPartialConsistencyLowerBound_of_sourceLength
    (hpartial.toSemanticStrongNatLowerBound hlower)

theorem
    PAHilbertPartialConsistencyMinCheckedExactness.localCheckedLowerBound_of_rescaling
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hpartial : PAHilbertPartialConsistencyMinCheckedExactness interp)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem) :
    SemanticStrongProofLengthLowerBound
      interp.localCheckedCodeProofLength partialConsistencyCode :=
  interp.localCheckedPartialConsistencyLowerBound_of_sourceLength
    (hpartial.semanticStrongNatLowerBound_of_rescaling hrescale)

theorem PAHilbertProjectionFamilyExactness.toPartialConsistencyMinCheckedExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertProjectionFamilyExactness interp) :
    PAHilbertPartialConsistencyMinCheckedExactness interp where
  partialConsistency_exact := hexact.partialConsistency_exact

theorem PAHilbertProjectionFamilyExactness.toReflectionGraftMinCheckedExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertProjectionFamilyExactness interp) :
    PAHilbertReflectionGraftMinCheckedExactness interp where
  reflectionGraft_exact := hexact.reflectionGraft_exact

theorem PAHilbertProjectionFamilyExactness.ofMinCheckedExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hpartial : PAHilbertPartialConsistencyMinCheckedExactness interp)
    (hgraft : PAHilbertReflectionGraftMinCheckedExactness interp) :
    PAHilbertProjectionFamilyExactness interp where
  partialConsistency_exact := hpartial.partialConsistency_exact
  reflectionGraft_exact := hgraft.reflectionGraft_exact

theorem FormulaCodeHilbertInterpretation.familyExactness_iff_minCheckedExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertProjectionFamilyExactness interp ↔
      PAHilbertPartialConsistencyMinCheckedExactness interp ∧
        PAHilbertReflectionGraftMinCheckedExactness interp :=
  ⟨fun hexact =>
    ⟨hexact.toPartialConsistencyMinCheckedExactness,
      hexact.toReflectionGraftMinCheckedExactness⟩,
    fun h =>
      PAHilbertProjectionFamilyExactness.ofMinCheckedExactness h.1 h.2⟩

theorem PAHilbertProjectionFamilyExactness.of_projectCheckedCodeProofLengthSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode) :
    PAHilbertProjectionFamilyExactness interp where
  partialConsistency_exact := by
    intro m
    rw [hsem.proof_length_eq (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)]
    exact_mod_cast interp.localCheckedCodeProofLength_partialConsistency m
  reflectionGraft_exact := by
    intro m
    rw [hsem.proof_length_eq (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)]
    exact_mod_cast interp.localCheckedCodeProofLength_reflectionGraft m

theorem PAHilbertProjectionFamilyExactness.to_projectCheckedCodeProofLengthSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertProjectionFamilyExactness interp) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode where
  proof_length_eq := by
    intro code hcode
    rcases hcode with ⟨m, hcode_eq⟩ | ⟨m, hcode_eq⟩
    · subst hcode_eq
      rw [hexact.partialConsistency_exact m]
      exact_mod_cast (interp.localCheckedCodeProofLength_partialConsistency m).symm
    · subst hcode_eq
      rw [hexact.reflectionGraft_exact m]
      exact_mod_cast (interp.localCheckedCodeProofLength_reflectionGraft m).symm

theorem FormulaCodeHilbertInterpretation.familyExactness_iff_projectCheckedCodeSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertProjectionFamilyExactness interp ↔
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode :=
  ⟨PAHilbertProjectionFamilyExactness.to_projectCheckedCodeProofLengthSemantics,
    PAHilbertProjectionFamilyExactness.of_projectCheckedCodeProofLengthSemantics interp⟩

theorem FormulaCodeHilbertInterpretation.projectCheckedCodeSemantics_iff_familyExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode ↔
      PAHilbertProjectionFamilyExactness interp :=
  (interp.familyExactness_iff_projectCheckedCodeSemantics).symm

theorem PAHilbertPartialConsistencyMinCheckedExactness.of_projectCheckedCodeProofLengthSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode) :
    PAHilbertPartialConsistencyMinCheckedExactness interp :=
  (PAHilbertProjectionFamilyExactness.of_projectCheckedCodeProofLengthSemantics
    interp hsem).toPartialConsistencyMinCheckedExactness

theorem PAHilbertReflectionGraftMinCheckedExactness.of_projectCheckedCodeProofLengthSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode) :
    PAHilbertReflectionGraftMinCheckedExactness interp :=
  (PAHilbertProjectionFamilyExactness.of_projectCheckedCodeProofLengthSemantics
    interp hsem).toReflectionGraftMinCheckedExactness

theorem FormulaCodeHilbertInterpretation.splitMinCheckedExactness_iff_projectCheckedCodeSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertPartialConsistencyMinCheckedExactness interp ∧
        PAHilbertReflectionGraftMinCheckedExactness interp ↔
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode :=
  ⟨fun hsplit =>
    (PAHilbertProjectionFamilyExactness.ofMinCheckedExactness
      hsplit.1 hsplit.2).to_projectCheckedCodeProofLengthSemantics,
    fun hsem =>
      ⟨PAHilbertPartialConsistencyMinCheckedExactness.of_projectCheckedCodeProofLengthSemantics
          interp hsem,
        PAHilbertReflectionGraftMinCheckedExactness.of_projectCheckedCodeProofLengthSemantics
          interp hsem⟩⟩

theorem FormulaCodeHilbertInterpretation.projectCheckedCodeSemantics_iff_splitMinCheckedExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode ↔
      PAHilbertPartialConsistencyMinCheckedExactness interp ∧
        PAHilbertReflectionGraftMinCheckedExactness interp :=
  (interp.splitMinCheckedExactness_iff_projectCheckedCodeSemantics).symm

-- The explicit recognition condition for replacing the abstract project-level
-- `proof_length` on the projection fragment by the checked-code length model.
structure PAHilbertProjectCheckedProofLengthRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  proof_length_eq_checked :
    ∀ code : FormulaCode, FormulaCodeHilbertRelevantCode code →
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
        interp.localCheckedCodeProofLength code

theorem PAHilbertProjectCheckedProofLengthRecognition.toSplitLocalCheckedRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAHilbertProjectCheckedProofLengthRecognition interp) :
    PASplitLocalCheckedRecognition interp where
  partial_recognition := {
    proof_length_eq_localChecked := by
      intro m
      exact hrec.proof_length_eq_checked
        (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)
  }
  reflection_recognition := {
    proof_length_eq_localChecked := by
      intro m
      exact hrec.proof_length_eq_checked
        (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)
  }

theorem PASplitLocalCheckedRecognition.toProjectCheckedRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PASplitLocalCheckedRecognition interp) :
    PAHilbertProjectCheckedProofLengthRecognition interp where
  proof_length_eq_checked := by
    intro code hcode
    rcases hcode with ⟨m, hcode_eq⟩ | ⟨m, hcode_eq⟩
    · subst hcode_eq
      exact hrec.partial_recognition.proof_length_eq_localChecked m
    · subst hcode_eq
      exact hrec.reflection_recognition.proof_length_eq_localChecked m

theorem FormulaCodeHilbertInterpretation.projectCheckedRecognition_iff_splitLocalCheckedRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertProjectCheckedProofLengthRecognition interp ↔
      PASplitLocalCheckedRecognition interp :=
  ⟨PAHilbertProjectCheckedProofLengthRecognition.toSplitLocalCheckedRecognition,
    PASplitLocalCheckedRecognition.toProjectCheckedRecognition⟩

structure PAHilbertProofLengthConvention where
  length : FormulaCode → ℕ
  proof_length_eq_length :
    ∀ code : FormulaCode, FormulaCodeHilbertRelevantCode code →
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
        length code

theorem PAHilbertProofLengthConvention.toProjectProofLengthSemantics
    (hconv : PAHilbertProofLengthConvention) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      hconv.length FormulaCodeHilbertRelevantCode where
  proof_length_eq := hconv.proof_length_eq_length

def PAHilbertProofLengthConvention.ofProjectProofLengthSemantics
    (length : FormulaCode → ℕ)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        length FormulaCodeHilbertRelevantCode) :
    PAHilbertProofLengthConvention where
  length := length
  proof_length_eq_length := hsem.proof_length_eq

def PAHilbertProofLengthConvention.toPartialConsistencyConvention
    (hconv : PAHilbertProofLengthConvention) :
    PAPartialConsistencyProofLengthConvention where
  length := fun m => hconv.length (partialConsistencyCode m)
  proof_length_eq_length := by
    intro m
    exact hconv.proof_length_eq_length
      (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)

def PAHilbertProofLengthConvention.toReflectionGraftConvention
    (hconv : PAHilbertProofLengthConvention) :
    PAReflectionGraftProofLengthConvention where
  length := fun m => hconv.length (sondowReflectionGraftCode m)
  proof_length_eq_length := by
    intro m
    exact hconv.proof_length_eq_length
      (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)

structure FormulaCodeHilbertCheckedCodeEncoderEquivalence
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hconv : PAHilbertProofLengthConvention) : Prop where
  length_eq_localChecked :
    ∀ code : FormulaCode, FormulaCodeHilbertRelevantCode code →
      hconv.length code = interp.localCheckedCodeProofLength code

structure FormulaCodeHilbertCheckedCodeFamilyEncoderEquivalence
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hconv : PAHilbertProofLengthConvention) : Prop where
  partialConsistency_length_eq :
    ∀ m : ℕ,
      hconv.length (partialConsistencyCode m) =
        interp.target_proof_family.rightConjElim.minCheckedCodeSize m
  reflectionGraft_length_eq :
    ∀ m : ℕ,
      hconv.length (sondowReflectionGraftCode m) =
        interp.target_proof_family.minCheckedCodeSize m

theorem FormulaCodeHilbertCheckedCodeEncoderEquivalence.toFamily
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    {hconv : PAHilbertProofLengthConvention}
    (hequiv : FormulaCodeHilbertCheckedCodeEncoderEquivalence interp hconv) :
    FormulaCodeHilbertCheckedCodeFamilyEncoderEquivalence interp hconv where
  partialConsistency_length_eq := by
    intro m
    rw [hequiv.length_eq_localChecked (partialConsistencyCode m)
      (Or.inl ⟨m, rfl⟩)]
    exact interp.localCheckedCodeProofLength_partialConsistency m
  reflectionGraft_length_eq := by
    intro m
    rw [hequiv.length_eq_localChecked (sondowReflectionGraftCode m)
      (Or.inr ⟨m, rfl⟩)]
    exact interp.localCheckedCodeProofLength_reflectionGraft m

theorem FormulaCodeHilbertCheckedCodeFamilyEncoderEquivalence.toEncoderEquivalence
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    {hconv : PAHilbertProofLengthConvention}
    (hfamily :
      FormulaCodeHilbertCheckedCodeFamilyEncoderEquivalence interp hconv) :
    FormulaCodeHilbertCheckedCodeEncoderEquivalence interp hconv where
  length_eq_localChecked := by
    intro code hcode
    rcases hcode with ⟨m, hcode_eq⟩ | ⟨m, hcode_eq⟩
    · subst hcode_eq
      rw [hfamily.partialConsistency_length_eq m]
      exact (interp.localCheckedCodeProofLength_partialConsistency m).symm
    · subst hcode_eq
      rw [hfamily.reflectionGraft_length_eq m]
      exact (interp.localCheckedCodeProofLength_reflectionGraft m).symm

theorem FormulaCodeHilbertInterpretation.checkedCodeEncoderEquivalence_iff_family
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hconv : PAHilbertProofLengthConvention) :
    FormulaCodeHilbertCheckedCodeEncoderEquivalence interp hconv ↔
      FormulaCodeHilbertCheckedCodeFamilyEncoderEquivalence interp hconv :=
  ⟨FormulaCodeHilbertCheckedCodeEncoderEquivalence.toFamily,
    FormulaCodeHilbertCheckedCodeFamilyEncoderEquivalence.toEncoderEquivalence⟩

theorem FormulaCodeHilbertInterpretation.localCheckedEncoderEquiv_ofProjectSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode) :
    FormulaCodeHilbertCheckedCodeEncoderEquivalence interp
      (PAHilbertProofLengthConvention.ofProjectProofLengthSemantics
        interp.localCheckedCodeProofLength hsem) where
  length_eq_localChecked := by
    intro _code _hcode
    rfl

theorem FormulaCodeHilbertCheckedCodeFamilyEncoderEquivalence.toPartialCheckedCodeExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    {hconv : PAHilbertProofLengthConvention}
    (hfamily :
      FormulaCodeHilbertCheckedCodeFamilyEncoderEquivalence interp hconv) :
    PAPartialConsistencyCheckedCodeExactness
      interp hconv.toPartialConsistencyConvention where
  length_eq_checked := by
    intro m
    change hconv.length (partialConsistencyCode m) =
      interp.localCheckedCodeProofLength (partialConsistencyCode m)
    rw [hfamily.partialConsistency_length_eq m]
    exact (interp.localCheckedCodeProofLength_partialConsistency m).symm

theorem FormulaCodeHilbertCheckedCodeFamilyEncoderEquivalence.toReflectionCheckedCodeExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    {hconv : PAHilbertProofLengthConvention}
    (hfamily :
      FormulaCodeHilbertCheckedCodeFamilyEncoderEquivalence interp hconv) :
    PAReflectionGraftCheckedCodeExactness
      interp hconv.toReflectionGraftConvention where
  length_eq_checked := by
    intro m
    change hconv.length (sondowReflectionGraftCode m) =
      interp.localCheckedCodeProofLength (sondowReflectionGraftCode m)
    rw [hfamily.reflectionGraft_length_eq m]
    exact (interp.localCheckedCodeProofLength_reflectionGraft m).symm

def FormulaCodeHilbertCheckedCodeFamilyEncoderEquivalence.toPartialConventionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    {hconv : PAHilbertProofLengthConvention}
    (hfamily :
      FormulaCodeHilbertCheckedCodeFamilyEncoderEquivalence interp hconv) :
    PAPartialConsistencyCanonicalConventionCertificate interp where
  convention := hconv.toPartialConsistencyConvention
  encoder_exactness := hfamily.toPartialCheckedCodeExactness

def FormulaCodeHilbertCheckedCodeFamilyEncoderEquivalence.toReflectionConventionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    {hconv : PAHilbertProofLengthConvention}
    (hfamily :
      FormulaCodeHilbertCheckedCodeFamilyEncoderEquivalence interp hconv) :
    PAReflectionGraftCanonicalConventionCertificate interp where
  convention := hconv.toReflectionGraftConvention
  encoder_exactness := hfamily.toReflectionCheckedCodeExactness

def FormulaCodeHilbertCheckedCodeFamilyEncoderEquivalence.toSplitConventionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    {hconv : PAHilbertProofLengthConvention}
    (hfamily :
      FormulaCodeHilbertCheckedCodeFamilyEncoderEquivalence interp hconv) :
    PASplitCanonicalConventionCertificate interp where
  partial_certificate := hfamily.toPartialConventionCertificate
  reflection_certificate := hfamily.toReflectionConventionCertificate

structure PAHilbertProjectCheckedRecognitionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  convention : PAHilbertProofLengthConvention
  encoder_equivalence :
    FormulaCodeHilbertCheckedCodeEncoderEquivalence interp convention

theorem PAHilbertProjectCheckedRecognitionCertificate.toProjectCheckedRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcert : PAHilbertProjectCheckedRecognitionCertificate interp) :
    PAHilbertProjectCheckedProofLengthRecognition interp where
  proof_length_eq_checked := by
    intro code hcode
    rw [hcert.convention.proof_length_eq_length code hcode]
    exact_mod_cast hcert.encoder_equivalence.length_eq_localChecked code hcode

noncomputable def
    PAHilbertProjectCheckedRecognitionCertificate.ofProjectCheckedRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAHilbertProjectCheckedProofLengthRecognition interp) :
    PAHilbertProjectCheckedRecognitionCertificate interp where
  convention := {
    length := interp.localCheckedCodeProofLength
    proof_length_eq_length := hrec.proof_length_eq_checked
  }
  encoder_equivalence := {
    length_eq_localChecked := by
      intro _code _hcode
      rfl
  }

theorem FormulaCodeHilbertInterpretation.projectCheckedRecognition_iff_conventionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertProjectCheckedProofLengthRecognition interp ↔
      Nonempty (PAHilbertProjectCheckedRecognitionCertificate interp) := by
  constructor
  · intro hrec
    exact
      ⟨PAHilbertProjectCheckedRecognitionCertificate.ofProjectCheckedRecognition
        hrec⟩
  · intro hcert
    rcases hcert with ⟨hcert⟩
    exact hcert.toProjectCheckedRecognition

noncomputable def
    PAHilbertProjectCheckedRecognitionCertificate.ofLocalCheckedProjectProofLengthSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode) :
    PAHilbertProjectCheckedRecognitionCertificate interp where
  convention :=
    PAHilbertProofLengthConvention.ofProjectProofLengthSemantics
      interp.localCheckedCodeProofLength hsem
  encoder_equivalence :=
    interp.localCheckedEncoderEquiv_ofProjectSemantics hsem

noncomputable def PAHilbertProjectionFamilyExactness.toCanonicalMinCheckedConvention
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertProjectionFamilyExactness interp) :
    PAHilbertProofLengthConvention where
  length := interp.canonicalMinCheckedLength
  proof_length_eq_length := by
    intro code hcode
    rcases hcode with ⟨m, hcode_eq⟩ | ⟨m, hcode_eq⟩
    · subst hcode_eq
      rw [hexact.partialConsistency_exact m]
      exact_mod_cast
        (interp.canonicalMinCheckedLength_partialConsistency m).symm
    · subst hcode_eq
      rw [hexact.reflectionGraft_exact m]
      exact_mod_cast
        (interp.canonicalMinCheckedLength_reflectionGraft m).symm

theorem PAHilbertProjectionFamilyExactness.toCanonicalFamilyEncoderEquivalence
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertProjectionFamilyExactness interp) :
    FormulaCodeHilbertCheckedCodeFamilyEncoderEquivalence
      interp hexact.toCanonicalMinCheckedConvention where
  partialConsistency_length_eq := by
    intro m
    exact interp.canonicalMinCheckedLength_partialConsistency m
  reflectionGraft_length_eq := by
    intro m
    exact interp.canonicalMinCheckedLength_reflectionGraft m

theorem PAHilbertProjectionFamilyExactness.toCanonicalEncoderEquivalence
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertProjectionFamilyExactness interp) :
    FormulaCodeHilbertCheckedCodeEncoderEquivalence
      interp hexact.toCanonicalMinCheckedConvention :=
  hexact.toCanonicalFamilyEncoderEquivalence.toEncoderEquivalence

noncomputable def PAHilbertProjectionFamilyExactness.toCanonicalRecognitionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertProjectionFamilyExactness interp) :
    PAHilbertProjectCheckedRecognitionCertificate interp where
  convention := hexact.toCanonicalMinCheckedConvention
  encoder_equivalence := hexact.toCanonicalEncoderEquivalence

theorem PAHilbertProjectCheckedProofLengthRecognition.toProjectProofLengthSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAHilbertProjectCheckedProofLengthRecognition interp) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode where
  proof_length_eq := hrec.proof_length_eq_checked

theorem PAHilbertProjectCheckedProofLengthRecognition.ofProjectProofLengthSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode) :
    PAHilbertProjectCheckedProofLengthRecognition interp where
  proof_length_eq_checked := hsem.proof_length_eq

theorem PAHilbertProjectCheckedProofLengthRecognition.iff_projectCheckedProofLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertProjectCheckedProofLengthRecognition interp ↔
      ∀ code : FormulaCode, FormulaCodeHilbertRelevantCode code →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          interp.projectCheckedProofLength code := by
  constructor
  · intro hrec code hcode
    rw [hrec.proof_length_eq_checked code hcode]
    exact (interp.projectCheckedProofLength_eq_localChecked code).symm
  · intro hrec
    refine ⟨?_⟩
    intro code hcode
    rw [hrec code hcode]
    exact interp.projectCheckedProofLength_eq_localChecked code

theorem FormulaCodeHilbertInterpretation.projectCheckedRecognition_iff_localProofCodeProjectLength
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ) :
    PAHilbertProjectCheckedProofLengthRecognition interp ↔
      ∀ code : FormulaCode, FormulaCodeHilbertRelevantCode code →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          interp.localProofCodeSemantics.projectLength fallback code := by
  rw [PAHilbertProjectCheckedProofLengthRecognition.iff_projectCheckedProofLength interp]
  constructor
  · intro h code hcode
    rw [h code hcode]
    exact (interp.localProofCode_projectLength_eq_projectChecked fallback code hcode).symm
  · intro h code hcode
    rw [h code hcode]
    exact interp.localProofCode_projectLength_eq_projectChecked fallback code hcode

-- Proof-code checker formulation of the recognition assumption.  This is the
-- same mathematical content as project-checked recognition, but stated through
-- the concrete `ProofCodeSemantics.projectLength` generated by the local
-- checker and a fallback outside the projection fragment.
structure PAHilbertProofCodeCheckerRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  fallback_length : FormulaCode → ℕ
  proof_length_eq_checker_projectLength :
    ∀ code : FormulaCode, FormulaCodeHilbertRelevantCode code →
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
        interp.localProofCodeSemantics.projectLength fallback_length code

def PAHilbertProofCodeCheckerRecognition.toProjectCheckedRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcheck : PAHilbertProofCodeCheckerRecognition interp) :
    PAHilbertProjectCheckedProofLengthRecognition interp :=
  (interp.projectCheckedRecognition_iff_localProofCodeProjectLength
    hcheck.fallback_length).2 hcheck.proof_length_eq_checker_projectLength

def PAHilbertProjectCheckedProofLengthRecognition.toProofCodeCheckerRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAHilbertProjectCheckedProofLengthRecognition interp)
    (fallback_length : FormulaCode → ℕ) :
    PAHilbertProofCodeCheckerRecognition interp where
  fallback_length := fallback_length
  proof_length_eq_checker_projectLength :=
    (interp.projectCheckedRecognition_iff_localProofCodeProjectLength
      fallback_length).1 hrec

theorem FormulaCodeHilbertInterpretation.projectCheckedRecognition_iff_proofCodeChecker
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertProjectCheckedProofLengthRecognition interp ↔
      Nonempty (PAHilbertProofCodeCheckerRecognition interp) := by
  constructor
  · intro hrec
    exact ⟨hrec.toProofCodeCheckerRecognition (fun _ => 0)⟩
  · intro h
    rcases h with ⟨hcheck⟩
    exact hcheck.toProjectCheckedRecognition

theorem PAHilbertProjectCheckedProofLengthRecognition.toFamilyExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAHilbertProjectCheckedProofLengthRecognition interp) :
    PAHilbertProjectionFamilyExactness interp :=
  PAHilbertProjectionFamilyExactness.of_projectCheckedCodeProofLengthSemantics
    interp hrec.toProjectProofLengthSemantics

theorem PAHilbertProjectCheckedProofLengthRecognition.ofFamilyExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertProjectionFamilyExactness interp) :
    PAHilbertProjectCheckedProofLengthRecognition interp :=
  PAHilbertProjectCheckedProofLengthRecognition.ofProjectProofLengthSemantics
    hexact.to_projectCheckedCodeProofLengthSemantics

theorem FormulaCodeHilbertInterpretation.projectCheckedRecognition_iff_familyExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertProjectCheckedProofLengthRecognition interp ↔
      PAHilbertProjectionFamilyExactness interp :=
  ⟨PAHilbertProjectCheckedProofLengthRecognition.toFamilyExactness,
    PAHilbertProjectCheckedProofLengthRecognition.ofFamilyExactness⟩

theorem PAHilbertLocalCheckerExactness.toLocalProofCodeRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertLocalCheckerExactness interp)
    (hrec : PAHilbertProjectCheckedProofLengthRecognition interp) :
    PAHilbertLocalProofCodeRecognition interp where
  proof_length_eq_minProofCodeSize := by
    intro code hcode
    rw [hrec.proof_length_eq_checked code hcode]
    exact_mod_cast (hexact.minProofCodeSize_eq_localChecked code hcode).symm

theorem PAHilbertLocalCheckerExactness.toProjectCheckedRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertLocalCheckerExactness interp)
    (hrec : PAHilbertLocalProofCodeRecognition interp) :
    PAHilbertProjectCheckedProofLengthRecognition interp where
  proof_length_eq_checked := by
    intro code hcode
    rw [hrec.proof_length_eq_minProofCodeSize code hcode]
    exact_mod_cast hexact.minProofCodeSize_eq_localChecked code hcode

theorem FormulaCodeHilbertInterpretation.localProofCodeRecognition_iff_projectCheckedRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertLocalProofCodeRecognition interp ↔
      PAHilbertProjectCheckedProofLengthRecognition interp :=
  ⟨fun hrec =>
    PAHilbertLocalCheckerExactness.toProjectCheckedRecognition
      interp.localHilbertCheckerExactness hrec,
    fun hrec =>
      PAHilbertLocalCheckerExactness.toLocalProofCodeRecognition
        interp.localHilbertCheckerExactness hrec⟩

def PAHilbertLocalProofCodeRecognition.toProofCodeCheckerRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAHilbertLocalProofCodeRecognition interp)
    (fallback_length : FormulaCode → ℕ) :
    PAHilbertProofCodeCheckerRecognition interp :=
  ((FormulaCodeHilbertInterpretation.localProofCodeRecognition_iff_projectCheckedRecognition
    interp).1 hrec).toProofCodeCheckerRecognition fallback_length

def PAHilbertProofCodeCheckerRecognition.ofProofLengthCodeCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (fallback_length : FormulaCode → ℕ)
    (hcal : (interp.localHilbertProofLengthCodeSemantics fallback_length).Calibration) :
    PAHilbertProofCodeCheckerRecognition interp :=
  (PAHilbertLocalProofCodeRecognition.ofProofLengthCodeCalibration
    fallback_length hcal).toProofCodeCheckerRecognition fallback_length

theorem PAHilbertProofCodeCheckerRecognition.toProofLengthCodeCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcheck : PAHilbertProofCodeCheckerRecognition interp)
    (fallback_length : FormulaCode → ℕ) :
    (interp.localHilbertProofLengthCodeSemantics fallback_length).Calibration :=
  (FormulaCodeHilbertInterpretation.localProofCodeRecognition_iff_projectCheckedRecognition
    interp).2 hcheck.toProjectCheckedRecognition |>.toProofLengthCodeCalibration
      fallback_length

theorem FormulaCodeHilbertInterpretation.proofCodeCheckerRecognition_iff_proofLengthCodeCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback_length : FormulaCode → ℕ) :
    Nonempty (PAHilbertProofCodeCheckerRecognition interp) ↔
      (interp.localHilbertProofLengthCodeSemantics fallback_length).Calibration := by
  constructor
  · intro hcheck
    rcases hcheck with ⟨hcheck⟩
    exact hcheck.toProofLengthCodeCalibration fallback_length
  · intro hcal
    exact
      ⟨PAHilbertProofCodeCheckerRecognition.ofProofLengthCodeCalibration
        fallback_length hcal⟩

structure PAHilbertLocalProofCodeRecognitionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) : Prop where
  checker_exactness : PAHilbertLocalCheckerExactness interp
  encoder_recognition : PAHilbertProjectCheckedProofLengthRecognition interp

theorem PAHilbertLocalProofCodeRecognitionCertificate.toLocalProofCodeRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcert : PAHilbertLocalProofCodeRecognitionCertificate interp) :
    PAHilbertLocalProofCodeRecognition interp :=
  hcert.checker_exactness.toLocalProofCodeRecognition
    hcert.encoder_recognition

theorem PAHilbertLocalProofCodeRecognitionCertificate.ofLocalProofCodeRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAHilbertLocalProofCodeRecognition interp) :
    PAHilbertLocalProofCodeRecognitionCertificate interp where
  checker_exactness := interp.localHilbertCheckerExactness
  encoder_recognition :=
    interp.localHilbertCheckerExactness.toProjectCheckedRecognition hrec

theorem FormulaCodeHilbertInterpretation.localProofCodeRecognition_iff_encoderCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertLocalProofCodeRecognition interp ↔
      PAHilbertLocalProofCodeRecognitionCertificate interp :=
  ⟨PAHilbertLocalProofCodeRecognitionCertificate.ofLocalProofCodeRecognition,
    PAHilbertLocalProofCodeRecognitionCertificate.toLocalProofCodeRecognition⟩

structure PAHilbertLocalProofCodeConventionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  checker_exactness : PAHilbertLocalCheckerExactness interp
  encoder_certificate : PAHilbertProjectCheckedRecognitionCertificate interp

theorem PAHilbertLocalProofCodeConventionCertificate.toRecognitionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcert : PAHilbertLocalProofCodeConventionCertificate interp) :
    PAHilbertLocalProofCodeRecognitionCertificate interp where
  checker_exactness := hcert.checker_exactness
  encoder_recognition :=
    hcert.encoder_certificate.toProjectCheckedRecognition

theorem PAHilbertLocalProofCodeConventionCertificate.toLocalProofCodeRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcert : PAHilbertLocalProofCodeConventionCertificate interp) :
    PAHilbertLocalProofCodeRecognition interp :=
  hcert.toRecognitionCertificate.toLocalProofCodeRecognition

noncomputable def
    PAHilbertLocalProofCodeConventionCertificate.ofRecognitionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcert : PAHilbertLocalProofCodeRecognitionCertificate interp) :
    PAHilbertLocalProofCodeConventionCertificate interp where
  checker_exactness := hcert.checker_exactness
  encoder_certificate :=
    PAHilbertProjectCheckedRecognitionCertificate.ofProjectCheckedRecognition
      hcert.encoder_recognition

noncomputable def
    PAHilbertLocalProofCodeConventionCertificate.ofLocalProofCodeRecognition
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAHilbertLocalProofCodeRecognition interp) :
    PAHilbertLocalProofCodeConventionCertificate interp :=
  PAHilbertLocalProofCodeConventionCertificate.ofRecognitionCertificate
    (PAHilbertLocalProofCodeRecognitionCertificate.ofLocalProofCodeRecognition
      hrec)

theorem FormulaCodeHilbertInterpretation.localProofCodeRecognition_iff_conventionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertLocalProofCodeRecognition interp ↔
      Nonempty (PAHilbertLocalProofCodeConventionCertificate interp) := by
  constructor
  · intro hrec
    exact
      ⟨PAHilbertLocalProofCodeConventionCertificate.ofLocalProofCodeRecognition
        hrec⟩
  · intro hcert
    rcases hcert with ⟨hcert⟩
    exact hcert.toLocalProofCodeRecognition

noncomputable def
    PAHilbertLocalProofCodeConventionCertificate.ofLocalCheckedProjectProofLengthSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode) :
    PAHilbertLocalProofCodeConventionCertificate interp where
  checker_exactness := interp.localHilbertCheckerExactness
  encoder_certificate :=
    PAHilbertProjectCheckedRecognitionCertificate.ofLocalCheckedProjectProofLengthSemantics
      interp hsem

/-- External project convention for the local Hilbert checked-code model.

This is a named calibration input, not an internal proof: it identifies the
project-level PA proof length with the project checked-code length for the
chosen local Hilbert interpretation. -/
axiom externalPAHilbertProofLength_eq_localChecked
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ∀ code : FormulaCode, FormulaCodeHilbertRelevantCode code →
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
        interp.localCheckedCodeProofLength code

noncomputable def externalPAHilbertProofLengthConvention
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertProofLengthConvention where
  length := interp.localCheckedCodeProofLength
  proof_length_eq_length :=
    externalPAHilbertProofLength_eq_localChecked interp

theorem externalPAHilbertCheckedCodeEncoderEquivalence
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    FormulaCodeHilbertCheckedCodeEncoderEquivalence
      interp (externalPAHilbertProofLengthConvention interp) where
  length_eq_localChecked := by
    intro _code _hcode
    rfl

noncomputable def externalPAHilbertProjectCheckedRecognitionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertProjectCheckedRecognitionCertificate interp where
  convention := externalPAHilbertProofLengthConvention interp
  encoder_equivalence :=
    externalPAHilbertCheckedCodeEncoderEquivalence interp

noncomputable def externalPAHilbertLocalProofCodeConventionCertificate
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertLocalProofCodeConventionCertificate interp where
  checker_exactness := interp.localHilbertCheckerExactness
  encoder_certificate :=
    externalPAHilbertProjectCheckedRecognitionCertificate interp

theorem FormulaCodeHilbertInterpretation.familyExactness_of_projectCheckedProofLength_eq
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hproject :
      ∀ code : FormulaCode, FormulaCodeHilbertRelevantCode code →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          interp.projectCheckedProofLength code) :
    PAHilbertProjectionFamilyExactness interp :=
  (PAHilbertProjectCheckedProofLengthRecognition.iff_projectCheckedProofLength
    interp).2 hproject |>.toFamilyExactness

theorem PAHilbertProjectionFamilyExactness.toBridge
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertProjectionFamilyExactness interp) :
    HilbertProofLengthSoundnessBridge :=
  SemanticHilbertProofLengthSoundnessBridge.toBridge_of_projectSemantics
    interp.semanticBridge_of_localCheckedCodeProofLength
    hexact.to_projectCheckedCodeProofLengthSemantics

theorem PAHilbertProjectionFamilyExactness.toPartialConsistencySourceMinCheckedCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertProjectionFamilyExactness interp) :
    PartialConsistencySourceMinCheckedCalibration interp where
  proof_length_eq_source_minChecked := hexact.partialConsistency_exact

theorem
    PAHilbertProjectCheckedProofLengthRecognition.toPartialConsistencySourceMinCheckedCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAHilbertProjectCheckedProofLengthRecognition interp) :
    PartialConsistencySourceMinCheckedCalibration interp :=
  hrec.toFamilyExactness.toPartialConsistencySourceMinCheckedCalibration

noncomputable def PAHilbertProjectionFamilyExactness.toConstantProofLengthProjection
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertProjectionFamilyExactness interp) :
    ConstantProofLengthProjection
      ProofSystem.PA ProofLengthMeasure.symbolSize
      partialConsistencyCode sondowReflectionGraftCode :=
  (interp.semanticConstantProjection_of_localCheckedCodeProofLength).toConstantProofLengthProjection
    hexact.to_projectCheckedCodeProofLengthSemantics
    (fun n => Or.inl ⟨n, rfl⟩)
    (fun n => Or.inr ⟨n, rfl⟩)

noncomputable def PAHilbertProjectionFamilyExactness.toLinearProofLengthProjection
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertProjectionFamilyExactness interp) :
    LinearProofLengthProjection
      ProofSystem.PA ProofLengthMeasure.symbolSize
      partialConsistencyCode sondowReflectionGraftCode :=
  hexact.toConstantProofLengthProjection.toLinearProofLengthProjection

noncomputable def PAHilbertProjectionFamilyExactness.toStrongLowerBoundTransfer
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertProjectionFamilyExactness interp) :
    StrongLowerBoundTransfer
      ProofSystem.PA ProofLengthMeasure.symbolSize
      partialConsistencyCode sondowReflectionGraftCode :=
  (interp.semanticStrongTransfer_of_localCheckedCodeProofLength).toStrongLowerBoundTransfer
    hexact.to_projectCheckedCodeProofLengthSemantics
    (fun n => Or.inl ⟨n, rfl⟩)
    (fun n => Or.inr ⟨n, rfl⟩)

theorem PAHilbertProjectCheckedProofLengthRecognition.toBridge
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAHilbertProjectCheckedProofLengthRecognition interp) :
    HilbertProofLengthSoundnessBridge :=
  hrec.toFamilyExactness.toBridge

noncomputable def PAHilbertProjectCheckedProofLengthRecognition.toStrongLowerBoundTransfer
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAHilbertProjectCheckedProofLengthRecognition interp) :
    StrongLowerBoundTransfer
      ProofSystem.PA ProofLengthMeasure.symbolSize
      partialConsistencyCode sondowReflectionGraftCode :=
  hrec.toFamilyExactness.toStrongLowerBoundTransfer

noncomputable def
    PAHilbertProjectCheckedProofLengthRecognition.toReflectionGraftStrongLowerBound
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAHilbertProjectCheckedProofLengthRecognition interp)
    (hsource :
      SemanticStrongProofLengthLowerBound
        interp.localCheckedCodeProofLength partialConsistencyCode) :
    StrongProofLengthLowerBound
      ProofSystem.PA ProofLengthMeasure.symbolSize sondowReflectionGraftCode :=
  SemanticStrongProofLengthLowerBound.toStrongProofLengthLowerBound
    (interp.semanticReflectionGraftLowerBound_of_localCheckedSource hsource)
    hrec.toProjectProofLengthSemantics
    (fun n => Or.inr ⟨n, rfl⟩)

noncomputable def
    PAHilbertProjectCheckedProofLengthRecognition.toReflectionGraftEventualLowerBound
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAHilbertProjectCheckedProofLengthRecognition interp)
    (hsource :
      SemanticStrongProofLengthLowerBound
        interp.localCheckedCodeProofLength partialConsistencyCode) :
    EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  SemanticEventualLowerBound.toEventualLowerBound
    (interp.semanticReflectionGraftEventualLowerBound_of_localCheckedSource hsource)
    hrec.toProjectProofLengthSemantics
    (fun n => Or.inr ⟨n, rfl⟩)

theorem PAHilbertProjectionFamilyExactness.toLocalPAHilbertCodeCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (fallback : FormulaCode → ℕ)
    (hexact : PAHilbertProjectionFamilyExactness interp) :
    (let model := interp.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.Calibration) :=
  (interp.localPAHilbert_calibration_iff_minChecked_exact fallback).2
    ⟨hexact.partialConsistency_exact, hexact.reflectionGraft_exact⟩

theorem PAHilbertProjectionFamilyExactness.ofLocalPAHilbertCodeCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (fallback : FormulaCode → ℕ)
    (hcal :
      (let model := interp.localPAHilbertProofLengthCodeSemanticsForProjection fallback
       model.code_model.Calibration)) :
    PAHilbertProjectionFamilyExactness interp where
  partialConsistency_exact :=
    ((interp.localPAHilbert_calibration_iff_minChecked_exact fallback).1 hcal).1
  reflectionGraft_exact :=
    ((interp.localPAHilbert_calibration_iff_minChecked_exact fallback).1 hcal).2

theorem FormulaCodeHilbertInterpretation.localPAHilbert_calibration_iff_familyExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ) :
    (let model := interp.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.Calibration) ↔
      PAHilbertProjectionFamilyExactness interp :=
  ⟨PAHilbertProjectionFamilyExactness.ofLocalPAHilbertCodeCalibration fallback,
    fun hexact => hexact.toLocalPAHilbertCodeCalibration fallback⟩

theorem PAHilbertProjectionFamilyExactness.toLocalHilbertProofLengthCodeCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertProjectionFamilyExactness interp)
    (fallback : FormulaCode → ℕ) :
    (interp.localHilbertProofLengthCodeSemantics fallback).Calibration := by
  simpa [
    FormulaCodeHilbertInterpretation.localPAHilbertProofLengthCodeSemanticsForProjection
  ] using hexact.toLocalPAHilbertCodeCalibration fallback

theorem FormulaCodeHilbertInterpretation.localHilbertProofLengthCodeCalibration_iff_familyExactness
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ) :
    (interp.localHilbertProofLengthCodeSemantics fallback).Calibration ↔
      PAHilbertProjectionFamilyExactness interp := by
  simpa [
    FormulaCodeHilbertInterpretation.localPAHilbertProofLengthCodeSemanticsForProjection
  ] using interp.localPAHilbert_calibration_iff_familyExactness fallback

theorem PAHilbertProjectionFamilyExactness.toStandardFormulaCodeProofLengthSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hexact : PAHilbertProjectionFamilyExactness interp) :
    StandardFormulaCodeProofLengthSemantics interp where
  target_minLength := by
    intro m
    rw [hexact.reflectionGraft_exact m]
    exact_mod_cast interp.target_proof_family.minCheckedCodeSize_eq_minLength m
  source_minLength := by
    intro m
    rw [hexact.partialConsistency_exact m]
    exact_mod_cast
      interp.target_proof_family.rightConjElim.minCheckedCodeSize_eq_minLength m

theorem PAHilbertProjectionFamilyExactness.ofStandardFormulaCodeProofLengthSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hsem : StandardFormulaCodeProofLengthSemantics interp) :
    PAHilbertProjectionFamilyExactness interp where
  partialConsistency_exact := by
    intro m
    rw [hsem.source_minLength m]
    exact_mod_cast
      (interp.target_proof_family.rightConjElim.minCheckedCodeSize_eq_minLength m).symm
  reflectionGraft_exact := by
    intro m
    rw [hsem.target_minLength m]
    exact_mod_cast
      (interp.target_proof_family.minCheckedCodeSize_eq_minLength m).symm

theorem FormulaCodeHilbertInterpretation.familyExactness_iff_standardSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertProjectionFamilyExactness interp ↔
      StandardFormulaCodeProofLengthSemantics interp :=
  ⟨PAHilbertProjectionFamilyExactness.toStandardFormulaCodeProofLengthSemantics,
    PAHilbertProjectionFamilyExactness.ofStandardFormulaCodeProofLengthSemantics⟩

theorem FormulaCodeHilbertInterpretation.toBridge_of_semanticProjectSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback : FormulaCode → ℕ)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        (interp.localHilbertSemanticProofLength fallback)
        FormulaCodeHilbertRelevantCode) :
    HilbertProofLengthSoundnessBridge :=
  SemanticHilbertProofLengthSoundnessBridge.toBridge_of_projectSemantics
    (interp.semanticBridge_of_localHilbertSemanticProofLength fallback)
    hsem

noncomputable def LocalHilbertProofCodeProjectionModel.toExactProjectionRealization
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hmodel : LocalHilbertProofCodeProjectionModel interp)
    (hproof_length :
      ∀ code : FormulaCode, ∀ hcode : FormulaCodeHilbertRelevantCode code,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          interp.localHilbertProofCodeSemantics.minProofCodeSize code hcode) :
    HilbertProofLengthExactProjectionRealization halign where
  sourceLength := fun m =>
    interp.localHilbertProofCodeSemantics.minProofCodeSize
      (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)
  targetLength := fun m =>
    interp.localHilbertProofCodeSemantics.minProofCodeSize
      (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)
  source_exact := by
    intro m
    exact hproof_length (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)
  target_exact := by
    intro m
    exact hproof_length (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)
  source_le_target_add_two := hmodel.source_le_target_add_two

theorem LocalHilbertProofCodeProjectionModel.toBridge
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hmodel : LocalHilbertProofCodeProjectionModel interp)
    (hproof_length :
      ∀ code : FormulaCode, ∀ hcode : FormulaCodeHilbertRelevantCode code,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          interp.localHilbertProofCodeSemantics.minProofCodeSize code hcode) :
    HilbertProofLengthSoundnessBridge :=
  (hmodel.toExactProjectionRealization hproof_length).toBridge

theorem FormulaCodeHilbertInterpretation.toBridge_of_localHilbertProofCodeSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hproof_length :
      ∀ code : FormulaCode, ∀ hcode : FormulaCodeHilbertRelevantCode code,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          interp.localHilbertProofCodeSemantics.minProofCodeSize code hcode) :
    HilbertProofLengthSoundnessBridge :=
  interp.localHilbertProofCodeProjectionModel.toBridge hproof_length

theorem
    FormulaCodeHilbertInterpretation.projectCheckedCodeSemantics_of_localHilbertProofCodeSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hproof_length :
      ∀ code : FormulaCode, ∀ hcode : FormulaCodeHilbertRelevantCode code,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          interp.localHilbertProofCodeSemantics.minProofCodeSize code hcode) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode where
  proof_length_eq := by
    intro code hcode
    rw [hproof_length code hcode]
    rcases hcode with ⟨m, hcode_eq⟩ | ⟨m, hcode_eq⟩
    · subst hcode_eq
      rw [interp.localHilbertProofCodeSemantics_source_min_eq m,
        interp.localCheckedCodeProofLength_partialConsistency m]
    · subst hcode_eq
      rw [interp.localHilbertProofCodeSemantics_target_min_eq m,
        interp.localCheckedCodeProofLength_reflectionGraft m]

-- The remaining project-level calibration, now named as a reusable symbol:
-- on the two formula-code families used by the projection bridge, the global
-- `proof_length` agrees with the fully closed local MiniHilbert length model.
structure FormulaCodeHilbertLocalCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  source_eq_local :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode m) =
        interp.localProofLength (partialConsistencyCode m)
  target_eq_local :
    ∀ m : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode m) =
        interp.localProofLength (sondowReflectionGraftCode m)

theorem FormulaCodeHilbertLocalCalibration.of_projectProofLengthSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localProofLength FormulaCodeHilbertRelevantCode) :
    FormulaCodeHilbertLocalCalibration interp where
  source_eq_local := by
    intro m
    exact hsem.proof_length_eq (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)
  target_eq_local := by
    intro m
    exact hsem.proof_length_eq (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)

theorem FormulaCodeHilbertLocalCalibration.of_projectCodeSizeProofLengthSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCodeSizeProofLength FormulaCodeHilbertRelevantCode) :
    FormulaCodeHilbertLocalCalibration interp where
  source_eq_local := by
    intro m
    rw [hsem.proof_length_eq (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)]
    exact_mod_cast
      interp.localCodeSizeProofLength_eq_localProofLength (partialConsistencyCode m)
  target_eq_local := by
    intro m
    rw [hsem.proof_length_eq (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)]
    exact_mod_cast
      interp.localCodeSizeProofLength_eq_localProofLength (sondowReflectionGraftCode m)

theorem FormulaCodeHilbertLocalCalibration.of_projectCheckedCodeProofLengthSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode) :
    FormulaCodeHilbertLocalCalibration interp where
  source_eq_local := by
    intro m
    rw [hsem.proof_length_eq (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)]
    exact_mod_cast
      interp.localCheckedCodeProofLength_eq_localProofLength (partialConsistencyCode m)
  target_eq_local := by
    intro m
    rw [hsem.proof_length_eq (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)]
    exact_mod_cast
      interp.localCheckedCodeProofLength_eq_localProofLength (sondowReflectionGraftCode m)

theorem FormulaCodeHilbertLocalCalibration.of_localHilbertProofCodeSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hproof_length :
      ∀ code : FormulaCode, ∀ hcode : FormulaCodeHilbertRelevantCode code,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          interp.localHilbertProofCodeSemantics.minProofCodeSize code hcode) :
    FormulaCodeHilbertLocalCalibration interp :=
  FormulaCodeHilbertLocalCalibration.of_projectCheckedCodeProofLengthSemantics
    interp
    (interp.projectCheckedCodeSemantics_of_localHilbertProofCodeSemantics hproof_length)

theorem FormulaCodeHilbertLocalCalibration.to_localHilbertProofCodeSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcal : FormulaCodeHilbertLocalCalibration interp) :
    ∀ code : FormulaCode, ∀ hcode : FormulaCodeHilbertRelevantCode code,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
        interp.localHilbertProofCodeSemantics.minProofCodeSize code hcode := by
  intro code hcode
  rcases hcode with ⟨m, hcode_eq⟩ | ⟨m, hcode_eq⟩
  · subst hcode_eq
    rw [hcal.source_eq_local m]
    rw [← interp.localCheckedCodeProofLength_eq_localProofLength (partialConsistencyCode m)]
    rw [interp.localCheckedCodeProofLength_partialConsistency m]
    rw [← interp.localHilbertProofCodeSemantics_source_min_eq m]
  · subst hcode_eq
    rw [hcal.target_eq_local m]
    rw [← interp.localCheckedCodeProofLength_eq_localProofLength (sondowReflectionGraftCode m)]
    rw [interp.localCheckedCodeProofLength_reflectionGraft m]
    rw [← interp.localHilbertProofCodeSemantics_target_min_eq m]

theorem PAHilbertLocalProofCodeRecognition.toFormulaCodeHilbertLocalCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAHilbertLocalProofCodeRecognition interp) :
    FormulaCodeHilbertLocalCalibration interp :=
  FormulaCodeHilbertLocalCalibration.of_localHilbertProofCodeSemantics
    interp hrec.proof_length_eq_minProofCodeSize

theorem PAHilbertLocalProofCodeRecognition.ofFormulaCodeHilbertLocalCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcal : FormulaCodeHilbertLocalCalibration interp) :
    PAHilbertLocalProofCodeRecognition interp where
  proof_length_eq_minProofCodeSize :=
    hcal.to_localHilbertProofCodeSemantics

theorem FormulaCodeHilbertInterpretation.localProofCodeRecognition_iff_localCalibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertLocalProofCodeRecognition interp ↔
      FormulaCodeHilbertLocalCalibration interp :=
  ⟨PAHilbertLocalProofCodeRecognition.toFormulaCodeHilbertLocalCalibration,
    PAHilbertLocalProofCodeRecognition.ofFormulaCodeHilbertLocalCalibration⟩

-- If the global project-level `proof_length` is calibrated to the closed local
-- model above on the two bridge families, the standard semantics package
-- follows.  The premise is now exactly the intended semantic calibration,
-- separated from the already-verified local proof-calculus theorem.
theorem FormulaCodeHilbertInterpretation.standardSemantics_of_localProofLength_calibration
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hcal :
      ∀ code : FormulaCode,
        code.family = FormulaFamily.partialConsistency ∨
          code.family = FormulaFamily.sondowReflectionGraft →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          interp.localProofLength code) :
    StandardFormulaCodeProofLengthSemantics interp where
  target_minLength := by
    intro m
    rw [hcal (sondowReflectionGraftCode m) (Or.inr rfl)]
    exact_mod_cast interp.localProofLength_reflectionGraft m
  source_minLength := by
    intro m
    rw [hcal (partialConsistencyCode m) (Or.inl rfl)]
    exact_mod_cast interp.localProofLength_partialConsistency m

theorem FormulaCodeHilbertLocalCalibration.toStandardSemantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcal : FormulaCodeHilbertLocalCalibration interp) :
    StandardFormulaCodeProofLengthSemantics interp where
  target_minLength := by
    intro m
    rw [hcal.target_eq_local m]
    exact_mod_cast interp.localProofLength_reflectionGraft m
  source_minLength := by
    intro m
    rw [hcal.source_eq_local m]
    exact_mod_cast interp.localProofLength_partialConsistency m

theorem FormulaCodeHilbertLocalCalibration.toBridge
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcal : FormulaCodeHilbertLocalCalibration interp) :
    HilbertProofLengthSoundnessBridge :=
  hcal.toStandardSemantics.toExactProjectionRealization.toBridge

noncomputable def FormulaCodeHilbertLocalCalibration.toExactProjectionRealization
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcal : FormulaCodeHilbertLocalCalibration interp) :
    HilbertProofLengthExactProjectionRealization halign :=
  hcal.toStandardSemantics.toExactProjectionRealization

noncomputable def FormulaCodeHilbertLocalCalibration.toTargetExactProjectionRealization
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcal : FormulaCodeHilbertLocalCalibration interp) :
    HilbertProofLengthTargetExactProjectionRealization halign :=
  hcal.toStandardSemantics.toTargetExactProjectionRealization

theorem FormulaCodeHilbertLocalCalibration.toTwoStepOverhead
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcal : FormulaCodeHilbertLocalCalibration interp) :
    HilbertRightConjunctionTwoStepOverhead :=
  hcal.toBridge.realizes_right_conj_elim

def FormulaCodeHilbertInterpretation.default
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (target : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) :
    FormulaCodeHilbertInterpretation
      Ax A B hilbert_projection_code_alignment_true where
  local_interpretation := LocalFormulaCodeHilbertInterpretation.default A B
  target_proof_family := target
  code_alignment := rfl

theorem FormulaCodeHilbertInterpretation.interprets_partialConsistency
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.local_interpretation.interpret (partialConsistencyCode m) = B m :=
  interp.local_interpretation.interprets_partial_consistency m

theorem FormulaCodeHilbertInterpretation.interprets_reflectionGraft
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    interp.local_interpretation.interpret (sondowReflectionGraftCode m) =
      A m ⊓ B m :=
  interp.local_interpretation.interprets_reflection_graft m

def FormulaCodeHilbertInterpretation.target_proof_of_interpreted_reflectionGraft
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    TheoryProof Ax
      (interp.local_interpretation.interpret (sondowReflectionGraftCode m)) := by
  rw [interp.interprets_reflectionGraft m]
  exact interp.target_proof_family.proof m

def FormulaCodeHilbertInterpretation.source_proof_of_interpreted_partialConsistency
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    TheoryProof Ax
      (interp.local_interpretation.interpret (partialConsistencyCode m)) := by
  rw [interp.interprets_partialConsistency m]
  exact interp.target_proof_family.rightConjElim.proof m

theorem FormulaCodeHilbertInterpretation.target_provable_of_interpreted_reflectionGraft
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    TheoryProof.Provable Ax
      (interp.local_interpretation.interpret (sondowReflectionGraftCode m)) :=
  ⟨interp.target_proof_of_interpreted_reflectionGraft m⟩

theorem FormulaCodeHilbertInterpretation.source_provable_of_interpreted_partialConsistency
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    TheoryProof.Provable Ax
      (interp.local_interpretation.interpret (partialConsistencyCode m)) :=
  ⟨interp.source_proof_of_interpreted_partialConsistency m⟩

theorem FormulaCodeHilbertInterpretation.hasProofOfLength_interpreted_reflectionGraft
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    TheoryProof.HasProofOfLength Ax
      (interp.local_interpretation.interpret (sondowReflectionGraftCode m))
      (interp.target_proof_of_interpreted_reflectionGraft m).length := by
  refine ⟨interp.target_proof_of_interpreted_reflectionGraft m, ?_⟩
  exact le_rfl

theorem FormulaCodeHilbertInterpretation.hasProofOfLength_interpreted_partialConsistency
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    TheoryProof.HasProofOfLength Ax
      (interp.local_interpretation.interpret (partialConsistencyCode m))
      (interp.source_proof_of_interpreted_partialConsistency m).length := by
  refine ⟨interp.source_proof_of_interpreted_partialConsistency m, ?_⟩
  exact le_rfl

theorem FormulaCodeHilbertInterpretation.minLength_interpreted_reflectionGraft_le
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    TheoryProof.minLength
      (interp.target_provable_of_interpreted_reflectionGraft m) ≤
      (interp.target_proof_of_interpreted_reflectionGraft m).length :=
  TheoryProof.minLength_le_of_hasProofOfLength
    (interp.target_provable_of_interpreted_reflectionGraft m)
    (interp.hasProofOfLength_interpreted_reflectionGraft m)

theorem FormulaCodeHilbertInterpretation.minLength_interpreted_partialConsistency_le
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) (m : ℕ) :
    TheoryProof.minLength
      (interp.source_provable_of_interpreted_partialConsistency m) ≤
      (interp.source_proof_of_interpreted_partialConsistency m).length :=
  TheoryProof.minLength_le_of_hasProofOfLength
    (interp.source_provable_of_interpreted_partialConsistency m)
    (interp.hasProofOfLength_interpreted_partialConsistency m)

theorem FormulaCodeHilbertInterpretation.default_target_proof_length
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (target : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) (m : ℕ) :
    let interp := FormulaCodeHilbertInterpretation.default target
    (interp.target_proof_of_interpreted_reflectionGraft m).length =
      target.length m := by
  rfl

theorem FormulaCodeHilbertInterpretation.default_source_proof_length
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (target : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) (m : ℕ) :
    let interp := FormulaCodeHilbertInterpretation.default target
    (interp.source_proof_of_interpreted_partialConsistency m).length =
      target.rightConjElim.length m := by
  rfl

theorem FormulaCodeHilbertInterpretation.default_minLength_reflectionGraft_le
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (target : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) (m : ℕ) :
    let interp := FormulaCodeHilbertInterpretation.default target
    TheoryProof.minLength
      (interp.target_provable_of_interpreted_reflectionGraft m) ≤
      target.length m := by
  dsimp only
  let interp := FormulaCodeHilbertInterpretation.default target
  rw [← FormulaCodeHilbertInterpretation.default_target_proof_length target m]
  exact interp.minLength_interpreted_reflectionGraft_le m

theorem FormulaCodeHilbertInterpretation.default_minLength_partialConsistency_le
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (target : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) (m : ℕ) :
    let interp := FormulaCodeHilbertInterpretation.default target
    TheoryProof.minLength
      (interp.source_provable_of_interpreted_partialConsistency m) ≤
      target.rightConjElim.length m := by
  dsimp only
  let interp := FormulaCodeHilbertInterpretation.default target
  rw [← FormulaCodeHilbertInterpretation.default_source_proof_length target m]
  exact interp.minLength_interpreted_partialConsistency_le m

noncomputable def FormulaCodeHilbertInterpretation.toTargetRealization
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (calib : FormulaCodeProofLengthCalibration interp) :
    FormulaCodeMinLengthRealization Ax (fun m => A m ⊓ B m)
      sondowReflectionGraftCode where
  proofFamily := interp.target_proof_family
  proof_length_exact := calib.target_exact

noncomputable def FormulaCodeHilbertInterpretation.toFormulaCodeRealization
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (calib : FormulaCodeProofLengthCalibration interp) :
    HilbertRightConjElimFormulaCodeRealization Ax A B halign where
  target := interp.toTargetRealization calib
  source_upper := calib.source_upper

abbrev DefaultHilbertRightConjElimFormulaCodeRealization
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  HilbertRightConjElimFormulaCodeRealization
    Ax A B hilbert_projection_code_alignment_true

noncomputable def HilbertRightConjElimFormulaCodeRealization.source
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    FormulaCodeUpperLengthRealization Ax B partialConsistencyCode :=
  h.target.rightConjElimUpperLengthRealization h.source_upper

noncomputable def HilbertRightConjElimFormulaCodeRealization.toTargetExactProjectionRealization
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    HilbertProofLengthTargetExactProjectionRealization halign :=
  FormulaCodeMinLengthRealization.toTargetExactProjectionRealization
    (halign := halign) h.target h.source_upper

theorem HilbertRightConjElimFormulaCodeRealization.toBridge
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    HilbertProofLengthSoundnessBridge :=
  h.toTargetExactProjectionRealization.toBridge

theorem HilbertRightConjElimFormulaCodeRealization.toTwoStepOverhead
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    HilbertRightConjunctionTwoStepOverhead :=
  h.toBridge.realizes_right_conj_elim

theorem DefaultHilbertRightConjElimFormulaCodeRealization.toBridge
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : DefaultHilbertRightConjElimFormulaCodeRealization Ax A B) :
    HilbertProofLengthSoundnessBridge :=
  HilbertRightConjElimFormulaCodeRealization.toBridge h

theorem DefaultHilbertRightConjElimFormulaCodeRealization.toTwoStepOverhead
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : DefaultHilbertRightConjElimFormulaCodeRealization Ax A B) :
    HilbertRightConjunctionTwoStepOverhead :=
  HilbertRightConjElimFormulaCodeRealization.toTwoStepOverhead h

noncomputable def FormulaCodeHilbertInterpretation.defaultRealization
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (interp :
      FormulaCodeHilbertInterpretation Ax A B
        hilbert_projection_code_alignment_true)
    (calib : FormulaCodeProofLengthCalibration interp) :
    DefaultHilbertRightConjElimFormulaCodeRealization Ax A B :=
  interp.toFormulaCodeRealization calib

noncomputable def FormulaCodeHilbertInterpretation.defaultRealization_of_target
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (target : ConcreteProofFamily Ax (fun m => A m ⊓ B m))
    (calib :
      FormulaCodeProofLengthCalibration
        (FormulaCodeHilbertInterpretation.default target)) :
    DefaultHilbertRightConjElimFormulaCodeRealization Ax A B :=
  (FormulaCodeHilbertInterpretation.default target).defaultRealization calib

theorem FormulaCodeHilbertInterpretation.default_toBridge
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (interp :
      FormulaCodeHilbertInterpretation Ax A B
        hilbert_projection_code_alignment_true)
    (calib : FormulaCodeProofLengthCalibration interp) :
    HilbertProofLengthSoundnessBridge :=
  (interp.defaultRealization calib).toBridge

theorem StandardFormulaCodeProofLengthSemantics.toBridge
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hsem : StandardFormulaCodeProofLengthSemantics interp) :
    HilbertProofLengthSoundnessBridge :=
  (interp.toFormulaCodeRealization hsem.toCalibration).toBridge

theorem FormulaCodeHilbertInterpretation.default_toBridge_of_standard_semantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (interp :
      FormulaCodeHilbertInterpretation Ax A B
        hilbert_projection_code_alignment_true)
    (hsem : StandardFormulaCodeProofLengthSemantics interp) :
    HilbertProofLengthSoundnessBridge :=
  hsem.toBridge

theorem FormulaCodeHilbertInterpretation.default_toTwoStepOverhead
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (interp :
      FormulaCodeHilbertInterpretation Ax A B
        hilbert_projection_code_alignment_true)
    (calib : FormulaCodeProofLengthCalibration interp) :
    HilbertRightConjunctionTwoStepOverhead :=
  (interp.defaultRealization calib).toTwoStepOverhead

theorem StandardFormulaCodeProofLengthSemantics.toTwoStepOverhead
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hsem : StandardFormulaCodeProofLengthSemantics interp) :
    HilbertRightConjunctionTwoStepOverhead :=
  hsem.toBridge.realizes_right_conj_elim

theorem FormulaCodeHilbertInterpretation.default_toTwoStepOverhead_of_standard_semantics
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (interp :
      FormulaCodeHilbertInterpretation Ax A B
        hilbert_projection_code_alignment_true)
    (hsem : StandardFormulaCodeProofLengthSemantics interp) :
    HilbertRightConjunctionTwoStepOverhead :=
  hsem.toTwoStepOverhead

end MiniHilbert

theorem HilbertProofLengthSoundnessForAlignedCoding.toBridge
    {halign : HilbertProjectionCodeAlignment}
    (h : HilbertProofLengthSoundnessForAlignedCoding halign) :
    HilbertProofLengthSoundnessBridge where
  realizes_right_conj_elim := h.realizes_aligned_right_conj_elim

theorem HilbertProofLengthSoundnessBridge.of_aligned_coding
    (halign : HilbertProjectionCodeAlignment)
    (h : HilbertProofLengthSoundnessForAlignedCoding halign) :
    HilbertProofLengthSoundnessBridge :=
  h.toBridge

abbrev HilbertAlignedProjectionSoundness : Prop :=
  HilbertProofLengthSoundnessForAlignedCoding
    hilbert_projection_code_alignment_true

theorem HilbertAlignedProjectionSoundness.toBridge
    (h : HilbertAlignedProjectionSoundness) :
    HilbertProofLengthSoundnessBridge :=
  HilbertProofLengthSoundnessForAlignedCoding.toBridge h

theorem HilbertProofLengthSoundnessBridge.toTwoStepRealization
    (h : HilbertProofLengthSoundnessBridge) :
    HilbertTwoStepProofLengthRealization where
  graft_syntax := reflection_graft_conjunction_syntax_true
  graft_syntax_true := rfl
  realizes_right_conj_elim := h.realizes_right_conj_elim

theorem HilbertTwoStepProofLengthRealization.of_two_step_overhead
    (h : HilbertRightConjunctionTwoStepOverhead) :
    HilbertTwoStepProofLengthRealization where
  graft_syntax := reflection_graft_conjunction_syntax_true
  graft_syntax_true := rfl
  realizes_right_conj_elim := h

theorem HilbertTwoStepProofLengthRealization.toTwoStepOverhead
    (h : HilbertTwoStepProofLengthRealization) :
    HilbertRightConjunctionTwoStepOverhead :=
  h.realizes_right_conj_elim

theorem hilbert_two_step_realization_iff_overhead :
    HilbertTwoStepProofLengthRealization ↔
      HilbertRightConjunctionTwoStepOverhead :=
  ⟨HilbertTwoStepProofLengthRealization.toTwoStepOverhead,
    HilbertTwoStepProofLengthRealization.of_two_step_overhead⟩

theorem hilbert_right_conjunction_constant_overhead_of_two_step
    (h : HilbertRightConjunctionTwoStepOverhead) :
    HilbertRightConjunctionConstantOverhead :=
  ⟨2, by norm_num, h⟩

-- Hilbert presentation of the right-conjunction projection.  At the present
-- abstraction level `proof_length` is still an external complexity function,
-- so this package records the exact proof-length inequality supplied by the
-- standard Hilbert transformation:
--
--   proof of A ∧ B
--   append the axiom instance (A ∧ B) -> B
--   apply modus ponens
--   obtain proof of B.
--
-- The source family is the right conjunct, `partialConsistencyCode`; the target
-- family is the conjunction graft, `sondowReflectionGraftCode`.
structure HilbertRightConjunctionEliminationPackage where
  graft_syntax : ReflectionGraftConjunctionSyntax
  right_projection_linear :
    LinearProofLengthProjection
      ProofSystem.PA ProofLengthMeasure.symbolSize
      partialConsistencyCode sondowReflectionGraftCode

structure HilbertRightConjunctionConstantEliminationPackage where
  graft_syntax : ReflectionGraftConjunctionSyntax
  right_projection_constant : PAConjunctionEliminationConstantCost

def hilbert_right_conjunction_two_step_elimination_package
    (h : HilbertRightConjunctionTwoStepOverhead) :
    HilbertRightConjunctionConstantEliminationPackage where
  graft_syntax := reflection_graft_conjunction_syntax_true
  right_projection_constant := {
    D := 2
    D_nonneg := by norm_num
    source_le_target_add := h }

def HilbertTwoStepProofLengthRealization.toConstantEliminationPackage
    (h : HilbertTwoStepProofLengthRealization) :
    HilbertRightConjunctionConstantEliminationPackage where
  graft_syntax := reflection_graft_conjunction_syntax_true
  right_projection_constant := {
    D := 2
    D_nonneg := by norm_num
    source_le_target_add := h.realizes_right_conj_elim }

def HilbertTwoStepProofLengthRealization.toEliminationPackage
    (h : HilbertTwoStepProofLengthRealization) :
    HilbertRightConjunctionEliminationPackage where
  graft_syntax := reflection_graft_conjunction_syntax_true
  right_projection_linear :=
    ConstantProofLengthProjection.toLinearProofLengthProjection
      (h.toConstantEliminationPackage).right_projection_constant

theorem HilbertTwoStepProofLengthRealization.toEliminationPackage_graft_syntax
    (h : HilbertTwoStepProofLengthRealization) :
    h.toEliminationPackage.graft_syntax =
      reflection_graft_conjunction_syntax_true :=
  rfl

def HilbertRightConjunctionConstantEliminationPackage.toEliminationPackage
    (h : HilbertRightConjunctionConstantEliminationPackage) :
    HilbertRightConjunctionEliminationPackage where
  graft_syntax := h.graft_syntax
  right_projection_linear :=
    h.right_projection_constant.toLinearProofLengthProjection

def hilbert_right_conjunction_elimination_package_of_two_step
    (h : HilbertRightConjunctionTwoStepOverhead) :
    HilbertRightConjunctionEliminationPackage :=
  (hilbert_right_conjunction_two_step_elimination_package h).toEliminationPackage

theorem exists_hilbert_right_conjunction_constant_package_of_overhead
    (hlinear : HilbertRightConjunctionConstantOverhead) :
    ∃ _ : HilbertRightConjunctionConstantEliminationPackage, True := by
  rcases hlinear with ⟨D, hD, hbound⟩
  exact ⟨{
    graft_syntax := reflection_graft_conjunction_syntax_true
    right_projection_constant := {
      D := D
      D_nonneg := hD
      source_le_target_add := hbound } }, trivial⟩

theorem partial_consistency_to_reflection_graft_projection_of_hilbert_right_conj
    (hprojection : HilbertRightConjunctionEliminationPackage) :
    PartialConsistencyToReflectionGraftLowerBoundTransfer :=
  hprojection.right_projection_linear.toStrongLowerBoundTransfer

theorem partial_consistency_to_reflection_graft_transfer_of_hilbert_two_step
    (h : HilbertRightConjunctionTwoStepOverhead) :
    PartialConsistencyToReflectionGraftLowerBoundTransfer :=
  LinearProofLengthProjection.toStrongLowerBoundTransfer
    (hilbert_right_conjunction_elimination_package_of_two_step h).right_projection_linear

def pa_conjunction_elimination_transfer_cost_of_hilbert
    (hprojection : HilbertRightConjunctionEliminationPackage) :
    PAConjunctionEliminationTransferCost where
  calculus := PAProofCalculus.hilbert
  linear_overhead := hprojection.right_projection_linear

def pa_conjunction_elimination_transfer_cost_of_hilbert_two_step
    (h : HilbertRightConjunctionTwoStepOverhead) :
    PAConjunctionEliminationTransferCost :=
  pa_conjunction_elimination_transfer_cost_of_hilbert
    (hilbert_right_conjunction_elimination_package_of_two_step h)

-- Narrow proof-calculus package for the chosen conjunction graft.  This is the
-- intended replacement for the older broad semantic projection principle on
-- the reflection-graft route: after the graft syntax is fixed as `A ∧ B`, the
-- only remaining proof-calculus work is right-conjunction elimination.
structure ConjunctionEliminationProjectionPackage where
  graft_syntax : ReflectionGraftConjunctionSyntax
  right_conj_elimination : PAConjunctionEliminationCost

structure ConjunctionEliminationTransferPackage where
  graft_syntax : ReflectionGraftConjunctionSyntax
  right_conj_elimination : PAConjunctionEliminationTransferCost

theorem partial_consistency_projection_of_right_conjunction_elimination
    (hprojection : ConjunctionEliminationProjectionPackage) :
    PartialConsistencyToReflectionGraftProjection :=
  hprojection.right_conj_elimination.linear_overhead

theorem partial_consistency_transfer_of_right_conjunction_elimination
    (hprojection : ConjunctionEliminationTransferPackage) :
    PartialConsistencyToReflectionGraftLowerBoundTransfer :=
  hprojection.right_conj_elimination.linear_overhead.toStrongLowerBoundTransfer

def conjunction_elimination_transfer_package_of_hilbert
    (hprojection : HilbertRightConjunctionEliminationPackage) :
    ConjunctionEliminationTransferPackage where
  graft_syntax := hprojection.graft_syntax
  right_conj_elimination :=
    pa_conjunction_elimination_transfer_cost_of_hilbert hprojection

def conjunction_elimination_transfer_package_of_hilbert_two_step
    (h : HilbertRightConjunctionTwoStepOverhead) :
    ConjunctionEliminationTransferPackage :=
  conjunction_elimination_transfer_package_of_hilbert
    (hilbert_right_conjunction_elimination_package_of_two_step h)

def conjunction_elimination_transfer_package_of_hilbert_realization
    (h : HilbertTwoStepProofLengthRealization) :
    ConjunctionEliminationTransferPackage :=
  conjunction_elimination_transfer_package_of_hilbert h.toEliminationPackage

def MiniHilbert.HilbertRightConjElimFormulaCodeRealization.toConstantEliminationPackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : MiniHilbert.HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    HilbertRightConjunctionConstantEliminationPackage :=
  hilbert_right_conjunction_two_step_elimination_package h.toTwoStepOverhead

def MiniHilbert.HilbertRightConjElimFormulaCodeRealization.toEliminationPackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : MiniHilbert.HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    HilbertRightConjunctionEliminationPackage :=
  h.toConstantEliminationPackage.toEliminationPackage

def MiniHilbert.HilbertRightConjElimFormulaCodeRealization.toConjunctionTransferPackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : MiniHilbert.HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    ConjunctionEliminationTransferPackage :=
  conjunction_elimination_transfer_package_of_hilbert h.toEliminationPackage

theorem MiniHilbert.HilbertRightConjElimFormulaCodeRealization.toLowerBoundTransfer
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : MiniHilbert.HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    PartialConsistencyToReflectionGraftLowerBoundTransfer :=
  partial_consistency_transfer_of_right_conjunction_elimination
    h.toConjunctionTransferPackage

theorem reflection_graft_conjunction_projection_bridge_of_projection
    (hprojection : PartialConsistencyToReflectionGraftProjection) :
    ReflectionGraftConjunctionProjectionBridge where
  graft_syntax := reflection_graft_conjunction_syntax_true
  projection := hprojection

theorem reflection_graft_conjunction_projection_bridge_of_conjunction_elimination
    (hprojection : ConjunctionEliminationProjectionPackage) :
    ReflectionGraftConjunctionProjectionBridge where
  graft_syntax := hprojection.graft_syntax
  projection := partial_consistency_projection_of_right_conjunction_elimination
    hprojection

theorem irrational_of_buss_pudlak_conjunction_projection_bridge
    (hfwd : SondowForwardInputs)
    (hver : PAStandardVerificationTheorem)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (hbridge : ReflectionGraftConjunctionProjectionBridge) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_conjunction_graft
    hfwd hver hbuss hbridge.projection

theorem irrational_of_buss_pudlak_conjunction_elimination
    (hfwd : SondowForwardInputs)
    (hver : PAStandardVerificationTheorem)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (hprojection : ConjunctionEliminationProjectionPackage) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_conjunction_projection_bridge
    hfwd hver hbuss
    (reflection_graft_conjunction_projection_bridge_of_conjunction_elimination
      hprojection)

theorem irrational_of_buss_pudlak_conjunction_elimination_transfer
    (hfwd : SondowForwardInputs)
    (hver : PAStandardVerificationTheorem)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (hprojection : ConjunctionEliminationTransferPackage) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_conjunction_transfer
    hfwd hver hbuss
    (partial_consistency_transfer_of_right_conjunction_elimination hprojection)

theorem irrational_of_buss_pudlak_conjunction_elimination_transfer_of_trace_soundness
    (hfwd : SondowForwardInputs)
    (hsound : S21VerifierTraceSoundness sondowReflectionGraftCode)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (hprojection : ConjunctionEliminationTransferPackage) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_conjunction_transfer_of_trace_soundness
    hfwd hsound hembed hbuss
    (partial_consistency_transfer_of_right_conjunction_elimination hprojection)

theorem irrational_of_buss_pudlak_conjunction_elimination_transfer_of_concrete_verification
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (hprojection : ConjunctionEliminationTransferPackage) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_conjunction_transfer_of_concrete_verification
    hfwd hver hbuss
    (partial_consistency_transfer_of_right_conjunction_elimination hprojection)

theorem irrational_of_buss_pudlak_conjunction_elimination_transfer_of_rescaled_package
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hbuss : BussPudlakRescaledPartialConsistencyPackage)
    (hprojection : ConjunctionEliminationTransferPackage) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_conjunction_elimination_transfer_of_concrete_verification
    hfwd hver hbuss.toBussPudlakPartialConsistencyPackage hprojection

theorem irrational_of_buss_pudlak_conjunction_elimination_transfer_of_time_constructible_rescaling
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (htruth : PartialConsistencyPayloadTruth)
    (hreading : PartialConsistencyPayloadIntendedReading)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (hprojection : ConjunctionEliminationTransferPackage) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_conjunction_elimination_transfer_of_rescaled_package
    hfwd hver
    (BussPudlakRescaledPartialConsistencyPackage.of_time_constructible_rescaling
      htruth hreading hrescale)
    hprojection

theorem irrational_of_time_rescaling_and_hilbert_two_step_transfer
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (htruth : PartialConsistencyPayloadTruth)
    (hreading : PartialConsistencyPayloadIntendedReading)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (htwo : HilbertRightConjunctionTwoStepOverhead) :
    ¬ (is_rational euler_mascheroni) := by
  exact
    irrational_of_buss_pudlak_conjunction_elimination_transfer_of_time_constructible_rescaling
      hfwd hver htruth hreading hrescale
      (conjunction_elimination_transfer_package_of_hilbert_two_step htwo)

theorem irrational_of_time_rescaling_and_hilbert_realization
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (htruth : PartialConsistencyPayloadTruth)
    (hreading : PartialConsistencyPayloadIntendedReading)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (hrealize : HilbertTwoStepProofLengthRealization) :
    ¬ (is_rational euler_mascheroni) := by
  exact
    irrational_of_buss_pudlak_conjunction_elimination_transfer_of_time_constructible_rescaling
      hfwd hver htruth hreading hrescale
      (conjunction_elimination_transfer_package_of_hilbert_realization hrealize)

theorem irrational_of_time_rescaling_and_hilbert_soundness_bridge
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (htruth : PartialConsistencyPayloadTruth)
    (hreading : PartialConsistencyPayloadIntendedReading)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (hsound : HilbertProofLengthSoundnessBridge) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_time_rescaling_and_hilbert_realization
    hfwd hver htruth hreading hrescale hsound.toTwoStepRealization

theorem irrational_of_time_rescaling_and_formula_code_realization
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (htruth : PartialConsistencyPayloadTruth)
    (hreading : PartialConsistencyPayloadIntendedReading)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (hrealize :
      MiniHilbert.HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_time_rescaling_and_hilbert_soundness_bridge
    hfwd hver htruth hreading hrescale hrealize.toBridge

theorem irrational_of_time_rescaling_and_default_formula_code_realization
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (htruth : PartialConsistencyPayloadTruth)
    (hreading : PartialConsistencyPayloadIntendedReading)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (hrealize :
      MiniHilbert.DefaultHilbertRightConjElimFormulaCodeRealization Ax A B) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_time_rescaling_and_formula_code_realization
    hfwd hver htruth hreading hrescale hrealize

theorem irrational_of_buss_pudlak_conjunction_transfer_of_formula_code_realization
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (hrealize :
      MiniHilbert.HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_conjunction_elimination_transfer_of_concrete_verification
    hfwd hver hbuss hrealize.toConjunctionTransferPackage

theorem irrational_of_buss_pudlak_rescaled_formula_code_realization
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hbuss : BussPudlakRescaledPartialConsistencyPackage)
    (hrealize :
      MiniHilbert.HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_conjunction_elimination_transfer_of_rescaled_package
    hfwd hver hbuss hrealize.toConjunctionTransferPackage

theorem irrational_of_buss_pudlak_rescaled_default_formula_code_realization
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hbuss : BussPudlakRescaledPartialConsistencyPackage)
    (hrealize :
      MiniHilbert.DefaultHilbertRightConjElimFormulaCodeRealization Ax A B) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_rescaled_formula_code_realization
    hfwd hver hbuss hrealize

theorem irrational_of_time_rescaling_and_formula_code_transfer
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (htruth : PartialConsistencyPayloadTruth)
    (hreading : PartialConsistencyPayloadIntendedReading)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (hrealize :
      MiniHilbert.HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_conjunction_elimination_transfer_of_time_constructible_rescaling
    hfwd hver htruth hreading hrescale hrealize.toConjunctionTransferPackage

theorem irrational_of_time_rescaling_and_default_formula_code_transfer
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (htruth : PartialConsistencyPayloadTruth)
    (hreading : PartialConsistencyPayloadIntendedReading)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (hrealize :
      MiniHilbert.DefaultHilbertRightConjElimFormulaCodeRealization Ax A B) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_time_rescaling_and_formula_code_transfer
    hfwd hver htruth hreading hrescale hrealize

theorem irrational_of_buss_pudlak_hilbert_conjunction_elimination
    (hfwd : SondowForwardInputs)
    (hver : PAStandardVerificationTheorem)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (hprojection : HilbertRightConjunctionEliminationPackage) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_conjunction_elimination_transfer
    hfwd hver hbuss
    (conjunction_elimination_transfer_package_of_hilbert hprojection)

theorem irrational_of_buss_pudlak_hilbert_conjunction_elimination_of_trace_soundness
    (hfwd : SondowForwardInputs)
    (hsound : S21VerifierTraceSoundness sondowReflectionGraftCode)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (hprojection : HilbertRightConjunctionEliminationPackage) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_conjunction_elimination_transfer_of_trace_soundness
    hfwd hsound hembed hbuss
    (conjunction_elimination_transfer_package_of_hilbert hprojection)

theorem irrational_of_buss_pudlak_hilbert_conjunction_elimination_of_concrete_verification
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (hprojection : HilbertRightConjunctionEliminationPackage) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_conjunction_elimination_transfer_of_concrete_verification
    hfwd hver hbuss
    (conjunction_elimination_transfer_package_of_hilbert hprojection)

theorem irrational_of_buss_pudlak_hilbert_conjunction_elimination_of_rescaled_package
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hbuss : BussPudlakRescaledPartialConsistencyPackage)
    (hprojection : HilbertRightConjunctionEliminationPackage) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_hilbert_conjunction_elimination_of_concrete_verification
    hfwd hver hbuss.toBussPudlakPartialConsistencyPackage hprojection

theorem irrational_of_buss_pudlak_hilbert_conjunction_elimination_of_time_constructible_rescaling
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (htruth : PartialConsistencyPayloadTruth)
    (hreading : PartialConsistencyPayloadIntendedReading)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (hprojection : HilbertRightConjunctionEliminationPackage) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_hilbert_conjunction_elimination_of_rescaled_package
    hfwd hver
    (BussPudlakRescaledPartialConsistencyPackage.of_time_constructible_rescaling
      htruth hreading hrescale)
    hprojection

theorem irrational_of_time_rescaling_and_hilbert_constant_elim
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (htruth : PartialConsistencyPayloadTruth)
    (hreading : PartialConsistencyPayloadIntendedReading)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (hprojection : HilbertRightConjunctionConstantEliminationPackage) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_hilbert_conjunction_elimination_of_time_constructible_rescaling
    hfwd hver htruth hreading hrescale hprojection.toEliminationPackage

theorem irrational_of_buss_pudlak_hilbert_formula_code_realization
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (hrealize :
      MiniHilbert.HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_hilbert_conjunction_elimination_of_concrete_verification
    hfwd hver hbuss hrealize.toEliminationPackage

theorem irrational_of_time_rescaling_and_formula_code_constant_elim
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (htruth : PartialConsistencyPayloadTruth)
    (hreading : PartialConsistencyPayloadIntendedReading)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (hrealize :
      MiniHilbert.HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_time_rescaling_and_hilbert_constant_elim
    hfwd hver htruth hreading hrescale hrealize.toConstantEliminationPackage

theorem irrational_of_time_rescaling_and_formula_code_linear_overhead
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (htruth : PartialConsistencyPayloadTruth)
    (hreading : PartialConsistencyPayloadIntendedReading)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (hrealize :
      MiniHilbert.HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_hilbert_conjunction_elimination_of_time_constructible_rescaling
    hfwd hver htruth hreading hrescale hrealize.toEliminationPackage

theorem irrational_of_buss_pudlak_hilbert_linear_overhead
    (hfwd : SondowForwardInputs)
    (hver : PAStandardVerificationTheorem)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (hlinear : HilbertRightConjunctionLinearOverhead) :
    ¬ (is_rational euler_mascheroni) := by
  rcases hlinear with ⟨C, D, hC, hD, hbound⟩
  exact irrational_of_buss_pudlak_hilbert_conjunction_elimination
    hfwd hver hbuss
    { graft_syntax := reflection_graft_conjunction_syntax_true
      right_projection_linear := {
        C := C
        D := D
        C_pos := hC
        D_nonneg := hD
        source_le_linear_target := hbound } }

theorem irrational_of_buss_pudlak_hilbert_linear_overhead_of_trace_soundness
    (hfwd : SondowForwardInputs)
    (hsound : S21VerifierTraceSoundness sondowReflectionGraftCode)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (hlinear : HilbertRightConjunctionLinearOverhead) :
    ¬ (is_rational euler_mascheroni) := by
  rcases hlinear with ⟨C, D, hC, hD, hbound⟩
  exact irrational_of_buss_pudlak_hilbert_conjunction_elimination_of_trace_soundness
    hfwd hsound hembed hbuss
    { graft_syntax := reflection_graft_conjunction_syntax_true
      right_projection_linear := {
        C := C
        D := D
        C_pos := hC
        D_nonneg := hD
        source_le_linear_target := hbound } }

theorem irrational_of_buss_pudlak_hilbert_linear_overhead_of_concrete_verification
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (hlinear : HilbertRightConjunctionLinearOverhead) :
    ¬ (is_rational euler_mascheroni) := by
  rcases hlinear with ⟨C, D, hC, hD, hbound⟩
  exact irrational_of_buss_pudlak_hilbert_conjunction_elimination_of_concrete_verification
    hfwd hver hbuss
    { graft_syntax := reflection_graft_conjunction_syntax_true
      right_projection_linear := {
        C := C
        D := D
        C_pos := hC
        D_nonneg := hD
        source_le_linear_target := hbound } }

theorem irrational_of_buss_pudlak_hilbert_linear_overhead_of_rescaled_package
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hbuss : BussPudlakRescaledPartialConsistencyPackage)
    (hlinear : HilbertRightConjunctionLinearOverhead) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_hilbert_linear_overhead_of_concrete_verification
    hfwd hver hbuss.toBussPudlakPartialConsistencyPackage hlinear

theorem irrational_of_buss_pudlak_hilbert_linear_overhead_of_time_constructible_rescaling
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (htruth : PartialConsistencyPayloadTruth)
    (hreading : PartialConsistencyPayloadIntendedReading)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (hlinear : HilbertRightConjunctionLinearOverhead) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_hilbert_linear_overhead_of_rescaled_package
    hfwd hver
    (BussPudlakRescaledPartialConsistencyPackage.of_time_constructible_rescaling
      htruth hreading hrescale)
    hlinear

theorem irrational_of_buss_pudlak_hilbert_constant_overhead_of_time_constructible_rescaling
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (htruth : PartialConsistencyPayloadTruth)
    (hreading : PartialConsistencyPayloadIntendedReading)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (hconstant : HilbertRightConjunctionConstantOverhead) :
    ¬ (is_rational euler_mascheroni) := by
  rcases exists_hilbert_right_conjunction_constant_package_of_overhead
    hconstant with ⟨hprojection, _⟩
  exact irrational_of_time_rescaling_and_hilbert_constant_elim
      hfwd hver htruth hreading hrescale
      hprojection

theorem irrational_of_buss_pudlak_hilbert_two_step_overhead_of_time_rescaling
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (htruth : PartialConsistencyPayloadTruth)
    (hreading : PartialConsistencyPayloadIntendedReading)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (htwo : HilbertRightConjunctionTwoStepOverhead) :
    ¬ (is_rational euler_mascheroni) := by
  exact
    irrational_of_buss_pudlak_hilbert_constant_overhead_of_time_constructible_rescaling
      hfwd hver htruth hreading hrescale
      (hilbert_right_conjunction_constant_overhead_of_two_step htwo)
