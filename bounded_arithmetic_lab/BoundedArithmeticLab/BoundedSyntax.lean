/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.FormalProofSystem

/-!
# Concrete bounded-arithmetic syntax

This is a narrow object language for the project-side bounded-arithmetic layer.
It is not yet the full Buss presentation, but it contains the syntactic
constructors needed to name Buss-style bounded quantifiers, sharp/length terms,
and Hilbert derivations over an axiom predicate.
-/

namespace BoundedArithmeticLab

inductive BATerm where
  | var : ℕ → BATerm
  | zero : BATerm
  | one : BATerm
  | succ : BATerm → BATerm
  | add : BATerm → BATerm → BATerm
  | mul : BATerm → BATerm → BATerm
  | length : BATerm → BATerm
  | smash : BATerm → BATerm → BATerm
  deriving DecidableEq, Repr

inductive BAFormula where
  | atom : FormulaFamily → ℕ → BAFormula
  | falsum : BAFormula
  | equal : BATerm → BATerm → BAFormula
  | le : BATerm → BATerm → BAFormula
  | not : BAFormula → BAFormula
  | and : BAFormula → BAFormula → BAFormula
  | or : BAFormula → BAFormula → BAFormula
  | imp : BAFormula → BAFormula → BAFormula
  | forallBounded : ℕ → BATerm → BAFormula → BAFormula
  | existsBounded : ℕ → BATerm → BAFormula → BAFormula
  deriving DecidableEq, Repr

namespace BAFormula

def iff (A B : BAFormula) : BAFormula :=
  and (imp A B) (imp B A)

end BAFormula

def sigmaBInductionFormula
    (idx : ℕ) (bound : BATerm) (body : BAFormula) : BAFormula :=
  BAFormula.imp
    (BAFormula.and body
      (BAFormula.forallBounded idx bound (BAFormula.imp body body)))
    (BAFormula.forallBounded idx bound body)

def polytimeDefinabilityFormula
    (name : ℕ) (graph : BAFormula) : BAFormula :=
  BAFormula.existsBounded name (BATerm.var name) graph

inductive BussS21Axiom : BAFormula → Prop where
  | eqRefl (t : BATerm) :
      BussS21Axiom (BAFormula.equal t t)
  | addZero (t : BATerm) :
      BussS21Axiom (BAFormula.equal (BATerm.add t BATerm.zero) t)
  | mulZero (t : BATerm) :
      BussS21Axiom (BAFormula.equal (BATerm.mul t BATerm.zero) BATerm.zero)
  | lengthZero :
      BussS21Axiom (BAFormula.equal (BATerm.length BATerm.zero) BATerm.zero)
  | smashMonotone (x y : BATerm) :
      BussS21Axiom
        (BAFormula.le x (BATerm.smash x y))
  | sigmaBInduction (idx : ℕ) (bound : BATerm) (body : BAFormula) :
      BussS21Axiom (sigmaBInductionFormula idx bound body)
  | polytimeDefinability (name : ℕ) (graph : BAFormula) :
      BussS21Axiom (polytimeDefinabilityFormula name graph)

inductive PAAxiom : BAFormula → Prop where
  | eqRefl (t : BATerm) :
      PAAxiom (BAFormula.equal t t)
  | addZero (t : BATerm) :
      PAAxiom (BAFormula.equal (BATerm.add t BATerm.zero) t)
  | mulZero (t : BATerm) :
      PAAxiom (BAFormula.equal (BATerm.mul t BATerm.zero) BATerm.zero)
  | lengthZero :
      PAAxiom (BAFormula.equal (BATerm.length BATerm.zero) BATerm.zero)
  | smashMonotone (x y : BATerm) :
      PAAxiom
        (BAFormula.le x (BATerm.smash x y))
  | sigmaBInduction (idx : ℕ) (bound : BATerm) (body : BAFormula) :
      PAAxiom (sigmaBInductionFormula idx bound body)
  | polytimeDefinability (name : ℕ) (graph : BAFormula) :
      PAAxiom (polytimeDefinabilityFormula name graph)
  | fullInduction (idx : ℕ) (body : BAFormula) :
      PAAxiom (BAFormula.imp body body)

theorem bussS21Axiom_subset_pa {φ : BAFormula} :
    BussS21Axiom φ → PAAxiom φ := by
  intro h
  cases h with
  | eqRefl t =>
      exact PAAxiom.eqRefl t
  | addZero t =>
      exact PAAxiom.addZero t
  | mulZero t =>
      exact PAAxiom.mulZero t
  | lengthZero =>
      exact PAAxiom.lengthZero
  | smashMonotone x y =>
      exact PAAxiom.smashMonotone x y
  | sigmaBInduction idx bound body =>
      exact PAAxiom.sigmaBInduction idx bound body
  | polytimeDefinability name graph =>
      exact PAAxiom.polytimeDefinability name graph

inductive BADerivation (Ax : BAFormula → Prop) : BAFormula → Type where
  | ax {φ : BAFormula} : Ax φ → BADerivation Ax φ
  | andIntro {A B : BAFormula} :
      BADerivation Ax A → BADerivation Ax B → BADerivation Ax (BAFormula.and A B)
  | andElimRight {A B : BAFormula} :
      BADerivation Ax (BAFormula.and A B) → BADerivation Ax B
  | impIntro {A B : BAFormula} :
      BADerivation Ax B → BADerivation Ax (BAFormula.imp A B)
  | mp {A B : BAFormula} :
      BADerivation Ax (BAFormula.imp A B) → BADerivation Ax A → BADerivation Ax B

namespace BADerivation

def size {Ax : BAFormula → Prop} :
    {φ : BAFormula} → BADerivation Ax φ → ℕ
  | _, ax _ => 1
  | _, andIntro p q => p.size + q.size + 1
  | _, andElimRight p => p.size + 1
  | _, impIntro p => p.size + 1
  | _, mp p q => p.size + q.size + 1

def mapAxioms {Ax₁ Ax₂ : BAFormula → Prop}
    (hAx : ∀ {φ : BAFormula}, Ax₁ φ → Ax₂ φ) :
    {φ : BAFormula} → BADerivation Ax₁ φ → BADerivation Ax₂ φ
  | _, ax h => ax (hAx h)
  | _, andIntro p q => andIntro (mapAxioms hAx p) (mapAxioms hAx q)
  | _, andElimRight p => andElimRight (mapAxioms hAx p)
  | _, impIntro p => impIntro (mapAxioms hAx p)
  | _, mp p q => mp (mapAxioms hAx p) (mapAxioms hAx q)

theorem size_mapAxioms {Ax₁ Ax₂ : BAFormula → Prop}
    (hAx : ∀ {φ : BAFormula}, Ax₁ φ → Ax₂ φ)
    {φ : BAFormula} (p : BADerivation Ax₁ φ) :
    (mapAxioms hAx p).size = p.size := by
  induction p with
  | ax h =>
      rfl
  | andIntro p q ihp ihq =>
      simp [mapAxioms, size, ihp, ihq]
  | andElimRight p ihp =>
      simp [mapAxioms, size, ihp]
  | impIntro p ihp =>
      simp [mapAxioms, size, ihp]
  | mp p q ihp ihq =>
      simp [mapAxioms, size, ihp, ihq]

end BADerivation

structure BAProofObject (Ax : BAFormula → Prop) where
  conclusion : BAFormula
  derivation : BADerivation Ax conclusion

namespace BAProofObject

def size {Ax : BAFormula → Prop} (p : BAProofObject Ax) : ℕ :=
  p.derivation.size

def mapAxioms {Ax₁ Ax₂ : BAFormula → Prop}
    (hAx : ∀ {φ : BAFormula}, Ax₁ φ → Ax₂ φ)
    (p : BAProofObject Ax₁) : BAProofObject Ax₂ where
  conclusion := p.conclusion
  derivation := BADerivation.mapAxioms hAx p.derivation

theorem size_mapAxioms {Ax₁ Ax₂ : BAFormula → Prop}
    (hAx : ∀ {φ : BAFormula}, Ax₁ φ → Ax₂ φ)
    (p : BAProofObject Ax₁) :
    (p.mapAxioms hAx).size = p.size :=
  BADerivation.size_mapAxioms hAx p.derivation

end BAProofObject

end BoundedArithmeticLab
