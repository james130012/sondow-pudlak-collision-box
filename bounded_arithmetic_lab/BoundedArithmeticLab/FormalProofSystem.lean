/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.S21ProofSystem

/-!
# Object-level proof-system interfaces

This module is the next layer below the abstract proof-length boxes.  It records
actual formula and proof-object types, while still leaving the heavy Buss `S21`
syntax and PA syntax to a later concrete instantiation.
-/

namespace BoundedArithmeticLab

universe u

structure FormalProofSystem where
  system : ProofSystem
  measure : ProofLengthMeasure
  Formula : Type u
  Proof : Type u
  formulaCode : Formula → FormulaCode
  targetFormula : ℕ → Formula
  proofConclusion : Proof → Formula
  proofSize : Proof → ℕ
  proves : Proof → Formula → Prop
  proves_conclusion : ∀ p : Proof, proves p (proofConclusion p)
  length : ℕ → ℝ
  proof_length_le_size :
    ∀ n : ℕ, ∀ p : Proof,
      proves p (targetFormula n) → length n ≤ (proofSize p : ℝ)

def FormalProofSystem.box (sys : FormalProofSystem.{u}) :
    AbstractProofLengthBox where
  system := sys.system
  measure := sys.measure
  formula := fun n => sys.formulaCode (sys.targetFormula n)
  length := sys.length

def FormalProofSystem.toBoxModel (sys : FormalProofSystem.{u}) :
    ProofSystemBoxModel.{u} sys.box where
  Proof := sys.Proof
  proves := fun p n => sys.proves p (sys.targetFormula n)
  size := sys.proofSize
  proof_length_le_size := by
    intro n p hp
    exact sys.proof_length_le_size n p hp

structure S21ProofSystemFormalization where
  core : FormalProofSystem.{u}
  system_eq : core.system = ProofSystem.S21
  measure_eq_symbolSize : core.measure = ProofLengthMeasure.symbolSize

def S21ProofSystemFormalization.box
    (sys : S21ProofSystemFormalization.{u}) :
    AbstractProofLengthBox :=
  sys.core.box

def S21ProofSystemFormalization.toBoxModel
    (sys : S21ProofSystemFormalization.{u}) :
    ProofSystemBoxModel.{u} sys.box :=
  sys.core.toBoxModel

@[simp] theorem S21ProofSystemFormalization.box_system
    (sys : S21ProofSystemFormalization.{u}) :
    sys.box.system = ProofSystem.S21 :=
  sys.system_eq

@[simp] theorem S21ProofSystemFormalization.box_measure
    (sys : S21ProofSystemFormalization.{u}) :
    sys.box.measure = ProofLengthMeasure.symbolSize :=
  sys.measure_eq_symbolSize

structure PAProofSystemFormalization where
  core : FormalProofSystem.{u}
  system_eq : core.system = ProofSystem.PA
  measure_eq_symbolSize : core.measure = ProofLengthMeasure.symbolSize

def PAProofSystemFormalization.box
    (sys : PAProofSystemFormalization.{u}) :
    AbstractProofLengthBox :=
  sys.core.box

def PAProofSystemFormalization.toBoxModel
    (sys : PAProofSystemFormalization.{u}) :
    ProofSystemBoxModel.{u} sys.box :=
  sys.core.toBoxModel

@[simp] theorem PAProofSystemFormalization.box_system
    (sys : PAProofSystemFormalization.{u}) :
    sys.box.system = ProofSystem.PA :=
  sys.system_eq

@[simp] theorem PAProofSystemFormalization.box_measure
    (sys : PAProofSystemFormalization.{u}) :
    sys.box.measure = ProofLengthMeasure.symbolSize :=
  sys.measure_eq_symbolSize

end BoundedArithmeticLab
