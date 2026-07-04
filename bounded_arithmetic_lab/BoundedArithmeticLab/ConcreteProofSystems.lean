/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.SemanticProofLength
import BoundedArithmeticLab.ProofObjectSimulation

/-!
# Concrete S21 and PA proof-system instances

This module instantiates the abstract proof-system interfaces with the narrow
bounded-arithmetic syntax and Hilbert derivations from `BoundedSyntax`.
-/

namespace BoundedArithmeticLab

def baFormulaCodeOfFamily
    (family : FormulaFamily) (indexOf : BAFormula → ℕ) (φ : BAFormula) :
    FormulaCode :=
  { family := family, index := indexOf φ }

noncomputable def boundedArithmeticFormalProofSystem
    (system : ProofSystem) (Ax : BAFormula → Prop)
    (target : ℕ → BAFormula) (code : BAFormula → FormulaCode) :
    FormalProofSystem where
  system := system
  measure := ProofLengthMeasure.symbolSize
  Formula := BAFormula
  Proof := BAProofObject Ax
  formulaCode := code
  targetFormula := target
  proofConclusion := fun p => p.conclusion
  proofSize := fun p => p.size
  proves := fun p φ => p.conclusion = φ
  proves_conclusion := by
    intro p
    rfl
  length := semanticBAProofLength Ax target
  proof_length_le_size := by
    intro n p hp
    exact semanticBAProofLength_le_size Ax target p hp

noncomputable def concreteS21Formalization
    (target : ℕ → BAFormula) (code : BAFormula → FormulaCode) :
    S21ProofSystemFormalization where
  core :=
    boundedArithmeticFormalProofSystem
      ProofSystem.S21 BussS21Axiom target code
  system_eq := rfl
  measure_eq_symbolSize := rfl

noncomputable def concretePAFormalization
    (target : ℕ → BAFormula) (code : BAFormula → FormulaCode) :
    PAProofSystemFormalization where
  core :=
    boundedArithmeticFormalProofSystem
      ProofSystem.PA PAAxiom target code
  system_eq := rfl
  measure_eq_symbolSize := rfl

def s21ProofObjectToPA
    {target : ℕ → BAFormula} {code : BAFormula → FormulaCode}
    (p : (concreteS21Formalization target code).toBoxModel.Proof) :
    (concretePAFormalization target code).toBoxModel.Proof :=
  p.mapAxioms bussS21Axiom_subset_pa

theorem s21ProofObjectToPA_size
    {target : ℕ → BAFormula} {code : BAFormula → FormulaCode}
    (p : (concreteS21Formalization target code).toBoxModel.Proof) :
    ((s21ProofObjectToPA p).size : ℝ) ≤ 1 * (p.size : ℝ) + 0 := by
  have hsize := BAProofObject.size_mapAxioms bussS21Axiom_subset_pa p
  dsimp [s21ProofObjectToPA]
  rw [hsize]
  simp

noncomputable def concreteS21ToPALinearObjectSimulation
    (target : ℕ → BAFormula) (code : BAFormula → FormulaCode) :
    S21ToPAFormalProofObjectSimulation
      (concreteS21Formalization target code)
      (concretePAFormalization target code) where
  same_formula := by
    intro n
    rfl
  C := 1
  D := 0
  C_nonneg := zero_le_one
  D_nonneg := le_rfl
  mapProof := s21ProofObjectToPA
  map_proves := by
    intro n p hp
    exact hp
  map_size_le := by
    intro p
    exact s21ProofObjectToPA_size p

theorem concreteS21ToPALinearObjectSimulation_semantic_length_le
    (target : ℕ → BAFormula) (code : BAFormula → FormulaCode)
    {n : ℕ}
    (hnonempty :
      ∃ p : BAProofObject BussS21Axiom, p.conclusion = target n) :
    (concretePAFormalization target code).box.length n ≤
      (concreteS21ToPALinearObjectSimulation target code).C *
        (concreteS21Formalization target code).box.length n +
        (concreteS21ToPALinearObjectSimulation target code).D := by
  have hsemantic :=
    semanticBAProofLength_pa_le_bussS21 target hnonempty
  change
    semanticBAProofLength PAAxiom target n ≤
      (1 : ℝ) * semanticBAProofLength BussS21Axiom target n + 0
  simpa using hsemantic

end BoundedArithmeticLab
