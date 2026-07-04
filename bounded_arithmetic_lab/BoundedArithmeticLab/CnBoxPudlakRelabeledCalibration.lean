/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakCanonicalCalibration

/-!
# Relabeled Pudlak calibration for finite-consistency Cn boxes

The exact-code route requires `externalPudlakCode` to equal
`partialConsistencyCode`, but those constructors are intentionally distinct in
the current interface.  This module records that obstruction and gives the
auditable replacement route: a semantic formula-relabeling certificate plus
length equality is enough to transport the lower bound.
-/

namespace BoundedArithmeticLab

theorem lowerBoundTransfer_of_length_eq
    {source target : AbstractProofLengthBox}
    (length_eq : ∀ n : Nat, source.length n = target.length n) :
    LowerBoundTransfer source target where
  transfer := by
    intro _f _hf hlower
    refine ⟨?_⟩
    intro g hg N
    rcases hlower.lower_bound g hg N with ⟨n, hn, hgt⟩
    exact ⟨n, hn, by simpa [length_eq n] using hgt⟩

namespace BoundedProofPredicate

theorem externalPudlakCode_ne_partialConsistencyCode
    (m n : Nat) :
    externalPudlakCode m ≠ partialConsistencyCode n := by
  intro h
  cases h

theorem rescaledExternalPudlakCode_ne_partialConsistencyCode
    (ρ : Nat → Nat) (n : Nat) :
    rescaledExternalPudlakCode ρ n ≠ partialConsistencyCode n := by
  intro h
  cases h

theorem not_canonicalExternalPudlakCalibration
    (lower_source : BussPudlakTheorem5PALowerBoundSource) :
    ¬ CanonicalExternalPudlakCalibration lower_source := by
  intro h
  exact rescaledExternalPudlakCode_ne_partialConsistencyCode
    lower_source.conditions.scale_data.scale 0 (h.formula_code_eq 0)

structure SemanticFormulaRelabeling
    (source target : Nat → FormulaCode) where
  relabels_same_formula_statement : Prop
  relabels_same_formula : relabels_same_formula_statement

structure RelabeledPudlakLowerCalibration
    (target : Nat → BAFormula) (code : BAFormula → FormulaCode) where
  lower_source : BussPudlakTheorem5PALowerBoundSource
  relabeling :
    SemanticFormulaRelabeling lower_source.box.formula
      (concretePAFormalization target code).box.formula
  length_eq :
    ∀ n : Nat,
      lower_source.box.length n =
        (concretePAFormalization target code).box.length n

def RelabeledPudlakLowerCalibration.toLowerForPA
    {target : Nat → BAFormula} {code : BAFormula → FormulaCode}
    (calibration : RelabeledPudlakLowerCalibration target code) :
    ConcreteBussPudlakLowerForPA target code where
  lower_source := calibration.lower_source
  source_to_concrete_pa :=
    lowerBoundTransfer_of_length_eq calibration.length_eq

def RelabeledPudlakLowerCalibration.toConcretePALowerBound
    {target : Nat → BAFormula} {code : BAFormula → FormulaCode}
    (calibration : RelabeledPudlakLowerCalibration target code) :
    EventualLowerBound (concretePAFormalization target code).box :=
  calibration.toLowerForPA.toLowerBound

structure CanonicalRelabeledPudlakCalibration
    (lower_source : BussPudlakTheorem5PALowerBoundSource) where
  relabeling :
    SemanticFormulaRelabeling lower_source.box.formula
      (concretePAFormalization
        canonicalPudlakTargetFamilySpec.target
        canonicalPudlakTargetFamilySpec.code).box.formula
  length_eq :
    ∀ n : Nat,
      lower_source.pa_length n =
        semanticBAProofLength PAAxiom finiteConsistencyFormula n

noncomputable def CanonicalRelabeledPudlakCalibration.toLowerCalibration
    {lower_source : BussPudlakTheorem5PALowerBoundSource}
    (calibration : CanonicalRelabeledPudlakCalibration lower_source) :
    RelabeledPudlakLowerCalibration
      canonicalPudlakTargetFamilySpec.target
      canonicalPudlakTargetFamilySpec.code where
  lower_source := lower_source
  relabeling := calibration.relabeling
  length_eq := by
    intro n
    change lower_source.pa_length n =
      semanticBAProofLength PAAxiom canonicalPudlakTargetFamilySpec.target n
    simpa [canonicalPudlakTargetFamilySpec,
      canonicalFiniteConsistencyGenerator]
      using calibration.length_eq n

noncomputable def CanonicalRelabeledPudlakCalibration.toConcretePALowerBound
    {lower_source : BussPudlakTheorem5PALowerBoundSource}
    (calibration : CanonicalRelabeledPudlakCalibration lower_source) :
    EventualLowerBound
      (concretePAFormalization
        canonicalPudlakTargetFamilySpec.target
        canonicalPudlakTargetFamilySpec.code).box :=
  calibration.toLowerCalibration.toConcretePALowerBound

end BoundedProofPredicate
end BoundedArithmeticLab
