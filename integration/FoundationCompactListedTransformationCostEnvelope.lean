import integration.FoundationCompactSyntaxNegationTrace
import integration.FoundationCompactSyntaxTransformationTrace

/-!
# A uniform local envelope for syntax-transformation traces

The concrete listed checker uses negation, shift, free-variable elimination,
list shift, and one-variable substitution.  This module places all five exact
execution traces under one fixed eighth-degree polynomial in the honest local
input weight.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedTransformationCostEnvelope

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactVerifierFormulaListChecks
open FoundationCompactSyntaxNegationTrace
open FoundationCompactSyntaxTransformationTraceCore
open FoundationCompactSyntaxTransformationTrace

def listedSyntaxTransformationCostEnvelope (weight : Nat) : Nat :=
  1024 * (weight + 1) ^ 8

theorem listedSyntaxTransformationCostEnvelope_mono
    {left right : Nat} (h : left <= right) :
    listedSyntaxTransformationCostEnvelope left <=
      listedSyntaxTransformationCostEnvelope right := by
  unfold listedSyntaxTransformationCostEnvelope
  exact Nat.mul_le_mul_left 1024
    (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 8)

theorem coefficient_power_le_transformationEnvelope
    (weight coefficient exponent : Nat)
    (hcoefficient : coefficient <= 1024)
    (hexponent : exponent <= 8) :
    coefficient * (weight + 1) ^ exponent <=
      listedSyntaxTransformationCostEnvelope weight := by
  have hpower :
      (weight + 1) ^ exponent <= (weight + 1) ^ 8 :=
    Nat.pow_le_pow_right (Nat.succ_pos weight) hexponent
  unfold listedSyntaxTransformationCostEnvelope
  exact Nat.mul_le_mul hcoefficient hpower

theorem binaryFormulaNegTrace_cost_le_envelope
    {arity weight : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity)
    (hformula : (binaryFormulaCode formula).length <= weight) :
    (binaryFormulaNegTrace formula).2 <=
      listedSyntaxTransformationCostEnvelope weight := by
  have htrace := binaryFormulaNegTrace_cost_le formula
  have hlinear :
      (binaryFormulaCode formula).length <=
        (weight + 1) ^ 1 := by
    simp
    omega
  exact htrace.trans <|
    hlinear.trans <|
      coefficient_power_le_transformationEnvelope weight 1 1
        (by omega) (by omega)

theorem binaryFormulaShiftTrace_cost_le_envelope
    (formula : LO.FirstOrder.ArithmeticProposition)
    (weight : Nat)
    (hformula : (binaryFormulaCode formula).length <= weight) :
    (binaryFormulaShiftTrace formula).2 <=
      listedSyntaxTransformationCostEnvelope weight := by
  let formulaLength := (binaryFormulaCode formula).length
  have htrace := binaryFormulaShiftTrace_cost_le formula
  have hfirst : formulaLength + 1 <= weight + 1 := by
    dsimp [formulaLength]
    omega
  have hsecond : formulaLength <= weight + 1 := by
    dsimp [formulaLength]
    omega
  have hproduct := Nat.mul_le_mul hfirst hsecond
  have hscaled := Nat.mul_le_mul_left 100 hproduct
  have hquadratic :
      100 * (formulaLength + 1) * formulaLength <=
        100 * (weight + 1) ^ 2 := by
    simpa [pow_two, Nat.mul_assoc] using hscaled
  exact htrace.trans <| hquadratic.trans <|
    coefficient_power_le_transformationEnvelope weight 100 2
      (by omega) (by omega)

theorem binaryFormulaFreeTrace_cost_le_envelope
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (weight : Nat)
    (hformula : (binaryFormulaCode formula).length <= weight) :
    (binaryFormulaFreeTrace formula).2 <=
      listedSyntaxTransformationCostEnvelope weight := by
  let formulaLength := (binaryFormulaCode formula).length
  have htrace := binaryFormulaFreeTrace_cost_le formula
  have hfirst : formulaLength + 1 <= weight + 1 := by
    dsimp [formulaLength]
    omega
  have hsecond : formulaLength <= weight + 1 := by
    dsimp [formulaLength]
    omega
  have hproduct := Nat.mul_le_mul hfirst hsecond
  have hscaled := Nat.mul_le_mul_left 100 hproduct
  have hquadratic :
      100 * (formulaLength + 1) * formulaLength <=
        100 * (weight + 1) ^ 2 := by
    simpa [pow_two, Nat.mul_assoc] using hscaled
  exact htrace.trans <| hquadratic.trans <|
    coefficient_power_le_transformationEnvelope weight 100 2
      (by omega) (by omega)

theorem formulaListShiftTrace_cost_le_envelope
    (formulas : List LO.FirstOrder.ArithmeticProposition)
    (weight : Nat)
    (hformulas : formulaListCodeWeight formulas <= weight) :
    (formulaListShiftTrace formulas).2 <=
      listedSyntaxTransformationCostEnvelope weight := by
  let listWeight := formulaListCodeWeight formulas
  have htrace := formulaListShiftTrace_cost_le formulas
  have hbase : 1 <= listWeight + 1 := by omega
  have hfactor :
      100 * (listWeight + 1) + 1 <= 101 * (listWeight + 1) := by
    nlinarith
  have hlist : listWeight <= listWeight + 1 := by omega
  have hproduct := Nat.mul_le_mul hfactor hlist
  have hone : 1 <= (listWeight + 1) ^ 2 := by
    nlinarith
  have hlocal :
      (100 * (listWeight + 1) + 1) * listWeight + 1 <=
        102 * (listWeight + 1) ^ 2 := by
    calc
      _ <= 101 * (listWeight + 1) * (listWeight + 1) + 1 :=
        Nat.add_le_add_right hproduct 1
      _ = 101 * (listWeight + 1) ^ 2 + 1 := by ring
      _ <= 102 * (listWeight + 1) ^ 2 := by nlinarith
  have hbaseMono : listWeight + 1 <= weight + 1 := by
    dsimp [listWeight]
    omega
  have hpowerMono := Nat.pow_le_pow_left hbaseMono 2
  have hscaledMono := Nat.mul_le_mul_left 102 hpowerMono
  have hweight :
      102 * (listWeight + 1) ^ 2 <=
        102 * (weight + 1) ^ 2 := hscaledMono
  exact htrace.trans <| hlocal.trans <| hweight.trans <|
    coefficient_power_le_transformationEnvelope weight 102 2
      (by omega) (by omega)

theorem binaryFormulaSubstitutionOneTrace_cost_le_envelope
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (weight : Nat)
    (hformula : (binaryFormulaCode formula).length <= weight)
    (hwitness : (binaryTermCode witness).length <= weight) :
    (binaryFormulaSubstitutionOneTrace formula witness).2 <=
      listedSyntaxTransformationCostEnvelope weight := by
  let formulaLength := (binaryFormulaCode formula).length
  let witnessLength := (binaryTermCode witness).length
  have htrace := binaryFormulaSubstitutionOneTrace_cost_le formula witness
  have hformulaSucc : formulaLength + 1 <= weight + 1 := by
    dsimp [formulaLength]
    omega
  have hwitnessSucc : witnessLength + 1 <= weight + 1 := by
    dsimp [witnessLength]
    omega
  have hformulaFinal : formulaLength <= weight + 1 := by
    dsimp [formulaLength]
    omega
  have hformulaSquare := Nat.pow_le_pow_left hformulaSucc 2
  have hfirst := Nat.mul_le_mul hformulaSquare hwitnessSucc
  have hsecond := Nat.mul_le_mul hfirst hformulaFinal
  have hscaled := Nat.mul_le_mul_left 16 hsecond
  have hquartic :
      16 * (formulaLength + 1) ^ 2 * (witnessLength + 1) *
          formulaLength <=
        16 * (weight + 1) ^ 4 := by
    calc
      _ <= 16 * (((weight + 1) ^ 2 * (weight + 1)) *
          (weight + 1)) := by
        simpa [Nat.mul_assoc] using hscaled
      _ = 16 * (weight + 1) ^ 4 := by ring
  exact htrace.trans <| hquartic.trans <|
    coefficient_power_le_transformationEnvelope weight 16 4
      (by omega) (by omega)

#print axioms listedSyntaxTransformationCostEnvelope_mono
#print axioms binaryFormulaNegTrace_cost_le_envelope
#print axioms binaryFormulaShiftTrace_cost_le_envelope
#print axioms binaryFormulaFreeTrace_cost_le_envelope
#print axioms formulaListShiftTrace_cost_le_envelope
#print axioms binaryFormulaSubstitutionOneTrace_cost_le_envelope

end FoundationCompactListedTransformationCostEnvelope
