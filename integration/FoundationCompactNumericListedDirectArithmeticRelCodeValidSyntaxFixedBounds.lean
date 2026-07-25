import integration.FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate
import integration.FoundationCompactPABinaryNumeralAdditionBounds

/-!
# Fixed syntax bounds for arithmetic relation-code validity

The accepted relation codes are exactly the two pairs `(2, 0)` and `(2, 1)`.
This file bounds the complete valid and invalid closed formulas using only one
common bit bound for the arity and code coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectArithmeticRelCodeValidSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate

def arithmeticRelCodeTermCodePolynomial (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (relCodeFixedNumeralTerm 0)).length +
    (binaryTermCode (relCodeFixedNumeralTerm 1)).length +
    (binaryTermCode (relCodeFixedNumeralTerm 2)).length + 1

def arithmeticRelCodeAtomicFormulaCodePolynomial (bitBound : Nat) : Nat :=
  2 * arithmeticRelCodeTermCodePolynomial bitBound +
    (binaryNatCode 0).length + (binaryNatCode 2).length + 128

def arithmeticRelCodeValidFormulaCodePolynomial (bitBound : Nat) : Nat :=
  4 * arithmeticRelCodeAtomicFormulaCodePolynomial bitBound +
    2 * (binaryNatCode 4).length + (binaryNatCode 5).length + 32

def arithmeticRelCodeInvalidFormulaCodePolynomial (bitBound : Nat) : Nat :=
  2 * arithmeticRelCodeValidFormulaCodePolynomial bitBound +
    (binaryNatCode 3).length + 272

theorem arithmeticRelCodeShortNumeralTerm_code_length_le_fixed
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      arithmeticRelCodeTermCodePolynomial bitBound := by
  have hraw :=
    binaryNumeralTerm_code_length_le_envelope value bitBound hvalue
  unfold arithmeticRelCodeTermCodePolynomial
  omega

theorem arithmeticRelCodeFixedNumeralTerm_code_length_le_fixed
    (expected bitBound : Nat) (hexpected : expected <= 2) :
    (binaryTermCode (relCodeFixedNumeralTerm expected)).length <=
      arithmeticRelCodeTermCodePolynomial bitBound := by
  have hcases : expected = 0 ∨ expected = 1 ∨ expected = 2 := by omega
  rcases hcases with rfl | rfl | rfl <;>
    unfold arithmeticRelCodeTermCodePolynomial <;> omega

private theorem arithmeticRelCodeFixedNumeralTerm_freeVariables_eq_empty
    (expected : Nat) :
    (relCodeFixedNumeralTerm expected).freeVariables = ∅ := by
  simp [relCodeFixedNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]

private theorem arithmeticRelCodeBinaryRelation_closed
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (LO.FirstOrder.Semiformula.rel relationSymbol
      ![left, right]).freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_rel]
  ext candidate
  constructor
  · intro hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero =>
        change candidate ∈ left.freeVariables at hcoordinate
        rw [hleft] at hcoordinate
        simp at hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero =>
            change candidate ∈ right.freeVariables at hcoordinate
            rw [hright] at hcoordinate
            simp at hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · simp

private theorem arithmeticRelCodeBinaryRelation_code_length_le_fixed
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm) (bitBound : Nat)
    (hleft :
      (binaryTermCode left).length <=
        arithmeticRelCodeTermCodePolynomial bitBound)
    (hright :
      (binaryTermCode right).length <=
        arithmeticRelCodeTermCodePolynomial bitBound) :
    (binaryFormulaCode
      (LO.FirstOrder.Semiformula.rel relationSymbol ![left, right])).length <=
      arithmeticRelCodeAtomicFormulaCodePolynomial bitBound := by
  simp [binaryFormulaCode, Matrix.fun_eq_vec_two]
  have hrelationTag :
      (binaryNatCode (Encodable.encode relationSymbol)).length <= 128 := by
    cases relationSymbol <;> decide
  unfold arithmeticRelCodeAtomicFormulaCodePolynomial
  omega

theorem relCodeFixedEqFormula_code_length_le_fixed
    (value expected bitBound : Nat)
    (hvalue : Nat.size value <= bitBound)
    (hexpected : expected <= 2) :
    (binaryFormulaCode (relCodeFixedEqFormula value expected)).length <=
      arithmeticRelCodeAtomicFormulaCodePolynomial bitBound := by
  unfold relCodeFixedEqFormula
  exact arithmeticRelCodeBinaryRelation_code_length_le_fixed Language.Eq.eq
    (shortBinaryNumeralTerm value) (relCodeFixedNumeralTerm expected) bitBound
    (arithmeticRelCodeShortNumeralTerm_code_length_le_fixed value bitBound
      hvalue)
    (arithmeticRelCodeFixedNumeralTerm_code_length_le_fixed expected bitBound
      hexpected)

@[simp] theorem relCodeFixedEqFormula_freeVariables_eq_empty_fixed
    (value expected : Nat) :
    (relCodeFixedEqFormula value expected).freeVariables = ∅ := by
  unfold relCodeFixedEqFormula
  exact arithmeticRelCodeBinaryRelation_closed Language.Eq.eq
    (shortBinaryNumeralTerm value) (relCodeFixedNumeralTerm expected)
    (shortBinaryNumeralTerm_freeVariables_eq_empty value)
    (arithmeticRelCodeFixedNumeralTerm_freeVariables_eq_empty expected)

theorem compactAdditiveArithmeticRelCodeValidClosedFormula_code_length_le_fixed
    (arity code bitBound : Nat)
    (harity : Nat.size arity <= bitBound)
    (hcode : Nat.size code <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveArithmeticRelCodeValidClosedFormula arity code)).length <=
      arithmeticRelCodeValidFormulaCodePolynomial bitBound := by
  have ha2 := relCodeFixedEqFormula_code_length_le_fixed arity 2 bitBound
    harity (by omega)
  have hc0 := relCodeFixedEqFormula_code_length_le_fixed code 0 bitBound
    hcode (by omega)
  have hc1 := relCodeFixedEqFormula_code_length_le_fixed code 1 bitBound
    hcode (by omega)
  rw [compactAdditiveArithmeticRelCodeValidClosedFormula_alignment]
  unfold compactAdditiveArithmeticRelCodeValidExplicitFormula
    arithmeticRelCodeValidFormulaCodePolynomial
  simp [binaryFormulaCode] at *
  omega

@[simp] theorem
    compactAdditiveArithmeticRelCodeValidClosedFormula_freeVariables_eq_empty_fixed
    (arity code : Nat) :
    (compactAdditiveArithmeticRelCodeValidClosedFormula arity code).freeVariables =
      ∅ := by
  rw [compactAdditiveArithmeticRelCodeValidClosedFormula_alignment]
  unfold compactAdditiveArithmeticRelCodeValidExplicitFormula
  simp

theorem compactAdditiveArithmeticRelCodeInvalidClosedFormula_code_length_le_fixed
    (arity code bitBound : Nat)
    (harity : Nat.size arity <= bitBound)
    (hcode : Nat.size code <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveArithmeticRelCodeInvalidClosedFormula arity code)).length <=
      arithmeticRelCodeInvalidFormulaCodePolynomial bitBound := by
  have hvalid :=
    compactAdditiveArithmeticRelCodeValidClosedFormula_code_length_le_fixed
      arity code bitBound harity hcode
  have hneg := binaryFormulaCode_neg_length_le
    (compactAdditiveArithmeticRelCodeValidClosedFormula arity code)
  unfold compactAdditiveArithmeticRelCodeInvalidClosedFormula
    arithmeticRelCodeInvalidFormulaCodePolynomial
  omega

@[simp] theorem
    compactAdditiveArithmeticRelCodeInvalidClosedFormula_freeVariables_eq_empty_fixed
    (arity code : Nat) :
    (compactAdditiveArithmeticRelCodeInvalidClosedFormula arity code).freeVariables =
      ∅ := by
  unfold compactAdditiveArithmeticRelCodeInvalidClosedFormula
  rw [LO.FirstOrder.Semiformula.freeVariables_not,
    compactAdditiveArithmeticRelCodeValidClosedFormula_freeVariables_eq_empty_fixed]

#print axioms
  compactAdditiveArithmeticRelCodeValidClosedFormula_code_length_le_fixed
#print axioms
  compactAdditiveArithmeticRelCodeValidClosedFormula_freeVariables_eq_empty_fixed
#print axioms
  compactAdditiveArithmeticRelCodeInvalidClosedFormula_code_length_le_fixed
#print axioms
  compactAdditiveArithmeticRelCodeInvalidClosedFormula_freeVariables_eq_empty_fixed

end FoundationCompactNumericListedDirectArithmeticRelCodeValidSyntaxFixedBounds
