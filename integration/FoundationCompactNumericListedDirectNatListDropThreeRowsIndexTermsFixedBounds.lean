import integration.FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
import integration.FoundationCompactSyntaxTransformationCodeBounds

/-!
# Native index terms for dropping three natural-list rows

The function parser branch consumes exactly three source rows.  These are the
four exact open index terms occurring in that original formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 50000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListDropThreeRowsIndexTermsFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate

def dropThreeSourceIndexTerm : ValuationTerm :=
  ‘!!(fixedNumeralTerm 3) + &0’

def dropThreeSourceNextTerm : ValuationTerm :=
  ‘(!!(fixedNumeralTerm 3) + &0) + 1’

def dropThreeTargetIndexTerm : ValuationTerm := &0

def dropThreeTargetNextTerm : ValuationTerm := ‘&0 + 1’

def dropThreeIndexTermCodeBound : Nat :=
  (binaryTermCode dropThreeSourceIndexTerm).length +
    (binaryTermCode dropThreeSourceNextTerm).length +
    (binaryTermCode dropThreeTargetIndexTerm).length +
    (binaryTermCode dropThreeTargetNextTerm).length + 1

private theorem binaryFunctionTerm_freeVariables_dropThree
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiterm.func functionSymbol
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr
        ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr
        ⟨1, Finset.mem_univ 1, hright⟩

theorem fixedNumeralTerm_three_freeVariables_eq_empty :
    (fixedNumeralTerm 3).freeVariables = ∅ := by
  unfold fixedNumeralTerm Semiterm.Operator.operator
  simp

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

theorem dropThreeSourceIndexTerm_freeVariables_subset :
    dropThreeSourceIndexTerm.freeVariables ⊆ {0} := by
  unfold dropThreeSourceIndexTerm
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![fixedNumeralTerm 3, &0]).freeVariables ⊆ {0}
  rw [binaryFunctionTerm_freeVariables_dropThree,
    fixedNumeralTerm_three_freeVariables_eq_empty]
  simp

theorem dropThreeSourceNextTerm_freeVariables_subset :
    dropThreeSourceNextTerm.freeVariables ⊆ {0} := by
  unfold dropThreeSourceNextTerm
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![LO.FirstOrder.Semiterm.func Language.Add.add
        ![fixedNumeralTerm 3, &0], ‘1’]).freeVariables ⊆ {0}
  rw [binaryFunctionTerm_freeVariables_dropThree,
    binaryFunctionTerm_freeVariables_dropThree,
    fixedNumeralTerm_three_freeVariables_eq_empty,
    arithmeticOneTerm_freeVariables_eq_empty]
  simp

theorem dropThreeTargetIndexTerm_freeVariables_subset :
    dropThreeTargetIndexTerm.freeVariables ⊆ {0} := by
  simp [dropThreeTargetIndexTerm]

theorem dropThreeTargetNextTerm_freeVariables_subset :
    dropThreeTargetNextTerm.freeVariables ⊆ {0} := by
  unfold dropThreeTargetNextTerm
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![(&0 : ValuationTerm), ‘1’]).freeVariables ⊆ {0}
  rw [binaryFunctionTerm_freeVariables_dropThree,
    arithmeticOneTerm_freeVariables_eq_empty]
  simp

private theorem termValue_fixedNumeralTerm_three (valuation : Nat -> Nat) :
    termValue valuation (fixedNumeralTerm 3) = 3 := by
  unfold termValue fixedNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘ (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) =
        (![] : Fin 0 -> Nat) by
      funext index
      exact Fin.elim0 index]
  simp

private theorem termValue_arithmeticAdd_dropThree
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  change termValue valuation
    (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]) = _
  exact termValue_add valuation ![left, right]

theorem termValue_dropThreeSourceIndexTerm (valuation : Nat -> Nat) :
    termValue valuation dropThreeSourceIndexTerm = 3 + valuation 0 := by
  unfold dropThreeSourceIndexTerm
  rw [termValue_arithmeticAdd_dropThree,
    termValue_fixedNumeralTerm_three]
  simp [termValue]

theorem termValue_dropThreeSourceNextTerm (valuation : Nat -> Nat) :
    termValue valuation dropThreeSourceNextTerm = 3 + valuation 0 + 1 := by
  unfold dropThreeSourceNextTerm
  rw [termValue_arithmeticAdd_dropThree,
    termValue_arithmeticAdd_dropThree,
    termValue_fixedNumeralTerm_three]
  simp [termValue]

theorem termValue_dropThreeTargetIndexTerm (valuation : Nat -> Nat) :
    termValue valuation dropThreeTargetIndexTerm = valuation 0 := by
  simp [dropThreeTargetIndexTerm, termValue]

theorem termValue_dropThreeTargetNextTerm (valuation : Nat -> Nat) :
    termValue valuation dropThreeTargetNextTerm = valuation 0 + 1 := by
  unfold dropThreeTargetNextTerm
  rw [termValue_arithmeticAdd_dropThree]
  simp [termValue]

theorem dropThreeSourceIndexTerm_code_length_le :
    (binaryTermCode dropThreeSourceIndexTerm).length <=
      dropThreeIndexTermCodeBound := by
  unfold dropThreeIndexTermCodeBound
  omega

theorem dropThreeSourceNextTerm_code_length_le :
    (binaryTermCode dropThreeSourceNextTerm).length <=
      dropThreeIndexTermCodeBound := by
  unfold dropThreeIndexTermCodeBound
  omega

theorem dropThreeTargetIndexTerm_code_length_le :
    (binaryTermCode dropThreeTargetIndexTerm).length <=
      dropThreeIndexTermCodeBound := by
  unfold dropThreeIndexTermCodeBound
  omega

theorem dropThreeTargetNextTerm_code_length_le :
    (binaryTermCode dropThreeTargetNextTerm).length <=
      dropThreeIndexTermCodeBound := by
  unfold dropThreeIndexTermCodeBound
  omega

#print axioms dropThreeSourceIndexTerm_freeVariables_subset
#print axioms dropThreeSourceNextTerm_freeVariables_subset
#print axioms termValue_dropThreeSourceIndexTerm
#print axioms termValue_dropThreeSourceNextTerm
#print axioms dropThreeSourceNextTerm_code_length_le

end FoundationCompactNumericListedDirectNatListDropThreeRowsIndexTermsFixedBounds
