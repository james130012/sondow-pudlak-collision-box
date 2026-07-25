import integration.FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
import integration.FoundationCompactSyntaxTransformationCodeBounds

/-!
# Native index terms for dropping two natural-list rows

The function parser branch consumes exactly two source rows.  These are the
four exact open index terms occurring in that original formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 50000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListDropTwoRowsIndexTermsFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate

def dropTwoSourceIndexTerm : ValuationTerm :=
  ‘!!(fixedNumeralTerm 2) + &0’

def dropTwoSourceNextTerm : ValuationTerm :=
  ‘(!!(fixedNumeralTerm 2) + &0) + 1’

def dropTwoTargetIndexTerm : ValuationTerm := &0

def dropTwoTargetNextTerm : ValuationTerm := ‘&0 + 1’

def dropTwoIndexTermCodeBound : Nat :=
  (binaryTermCode dropTwoSourceIndexTerm).length +
    (binaryTermCode dropTwoSourceNextTerm).length +
    (binaryTermCode dropTwoTargetIndexTerm).length +
    (binaryTermCode dropTwoTargetNextTerm).length + 1

private theorem binaryFunctionTerm_freeVariables_dropTwo
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
    (fixedNumeralTerm 2).freeVariables = ∅ := by
  unfold fixedNumeralTerm Semiterm.Operator.operator
  simp

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

theorem dropTwoSourceIndexTerm_freeVariables_subset :
    dropTwoSourceIndexTerm.freeVariables ⊆ {0} := by
  unfold dropTwoSourceIndexTerm
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![fixedNumeralTerm 2, &0]).freeVariables ⊆ {0}
  rw [binaryFunctionTerm_freeVariables_dropTwo,
    fixedNumeralTerm_three_freeVariables_eq_empty]
  simp

theorem dropTwoSourceNextTerm_freeVariables_subset :
    dropTwoSourceNextTerm.freeVariables ⊆ {0} := by
  unfold dropTwoSourceNextTerm
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![LO.FirstOrder.Semiterm.func Language.Add.add
        ![fixedNumeralTerm 2, &0], ‘1’]).freeVariables ⊆ {0}
  rw [binaryFunctionTerm_freeVariables_dropTwo,
    binaryFunctionTerm_freeVariables_dropTwo,
    fixedNumeralTerm_three_freeVariables_eq_empty,
    arithmeticOneTerm_freeVariables_eq_empty]
  simp

theorem dropTwoTargetIndexTerm_freeVariables_subset :
    dropTwoTargetIndexTerm.freeVariables ⊆ {0} := by
  simp [dropTwoTargetIndexTerm]

theorem dropTwoTargetNextTerm_freeVariables_subset :
    dropTwoTargetNextTerm.freeVariables ⊆ {0} := by
  unfold dropTwoTargetNextTerm
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![(&0 : ValuationTerm), ‘1’]).freeVariables ⊆ {0}
  rw [binaryFunctionTerm_freeVariables_dropTwo,
    arithmeticOneTerm_freeVariables_eq_empty]
  simp

private theorem termValue_fixedNumeralTerm_three (valuation : Nat -> Nat) :
    termValue valuation (fixedNumeralTerm 2) = 2 := by
  unfold termValue fixedNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘ (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) =
        (![] : Fin 0 -> Nat) by
      funext index
      exact Fin.elim0 index]
  simp

private theorem termValue_arithmeticAdd_dropTwo
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  change termValue valuation
    (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]) = _
  exact termValue_add valuation ![left, right]

theorem termValue_dropTwoSourceIndexTerm (valuation : Nat -> Nat) :
    termValue valuation dropTwoSourceIndexTerm = 2 + valuation 0 := by
  unfold dropTwoSourceIndexTerm
  rw [termValue_arithmeticAdd_dropTwo,
    termValue_fixedNumeralTerm_three]
  simp [termValue]

theorem termValue_dropTwoSourceNextTerm (valuation : Nat -> Nat) :
    termValue valuation dropTwoSourceNextTerm = 2 + valuation 0 + 1 := by
  unfold dropTwoSourceNextTerm
  rw [termValue_arithmeticAdd_dropTwo,
    termValue_arithmeticAdd_dropTwo,
    termValue_fixedNumeralTerm_three]
  simp [termValue]

theorem termValue_dropTwoTargetIndexTerm (valuation : Nat -> Nat) :
    termValue valuation dropTwoTargetIndexTerm = valuation 0 := by
  simp [dropTwoTargetIndexTerm, termValue]

theorem termValue_dropTwoTargetNextTerm (valuation : Nat -> Nat) :
    termValue valuation dropTwoTargetNextTerm = valuation 0 + 1 := by
  unfold dropTwoTargetNextTerm
  rw [termValue_arithmeticAdd_dropTwo]
  simp [termValue]

theorem dropTwoSourceIndexTerm_code_length_le :
    (binaryTermCode dropTwoSourceIndexTerm).length <=
      dropTwoIndexTermCodeBound := by
  unfold dropTwoIndexTermCodeBound
  omega

theorem dropTwoSourceNextTerm_code_length_le :
    (binaryTermCode dropTwoSourceNextTerm).length <=
      dropTwoIndexTermCodeBound := by
  unfold dropTwoIndexTermCodeBound
  omega

theorem dropTwoTargetIndexTerm_code_length_le :
    (binaryTermCode dropTwoTargetIndexTerm).length <=
      dropTwoIndexTermCodeBound := by
  unfold dropTwoIndexTermCodeBound
  omega

theorem dropTwoTargetNextTerm_code_length_le :
    (binaryTermCode dropTwoTargetNextTerm).length <=
      dropTwoIndexTermCodeBound := by
  unfold dropTwoIndexTermCodeBound
  omega

#print axioms dropTwoSourceIndexTerm_freeVariables_subset
#print axioms dropTwoSourceNextTerm_freeVariables_subset
#print axioms termValue_dropTwoSourceIndexTerm
#print axioms termValue_dropTwoSourceNextTerm
#print axioms dropTwoSourceNextTerm_code_length_le

end FoundationCompactNumericListedDirectNatListDropTwoRowsIndexTermsFixedBounds
