import integration.FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
import integration.FoundationCompactSyntaxTransformationCodeBounds

/-!
# Native index terms for dropping one natural-list row

The parser continuation branch uses the original fixed numeral `1`, not a
short binary numeral.  This file exposes the four exact open row-index terms
and proves their syntax, free-variable, and valuation facts without replacing
them by extensionally equal terms.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListDropOneRowsIndexTermsFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate

def dropOneSourceIndexTerm : ValuationTerm :=
  ‘!!(fixedNumeralTerm 1) + &0’

def dropOneSourceNextTerm : ValuationTerm :=
  ‘(!!(fixedNumeralTerm 1) + &0) + 1’

def dropOneTargetIndexTerm : ValuationTerm := &0

def dropOneTargetNextTerm : ValuationTerm := ‘&0 + 1’

def dropOneIndexTermCodeBound : Nat :=
  (binaryTermCode dropOneSourceIndexTerm).length +
    (binaryTermCode dropOneSourceNextTerm).length +
    (binaryTermCode dropOneTargetIndexTerm).length +
    (binaryTermCode dropOneTargetNextTerm).length + 1

private theorem binaryFunctionTerm_freeVariables_dropOne
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

theorem fixedNumeralTerm_one_freeVariables_eq_empty :
    (fixedNumeralTerm 1).freeVariables = ∅ := by
  unfold fixedNumeralTerm Semiterm.Operator.operator
  simp

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

theorem dropOneSourceIndexTerm_freeVariables_subset :
    dropOneSourceIndexTerm.freeVariables ⊆ {0} := by
  unfold dropOneSourceIndexTerm
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![fixedNumeralTerm 1, &0]).freeVariables ⊆ {0}
  rw [binaryFunctionTerm_freeVariables_dropOne,
    fixedNumeralTerm_one_freeVariables_eq_empty]
  simp

theorem dropOneSourceNextTerm_freeVariables_subset :
    dropOneSourceNextTerm.freeVariables ⊆ {0} := by
  unfold dropOneSourceNextTerm
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![LO.FirstOrder.Semiterm.func Language.Add.add
        ![fixedNumeralTerm 1, &0], ‘1’]).freeVariables ⊆ {0}
  rw [binaryFunctionTerm_freeVariables_dropOne,
    binaryFunctionTerm_freeVariables_dropOne,
    fixedNumeralTerm_one_freeVariables_eq_empty,
    arithmeticOneTerm_freeVariables_eq_empty]
  simp

theorem dropOneTargetIndexTerm_freeVariables_subset :
    dropOneTargetIndexTerm.freeVariables ⊆ {0} := by
  simp [dropOneTargetIndexTerm]

theorem dropOneTargetNextTerm_freeVariables_subset :
    dropOneTargetNextTerm.freeVariables ⊆ {0} := by
  unfold dropOneTargetNextTerm
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![(&0 : ValuationTerm), ‘1’]).freeVariables ⊆ {0}
  rw [binaryFunctionTerm_freeVariables_dropOne]
  rw [arithmeticOneTerm_freeVariables_eq_empty]
  simp

private theorem termValue_fixedNumeralTerm_one (valuation : Nat -> Nat) :
    termValue valuation (fixedNumeralTerm 1) = 1 := by
  unfold termValue fixedNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘ (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) =
        (![] : Fin 0 -> Nat) by
      funext index
      exact Fin.elim0 index]
  simp

private theorem termValue_arithmeticAdd_dropOne
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  change termValue valuation
    (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]) = _
  exact termValue_add valuation ![left, right]

theorem termValue_dropOneSourceIndexTerm (valuation : Nat -> Nat) :
    termValue valuation dropOneSourceIndexTerm = 1 + valuation 0 := by
  unfold dropOneSourceIndexTerm
  rw [termValue_arithmeticAdd_dropOne,
    termValue_fixedNumeralTerm_one]
  simp [termValue]

theorem termValue_dropOneSourceNextTerm (valuation : Nat -> Nat) :
    termValue valuation dropOneSourceNextTerm = 1 + valuation 0 + 1 := by
  unfold dropOneSourceNextTerm
  rw [termValue_arithmeticAdd_dropOne,
    termValue_arithmeticAdd_dropOne,
    termValue_fixedNumeralTerm_one]
  simp [termValue]

theorem termValue_dropOneTargetIndexTerm (valuation : Nat -> Nat) :
    termValue valuation dropOneTargetIndexTerm = valuation 0 := by
  simp [dropOneTargetIndexTerm, termValue]

theorem termValue_dropOneTargetNextTerm (valuation : Nat -> Nat) :
    termValue valuation dropOneTargetNextTerm = valuation 0 + 1 := by
  unfold dropOneTargetNextTerm
  rw [termValue_arithmeticAdd_dropOne]
  simp [termValue]

theorem dropOneSourceIndexTerm_code_length_le :
    (binaryTermCode dropOneSourceIndexTerm).length <=
      dropOneIndexTermCodeBound := by
  unfold dropOneIndexTermCodeBound
  omega

theorem dropOneSourceNextTerm_code_length_le :
    (binaryTermCode dropOneSourceNextTerm).length <=
      dropOneIndexTermCodeBound := by
  unfold dropOneIndexTermCodeBound
  omega

theorem dropOneTargetIndexTerm_code_length_le :
    (binaryTermCode dropOneTargetIndexTerm).length <=
      dropOneIndexTermCodeBound := by
  unfold dropOneIndexTermCodeBound
  omega

theorem dropOneTargetNextTerm_code_length_le :
    (binaryTermCode dropOneTargetNextTerm).length <=
      dropOneIndexTermCodeBound := by
  unfold dropOneIndexTermCodeBound
  omega

#print axioms dropOneSourceIndexTerm_freeVariables_subset
#print axioms dropOneSourceNextTerm_freeVariables_subset
#print axioms termValue_dropOneSourceIndexTerm
#print axioms termValue_dropOneSourceNextTerm
#print axioms dropOneSourceNextTerm_code_length_le

end FoundationCompactNumericListedDirectNatListDropOneRowsIndexTermsFixedBounds
