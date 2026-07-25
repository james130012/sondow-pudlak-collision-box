import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds

/-!
# Fully fixed count leaf for syntax-task-list cons rows

The original checked equality `targetCount = sourceCount + 1` is bounded only
by the shared bit coordinate.  Both the formula code and the real positive
atomic certificate are included.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsCountFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds

private abbrev taskConsCountZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation

def taskConsCountTermCodePolynomial (bitBound : Nat) : Nat :=
  2 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (‘1’ : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def taskConsCountFormulaCodePolynomial (bitBound : Nat) : Nat :=
  orderAtomicFormulaCodeEnvelope
    (taskConsCountTermCodePolynomial bitBound)

def taskConsCountFullyFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (taskConsCountTermCodePolynomial bitBound)

private theorem taskConsArithmeticAdd_freeVariables
    {Variable : Type*} [DecidableEq Variable] {arity : Nat}
    (left right : ArithmeticSemiterm Variable arity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable arity).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables
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
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem taskConsBinaryRelation_freeVariables
    (relation : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiformula.rel relation
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiformula.freeVariables_rel] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiformula.freeVariables_rel]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

@[simp] private theorem taskConsArithmeticOne_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem taskConsCountTerms_code_length_le
    (sourceCount targetCount bitBound : Nat)
    (hsourceSize : Nat.size sourceCount <= bitBound)
    (htargetSize : Nat.size targetCount <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm targetCount)).length <=
        taskConsCountTermCodePolynomial bitBound ∧
      (binaryTermCode
        (‘!!(shortBinaryNumeralTerm sourceCount) + 1’ :
          ValuationTerm)).length <=
        taskConsCountTermCodePolynomial bitBound := by
  have hsource := binaryNumeralTerm_code_length_le_envelope sourceCount
    bitBound hsourceSize
  have htarget := binaryNumeralTerm_code_length_le_envelope targetCount
    bitBound htargetSize
  have hadd := arithmeticAddTerm_code_length_le
    (shortBinaryNumeralTerm sourceCount) (‘1’ : ValuationTerm)
  unfold taskConsCountTermCodePolynomial
  omega

theorem taskConsCountFormula_code_length_le_fixed
    (sourceCount targetCount bitBound : Nat)
    (hsourceSize : Nat.size sourceCount <= bitBound)
    (htargetSize : Nat.size targetCount <= bitBound) :
    (binaryFormulaCode
      (“!!(shortBinaryNumeralTerm targetCount) =
        !!(shortBinaryNumeralTerm sourceCount) + 1” :
        ValuationFormula)).length <=
      taskConsCountFormulaCodePolynomial bitBound := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm sourceCount) + 1’
  have hterms := taskConsCountTerms_code_length_le sourceCount targetCount
    bitBound hsourceSize htargetSize
  unfold taskConsCountFormulaCodePolynomial
  exact binaryRelationFormula_code_le_orderAtomic Language.Eq.eq
    (shortBinaryNumeralTerm targetCount) rightTerm
    (taskConsCountTermCodePolynomial bitBound) hterms.1 hterms.2

@[simp] theorem taskConsCountFormula_freeVariables_eq_empty
    (sourceCount targetCount : Nat) :
    (“!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount) + 1” :
      ValuationFormula).freeVariables = ∅ := by
  let leftTerm : ValuationTerm := shortBinaryNumeralTerm targetCount
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm sourceCount) + 1’
  have hleft : leftTerm.freeVariables = ∅ := by
    exact shortBinaryNumeralTerm_freeVariables_eq_empty targetCount
  have hright : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    rw [taskConsArithmeticAdd_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      taskConsArithmeticOne_freeVariables_eq_empty]
    simp
  change
    (LO.FirstOrder.Semiformula.rel Language.Eq.eq
      ![leftTerm, rightTerm]).freeVariables = ∅
  rw [taskConsBinaryRelation_freeVariables, hleft, hright]
  simp

theorem taskConsCountPayloadPolynomial_le_fullyFixed
    (sourceCount targetCount bitBound : Nat)
    (hsourceSize : Nat.size sourceCount <= bitBound)
    (htargetSize : Nat.size targetCount <= bitBound) :
    compactAdditiveSyntaxTaskListConsRowsCountEqualityPayloadPolynomial
        sourceCount targetCount <=
      taskConsCountFullyFixedPayloadPolynomial bitBound := by
  let leftTerm : ValuationTerm := shortBinaryNumeralTerm targetCount
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm sourceCount) + 1’
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  have hterms := taskConsCountTerms_code_length_le sourceCount targetCount
    bitBound hsourceSize htargetSize
  have hleftClosed : leftTerm.freeVariables = ∅ := by
    exact shortBinaryNumeralTerm_freeVariables_eq_empty targetCount
  have hrightClosed : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    rw [taskConsArithmeticAdd_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      taskConsArithmeticOne_freeVariables_eq_empty]
    simp
  unfold
    compactAdditiveSyntaxTaskListConsRowsCountEqualityPayloadPolynomial
    taskConsCountFullyFixedPayloadPolynomial
  exact compilePositiveRelationPayloadPolynomial_le_fixed
    taskConsCountZeroValuation Language.Eq.eq args 0
    (taskConsCountTermCodePolynomial bitBound)
    (by
      change leftTerm.freeVariables ⊆ {0}
      rw [hleftClosed]
      simp)
    (by
      change rightTerm.freeVariables ⊆ {0}
      rw [hrightClosed]
      simp)
    (by rfl) hterms.1 hterms.2

#print axioms taskConsCountFormula_code_length_le_fixed
#print axioms taskConsCountFormula_freeVariables_eq_empty
#print axioms taskConsCountPayloadPolynomial_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsCountFullyFixedBounds
