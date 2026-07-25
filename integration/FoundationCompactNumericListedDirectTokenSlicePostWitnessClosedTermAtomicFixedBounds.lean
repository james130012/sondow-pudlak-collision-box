import integration.FoundationCompactNumericListedDirectTokenSlicePostWitnessAtomicFixedBounds

/-!
# Fixed post-witness atoms for token slices with closed endpoint terms

The five arithmetic atoms outside the offset universal are bounded directly
from closedness and one common code bound for their endpoint terms.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSlicePostWitnessClosedTermAtomicFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixAtomicFixedBounds
open FoundationCompactNumericListedDirectTokenSlicePublicBounds

def tokenSlicePostWitnessClosedTermCompositeCodePolynomial
    (termCode : Nat) : Nat :=
  2 * termCode + (binaryTermCode (‘1’ : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def tokenSlicePostWitnessClosedTermPositiveAtomicFixedPayloadPolynomial
    (termCode : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (tokenSlicePostWitnessClosedTermCompositeCodePolynomial termCode)

def tokenSlicePostWitnessClosedTermLeFixedPayloadPolynomial
    (termCode : Nat) : Nat :=
  appendSourcePrefixLeFixedPayloadPolynomial termCode

private theorem tokenSliceClosedAddTerm_eq_paAddTerm
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) = paAddTerm left right := by
  rfl

private theorem tokenSliceClosedBinaryFunction_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiterm.func functionSymbol ![left, right]).freeVariables =
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
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem tokenSliceClosedAddTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [tokenSliceClosedAddTerm_eq_paAddTerm,
    ← finiteCaseAddTerm_eq_paAddTerm]
  exact tokenSliceClosedBinaryFunction_freeVariables Language.Add.add left right

private theorem tokenSliceClosedOne_freeVariables :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem tokenSliceClosedAdd_closed
    (left right : ValuationTerm)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables = ∅ := by
  rw [tokenSliceClosedAddTerm_freeVariables, hleft, hright]
  simp

private theorem tokenSliceClosedAdd_code_le
    (left right : ValuationTerm) (termCode : Nat)
    (hleft : (binaryTermCode left).length <= termCode)
    (hright : (binaryTermCode right).length <= termCode) :
    (binaryTermCode (‘!!left + !!right’ : ValuationTerm)).length <=
      tokenSlicePostWitnessClosedTermCompositeCodePolynomial termCode := by
  have hraw := paAddTerm_code_length_le left right
  rw [tokenSliceClosedAddTerm_eq_paAddTerm]
  unfold tokenSlicePostWitnessClosedTermCompositeCodePolynomial
  omega

private theorem tokenSliceClosedAddOne_code_le
    (term : ValuationTerm) (termCode : Nat)
    (hterm : (binaryTermCode term).length <= termCode) :
    (binaryTermCode (‘!!term + 1’ : ValuationTerm)).length <=
      tokenSlicePostWitnessClosedTermCompositeCodePolynomial termCode := by
  have hraw := paAddTerm_code_length_le term (‘1’ : ValuationTerm)
  change (binaryTermCode
    (‘!!term + !!(‘1’ : ValuationTerm)’ : ValuationTerm)).length <= _
  rw [tokenSliceClosedAddTerm_eq_paAddTerm]
  unfold tokenSlicePostWitnessClosedTermCompositeCodePolynomial
  omega

private theorem tokenSliceClosedTerm_code_le_composite
    (term : ValuationTerm) (termCode : Nat)
    (hterm : (binaryTermCode term).length <= termCode) :
    (binaryTermCode term).length <=
      tokenSlicePostWitnessClosedTermCompositeCodePolynomial termCode := by
  unfold tokenSlicePostWitnessClosedTermCompositeCodePolynomial
  omega

theorem tokenSliceAtValuationCountGuardStructuralEnvelope_le_closedFixed
    (valuation : Nat -> Nat)
    (tokenCountTerm : ValuationTerm) (count termCode : Nat)
    (htokenCountClosed : tokenCountTerm.freeVariables = ∅)
    (hcountClosed :
      (shortBinaryNumeralTerm count : ValuationTerm).freeVariables = ∅)
    (htokenCountCode :
      (binaryTermCode tokenCountTerm).length <= termCode)
    (hcountCode :
      (binaryTermCode (shortBinaryNumeralTerm count)).length <= termCode) :
    tokenSliceAtValuationCountGuardStructuralEnvelope valuation tokenCountTerm
        count <=
      tokenSlicePostWitnessClosedTermPositiveAtomicFixedPayloadPolynomial
        termCode := by
  unfold tokenSliceAtValuationCountGuardStructuralEnvelope
    tokenSlicePostWitnessClosedTermPositiveAtomicFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed valuation
    Language.ORing.Rel.lt (shortBinaryNumeralTerm count)
    (‘!!tokenCountTerm + 1’ : ValuationTerm) 0
    (tokenSlicePostWitnessClosedTermCompositeCodePolynomial termCode)
    hcountClosed
    (tokenSliceClosedAdd_closed tokenCountTerm (‘1’ : ValuationTerm)
      htokenCountClosed tokenSliceClosedOne_freeVariables)
    (tokenSliceClosedTerm_code_le_composite
      (shortBinaryNumeralTerm count) termCode hcountCode)
    (tokenSliceClosedAddOne_code_le tokenCountTerm termCode htokenCountCode)

theorem tokenSliceAtValuationEndpointStructuralEnvelope_le_closedFixed
    (valuation : Nat -> Nat)
    (startTerm finishTerm : ValuationTerm) (count termCode : Nat)
    (hstartClosed : startTerm.freeVariables = ∅)
    (hfinishClosed : finishTerm.freeVariables = ∅)
    (hcountClosed :
      (shortBinaryNumeralTerm count : ValuationTerm).freeVariables = ∅)
    (hstartCode : (binaryTermCode startTerm).length <= termCode)
    (hfinishCode : (binaryTermCode finishTerm).length <= termCode)
    (hcountCode :
      (binaryTermCode (shortBinaryNumeralTerm count)).length <= termCode) :
    tokenSliceAtValuationEndpointStructuralEnvelope valuation startTerm
        finishTerm count <=
      tokenSlicePostWitnessClosedTermPositiveAtomicFixedPayloadPolynomial
        termCode := by
  unfold tokenSliceAtValuationEndpointStructuralEnvelope
    tokenSlicePostWitnessClosedTermPositiveAtomicFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed valuation
    Language.Eq.eq finishTerm
    (‘!!startTerm + !!(shortBinaryNumeralTerm count)’ : ValuationTerm) 0
    (tokenSlicePostWitnessClosedTermCompositeCodePolynomial termCode)
    hfinishClosed
    (tokenSliceClosedAdd_closed startTerm (shortBinaryNumeralTerm count)
      hstartClosed hcountClosed)
    (tokenSliceClosedTerm_code_le_composite finishTerm termCode hfinishCode)
    (tokenSliceClosedAdd_code_le startTerm (shortBinaryNumeralTerm count)
      termCode hstartCode hcountCode)

theorem tokenSliceAtValuationLeStructuralEnvelope_le_closedFixed
    (valuation : Nat -> Nat) (left right : ValuationTerm) (termCode : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <= termCode)
    (hrightCode : (binaryTermCode right).length <= termCode) :
    tokenSliceAtValuationLeStructuralEnvelope valuation left right <=
      tokenSlicePostWitnessClosedTermLeFixedPayloadPolynomial termCode := by
  change appendSourcePrefixValuationLeStructuralEnvelopeAt valuation left
      right <= appendSourcePrefixLeFixedPayloadPolynomial termCode
  exact appendSourcePrefixValuationLeStructuralEnvelopeAt_le_fixed valuation
    left right termCode hleftClosed hrightClosed hleftCode hrightCode

#print axioms
  tokenSliceAtValuationCountGuardStructuralEnvelope_le_closedFixed
#print axioms
  tokenSliceAtValuationEndpointStructuralEnvelope_le_closedFixed
#print axioms tokenSliceAtValuationLeStructuralEnvelope_le_closedFixed

end FoundationCompactNumericListedDirectTokenSlicePostWitnessClosedTermAtomicFixedBounds
