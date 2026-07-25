import integration.FoundationCompactNumericListedDirectTokenSliceOffsetUniversalFullyFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixAtomicFixedBounds
import integration.FoundationCompactPABinaryNumeralAdditionBounds

/-!
# Fixed atomic resources outside the token-slice offset universal

The count guard, two endpoint equalities, and two endpoint bounds are reduced
to closed short numerals and one binary addition.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSlicePostWitnessAtomicFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixAtomicFixedBounds
open FoundationCompactNumericListedDirectTokenSlicePublicBounds

def tokenSlicePostWitnessCompositeTermCodePolynomial
    (bitBound : Nat) : Nat :=
  2 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (‘1’ : ValuationTerm)).length +
    2 * binaryFunctionTermCodeOverhead Language.Add.add + 1

def tokenSlicePostWitnessPositiveAtomicFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (tokenSlicePostWitnessCompositeTermCodePolynomial bitBound)

def tokenSlicePostWitnessLeFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  appendSourcePrefixLeFixedPayloadPolynomial
    (tokenSlicePostWitnessCompositeTermCodePolynomial bitBound)

private theorem tokenSliceAddTerm_eq_paAddTerm
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) = paAddTerm left right := by
  rfl

private theorem binaryFunctionTerm_freeVariables_tokenSlicePost
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
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem tokenSliceAddTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [tokenSliceAddTerm_eq_paAddTerm, ← finiteCaseAddTerm_eq_paAddTerm]
  exact binaryFunctionTerm_freeVariables_tokenSlicePost Language.Add.add
    left right

private theorem tokenSliceOne_closed :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem tokenSliceShort_closed (value : Nat) :
    (shortBinaryNumeralTerm value : ValuationTerm).freeVariables = ∅ :=
  shortBinaryNumeralTerm_freeVariables_eq_empty value

private theorem tokenSliceAddShort_closed (left right : Nat) :
    (‘!!(shortBinaryNumeralTerm left) +
      !!(shortBinaryNumeralTerm right)’ : ValuationTerm).freeVariables = ∅ := by
  rw [tokenSliceAddTerm_freeVariables, tokenSliceShort_closed,
    tokenSliceShort_closed]
  simp

private theorem tokenSliceAddOne_closed (value : Nat) :
    (‘!!(shortBinaryNumeralTerm value) + 1’ :
      ValuationTerm).freeVariables = ∅ := by
  rw [tokenSliceAddTerm_freeVariables, tokenSliceShort_closed,
    tokenSliceOne_closed]
  simp

private theorem tokenSliceShort_code_le
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      tokenSlicePostWitnessCompositeTermCodePolynomial bitBound := by
  have hraw := binaryNumeralTerm_code_length_le_envelope value bitBound hvalue
  unfold tokenSlicePostWitnessCompositeTermCodePolynomial
  omega

private theorem tokenSliceAddShort_code_le
    (left right bitBound : Nat)
    (hleft : Nat.size left <= bitBound)
    (hright : Nat.size right <= bitBound) :
    (binaryTermCode
      (‘!!(shortBinaryNumeralTerm left) +
        !!(shortBinaryNumeralTerm right)’ : ValuationTerm)).length <=
      tokenSlicePostWitnessCompositeTermCodePolynomial bitBound := by
  have hleftCode :=
    binaryNumeralTerm_code_length_le_envelope left bitBound hleft
  have hrightCode :=
    binaryNumeralTerm_code_length_le_envelope right bitBound hright
  have hraw := paAddTerm_code_length_le
    (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right)
  rw [tokenSliceAddTerm_eq_paAddTerm]
  unfold tokenSlicePostWitnessCompositeTermCodePolynomial
  omega

private theorem tokenSliceAddOne_code_le
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode
      (‘!!(shortBinaryNumeralTerm value) + 1’ : ValuationTerm)).length <=
      tokenSlicePostWitnessCompositeTermCodePolynomial bitBound := by
  have hvalueCode :=
    binaryNumeralTerm_code_length_le_envelope value bitBound hvalue
  have hraw := paAddTerm_code_length_le
    (shortBinaryNumeralTerm value) (‘1’ : ValuationTerm)
  change (binaryTermCode
    (‘!!(shortBinaryNumeralTerm value) +
      !!(‘1’ : ValuationTerm)’ : ValuationTerm)).length <= _
  rw [tokenSliceAddTerm_eq_paAddTerm]
  unfold tokenSlicePostWitnessCompositeTermCodePolynomial
  omega

theorem tokenSliceAtValuationCountGuardStructuralEnvelope_le_fixed
    (valuation : Nat -> Nat)
    (tokenCount count bitBound : Nat)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcountSize : Nat.size count <= bitBound) :
    tokenSliceAtValuationCountGuardStructuralEnvelope valuation
        (shortBinaryNumeralTerm tokenCount) count <=
      tokenSlicePostWitnessPositiveAtomicFixedPayloadPolynomial bitBound := by
  unfold tokenSliceAtValuationCountGuardStructuralEnvelope
    tokenSlicePostWitnessPositiveAtomicFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed valuation
    Language.ORing.Rel.lt (shortBinaryNumeralTerm count)
    (‘!!(shortBinaryNumeralTerm tokenCount) + 1’ : ValuationTerm)
    0 (tokenSlicePostWitnessCompositeTermCodePolynomial bitBound)
    (tokenSliceShort_closed count) (tokenSliceAddOne_closed tokenCount)
    (tokenSliceShort_code_le count bitBound hcountSize)
    (tokenSliceAddOne_code_le tokenCount bitBound htokenCountSize)

theorem tokenSliceAtValuationEndpointStructuralEnvelope_le_fixed
    (valuation : Nat -> Nat)
    (start finish count bitBound : Nat)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hcountSize : Nat.size count <= bitBound) :
    tokenSliceAtValuationEndpointStructuralEnvelope valuation
        (shortBinaryNumeralTerm start) (shortBinaryNumeralTerm finish)
        count <=
      tokenSlicePostWitnessPositiveAtomicFixedPayloadPolynomial bitBound := by
  unfold tokenSliceAtValuationEndpointStructuralEnvelope
    tokenSlicePostWitnessPositiveAtomicFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed valuation
    Language.Eq.eq (shortBinaryNumeralTerm finish)
    (‘!!(shortBinaryNumeralTerm start) +
      !!(shortBinaryNumeralTerm count)’ : ValuationTerm)
    0 (tokenSlicePostWitnessCompositeTermCodePolynomial bitBound)
    (tokenSliceShort_closed finish) (tokenSliceAddShort_closed start count)
    (tokenSliceShort_code_le finish bitBound hfinishSize)
    (tokenSliceAddShort_code_le start count bitBound hstartSize hcountSize)

theorem tokenSliceAtValuationLeStructuralEnvelope_le_fixed
    (valuation : Nat -> Nat)
    (left right bitBound : Nat)
    (hleftSize : Nat.size left <= bitBound)
    (hrightSize : Nat.size right <= bitBound) :
    tokenSliceAtValuationLeStructuralEnvelope valuation
        (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right) <=
      tokenSlicePostWitnessLeFixedPayloadPolynomial bitBound := by
  change appendSourcePrefixValuationLeStructuralEnvelopeAt valuation
      (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right) <=
    appendSourcePrefixLeFixedPayloadPolynomial
      (tokenSlicePostWitnessCompositeTermCodePolynomial bitBound)
  exact appendSourcePrefixValuationLeStructuralEnvelopeAt_le_fixed valuation
    (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right)
    (tokenSlicePostWitnessCompositeTermCodePolynomial bitBound)
    (tokenSliceShort_closed left) (tokenSliceShort_closed right)
    (tokenSliceShort_code_le left bitBound hleftSize)
    (tokenSliceShort_code_le right bitBound hrightSize)

#print axioms tokenSliceAtValuationCountGuardStructuralEnvelope_le_fixed
#print axioms tokenSliceAtValuationEndpointStructuralEnvelope_le_fixed
#print axioms tokenSliceAtValuationLeStructuralEnvelope_le_fixed

end FoundationCompactNumericListedDirectTokenSlicePostWitnessAtomicFixedBounds
