import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixAtomicFixedBounds
import integration.FoundationCompactPABinaryNumeralAdditionBounds

/-!
# Fixed concrete arithmetic resources for source-prefix append

All short numerals, successors, and binary sums appearing in the three
arithmetic leaves are bounded by one bit-width coordinate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixAtomicFixedBounds

def appendSourcePrefixCompositeTermCodePolynomial (bitBound : Nat) : Nat :=
  2 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (‘1’ : ValuationTerm)).length +
    2 * binaryFunctionTermCodeOverhead Language.Add.add + 1

theorem appendSourcePrefixAddTerm_eq_paAddTerm
    (left right : ValuationTerm) :
    addTerm left right = paAddTerm left right := by
  rfl

theorem appendSourcePrefixBinaryFunction_freeVariables
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

theorem appendSourcePrefixAddTerm_freeVariables
    (left right : ValuationTerm) :
    (addTerm left right).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [appendSourcePrefixAddTerm_eq_paAddTerm]
  rw [← finiteCaseAddTerm_eq_paAddTerm]
  exact appendSourcePrefixBinaryFunction_freeVariables Language.Add.add left
    right

theorem appendSourcePrefixSuccessorTerm_eq_paAddTerm
    (term : ValuationTerm) :
    successorTerm term = paAddTerm term (‘1’ : ValuationTerm) := by
  rfl

theorem appendSourcePrefixOne_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

theorem appendSourcePrefixSuccessorTerm_freeVariables
    (term : ValuationTerm) :
    (successorTerm term).freeVariables = term.freeVariables := by
  change (addTerm term (‘1’ : ValuationTerm)).freeVariables =
    term.freeVariables
  rw [appendSourcePrefixAddTerm_freeVariables,
    appendSourcePrefixOne_freeVariables_eq_empty]
  simp

theorem appendSourcePrefixShortNumeral_code_le
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      appendSourcePrefixCompositeTermCodePolynomial bitBound := by
  have hraw :=
    binaryNumeralTerm_code_length_le_envelope value bitBound hvalue
  unfold appendSourcePrefixCompositeTermCodePolynomial
  omega

theorem appendSourcePrefixSuccessorShortNumeral_code_le
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode
      (successorTerm (shortBinaryNumeralTerm value))).length <=
        appendSourcePrefixCompositeTermCodePolynomial bitBound := by
  have hvalueCode :=
    binaryNumeralTerm_code_length_le_envelope value bitBound hvalue
  have hraw := paAddTerm_code_length_le
    (shortBinaryNumeralTerm value) (‘1’ : ValuationTerm)
  rw [appendSourcePrefixSuccessorTerm_eq_paAddTerm]
  unfold appendSourcePrefixCompositeTermCodePolynomial
  omega

theorem appendSourcePrefixAddShortNumerals_code_le
    (left right bitBound : Nat)
    (hleft : Nat.size left <= bitBound)
    (hright : Nat.size right <= bitBound) :
    (binaryTermCode
      (addTerm (shortBinaryNumeralTerm left)
        (shortBinaryNumeralTerm right))).length <=
      appendSourcePrefixCompositeTermCodePolynomial bitBound := by
  have hleftCode :=
    binaryNumeralTerm_code_length_le_envelope left bitBound hleft
  have hrightCode :=
    binaryNumeralTerm_code_length_le_envelope right bitBound hright
  have hraw := paAddTerm_code_length_le
    (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right)
  rw [appendSourcePrefixAddTerm_eq_paAddTerm]
  unfold appendSourcePrefixCompositeTermCodePolynomial
  omega

theorem appendSourcePrefixAddSuccessorAndShort_code_le
    (left right bitBound : Nat)
    (hleft : Nat.size left <= bitBound)
    (hright : Nat.size right <= bitBound) :
    (binaryTermCode
      (addTerm (successorTerm (shortBinaryNumeralTerm left))
        (shortBinaryNumeralTerm right))).length <=
      appendSourcePrefixCompositeTermCodePolynomial bitBound := by
  have hleftCode :=
    binaryNumeralTerm_code_length_le_envelope left bitBound hleft
  have hrightCode :=
    binaryNumeralTerm_code_length_le_envelope right bitBound hright
  have hsuccessorRaw := paAddTerm_code_length_le
    (shortBinaryNumeralTerm left) (‘1’ : ValuationTerm)
  have haddRaw := paAddTerm_code_length_le
    (successorTerm (shortBinaryNumeralTerm left))
    (shortBinaryNumeralTerm right)
  rw [appendSourcePrefixSuccessorTerm_eq_paAddTerm] at haddRaw
  rw [appendSourcePrefixSuccessorTerm_eq_paAddTerm]
  rw [appendSourcePrefixAddTerm_eq_paAddTerm]
  unfold appendSourcePrefixCompositeTermCodePolynomial
  omega

theorem appendSourcePrefixShortNumeral_closed (value : Nat) :
    (shortBinaryNumeralTerm value : ValuationTerm).freeVariables = ∅ :=
  shortBinaryNumeralTerm_freeVariables_eq_empty value

theorem appendSourcePrefixSuccessorShortNumeral_closed (value : Nat) :
    (successorTerm
      (shortBinaryNumeralTerm value : ValuationTerm)).freeVariables = ∅ := by
  rw [appendSourcePrefixSuccessorTerm_freeVariables,
    appendSourcePrefixShortNumeral_closed]

theorem appendSourcePrefixAddShortNumerals_closed
    (left right : Nat) :
    (addTerm (shortBinaryNumeralTerm left)
      (shortBinaryNumeralTerm right) : ValuationTerm).freeVariables = ∅ := by
  rw [appendSourcePrefixAddTerm_freeVariables,
    appendSourcePrefixShortNumeral_closed,
    appendSourcePrefixShortNumeral_closed]
  simp

theorem appendSourcePrefixAddSuccessorAndShort_closed
    (left right : Nat) :
    (addTerm (successorTerm (shortBinaryNumeralTerm left))
      (shortBinaryNumeralTerm right) : ValuationTerm).freeVariables = ∅ := by
  rw [appendSourcePrefixAddTerm_freeVariables,
    appendSourcePrefixSuccessorShortNumeral_closed,
    appendSourcePrefixShortNumeral_closed]
  simp

def appendSourcePrefixArithmeticLeavesFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  2 * appendSourcePrefixLeFixedPayloadPolynomial
      (appendSourcePrefixCompositeTermCodePolynomial bitBound) +
    appendSourcePrefixAtomicFixedPayloadPolynomial
      (appendSourcePrefixCompositeTermCodePolynomial bitBound)

theorem appendSourcePrefixArithmeticLeavesResource_le_fixed
    (sourceStart sourceFinish sourceCount prefixCount leftCount targetCount
      bitBound : Nat)
    (hsourceStart : Nat.size sourceStart <= bitBound)
    (hsourceFinish : Nat.size sourceFinish <= bitBound)
    (hsourceCount : Nat.size sourceCount <= bitBound)
    (hprefixCount : Nat.size prefixCount <= bitBound)
    (hleftCount : Nat.size leftCount <= bitBound)
    (htargetCount : Nat.size targetCount <= bitBound) :
    appendSourcePrefixValuationLeStructuralEnvelope
          (shortBinaryNumeralTerm prefixCount)
          (shortBinaryNumeralTerm sourceCount) +
        appendSourcePrefixValuationLeStructuralEnvelope
          (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
            (shortBinaryNumeralTerm prefixCount))
          (shortBinaryNumeralTerm sourceFinish) +
      appendSourcePrefixValuationEqStructuralEnvelope
        (shortBinaryNumeralTerm targetCount)
        (addTerm (shortBinaryNumeralTerm leftCount)
          (shortBinaryNumeralTerm prefixCount)) <=
      appendSourcePrefixArithmeticLeavesFixedPayloadPolynomial bitBound := by
  let termCode := appendSourcePrefixCompositeTermCodePolynomial bitBound
  have hprefix :=
    appendSourcePrefixValuationLeStructuralEnvelope_le_fixed
      (shortBinaryNumeralTerm prefixCount)
      (shortBinaryNumeralTerm sourceCount) termCode
      (appendSourcePrefixShortNumeral_closed prefixCount)
      (appendSourcePrefixShortNumeral_closed sourceCount)
      (appendSourcePrefixShortNumeral_code_le prefixCount bitBound
        hprefixCount)
      (appendSourcePrefixShortNumeral_code_le sourceCount bitBound
        hsourceCount)
  have hwithin :=
    appendSourcePrefixValuationLeStructuralEnvelope_le_fixed
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (shortBinaryNumeralTerm sourceFinish) termCode
      (appendSourcePrefixAddSuccessorAndShort_closed sourceStart prefixCount)
      (appendSourcePrefixShortNumeral_closed sourceFinish)
      (appendSourcePrefixAddSuccessorAndShort_code_le sourceStart prefixCount
        bitBound hsourceStart hprefixCount)
      (appendSourcePrefixShortNumeral_code_le sourceFinish bitBound
        hsourceFinish)
  have hcount :=
    appendSourcePrefixValuationEqStructuralEnvelope_le_fixed
      (shortBinaryNumeralTerm targetCount)
      (addTerm (shortBinaryNumeralTerm leftCount)
        (shortBinaryNumeralTerm prefixCount))
      termCode (appendSourcePrefixShortNumeral_closed targetCount)
      (appendSourcePrefixAddShortNumerals_closed leftCount prefixCount)
      (appendSourcePrefixShortNumeral_code_le targetCount bitBound
        htargetCount)
      (appendSourcePrefixAddShortNumerals_code_le leftCount prefixCount
        bitBound hleftCount hprefixCount)
  unfold appendSourcePrefixArithmeticLeavesFixedPayloadPolynomial
  dsimp only [termCode] at hprefix hwithin hcount ⊢
  omega

#print axioms appendSourcePrefixArithmeticLeavesResource_le_fixed

end FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
