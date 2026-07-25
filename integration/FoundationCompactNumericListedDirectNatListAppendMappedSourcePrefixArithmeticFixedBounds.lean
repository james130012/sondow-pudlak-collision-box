import integration.FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixPublicBounds
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds

/-!
# Fixed arithmetic resources for mapped source-prefix append

The mapped graph adds positivity and target-finish leaves to the three
arithmetic leaves of ordinary source-prefix append.  All five are closed terms
with one common fixed code coordinate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixArithmeticFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixAtomicFixedBounds

def appendMappedSourcePrefixArithmeticLeavesFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  3 * appendSourcePrefixLeFixedPayloadPolynomial
      (appendSourcePrefixCompositeTermCodePolynomial bitBound) +
    2 * appendSourcePrefixAtomicFixedPayloadPolynomial
      (appendSourcePrefixCompositeTermCodePolynomial bitBound)

theorem appendMappedSourcePrefixArithmeticLeavesResource_le_fixed
    (sourceStart sourceFinish sourceCount prefixCount targetStart targetFinish
      targetCount leftCount bitBound : Nat)
    (hsourceStart : Nat.size sourceStart <= bitBound)
    (hsourceFinish : Nat.size sourceFinish <= bitBound)
    (hsourceCount : Nat.size sourceCount <= bitBound)
    (hprefixCount : Nat.size prefixCount <= bitBound)
    (htargetStart : Nat.size targetStart <= bitBound)
    (htargetFinish : Nat.size targetFinish <= bitBound)
    (htargetCount : Nat.size targetCount <= bitBound)
    (hleftCount : Nat.size leftCount <= bitBound) :
    mappedSourcePrefixValuationLeStructuralEnvelope
          (‘1’ : ValuationTerm) (shortBinaryNumeralTerm prefixCount) +
        mappedSourcePrefixValuationLeStructuralEnvelope
          (shortBinaryNumeralTerm prefixCount)
          (shortBinaryNumeralTerm sourceCount) +
        mappedSourcePrefixValuationLeStructuralEnvelope
          (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
            (shortBinaryNumeralTerm prefixCount))
          (shortBinaryNumeralTerm sourceFinish) +
        mappedSourcePrefixValuationEqStructuralEnvelope
          (shortBinaryNumeralTerm targetFinish)
          (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
            (shortBinaryNumeralTerm targetCount)) +
      mappedSourcePrefixValuationEqStructuralEnvelope
        (shortBinaryNumeralTerm targetCount)
        (addTerm (shortBinaryNumeralTerm leftCount)
          (shortBinaryNumeralTerm prefixCount)) <=
      appendMappedSourcePrefixArithmeticLeavesFixedPayloadPolynomial
        bitBound := by
  let termCode := appendSourcePrefixCompositeTermCodePolynomial bitBound
  have honeCode :
      (binaryTermCode (‘1’ : ValuationTerm)).length <= termCode := by
    unfold termCode appendSourcePrefixCompositeTermCodePolynomial
    omega
  have hpositive :
      mappedSourcePrefixValuationLeStructuralEnvelope
          (‘1’ : ValuationTerm) (shortBinaryNumeralTerm prefixCount) <=
        appendSourcePrefixLeFixedPayloadPolynomial termCode := by
    change appendSourcePrefixValuationLeStructuralEnvelope
        (‘1’ : ValuationTerm) (shortBinaryNumeralTerm prefixCount) <= _
    exact appendSourcePrefixValuationLeStructuralEnvelope_le_fixed
      (‘1’ : ValuationTerm) (shortBinaryNumeralTerm prefixCount) termCode
      appendSourcePrefixOne_freeVariables_eq_empty
      (appendSourcePrefixShortNumeral_closed prefixCount) honeCode
      (appendSourcePrefixShortNumeral_code_le prefixCount bitBound
        hprefixCount)
  have hprefix :
      mappedSourcePrefixValuationLeStructuralEnvelope
          (shortBinaryNumeralTerm prefixCount)
          (shortBinaryNumeralTerm sourceCount) <=
        appendSourcePrefixLeFixedPayloadPolynomial termCode := by
    change appendSourcePrefixValuationLeStructuralEnvelope
      (shortBinaryNumeralTerm prefixCount)
      (shortBinaryNumeralTerm sourceCount) <= _
    exact appendSourcePrefixValuationLeStructuralEnvelope_le_fixed
      (shortBinaryNumeralTerm prefixCount)
      (shortBinaryNumeralTerm sourceCount) termCode
      (appendSourcePrefixShortNumeral_closed prefixCount)
      (appendSourcePrefixShortNumeral_closed sourceCount)
      (appendSourcePrefixShortNumeral_code_le prefixCount bitBound hprefixCount)
      (appendSourcePrefixShortNumeral_code_le sourceCount bitBound hsourceCount)
  have hwithin :
      mappedSourcePrefixValuationLeStructuralEnvelope
          (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
            (shortBinaryNumeralTerm prefixCount))
          (shortBinaryNumeralTerm sourceFinish) <=
        appendSourcePrefixLeFixedPayloadPolynomial termCode := by
    change appendSourcePrefixValuationLeStructuralEnvelope
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (shortBinaryNumeralTerm sourceFinish) <= _
    exact appendSourcePrefixValuationLeStructuralEnvelope_le_fixed
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (shortBinaryNumeralTerm sourceFinish) termCode
      (appendSourcePrefixAddSuccessorAndShort_closed sourceStart prefixCount)
      (appendSourcePrefixShortNumeral_closed sourceFinish)
      (appendSourcePrefixAddSuccessorAndShort_code_le sourceStart prefixCount
        bitBound hsourceStart hprefixCount)
      (appendSourcePrefixShortNumeral_code_le sourceFinish bitBound
        hsourceFinish)
  have htarget :
      mappedSourcePrefixValuationEqStructuralEnvelope
          (shortBinaryNumeralTerm targetFinish)
          (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
            (shortBinaryNumeralTerm targetCount)) <=
        appendSourcePrefixAtomicFixedPayloadPolynomial termCode := by
    change appendSourcePrefixValuationEqStructuralEnvelope
      (shortBinaryNumeralTerm targetFinish)
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm targetCount)) <= _
    exact appendSourcePrefixValuationEqStructuralEnvelope_le_fixed
      (shortBinaryNumeralTerm targetFinish)
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm targetCount))
      termCode (appendSourcePrefixShortNumeral_closed targetFinish)
      (appendSourcePrefixAddSuccessorAndShort_closed targetStart targetCount)
      (appendSourcePrefixShortNumeral_code_le targetFinish bitBound
        htargetFinish)
      (appendSourcePrefixAddSuccessorAndShort_code_le targetStart targetCount
        bitBound htargetStart htargetCount)
  have hcount :
      mappedSourcePrefixValuationEqStructuralEnvelope
          (shortBinaryNumeralTerm targetCount)
          (addTerm (shortBinaryNumeralTerm leftCount)
            (shortBinaryNumeralTerm prefixCount)) <=
        appendSourcePrefixAtomicFixedPayloadPolynomial termCode := by
    change appendSourcePrefixValuationEqStructuralEnvelope
      (shortBinaryNumeralTerm targetCount)
      (addTerm (shortBinaryNumeralTerm leftCount)
        (shortBinaryNumeralTerm prefixCount)) <= _
    exact appendSourcePrefixValuationEqStructuralEnvelope_le_fixed
      (shortBinaryNumeralTerm targetCount)
      (addTerm (shortBinaryNumeralTerm leftCount)
        (shortBinaryNumeralTerm prefixCount))
      termCode (appendSourcePrefixShortNumeral_closed targetCount)
      (appendSourcePrefixAddShortNumerals_closed leftCount prefixCount)
      (appendSourcePrefixShortNumeral_code_le targetCount bitBound
        htargetCount)
      (appendSourcePrefixAddShortNumerals_code_le leftCount prefixCount
        bitBound hleftCount hprefixCount)
  unfold appendMappedSourcePrefixArithmeticLeavesFixedPayloadPolynomial
  dsimp only [termCode] at hpositive hprefix hwithin htarget hcount ⊢
  omega

#print axioms appendMappedSourcePrefixArithmeticLeavesResource_le_fixed

end FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixArithmeticFixedBounds
