import integration.FoundationCompactNumericListedDirectNatListAppendSlicesPublicBounds
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
import integration.FoundationCompactNumericListedDirectTokenSliceClosedTermFullyFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds

/-! # Fixed resources for the two concrete append-slice witnesses -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectNatListAppendSlicesFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceClosedTermFullyFixedBounds

private theorem appendSlicesArithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem appendSlicesTermValue_add
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [appendSlicesArithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem appendSlicesAddTerm_eq_paAddTerm
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) = paAddTerm left right := by
  rfl

private theorem appendSlicesSuccessorTerm_eq_paAddTerm
    (term : ValuationTerm) :
    successorTerm term = paAddTerm term (‘1’ : ValuationTerm) := by
  rfl

private theorem appendSlicesMidpointTerm_eq_paAddTerm
    (targetStartTerm leftCountTerm : ValuationTerm) :
    appendMidpointTerm targetStartTerm leftCountTerm =
      paAddTerm (successorTerm targetStartTerm) leftCountTerm := by
  rfl

def appendSlicesTokenSlicesFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  2 *
    compactFixedWidthTokenSlicesEqAtValuationClosedTermFullyFixedPayloadPolynomial
      numericBound (appendSourcePrefixCompositeTermCodePolynomial bitBound)
      bitBound

def appendSlicesCountFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (appendSourcePrefixCompositeTermCodePolynomial bitBound)

private theorem appendSlicesMidpoint_code_le
    (targetStart leftCount bitBound : Nat)
    (htarget : Nat.size targetStart <= bitBound)
    (hleft : Nat.size leftCount <= bitBound) :
    (binaryTermCode
      (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm leftCount))).length <=
      appendSourcePrefixCompositeTermCodePolynomial bitBound := by
  have htargetCode :=
    binaryNumeralTerm_code_length_le_envelope targetStart bitBound htarget
  have hleftCode :=
    binaryNumeralTerm_code_length_le_envelope leftCount bitBound hleft
  have hsuccessorRaw :
      (binaryTermCode
        (successorTerm (shortBinaryNumeralTerm targetStart))).length <=
      (binaryTermCode (shortBinaryNumeralTerm targetStart)).length +
        (binaryTermCode (‘1’ : ValuationTerm)).length +
        binaryFunctionTermCodeOverhead Language.Add.add := by
    rw [appendSlicesSuccessorTerm_eq_paAddTerm]
    exact paAddTerm_code_length_le
      (shortBinaryNumeralTerm targetStart) (‘1’ : ValuationTerm)
  have hmidpointRaw := paAddTerm_code_length_le
    (successorTerm (shortBinaryNumeralTerm targetStart))
    (shortBinaryNumeralTerm leftCount)
  rw [appendSlicesMidpointTerm_eq_paAddTerm]
  unfold appendSourcePrefixCompositeTermCodePolynomial
  omega

private theorem appendSlicesMidpoint_closed
    (targetStart leftCount : Nat) :
    (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
      (shortBinaryNumeralTerm leftCount)).freeVariables = ∅ := by
  unfold appendMidpointTerm successorTerm
  rw [arithmeticAddTerm_freeVariables_eq_union,
    arithmeticAddTerm_freeVariables_eq_union,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    shortBinaryNumeralTerm_freeVariables_eq_empty]
  have hone : (‘1’ : ValuationTerm).freeVariables = ∅ := by
    simp [LO.FirstOrder.Semiterm.Operator.operator]
  rw [hone]
  simp

private theorem appendSlicesMidpoint_value
    (targetStart leftCount : Nat) :
    termValue zeroValuation
      (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm leftCount)) =
      targetStart + 1 + leftCount := by
  unfold appendMidpointTerm successorTerm
  rw [appendSlicesTermValue_add, appendSlicesTermValue_add,
    termValue_shortBinaryNumeralTerm, termValue_shortBinaryNumeralTerm]
  have hone : termValue zeroValuation (‘1’ : ValuationTerm) = 1 := by
    exact termValue_one zeroValuation ![]
  rw [hone]

theorem appendSlicesCountPayloadEnvelope_le_fixed
    (leftCount rightCount targetCount bitBound : Nat)
    (hleftSize : Nat.size leftCount <= bitBound)
    (hrightSize : Nat.size rightCount <= bitBound)
    (htargetSize : Nat.size targetCount <= bitBound) :
    appendSlicesCountPayloadEnvelope leftCount rightCount targetCount <=
      appendSlicesCountFixedPayloadPolynomial bitBound := by
  let leftTerm := shortBinaryNumeralTerm targetCount
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm leftCount) +
      !!(shortBinaryNumeralTerm rightCount)’
  let termCode := appendSourcePrefixCompositeTermCodePolynomial bitBound
  have hleftCode : (binaryTermCode leftTerm).length <= termCode :=
    appendSourcePrefixShortNumeral_code_le targetCount bitBound htargetSize
  have hrightCode : (binaryTermCode rightTerm).length <= termCode := by
    have hfirst :=
      binaryNumeralTerm_code_length_le_envelope leftCount bitBound hleftSize
    have hsecond :=
      binaryNumeralTerm_code_length_le_envelope rightCount bitBound hrightSize
    have hraw := paAddTerm_code_length_le
      (shortBinaryNumeralTerm leftCount)
      (shortBinaryNumeralTerm rightCount)
    dsimp only [rightTerm, termCode]
    rw [appendSlicesAddTerm_eq_paAddTerm]
    unfold appendSourcePrefixCompositeTermCodePolynomial
    omega
  have hleftClosed : leftTerm.freeVariables = ∅ := by
    exact shortBinaryNumeralTerm_freeVariables_eq_empty targetCount
  have hrightClosed : rightTerm.freeVariables = ∅ := by
    dsimp only [rightTerm]
    rw [arithmeticAddTerm_freeVariables_eq_union,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  unfold appendSlicesCountPayloadEnvelope
    appendSlicesCountFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed
    zeroValuation Language.Eq.eq leftTerm rightTerm 0 termCode
      hleftClosed hrightClosed hleftCode hrightCode

theorem appendSlicesTokenSlicesResource_le_fixed
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListAppendSlices tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    let leftSliceCount := Classical.choose hgraph.2.1
    let rightSliceCount := Classical.choose hgraph.2.2
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope
          zeroValuation
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (successorTerm (shortBinaryNumeralTerm leftStart))
          (shortBinaryNumeralTerm leftFinish)
          (successorTerm (shortBinaryNumeralTerm targetStart))
          (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
            (shortBinaryNumeralTerm leftCount))
          leftSliceCount +
        compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope
          zeroValuation
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (successorTerm (shortBinaryNumeralTerm rightStart))
          (shortBinaryNumeralTerm rightFinish)
          (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
            (shortBinaryNumeralTerm leftCount))
          (shortBinaryNumeralTerm targetFinish)
          rightSliceCount <=
      appendSlicesTokenSlicesFixedPayloadPolynomial numericBound bitBound := by
  let leftSliceCount := Classical.choose hgraph.2.1
  let rightSliceCount := Classical.choose hgraph.2.2
  let termCode := appendSourcePrefixCompositeTermCodePolynomial bitBound
  have hleftSpec :
      leftSliceCount <= tokenCount /\
      leftFinish = leftStart + 1 + leftSliceCount /\
      targetStart + 1 + leftCount =
        targetStart + 1 + leftSliceCount /\
      leftFinish <= tokenCount /\
      targetStart + 1 + leftCount <= tokenCount /\
      ∀ offset < leftSliceCount, ∀ bitIndex < width,
        tokenTable.testBit ((leftStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + offset) * width + bitIndex) := by
    simpa [leftSliceCount, Nat.add_assoc] using
      Classical.choose_spec hgraph.2.1
  have hrightSpec :
      rightSliceCount <= tokenCount /\
      rightFinish = rightStart + 1 + rightSliceCount /\
      targetFinish = targetStart + 1 + leftCount + rightSliceCount /\
      rightFinish <= tokenCount /\
      targetFinish <= tokenCount /\
      ∀ offset < rightSliceCount, ∀ bitIndex < width,
        tokenTable.testBit ((rightStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + leftCount + offset) * width + bitIndex) := by
    simpa [rightSliceCount, Nat.add_assoc] using
      Classical.choose_spec hgraph.2.2
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidthBound).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCountBound).trans hnumericSize
  have hleftCountBound : leftSliceCount <= numericBound :=
    hleftSpec.1.trans htokenCountBound
  have hrightCountBound : rightSliceCount <= numericBound :=
    hrightSpec.1.trans htokenCountBound
  have hleftCountSize : Nat.size leftSliceCount <= bitBound :=
    (Nat.size_le_size hleftCountBound).trans hnumericSize
  have hrightCountSize : Nat.size rightSliceCount <= bitBound :=
    (Nat.size_le_size hrightCountBound).trans hnumericSize
  have hleftStartSize : Nat.size leftStart <= bitBound :=
    (Nat.size_le_size (show leftStart <= numericBound by omega)).trans
      hnumericSize
  have hleftFinishSize : Nat.size leftFinish <= bitBound :=
    (Nat.size_le_size (show leftFinish <= numericBound by omega)).trans
      hnumericSize
  have hleftPublicCountSize : Nat.size leftCount <= bitBound :=
    (Nat.size_le_size (show leftCount <= numericBound by omega)).trans
      hnumericSize
  have hrightStartSize : Nat.size rightStart <= bitBound :=
    (Nat.size_le_size (show rightStart <= numericBound by omega)).trans
      hnumericSize
  have hrightFinishSize : Nat.size rightFinish <= bitBound :=
    (Nat.size_le_size (show rightFinish <= numericBound by omega)).trans
      hnumericSize
  have htargetStartSize : Nat.size targetStart <= bitBound :=
    (Nat.size_le_size (show targetStart <= numericBound by omega)).trans
      hnumericSize
  have htargetFinishSize : Nat.size targetFinish <= bitBound :=
    (Nat.size_le_size (show targetFinish <= numericBound by omega)).trans
      hnumericSize
  have hleftResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_closedFixed
      zeroValuation tokenTable width leftSliceCount numericBound termCode
      bitBound
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm leftCount))
      (appendSourcePrefixShortNumeral_code_le tokenTable bitBound htableSize)
      (appendSourcePrefixShortNumeral_code_le width bitBound hwidthSize)
      (appendSourcePrefixShortNumeral_code_le leftSliceCount bitBound
        hleftCountSize)
      (appendSourcePrefixShortNumeral_code_le tokenCount bitBound
        htokenCountSize)
      (appendSourcePrefixSuccessorShortNumeral_code_le leftStart bitBound
        hleftStartSize)
      (appendSourcePrefixShortNumeral_code_le leftFinish bitBound
        hleftFinishSize)
      (appendSourcePrefixSuccessorShortNumeral_code_le targetStart bitBound
        htargetStartSize)
      (appendSlicesMidpoint_code_le targetStart leftCount bitBound
        htargetStartSize hleftPublicCountSize)
      (appendSourcePrefixShortNumeral_closed tokenCount)
      (appendSourcePrefixSuccessorShortNumeral_closed leftStart)
      (appendSourcePrefixShortNumeral_closed leftFinish)
      (appendSourcePrefixSuccessorShortNumeral_closed targetStart)
      (appendSlicesMidpoint_closed targetStart leftCount)
      hwidthBound (by
        simpa [termValue_shortBinaryNumeralTerm] using
          (show leftStart + 1 <= numericBound by omega))
      (by
        simpa [termValue_shortBinaryNumeralTerm] using
          (show targetStart + 1 <= numericBound by omega))
      hleftCountBound htableSize hwidthSize hnumericSize
  have hrightResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_closedFixed
      zeroValuation tokenTable width rightSliceCount numericBound termCode
      bitBound
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm rightStart))
      (shortBinaryNumeralTerm rightFinish)
      (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish)
      (appendSourcePrefixShortNumeral_code_le tokenTable bitBound htableSize)
      (appendSourcePrefixShortNumeral_code_le width bitBound hwidthSize)
      (appendSourcePrefixShortNumeral_code_le rightSliceCount bitBound
        hrightCountSize)
      (appendSourcePrefixShortNumeral_code_le tokenCount bitBound
        htokenCountSize)
      (appendSourcePrefixSuccessorShortNumeral_code_le rightStart bitBound
        hrightStartSize)
      (appendSourcePrefixShortNumeral_code_le rightFinish bitBound
        hrightFinishSize)
      (appendSlicesMidpoint_code_le targetStart leftCount bitBound
        htargetStartSize hleftPublicCountSize)
      (appendSourcePrefixShortNumeral_code_le targetFinish bitBound
        htargetFinishSize)
      (appendSourcePrefixShortNumeral_closed tokenCount)
      (appendSourcePrefixSuccessorShortNumeral_closed rightStart)
      (appendSourcePrefixShortNumeral_closed rightFinish)
      (appendSlicesMidpoint_closed targetStart leftCount)
      (appendSourcePrefixShortNumeral_closed targetFinish)
      hwidthBound (by
        simpa [termValue_shortBinaryNumeralTerm] using
          (show rightStart + 1 <= numericBound by omega))
      (by
        rw [appendSlicesMidpoint_value]
        exact
          (show targetStart + 1 + leftCount <= numericBound by omega))
      hrightCountBound htableSize hwidthSize hnumericSize
  unfold appendSlicesTokenSlicesFixedPayloadPolynomial
  dsimp only [leftSliceCount, rightSliceCount, termCode] at hleftResource hrightResource ⊢
  simpa only [two_mul] using Nat.add_le_add hleftResource hrightResource

#print axioms appendSlicesTokenSlicesResource_le_fixed
#print axioms appendSlicesCountPayloadEnvelope_le_fixed

end FoundationCompactNumericListedDirectNatListAppendSlicesFixedBounds
