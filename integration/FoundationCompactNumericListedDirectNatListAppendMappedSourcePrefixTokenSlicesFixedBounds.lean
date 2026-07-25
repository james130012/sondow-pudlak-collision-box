import integration.FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixArithmeticFixedBounds
import integration.FoundationCompactNumericListedDirectTokenSliceClosedTermFullyFixedBounds

/-!
# Fixed resources for mapped source-prefix token slices

The graph supplies both slice witnesses.  The second slice uses the genuine
`+ 2` source and target offsets; their nested term codes are bounded directly.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 150000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixTokenSlicesFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefix
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixArithmeticFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceClosedTermFullyFixedBounds

def appendMappedSourcePrefixSliceTermCodePolynomial (bitBound : Nat) : Nat :=
  3 * appendSourcePrefixCompositeTermCodePolynomial bitBound +
    2 * (binaryTermCode
      (FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixExplicitHybridCertificate.twoTerm)).length +
    3 * binaryFunctionTermCodeOverhead Language.Add.add + 1

private theorem mappedAddTerm_eq_paAddTerm
    (left right : ValuationTerm) :
    FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixExplicitHybridCertificate.addTerm
      left right = paAddTerm left right := by
  rfl

private theorem mappedAddTerm_freeVariables
    (left right : ValuationTerm) :
    (FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixExplicitHybridCertificate.addTerm
      left right).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  rw [mappedAddTerm_eq_paAddTerm, ← finiteCaseAddTerm_eq_paAddTerm]
  exact appendSourcePrefixAddTerm_freeVariables left right

private theorem mappedTwoTerm_closed :
    (FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixExplicitHybridCertificate.twoTerm).freeVariables =
      ∅ := by
  change ((‘2’ : ValuationTerm)).freeVariables = ∅
  ext x
  simp [Semiterm.Operator.numeral, Semiterm.Operator.foldr,
    Semiterm.Operator.operator, Semiterm.Operator.comp,
    Semiterm.Operator.Add.term_eq, Semiterm.freeVariables_func,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem mappedSimpleTermCode_le
    (term : ValuationTerm) (bitBound : Nat)
    (hterm :
      (binaryTermCode term).length <=
        appendSourcePrefixCompositeTermCodePolynomial bitBound) :
    (binaryTermCode term).length <=
      appendMappedSourcePrefixSliceTermCodePolynomial bitBound := by
  unfold appendMappedSourcePrefixSliceTermCodePolynomial
  omega

private theorem mappedAddShortAndTwo_code_le
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode
      (addTerm (shortBinaryNumeralTerm value) twoTerm)).length <=
        appendMappedSourcePrefixSliceTermCodePolynomial bitBound := by
  have hvalueCode :=
    binaryNumeralTerm_code_length_le_envelope value bitBound hvalue
  have hraw := paAddTerm_code_length_le
    (shortBinaryNumeralTerm value) twoTerm
  rw [mappedAddTerm_eq_paAddTerm]
  unfold appendMappedSourcePrefixSliceTermCodePolynomial
    appendSourcePrefixCompositeTermCodePolynomial
  omega

private theorem mappedAddAddTwoAndShort_code_le
    (base offset bitBound : Nat)
    (hbase : Nat.size base <= bitBound)
    (hoffset : Nat.size offset <= bitBound) :
    (binaryTermCode
      (addTerm (addTerm (shortBinaryNumeralTerm base) twoTerm)
        (shortBinaryNumeralTerm offset))).length <=
      appendMappedSourcePrefixSliceTermCodePolynomial bitBound := by
  have hbaseCode :=
    binaryNumeralTerm_code_length_le_envelope base bitBound hbase
  have hoffsetCode :=
    binaryNumeralTerm_code_length_le_envelope offset bitBound hoffset
  have hinner := paAddTerm_code_length_le
    (shortBinaryNumeralTerm base) twoTerm
  have houter := paAddTerm_code_length_le
    (addTerm (shortBinaryNumeralTerm base) twoTerm)
    (shortBinaryNumeralTerm offset)
  rw [mappedAddTerm_eq_paAddTerm] at houter
  rw [mappedAddTerm_eq_paAddTerm]
  rw [mappedAddTerm_eq_paAddTerm]
  unfold appendMappedSourcePrefixSliceTermCodePolynomial
    appendSourcePrefixCompositeTermCodePolynomial
  omega

private theorem mappedAddShortAndTwo_closed (value : Nat) :
    (addTerm (shortBinaryNumeralTerm value) twoTerm).freeVariables = ∅ := by
  rw [mappedAddTerm_freeVariables,
    shortBinaryNumeralTerm_freeVariables_eq_empty, mappedTwoTerm_closed]
  simp

private theorem mappedAddAddTwoAndShort_closed (base offset : Nat) :
    (addTerm (addTerm (shortBinaryNumeralTerm base) twoTerm)
      (shortBinaryNumeralTerm offset)).freeVariables = ∅ := by
  rw [mappedAddTerm_freeVariables, mappedAddTerm_freeVariables,
    shortBinaryNumeralTerm_freeVariables_eq_empty, mappedTwoTerm_closed,
    shortBinaryNumeralTerm_freeVariables_eq_empty]
  simp

def appendMappedSourcePrefixTokenSlicesFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  2 *
    compactFixedWidthTokenSlicesEqAtValuationClosedTermFullyFixedPayloadPolynomial
      numericBound (appendMappedSourcePrefixSliceTermCodePolynomial bitBound)
      bitBound

theorem appendMappedSourcePrefixTokenSlicesResource_le_fixed
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount mappedHead
      numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListAppendMappedSourcePrefix tokenTable width
      tokenCount leftStart leftFinish leftCount sourceStart sourceFinish
      sourceCount prefixCount targetStart targetFinish targetBoundary
      targetCount mappedHead)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    let leftSliceCount := Classical.choose hgraph.2.2.2.2.2.1
    let tailSliceCount := Classical.choose hgraph.2.2.2.2.2.2.2
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope
          zeroValuation
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (successorTerm (shortBinaryNumeralTerm leftStart))
          (shortBinaryNumeralTerm leftFinish)
          (successorTerm (shortBinaryNumeralTerm targetStart))
          (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
            (shortBinaryNumeralTerm leftCount))
          leftSliceCount +
        compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope
          zeroValuation
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (addTerm (shortBinaryNumeralTerm sourceStart) twoTerm)
          (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
            (shortBinaryNumeralTerm prefixCount))
          (addTerm (addTerm (shortBinaryNumeralTerm targetStart) twoTerm)
            (shortBinaryNumeralTerm leftCount))
          (shortBinaryNumeralTerm targetFinish)
          tailSliceCount <=
      appendMappedSourcePrefixTokenSlicesFixedPayloadPolynomial numericBound
        bitBound := by
  let leftSliceCount := Classical.choose hgraph.2.2.2.2.2.1
  let tailSliceCount := Classical.choose hgraph.2.2.2.2.2.2.2
  let termCode := appendMappedSourcePrefixSliceTermCodePolynomial bitBound
  have hleftSpec :
      leftSliceCount <= tokenCount ∧
      leftFinish = leftStart + 1 + leftSliceCount ∧
      targetStart + 1 + leftCount = targetStart + 1 + leftSliceCount ∧
      leftFinish <= tokenCount ∧
      targetStart + 1 + leftCount <= tokenCount ∧
      ∀ offset < leftSliceCount, ∀ bitIndex < width,
        tokenTable.testBit ((leftStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + offset) * width + bitIndex) := by
    simpa [leftSliceCount, Nat.add_assoc] using
      Classical.choose_spec hgraph.2.2.2.2.2.1
  have htailSpec :
      tailSliceCount <= tokenCount ∧
      sourceStart + 1 + prefixCount = sourceStart + 2 + tailSliceCount ∧
      targetFinish = targetStart + 2 + leftCount + tailSliceCount ∧
      sourceStart + 1 + prefixCount <= tokenCount ∧
      targetFinish <= tokenCount ∧
      ∀ offset < tailSliceCount, ∀ bitIndex < width,
        tokenTable.testBit ((sourceStart + 2 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 2 + leftCount + offset) * width + bitIndex) := by
    simpa [tailSliceCount, Nat.add_assoc] using
      Classical.choose_spec hgraph.2.2.2.2.2.2.2
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidthBound).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCountBound).trans hnumericSize
  have hleftSliceCountBound : leftSliceCount <= numericBound :=
    hleftSpec.1.trans htokenCountBound
  have htailSliceCountBound : tailSliceCount <= numericBound :=
    htailSpec.1.trans htokenCountBound
  have hleftSliceCountSize : Nat.size leftSliceCount <= bitBound :=
    (Nat.size_le_size hleftSliceCountBound).trans hnumericSize
  have htailSliceCountSize : Nat.size tailSliceCount <= bitBound :=
    (Nat.size_le_size htailSliceCountBound).trans hnumericSize
  have hleftStartBound : leftStart <= numericBound := by omega
  have hleftFinishBound : leftFinish <= numericBound := by omega
  have hleftCountBound : leftCount <= numericBound := by omega
  have hsourceStartBound : sourceStart <= numericBound := by omega
  have hprefixCountBound : prefixCount <= numericBound := by omega
  have htargetStartBound : targetStart <= numericBound := by omega
  have htargetFinishBound : targetFinish <= numericBound := by omega
  have hleftStartSize := (Nat.size_le_size hleftStartBound).trans hnumericSize
  have hleftFinishSize := (Nat.size_le_size hleftFinishBound).trans hnumericSize
  have hleftCountSize := (Nat.size_le_size hleftCountBound).trans hnumericSize
  have hsourceStartSize := (Nat.size_le_size hsourceStartBound).trans hnumericSize
  have hprefixCountSize := (Nat.size_le_size hprefixCountBound).trans hnumericSize
  have htargetStartSize := (Nat.size_le_size htargetStartBound).trans hnumericSize
  have htargetFinishSize := (Nat.size_le_size htargetFinishBound).trans hnumericSize
  have hleftStartSuccessorBound : leftStart + 1 <= numericBound := by omega
  have htargetStartSuccessorBound : targetStart + 1 <= numericBound := by omega
  have hleftTargetBound : targetStart + 1 + leftCount <= numericBound := by omega
  have hsourceTwoBound : sourceStart + 2 <= numericBound := by omega
  have htargetTwoLeftBound :
      targetStart + 2 + leftCount <= numericBound := by omega
  have hleftResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_closedFixed
      zeroValuation tokenTable width leftSliceCount numericBound termCode
      bitBound (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount))
      (mappedSimpleTermCode_le _ bitBound
        (appendSourcePrefixShortNumeral_code_le tokenTable bitBound htableSize))
      (mappedSimpleTermCode_le _ bitBound
        (appendSourcePrefixShortNumeral_code_le width bitBound hwidthSize))
      (mappedSimpleTermCode_le _ bitBound
        (appendSourcePrefixShortNumeral_code_le leftSliceCount bitBound
          hleftSliceCountSize))
      (mappedSimpleTermCode_le _ bitBound
        (appendSourcePrefixShortNumeral_code_le tokenCount bitBound
          htokenCountSize))
      (mappedSimpleTermCode_le _ bitBound
        (appendSourcePrefixSuccessorShortNumeral_code_le leftStart bitBound
          hleftStartSize))
      (mappedSimpleTermCode_le _ bitBound
        (appendSourcePrefixShortNumeral_code_le leftFinish bitBound
          hleftFinishSize))
      (mappedSimpleTermCode_le _ bitBound
        (appendSourcePrefixSuccessorShortNumeral_code_le targetStart bitBound
          htargetStartSize))
      (mappedSimpleTermCode_le _ bitBound
        (appendSourcePrefixAddSuccessorAndShort_code_le targetStart leftCount
          bitBound htargetStartSize hleftCountSize))
      (appendSourcePrefixShortNumeral_closed tokenCount)
      (appendSourcePrefixSuccessorShortNumeral_closed leftStart)
      (appendSourcePrefixShortNumeral_closed leftFinish)
      (appendSourcePrefixSuccessorShortNumeral_closed targetStart)
      (appendSourcePrefixAddSuccessorAndShort_closed targetStart leftCount)
      hwidthBound
      (by simpa [termValue_shortBinaryNumeralTerm] using
        hleftStartSuccessorBound)
      (by simpa [termValue_shortBinaryNumeralTerm] using
        htargetStartSuccessorBound)
      hleftSliceCountBound htableSize hwidthSize hnumericSize
  have htailResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_closedFixed
      zeroValuation tokenTable width tailSliceCount numericBound termCode
      bitBound (shortBinaryNumeralTerm tokenCount)
      (addTerm (shortBinaryNumeralTerm sourceStart) twoTerm)
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (addTerm (addTerm (shortBinaryNumeralTerm targetStart) twoTerm)
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish)
      (mappedSimpleTermCode_le _ bitBound
        (appendSourcePrefixShortNumeral_code_le tokenTable bitBound htableSize))
      (mappedSimpleTermCode_le _ bitBound
        (appendSourcePrefixShortNumeral_code_le width bitBound hwidthSize))
      (mappedSimpleTermCode_le _ bitBound
        (appendSourcePrefixShortNumeral_code_le tailSliceCount bitBound
          htailSliceCountSize))
      (mappedSimpleTermCode_le _ bitBound
        (appendSourcePrefixShortNumeral_code_le tokenCount bitBound
          htokenCountSize))
      (mappedAddShortAndTwo_code_le sourceStart bitBound hsourceStartSize)
      (mappedSimpleTermCode_le _ bitBound
        (appendSourcePrefixAddSuccessorAndShort_code_le sourceStart prefixCount
          bitBound hsourceStartSize hprefixCountSize))
      (mappedAddAddTwoAndShort_code_le targetStart leftCount bitBound
        htargetStartSize hleftCountSize)
      (mappedSimpleTermCode_le _ bitBound
        (appendSourcePrefixShortNumeral_code_le targetFinish bitBound
          htargetFinishSize))
      (appendSourcePrefixShortNumeral_closed tokenCount)
      (mappedAddShortAndTwo_closed sourceStart)
      (appendSourcePrefixAddSuccessorAndShort_closed sourceStart prefixCount)
      (mappedAddAddTwoAndShort_closed targetStart leftCount)
      (appendSourcePrefixShortNumeral_closed targetFinish)
      hwidthBound
      (by simpa [termValue_shortBinaryNumeralTerm] using hsourceTwoBound)
      (by simpa [termValue_shortBinaryNumeralTerm] using htargetTwoLeftBound)
      htailSliceCountBound htableSize hwidthSize hnumericSize
  unfold appendMappedSourcePrefixTokenSlicesFixedPayloadPolynomial
  dsimp only [leftSliceCount, tailSliceCount, termCode] at hleftResource htailResource
  dsimp only [leftSliceCount, tailSliceCount, termCode]
  simpa only [two_mul] using Nat.add_le_add hleftResource htailResource

#print axioms appendMappedSourcePrefixTokenSlicesResource_le_fixed

end FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixTokenSlicesFixedBounds
