import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
import integration.FoundationCompactNumericListedDirectTokenSliceClosedTermFullyFixedBounds

/-!
# Fixed resources for the two source-prefix append token slices

The two existential slice witnesses are extracted from the actual append graph.
Their closed arithmetic endpoint terms are compiled with one public numeric,
term-code, and bit-width envelope.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 150000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAppendSourcePrefixTokenSlicesFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListAppendSourcePrefix
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceClosedTermFullyFixedBounds

def appendSourcePrefixTokenSlicesFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  2 *
    compactFixedWidthTokenSlicesEqAtValuationClosedTermFullyFixedPayloadPolynomial
      numericBound (appendSourcePrefixCompositeTermCodePolynomial bitBound)
      bitBound

theorem appendSourcePrefixTokenSlicesResource_le_fixed
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListAppendSourcePrefix tokenTable width tokenCount
      leftStart leftFinish leftCount sourceStart sourceFinish sourceCount
      prefixCount targetStart targetFinish targetCount)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    let leftSliceCount := Classical.choose hgraph.2.2.2.1
    let sourceSliceCount := Classical.choose hgraph.2.2.2.2
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
          (successorTerm (shortBinaryNumeralTerm sourceStart))
          (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
            (shortBinaryNumeralTerm prefixCount))
          (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
            (shortBinaryNumeralTerm leftCount))
          (shortBinaryNumeralTerm targetFinish)
          sourceSliceCount <=
      appendSourcePrefixTokenSlicesFixedPayloadPolynomial numericBound bitBound := by
  let leftSliceCount := Classical.choose hgraph.2.2.2.1
  let sourceSliceCount := Classical.choose hgraph.2.2.2.2
  let termCode := appendSourcePrefixCompositeTermCodePolynomial bitBound
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
      Classical.choose_spec hgraph.2.2.2.1
  have hsourceSpec :
      sourceSliceCount <= tokenCount ∧
      sourceStart + 1 + prefixCount =
        sourceStart + 1 + sourceSliceCount ∧
      targetFinish = targetStart + 1 + leftCount + sourceSliceCount ∧
      sourceStart + 1 + prefixCount <= tokenCount ∧
      targetFinish <= tokenCount ∧
      ∀ offset < sourceSliceCount, ∀ bitIndex < width,
        tokenTable.testBit
            ((sourceStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + leftCount + offset) * width + bitIndex) := by
    simpa [sourceSliceCount, Nat.add_assoc] using
      Classical.choose_spec hgraph.2.2.2.2
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidthBound).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCountBound).trans hnumericSize
  have hleftSliceCountBound : leftSliceCount <= numericBound :=
    hleftSpec.1.trans htokenCountBound
  have hsourceSliceCountBound : sourceSliceCount <= numericBound :=
    hsourceSpec.1.trans htokenCountBound
  have hleftSliceCountSize : Nat.size leftSliceCount <= bitBound :=
    (Nat.size_le_size hleftSliceCountBound).trans hnumericSize
  have hsourceSliceCountSize : Nat.size sourceSliceCount <= bitBound :=
    (Nat.size_le_size hsourceSliceCountBound).trans hnumericSize
  have hleftStartSuccessorBound : leftStart + 1 <= numericBound := by
    omega
  have htargetStartSuccessorBound : targetStart + 1 <= numericBound := by
    omega
  have hsourceStartSuccessorBound : sourceStart + 1 <= numericBound := by
    omega
  have htargetCompositeBound :
      targetStart + 1 + leftCount <= numericBound := by
    omega
  have hleftStartSize : Nat.size leftStart <= bitBound :=
    (Nat.size_le_size (show leftStart <= numericBound by omega)).trans
      hnumericSize
  have hleftFinishSize : Nat.size leftFinish <= bitBound :=
    (Nat.size_le_size (show leftFinish <= numericBound by omega)).trans
      hnumericSize
  have hleftCountSize : Nat.size leftCount <= bitBound :=
    (Nat.size_le_size (show leftCount <= numericBound by omega)).trans
      hnumericSize
  have hsourceStartSize : Nat.size sourceStart <= bitBound :=
    (Nat.size_le_size (show sourceStart <= numericBound by omega)).trans
      hnumericSize
  have hprefixCountSize : Nat.size prefixCount <= bitBound :=
    (Nat.size_le_size (show prefixCount <= numericBound by omega)).trans
      hnumericSize
  have htargetStartSize : Nat.size targetStart <= bitBound :=
    (Nat.size_le_size (show targetStart <= numericBound by omega)).trans
      hnumericSize
  have htargetFinishSize : Nat.size targetFinish <= bitBound :=
    (Nat.size_le_size (show targetFinish <= numericBound by omega)).trans
      hnumericSize
  have hleftResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_closedFixed
      zeroValuation tokenTable width leftSliceCount numericBound
      termCode bitBound
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount))
      (appendSourcePrefixShortNumeral_code_le tokenTable bitBound htableSize)
      (appendSourcePrefixShortNumeral_code_le width bitBound hwidthSize)
      (appendSourcePrefixShortNumeral_code_le leftSliceCount bitBound
        hleftSliceCountSize)
      (appendSourcePrefixShortNumeral_code_le tokenCount bitBound
        htokenCountSize)
      (appendSourcePrefixSuccessorShortNumeral_code_le leftStart bitBound
        hleftStartSize)
      (appendSourcePrefixShortNumeral_code_le leftFinish bitBound
        hleftFinishSize)
      (appendSourcePrefixSuccessorShortNumeral_code_le targetStart bitBound
        htargetStartSize)
      (appendSourcePrefixAddSuccessorAndShort_code_le targetStart leftCount
        bitBound htargetStartSize hleftCountSize)
      (appendSourcePrefixShortNumeral_closed tokenCount)
      (appendSourcePrefixSuccessorShortNumeral_closed leftStart)
      (appendSourcePrefixShortNumeral_closed leftFinish)
      (appendSourcePrefixSuccessorShortNumeral_closed targetStart)
      (appendSourcePrefixAddSuccessorAndShort_closed targetStart leftCount)
      hwidthBound
      (by
        simpa [termValue_shortBinaryNumeralTerm] using
          hleftStartSuccessorBound)
      (by
        simpa [termValue_shortBinaryNumeralTerm] using
          htargetStartSuccessorBound)
      hleftSliceCountBound htableSize hwidthSize hnumericSize
  have hsourceResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_closedFixed
      zeroValuation tokenTable width sourceSliceCount numericBound
      termCode bitBound
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish)
      (appendSourcePrefixShortNumeral_code_le tokenTable bitBound htableSize)
      (appendSourcePrefixShortNumeral_code_le width bitBound hwidthSize)
      (appendSourcePrefixShortNumeral_code_le sourceSliceCount bitBound
        hsourceSliceCountSize)
      (appendSourcePrefixShortNumeral_code_le tokenCount bitBound
        htokenCountSize)
      (appendSourcePrefixSuccessorShortNumeral_code_le sourceStart bitBound
        hsourceStartSize)
      (appendSourcePrefixAddSuccessorAndShort_code_le sourceStart prefixCount
        bitBound hsourceStartSize hprefixCountSize)
      (appendSourcePrefixAddSuccessorAndShort_code_le targetStart leftCount
        bitBound htargetStartSize hleftCountSize)
      (appendSourcePrefixShortNumeral_code_le targetFinish bitBound
        htargetFinishSize)
      (appendSourcePrefixShortNumeral_closed tokenCount)
      (appendSourcePrefixSuccessorShortNumeral_closed sourceStart)
      (appendSourcePrefixAddSuccessorAndShort_closed sourceStart prefixCount)
      (appendSourcePrefixAddSuccessorAndShort_closed targetStart leftCount)
      (appendSourcePrefixShortNumeral_closed targetFinish)
      hwidthBound
      (by
        simpa [termValue_shortBinaryNumeralTerm] using
          hsourceStartSuccessorBound)
      (by
        simpa [termValue_shortBinaryNumeralTerm] using htargetCompositeBound)
      hsourceSliceCountBound htableSize hwidthSize hnumericSize
  unfold appendSourcePrefixTokenSlicesFixedPayloadPolynomial
  dsimp only [leftSliceCount, sourceSliceCount, termCode] at hleftResource hsourceResource ⊢
  simpa only [two_mul] using Nat.add_le_add hleftResource hsourceResource

#print axioms appendSourcePrefixTokenSlicesResource_le_fixed

end FoundationCompactNumericListedDirectNatListAppendSourcePrefixTokenSlicesFixedBounds
