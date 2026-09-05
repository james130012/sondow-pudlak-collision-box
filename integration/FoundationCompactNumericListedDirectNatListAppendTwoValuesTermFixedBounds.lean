import integration.FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds

/-! # Fixed term coordinates for appending two exact values -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 60000

namespace FoundationCompactNumericListedDirectNatListAppendTwoValuesFormulaFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate

def appendTwoExactTermCodePolynomial (bitBound : Nat) : Nat :=
  appendSourcePrefixCompositeTermCodePolynomial bitBound +
    (binaryTermCode (‘2’ : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def appendTwoRowBitBound (bitBound : Nat) : Nat :=
  appendTwoExactTermCodePolynomial bitBound

def appendTwoAtValuationValuesTerms
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount : Nat)
    (firstTerm secondTerm : ValuationTerm) : Fin 12 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm sourceStart,
    shortBinaryNumeralTerm sourceFinish,
    shortBinaryNumeralTerm sourceCount,
    shortBinaryNumeralTerm targetStart,
    shortBinaryNumeralTerm targetFinish,
    shortBinaryNumeralTerm targetBoundary,
    shortBinaryNumeralTerm targetCount,
    firstTerm,
    secondTerm]

theorem binaryNumeralTermCodeEnvelope_ge_coordinate_appendTwo
    (coordinate : Nat) :
    coordinate <= binaryNumeralTermCodeEnvelope coordinate := by
  have hstep : 1 <= binaryNumeralStepBudget := by decide
  have hmul := Nat.mul_le_mul_right coordinate hstep
  unfold binaryNumeralTermCodeEnvelope
  omega

theorem bitBound_le_appendTwoRowBitBound (bitBound : Nat) :
    bitBound <= appendTwoRowBitBound bitBound := by
  have hbase :=
    binaryNumeralTermCodeEnvelope_ge_coordinate_appendTwo bitBound
  unfold appendTwoRowBitBound appendTwoExactTermCodePolynomial
    appendSourcePrefixCompositeTermCodePolynomial
  omega

theorem appendSourcePrefixTermCode_le_appendTwoExact
    (bitBound : Nat) :
    appendSourcePrefixCompositeTermCodePolynomial bitBound <=
      appendTwoExactTermCodePolynomial bitBound := by
  unfold appendTwoExactTermCodePolynomial
  omega

theorem appendTwoTermCode_le_rowEnvelope (bitBound : Nat) :
    appendTwoExactTermCodePolynomial bitBound <=
      binaryNumeralTermCodeEnvelope (appendTwoRowBitBound bitBound) := by
  unfold appendTwoRowBitBound
  exact binaryNumeralTermCodeEnvelope_ge_coordinate_appendTwo _

theorem appendTwoShortNumeralCode_le
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      appendTwoExactTermCodePolynomial bitBound :=
  (appendSourcePrefixShortNumeral_code_le value bitBound hvalue).trans
    (appendSourcePrefixTermCode_le_appendTwoExact bitBound)

theorem appendTwoSuccessorIndexCode_le_rowEnvelope
    (sourceCount bitBound : Nat)
    (hsourceCountSize : Nat.size sourceCount <= bitBound) :
    (binaryTermCode
      (FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.successorTerm
        (shortBinaryNumeralTerm sourceCount))).length <=
      binaryNumeralTermCodeEnvelope (appendTwoRowBitBound bitBound) := by
  have hsuccessor :=
    appendSourcePrefixSuccessorShortNumeral_code_le sourceCount bitBound
      hsourceCountSize
  have hsuccessor' :
      (binaryTermCode
        (FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.successorTerm
          (shortBinaryNumeralTerm sourceCount))).length <=
        appendSourcePrefixCompositeTermCodePolynomial bitBound := by
    simpa only [
      FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.successorTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.successorTerm]
      using hsuccessor
  exact hsuccessor'.trans
      ((appendSourcePrefixTermCode_le_appendTwoExact bitBound).trans
        (appendTwoTermCode_le_rowEnvelope bitBound))

theorem appendTwoArbitraryTermCode_le_rowEnvelope
    (term : ValuationTerm) (bitBound : Nat)
    (htermCode : (binaryTermCode term).length <=
      appendTwoExactTermCodePolynomial bitBound) :
    (binaryTermCode term).length <=
      binaryNumeralTermCodeEnvelope (appendTwoRowBitBound bitBound) :=
  htermCode.trans (appendTwoTermCode_le_rowEnvelope bitBound)

#print axioms bitBound_le_appendTwoRowBitBound
#print axioms appendTwoSuccessorIndexCode_le_rowEnvelope
#print axioms appendTwoArbitraryTermCode_le_rowEnvelope

end FoundationCompactNumericListedDirectNatListAppendTwoValuesFormulaFixedBounds
