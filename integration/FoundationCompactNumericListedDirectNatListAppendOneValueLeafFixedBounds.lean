import integration.FoundationCompactNumericListedDirectNatListAppendOneValueFormulaFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAppendOneValuePublicBounds
import integration.FoundationCompactNumericListedDirectTokenSliceClosedTermFullyFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsFullyUniformBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds

/-! # Fixed leaf resources for the append-one certificate -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 240000

namespace FoundationCompactNumericListedDirectNatListAppendOneValueLeafFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendOneValuePublicBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceClosedTermFullyFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsFullyUniformBounds

private abbrev appendOneFixedValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.zeroValuation

def appendOneTermCodePolynomial (bitBound : Nat) : Nat :=
  appendSourcePrefixCompositeTermCodePolynomial bitBound

def appendOneEqualityFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (appendOneTermCodePolynomial bitBound)

def appendOneSliceFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthTokenSlicesEqAtValuationClosedTermFullyFixedPayloadPolynomial
    numericBound (appendOneTermCodePolynomial bitBound) bitBound

theorem appendOneEqualityPayloadEnvelope_le_fixed
    (left right : ValuationTerm) (bitBound : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <=
      appendOneTermCodePolynomial bitBound)
    (hrightCode : (binaryTermCode right).length <=
      appendOneTermCodePolynomial bitBound) :
    appendOneEqualityPayloadEnvelope left right <=
      appendOneEqualityFixedPayloadPolynomial bitBound := by
  unfold appendOneEqualityPayloadEnvelope
    appendOneEqualityFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed
    appendOneFixedValuation Language.Eq.eq left right 0
    (appendOneTermCodePolynomial bitBound) hleftClosed hrightClosed hleftCode
    hrightCode

theorem appendOneTokenSliceCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount sourceStart sourceFinish sourceCount
      targetStart sliceCount numericBound bitBound : Nat)
    (hcountBound : sliceCount <= tokenCount)
    (hsourceEndpoint : sourceFinish = sourceStart + 1 + sliceCount)
    (htargetEndpoint :
      targetStart + 1 + sourceCount = targetStart + 1 + sliceCount)
    (hsourceFinishBound : sourceFinish <= tokenCount)
    (htargetFinishBound : targetStart + 1 + sourceCount <= tokenCount)
    (hbits : ∀ offset < sliceCount, ∀ bitIndex < width,
      tokenTable.testBit ((sourceStart + 1 + offset) * width + bitIndex) =
        tokenTable.testBit
          ((targetStart + 1 + offset) * width + bitIndex))
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (hsourceFinishSize : Nat.size sourceFinish <= bitBound)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound)
    (hwidthBound : width <= numericBound)
    (hsourceStartBound : sourceStart + 1 <= numericBound)
    (htargetStartBound : targetStart + 1 <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
          appendOneFixedValuation
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm
            (shortBinaryNumeralTerm sourceStart))
          (shortBinaryNumeralTerm sourceFinish)
          (FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm
            (shortBinaryNumeralTerm targetStart))
          (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
            (shortBinaryNumeralTerm sourceCount))
          sliceCount
          (by simpa [termValue_shortBinaryNumeralTerm] using hcountBound)
          (by simpa [termValue_shortBinaryNumeralTerm] using hsourceEndpoint)
          (by simpa [termValue_shortBinaryNumeralTerm] using htargetEndpoint)
          (by simpa [termValue_shortBinaryNumeralTerm] using hsourceFinishBound)
          (by simpa [termValue_shortBinaryNumeralTerm] using htargetFinishBound)
          (by
            intro offset hoffset bitIndex hbitIndex
            have hbitIndex' : bitIndex < width := by
              simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
            simpa [termValue_shortBinaryNumeralTerm] using
              hbits offset hoffset bitIndex hbitIndex')) <=
      appendOneSliceFixedPayloadPolynomial numericBound bitBound := by
  let tokenCountTerm := shortBinaryNumeralTerm tokenCount
  let sourceStartTerm :=
    FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm
      (shortBinaryNumeralTerm sourceStart)
  let sourceFinishTerm := shortBinaryNumeralTerm sourceFinish
  let targetStartTerm :=
    FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm
      (shortBinaryNumeralTerm targetStart)
  let targetFinishTerm := appendOneTargetFinishTerm
    (shortBinaryNumeralTerm targetStart) (shortBinaryNumeralTerm sourceCount)
  let termCode := appendOneTermCodePolynomial bitBound
  have hsliceCountSize : Nat.size sliceCount <= bitBound :=
    (Nat.size_le_size hcountBound).trans htokenCountSize
  have htableCode := appendSourcePrefixShortNumeral_code_le tokenTable bitBound
    htableSize
  have hwidthCode := appendSourcePrefixShortNumeral_code_le width bitBound
    hwidthSize
  have hsliceCountCode := appendSourcePrefixShortNumeral_code_le sliceCount
    bitBound hsliceCountSize
  have htokenCountCode := appendSourcePrefixShortNumeral_code_le tokenCount
    bitBound htokenCountSize
  have hsourceStartCode : (binaryTermCode sourceStartTerm).length <= termCode := by
    dsimp only [sourceStartTerm, termCode, appendOneTermCodePolynomial]
    simpa only [
      FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.successorTerm]
      using appendSourcePrefixSuccessorShortNumeral_code_le sourceStart
        bitBound hsourceStartSize
  have hsourceFinishCode := appendSourcePrefixShortNumeral_code_le sourceFinish
    bitBound hsourceFinishSize
  have htargetStartCode : (binaryTermCode targetStartTerm).length <= termCode := by
    dsimp only [targetStartTerm, termCode, appendOneTermCodePolynomial]
    simpa only [
      FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.successorTerm]
      using appendSourcePrefixSuccessorShortNumeral_code_le targetStart
        bitBound htargetStartSize
  have htargetFinishCode :
      (binaryTermCode targetFinishTerm).length <= termCode := by
    dsimp only [targetFinishTerm, termCode, appendOneTermCodePolynomial]
    simpa only [appendOneTargetFinishTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.addTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.successorTerm]
      using appendSourcePrefixAddSuccessorAndShort_code_le targetStart
        sourceCount bitBound htargetStartSize hsourceCountSize
  have htokenCountClosed : tokenCountTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have hsourceStartClosed : sourceStartTerm.freeVariables = ∅ := by
    dsimp only [sourceStartTerm]
    simpa only [
      FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.successorTerm]
      using appendSourcePrefixSuccessorShortNumeral_closed sourceStart
  have hsourceFinishClosed : sourceFinishTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have htargetStartClosed : targetStartTerm.freeVariables = ∅ := by
    dsimp only [targetStartTerm]
    simpa only [
      FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.successorTerm]
      using appendSourcePrefixSuccessorShortNumeral_closed targetStart
  have htargetFinishClosed : targetFinishTerm.freeVariables = ∅ := by
    dsimp only [targetFinishTerm]
    simpa only [appendOneTargetFinishTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.addTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.successorTerm]
      using appendSourcePrefixAddSuccessorAndShort_closed targetStart sourceCount
  have htransparent :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_transparent
      appendOneFixedValuation (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width) tokenCountTerm sourceStartTerm
      sourceFinishTerm targetStartTerm targetFinishTerm sliceCount
      (by simpa only [tokenCountTerm, termValue_shortBinaryNumeralTerm] using
        hcountBound)
      (by simpa only [sourceFinishTerm, sourceStartTerm,
        termValue_shortBinaryNumeralTerm, termValue_successorTerm] using
        hsourceEndpoint)
      (by simpa only [targetFinishTerm, targetStartTerm,
        termValue_shortBinaryNumeralTerm, termValue_successorTerm,
        termValue_appendOneTargetFinishTerm] using htargetEndpoint)
      (by simpa only [sourceFinishTerm, tokenCountTerm,
        termValue_shortBinaryNumeralTerm] using hsourceFinishBound)
      (by simpa only [targetFinishTerm, tokenCountTerm,
        termValue_shortBinaryNumeralTerm,
        termValue_appendOneTargetFinishTerm] using htargetFinishBound)
      (by
        intro offset hoffset bitIndex hbitIndex
        have hbitIndex' : bitIndex < width := by
          simpa only [termValue_shortBinaryNumeralTerm] using hbitIndex
        simpa only [sourceStartTerm, targetStartTerm, tokenCountTerm,
          sourceFinishTerm, targetFinishTerm, termValue_shortBinaryNumeralTerm,
          termValue_successorTerm, termValue_appendOneTargetFinishTerm] using
          hbits offset hoffset bitIndex hbitIndex')
  have hfixed :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_closedFixed
      appendOneFixedValuation tokenTable width sliceCount numericBound termCode
      bitBound tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm htableCode hwidthCode hsliceCountCode htokenCountCode
      hsourceStartCode hsourceFinishCode htargetStartCode htargetFinishCode
      htokenCountClosed hsourceStartClosed hsourceFinishClosed
      htargetStartClosed htargetFinishClosed hwidthBound
      (by simpa only [sourceStartTerm, termValue_successorTerm,
        termValue_shortBinaryNumeralTerm] using hsourceStartBound)
      (by simpa only [targetStartTerm, termValue_successorTerm,
        termValue_shortBinaryNumeralTerm] using htargetStartBound)
      (hcountBound.trans htokenCountBound) htableSize hwidthSize hnumericSize
  unfold appendOneSliceFixedPayloadPolynomial
  simpa only [tokenCountTerm, sourceStartTerm, sourceFinishTerm,
    targetStartTerm, targetFinishTerm, termCode] using htransparent.trans hfixed

#print axioms appendOneEqualityPayloadEnvelope_le_fixed
#print axioms
  appendOneTokenSliceCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectNatListAppendOneValueLeafFixedBounds
