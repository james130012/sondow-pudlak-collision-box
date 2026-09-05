import integration.FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixArithmeticFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixTokenSlicesFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixFormulaFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsFullyUniformBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueFullyFixedBounds
import integration.FoundationCompactPAHybridEightConjunctionCheckedGeneralBounds

/-!
# Fully fixed checked certificate for a mapped source prefix

The theorem composes the five arithmetic certificates, two graph-extracted
token slices, and the genuine row-lookup certificate.  Every leaf is charged
by a fixed polynomial resource; no graph payload envelope remains.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefix
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixPublicBounds
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixArithmeticFixedBounds
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixTokenSlicesFixedBounds
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixFormulaFixedBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsFullyUniformBounds
open FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueFullyFixedBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactPAHybridEightConjunctionCheckedGeneralBounds

private theorem termValue_mappedOne :
    termValue zeroValuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one zeroValuation ![]

def appendMappedSourcePrefixFullyFixedSyntaxPolynomial
    (bitBound : Nat) : Nat :=
  appendMappedSourcePrefixFullFormulaCodePolynomial bitBound + 1

def appendMappedSourcePrefixFullyFixedPayloadPolynomial
    (_leftCount numericBound bitBound : Nat) : Nat :=
  hybridEightConjunctionCheckedGeneralPayloadEnvelope
    (appendMappedSourcePrefixFullyFixedSyntaxPolynomial bitBound)
    (appendMappedSourcePrefixArithmeticLeavesFixedPayloadPolynomial bitBound)
    (appendMappedSourcePrefixArithmeticLeavesFixedPayloadPolynomial bitBound)
    (appendMappedSourcePrefixArithmeticLeavesFixedPayloadPolynomial bitBound)
    (appendMappedSourcePrefixArithmeticLeavesFixedPayloadPolynomial bitBound)
    (appendMappedSourcePrefixArithmeticLeavesFixedPayloadPolynomial bitBound)
    (appendMappedSourcePrefixTokenSlicesFixedPayloadPolynomial numericBound
      bitBound)
    (compactAdditiveNatListAtRowsExactValueFullyFixedPayloadPolynomial
      numericBound bitBound)
    (appendMappedSourcePrefixTokenSlicesFixedPayloadPolynomial numericBound
      bitBound)

theorem
    compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
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
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hleftStartSize : Nat.size leftStart <= bitBound)
    (hleftFinishSize : Nat.size leftFinish <= bitBound)
    (hleftCountSize : Nat.size leftCount <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (hsourceFinishSize : Nat.size sourceFinish <= bitBound)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (hprefixCountSize : Nat.size prefixCount <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound)
    (htargetFinishSize : Nat.size targetFinish <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (htargetCountSize : Nat.size targetCount <= bitBound)
    (hmappedHeadSize : Nat.size mappedHead <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount leftStart leftFinish leftCount
          sourceStart sourceFinish sourceCount prefixCount targetStart
          targetFinish targetBoundary targetCount mappedHead hgraph) <=
      appendMappedSourcePrefixFullyFixedPayloadPolynomial leftCount numericBound
        bitBound := by
  rcases hgraph with
    ⟨hpositive, hprefix, hsourceWithin, htargetFinish, hcount,
      hleftSlice, hhead, htailSlice⟩
  let graph : CompactAdditiveNatListAppendMappedSourcePrefix tokenTable width
      tokenCount leftStart leftFinish leftCount sourceStart sourceFinish
      sourceCount prefixCount targetStart targetFinish targetBoundary
      targetCount mappedHead :=
    ⟨hpositive, hprefix, hsourceWithin, htargetFinish, hcount,
      hleftSlice, hhead, htailSlice⟩
  let leftSliceCount := Classical.choose hleftSlice
  have hleftSpec :
      leftSliceCount <= tokenCount ∧
      leftFinish = leftStart + 1 + leftSliceCount ∧
      targetStart + 1 + leftCount = targetStart + 1 + leftSliceCount ∧
      leftFinish <= tokenCount ∧
      targetStart + 1 + leftCount <= tokenCount ∧
      targetStart + 1 + leftCount <= tokenCount ∧
      ∀ offset < leftSliceCount, ∀ bitIndex < width,
        tokenTable.testBit ((leftStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + offset) * width + bitIndex) := by
    simpa [leftSliceCount, Nat.add_assoc] using
      Classical.choose_spec hleftSlice
  let tailSliceCount := Classical.choose htailSlice
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
      Classical.choose_spec htailSlice
  let positiveFormula : ValuationFormula :=
    “!!(‘1’ : ValuationTerm) ≤ !!(shortBinaryNumeralTerm prefixCount)”
  let prefixFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm prefixCount) ≤
      !!(shortBinaryNumeralTerm sourceCount)”
  let sourceWithinFormula : ValuationFormula :=
    “!!(addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
          (shortBinaryNumeralTerm prefixCount)) ≤
      !!(shortBinaryNumeralTerm sourceFinish)”
  let targetFinishFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetFinish) =
      !!(addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm targetCount))”
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(addTerm (shortBinaryNumeralTerm leftCount)
        (shortBinaryNumeralTerm prefixCount))”
  let leftSliceFormula := compactFixedWidthTokenSlicesEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (successorTerm (shortBinaryNumeralTerm leftStart))
    (shortBinaryNumeralTerm leftFinish)
    (successorTerm (shortBinaryNumeralTerm targetStart))
    (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
      (shortBinaryNumeralTerm leftCount))
  let headFormula :=
    FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.compactAdditiveNatListAtRowsAtValuationIndexFormula
      tokenTable width tokenCount targetBoundary targetCount mappedHead
      (shortBinaryNumeralTerm leftCount)
  let tailSliceFormula := compactFixedWidthTokenSlicesEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (addTerm (shortBinaryNumeralTerm sourceStart) twoTerm)
    (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm prefixCount))
    (addTerm (addTerm (shortBinaryNumeralTerm targetStart) twoTerm)
      (shortBinaryNumeralTerm leftCount))
    (shortBinaryNumeralTerm targetFinish)
  let arithmeticResource :=
    appendMappedSourcePrefixArithmeticLeavesFixedPayloadPolynomial bitBound
  let slicesResource :=
    appendMappedSourcePrefixTokenSlicesFixedPayloadPolynomial numericBound
      bitBound
  let headResource :=
    compactAdditiveNatListAtRowsExactValueFullyFixedPayloadPolynomial
      numericBound bitBound
  let syntaxResource :=
    appendMappedSourcePrefixFullyFixedSyntaxPolynomial bitBound
  have hleftCountBound : leftSliceCount <=
      termValue zeroValuation (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.1
  have hleftSourceEndpoint : termValue zeroValuation
      (shortBinaryNumeralTerm leftFinish) =
        termValue zeroValuation
          (successorTerm (shortBinaryNumeralTerm leftStart)) +
          leftSliceCount := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.1
  have hleftTargetEndpoint : termValue zeroValuation
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount)) =
        termValue zeroValuation
          (successorTerm (shortBinaryNumeralTerm targetStart)) +
          leftSliceCount := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.2.1
  have hleftSourceFinish : termValue zeroValuation
      (shortBinaryNumeralTerm leftFinish) <=
        termValue zeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.2.2.1
  have hleftTargetFinish : termValue zeroValuation
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount)) <=
        termValue zeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.2.2.2.1
  have hleftBits : ∀ offset < leftSliceCount,
      ∀ bitIndex < termValue zeroValuation
        (shortBinaryNumeralTerm width),
        (termValue zeroValuation
          (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue zeroValuation
                (successorTerm (shortBinaryNumeralTerm leftStart)) + offset) *
              termValue zeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) =
          (termValue zeroValuation
            (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue zeroValuation
                (successorTerm (shortBinaryNumeralTerm targetStart)) +
                  offset) *
              termValue zeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) := by
    intro offset hoffset bitIndex hbitIndex
    have hbitIndex' : bitIndex < width := by
      simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
    simpa [termValue_shortBinaryNumeralTerm] using
      hleftSpec.2.2.2.2.2.2 offset hoffset bitIndex hbitIndex'
  have htailCountBound : tailSliceCount <=
      termValue zeroValuation (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using htailSpec.1
  have htailSourceEndpoint : termValue zeroValuation
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount)) =
        termValue zeroValuation
          (addTerm (shortBinaryNumeralTerm sourceStart) twoTerm) +
          tailSliceCount := by
    simpa [termValue_shortBinaryNumeralTerm, Nat.add_assoc] using
      htailSpec.2.1
  have htailTargetEndpoint : termValue zeroValuation
      (shortBinaryNumeralTerm targetFinish) =
        termValue zeroValuation
          (addTerm (addTerm (shortBinaryNumeralTerm targetStart) twoTerm)
            (shortBinaryNumeralTerm leftCount)) + tailSliceCount := by
    simpa [termValue_shortBinaryNumeralTerm, Nat.add_assoc] using
      htailSpec.2.2.1
  have htailSourceFinish : termValue zeroValuation
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount)) <=
        termValue zeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using htailSpec.2.2.2.1
  have htailTargetFinish : termValue zeroValuation
      (shortBinaryNumeralTerm targetFinish) <=
        termValue zeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using
      htailSpec.2.2.2.2.1
  have htailBits : ∀ offset < tailSliceCount,
      ∀ bitIndex < termValue zeroValuation
        (shortBinaryNumeralTerm width),
        (termValue zeroValuation
          (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue zeroValuation
                (addTerm (shortBinaryNumeralTerm sourceStart) twoTerm) +
                  offset) *
              termValue zeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) =
          (termValue zeroValuation
            (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue zeroValuation
                (addTerm (addTerm (shortBinaryNumeralTerm targetStart) twoTerm)
                  (shortBinaryNumeralTerm leftCount)) + offset) *
              termValue zeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) := by
    intro offset hoffset bitIndex hbitIndex
    have hbitIndex' : bitIndex < width := by
      simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
    simpa [termValue_shortBinaryNumeralTerm, Nat.add_assoc] using
      htailSpec.2.2.2.2.2 offset hoffset bitIndex hbitIndex'
  let leftCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      zeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount)) leftSliceCount hleftCountBound
      hleftSourceEndpoint hleftTargetEndpoint hleftSourceFinish
      hleftTargetFinish hleftBits
  let headCertificateRaw :=
    FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph
      zeroValuation tokenTable width tokenCount targetBoundary targetCount
      leftCount mappedHead (shortBinaryNumeralTerm leftCount)
      (shortBinaryNumeralTerm mappedHead)
      (by simp [termValue_shortBinaryNumeralTerm])
      (by simp [termValue_shortBinaryNumeralTerm]) hhead
  let headCertificate : CheckedHybridValuationBoundedFormulaCertificate
      zeroValuation
      (FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.compactAdditiveNatListAtRowsAtValuationIndexFormula
        tokenTable width tokenCount targetBoundary targetCount mappedHead
        (shortBinaryNumeralTerm leftCount)) :=
    .cast (by rfl) headCertificateRaw
  let tailCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      zeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (addTerm (shortBinaryNumeralTerm sourceStart) twoTerm)
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (addTerm (addTerm (shortBinaryNumeralTerm targetStart) twoTerm)
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish) tailSliceCount htailCountBound
      htailSourceEndpoint htailTargetEndpoint htailSourceFinish
      htailTargetFinish htailBits
  let positiveCertificate := valuationLeCertificate (‘1’ : ValuationTerm)
    (shortBinaryNumeralTerm prefixCount) (by
      simpa [termValue_mappedOne, termValue_shortBinaryNumeralTerm] using
        hpositive)
  let prefixCertificate := valuationLeCertificate
    (shortBinaryNumeralTerm prefixCount)
    (shortBinaryNumeralTerm sourceCount) (by
      simpa [termValue_shortBinaryNumeralTerm] using hprefix)
  let sourceWithinCertificate := valuationLeCertificate
    (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm prefixCount))
    (shortBinaryNumeralTerm sourceFinish) (by
      simpa [termValue_shortBinaryNumeralTerm] using hsourceWithin)
  let targetFinishCertificate := valuationEqCertificate
    (shortBinaryNumeralTerm targetFinish)
    (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
      (shortBinaryNumeralTerm targetCount)) (by
        simpa [termValue_shortBinaryNumeralTerm] using htargetFinish)
  let countCertificate := valuationEqCertificate
    (shortBinaryNumeralTerm targetCount)
    (addTerm (shortBinaryNumeralTerm leftCount)
      (shortBinaryNumeralTerm prefixCount)) (by
        simpa [termValue_shortBinaryNumeralTerm] using hcount)
  have harithmetic :=
    appendMappedSourcePrefixArithmeticLeavesResource_le_fixed sourceStart
      sourceFinish sourceCount prefixCount targetStart targetFinish targetCount
      leftCount bitBound hsourceStartSize hsourceFinishSize hsourceCountSize
      hprefixCountSize htargetStartSize htargetFinishSize htargetCountSize
      hleftCountSize
  have hslices :=
    appendMappedSourcePrefixTokenSlicesResource_le_fixed tokenTable width
      tokenCount leftStart leftFinish leftCount sourceStart sourceFinish
      sourceCount prefixCount targetStart targetFinish targetBoundary
      targetCount mappedHead numericBound bitBound graph htableSize hwidthBound
      htokenCountBound hnumericSize
  have hpositiveTransparent :=
    valuationLeCertificate_structuralPayloadBound_le_transparent
      (‘1’ : ValuationTerm) (shortBinaryNumeralTerm prefixCount) (by
        simpa [termValue_mappedOne, termValue_shortBinaryNumeralTerm] using
          hpositive)
  have hprefixTransparent :=
    valuationLeCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm prefixCount)
      (shortBinaryNumeralTerm sourceCount) (by
        simpa [termValue_shortBinaryNumeralTerm] using hprefix)
  have hsourceWithinTransparent :=
    valuationLeCertificate_structuralPayloadBound_le_transparent
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (shortBinaryNumeralTerm sourceFinish) (by
        simpa [termValue_shortBinaryNumeralTerm] using hsourceWithin)
  have htargetFinishTransparent :=
    valuationEqCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm targetFinish)
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm targetCount)) (by
          simpa [termValue_shortBinaryNumeralTerm] using htargetFinish)
  have hcountTransparent :=
    valuationEqCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm targetCount)
      (addTerm (shortBinaryNumeralTerm leftCount)
        (shortBinaryNumeralTerm prefixCount)) (by
          simpa [termValue_shortBinaryNumeralTerm] using hcount)
  have hpositiveResource :
      hybridFormulaStructuralPayloadBound positiveCertificate <=
        arithmeticResource := by
    apply hpositiveTransparent.trans
    dsimp only [arithmeticResource] at harithmetic ⊢
    omega
  have hprefixResource :
      hybridFormulaStructuralPayloadBound prefixCertificate <=
        arithmeticResource := by
    apply hprefixTransparent.trans
    dsimp only [arithmeticResource] at harithmetic ⊢
    omega
  have hsourceWithinResource :
      hybridFormulaStructuralPayloadBound sourceWithinCertificate <=
        arithmeticResource := by
    apply hsourceWithinTransparent.trans
    dsimp only [arithmeticResource] at harithmetic ⊢
    omega
  have htargetFinishResource :
      hybridFormulaStructuralPayloadBound targetFinishCertificate <=
        arithmeticResource := by
    apply htargetFinishTransparent.trans
    dsimp only [arithmeticResource] at harithmetic ⊢
    omega
  have hcountResource :
      hybridFormulaStructuralPayloadBound countCertificate <=
        arithmeticResource := by
    apply hcountTransparent.trans
    dsimp only [arithmeticResource] at harithmetic ⊢
    omega
  have hleftTransparent :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_transparent
      zeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount)) leftSliceCount hleftCountBound
      hleftSourceEndpoint hleftTargetEndpoint hleftSourceFinish
      hleftTargetFinish hleftBits
  have htailTransparent :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_transparent
      zeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (addTerm (shortBinaryNumeralTerm sourceStart) twoTerm)
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (addTerm (addTerm (shortBinaryNumeralTerm targetStart) twoTerm)
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish) tailSliceCount htailCountBound
      htailSourceEndpoint htailTargetEndpoint htailSourceFinish
      htailTargetFinish htailBits
  have hleftResource :
      hybridFormulaStructuralPayloadBound leftCertificate <=
        slicesResource := by
    apply hleftTransparent.trans
    dsimp only [leftSliceCount, tailSliceCount, slicesResource] at hslices ⊢
    omega
  have htailResource :
      hybridFormulaStructuralPayloadBound tailCertificate <=
        slicesResource := by
    apply htailTransparent.trans
    dsimp only [leftSliceCount, tailSliceCount, slicesResource] at hslices ⊢
    omega
  have htargetCountBound : targetCount <= numericBound := by
    have hfinishBound : targetFinish <= tokenCount :=
      htailSpec.2.2.2.2.1
    omega
  have hheadResource :
      hybridFormulaStructuralPayloadBound headCertificate <=
        headResource := by
    rw [show hybridFormulaStructuralPayloadBound headCertificate =
        hybridFormulaStructuralPayloadBound headCertificateRaw by
      simp only [headCertificate, hybridFormulaStructuralPayloadBound]]
    simpa only [headCertificateRaw, headResource] using
      compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount targetBoundary targetCount leftCount
        mappedHead numericBound bitBound (shortBinaryNumeralTerm leftCount)
        (shortBinaryNumeralTerm mappedHead) hhead
        (by simp [termValue_shortBinaryNumeralTerm])
        (by simp [termValue_shortBinaryNumeralTerm])
        (shortBinaryNumeralTerm_freeVariables_eq_empty leftCount)
        (shortBinaryNumeralTerm_freeVariables_eq_empty mappedHead)
        hwidthBound htokenCountBound htargetCountBound htableSize hwidthSize
        htokenCountSize htargetBoundarySize htargetCountSize hleftCountSize
        hmappedHeadSize
        (by
          simpa only [natListAtRowsExactIndexCodeEnvelope] using
            binaryNumeralTerm_code_length_le_envelope leftCount bitBound
              hleftCountSize)
        (binaryNumeralTerm_code_length_le_envelope mappedHead bitBound
          hmappedHeadSize)
  have hclosedRaw :=
    compactAdditiveNatListAppendMappedSourcePrefixExplicitFormula_closed
      tokenTable width tokenCount leftStart leftFinish leftCount sourceStart
      sourceFinish sourceCount prefixCount targetStart targetFinish
      targetBoundary targetCount mappedHead
  have hclosed :
      (positiveFormula ⋏
        (prefixFormula ⋏
          (sourceWithinFormula ⋏
            (targetFinishFormula ⋏
              (countFormula ⋏
                (leftSliceFormula ⋏
                  (headFormula ⋏ tailSliceFormula))))))).freeVariables =
        ∅ := by
    simpa only [positiveFormula, prefixFormula, sourceWithinFormula,
      targetFinishFormula, countFormula, leftSliceFormula, headFormula,
      tailSliceFormula,
      compactAdditiveNatListAppendMappedSourcePrefixExplicitFormula] using
        hclosedRaw
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
  have hclosed1 := (Finset.union_eq_empty.mp hclosed).1
  have hclosedTail1 := (Finset.union_eq_empty.mp hclosed).2
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosedTail1
  have hclosed2 := (Finset.union_eq_empty.mp hclosedTail1).1
  have hclosedTail2 := (Finset.union_eq_empty.mp hclosedTail1).2
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosedTail2
  have hclosed3 := (Finset.union_eq_empty.mp hclosedTail2).1
  have hclosedTail3 := (Finset.union_eq_empty.mp hclosedTail2).2
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosedTail3
  have hclosed4 := (Finset.union_eq_empty.mp hclosedTail3).1
  have hclosedTail4 := (Finset.union_eq_empty.mp hclosedTail3).2
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosedTail4
  have hclosed5 := (Finset.union_eq_empty.mp hclosedTail4).1
  have hclosedTail5 := (Finset.union_eq_empty.mp hclosedTail4).2
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosedTail5
  have hclosed6 := (Finset.union_eq_empty.mp hclosedTail5).1
  have hclosedTail6 := (Finset.union_eq_empty.mp hclosedTail5).2
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosedTail6
  have hclosed7 := (Finset.union_eq_empty.mp hclosedTail6).1
  have hclosed8 := (Finset.union_eq_empty.mp hclosedTail6).2
  have hcodeRaw :=
    compactAdditiveNatListAppendMappedSourcePrefixClosedFormula_code_length_le_fixed
      tokenTable width tokenCount leftStart leftFinish leftCount sourceStart
      sourceFinish sourceCount prefixCount targetStart targetFinish
      targetBoundary targetCount mappedHead bitBound htableSize hwidthSize
      htokenCountSize hleftStartSize hleftFinishSize hleftCountSize
      hsourceStartSize hsourceFinishSize hsourceCountSize hprefixCountSize
      htargetStartSize htargetFinishSize htargetBoundarySize htargetCountSize
      hmappedHeadSize
  rw [compactAdditiveNatListAppendMappedSourcePrefixClosedFormula_alignment] at hcodeRaw
  have hcode :
      (binaryFormulaCode
        (positiveFormula ⋏
          (prefixFormula ⋏
            (sourceWithinFormula ⋏
              (targetFinishFormula ⋏
                (countFormula ⋏
                  (leftSliceFormula ⋏
                    (headFormula ⋏ tailSliceFormula)))))))).length <=
        syntaxResource := by
    have hcodeBase :
        (binaryFormulaCode
          (positiveFormula ⋏
            (prefixFormula ⋏
              (sourceWithinFormula ⋏
                (targetFinishFormula ⋏
                  (countFormula ⋏
                    (leftSliceFormula ⋏
                      (headFormula ⋏ tailSliceFormula)))))))).length <=
          appendMappedSourcePrefixFullFormulaCodePolynomial bitBound := by
      simpa only [positiveFormula, prefixFormula, sourceWithinFormula,
        targetFinishFormula, countFormula, leftSliceFormula, headFormula,
        tailSliceFormula,
        compactAdditiveNatListAppendMappedSourcePrefixExplicitFormula] using
          hcodeRaw
    exact hcodeBase.trans (by
      unfold syntaxResource
        appendMappedSourcePrefixFullyFixedSyntaxPolynomial
      omega)
  have hsyntaxPositive : 1 <= syntaxResource := by
    unfold syntaxResource appendMappedSourcePrefixFullyFixedSyntaxPolynomial
    omega
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      positiveCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        prefixCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          sourceWithinCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            targetFinishCertificate
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              countCertificate
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                leftCertificate
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  headCertificate tailCertificate))))))
  have hdirect :
      hybridFormulaStructuralPayloadBound direct <=
        hybridEightConjunctionCheckedGeneralPayloadEnvelope syntaxResource
          arithmeticResource arithmeticResource arithmeticResource
          arithmeticResource arithmeticResource slicesResource headResource
          slicesResource := by
    simpa only [direct] using
      checkedHybridEightConjunctionPayloadBound_le_closedGeneral
        positiveCertificate prefixCertificate sourceWithinCertificate
        targetFinishCertificate countCertificate leftCertificate
        headCertificate tailCertificate arithmeticResource
        arithmeticResource arithmeticResource arithmeticResource
        arithmeticResource slicesResource headResource slicesResource
        syntaxResource hpositiveResource hprefixResource hsourceWithinResource
        htargetFinishResource hcountResource hleftResource hheadResource
        htailResource hsyntaxPositive hclosed1 hclosed2 hclosed3 hclosed4
        hclosed5 hclosed6 hclosed7 hclosed8 hcode
  have hcertificate :
      hybridFormulaStructuralPayloadBound
          (compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph
            tokenTable width tokenCount leftStart leftFinish leftCount
            sourceStart sourceFinish sourceCount prefixCount targetStart
            targetFinish targetBoundary targetCount mappedHead
            ⟨hpositive, hprefix, hsourceWithin, htargetFinish, hcount,
              hleftSlice, hhead, htailSlice⟩) =
      hybridFormulaStructuralPayloadBound direct := by
    simp only [
      compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph,
      hybridFormulaStructuralPayloadBound, leftSliceCount, tailSliceCount,
      leftCertificate, headCertificateRaw, headCertificate, tailCertificate,
      positiveCertificate, prefixCertificate, sourceWithinCertificate,
      targetFinishCertificate, countCertificate, direct]
  rw [hcertificate]
  unfold appendMappedSourcePrefixFullyFixedPayloadPolynomial
  simpa only [syntaxResource, arithmeticResource, slicesResource,
    headResource] using hdirect

#print axioms
  compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixFullyFixedBounds
