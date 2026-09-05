import integration.FoundationCompactNumericListedDirectNatListAppendTwoValuesLeafFixedBounds
import integration.FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds

/-! # Fully fixed structural payload for appending two exact values -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 240000

namespace FoundationCompactNumericListedDirectNatListAppendTwoValuesFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListAppendOneValueLeafFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
open FoundationCompactNumericListedDirectNatListAppendTwoValues
open FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendTwoValuesFormulaFixedBounds
open FoundationCompactNumericListedDirectNatListAppendTwoValuesLeafFixedBounds
open FoundationCompactNumericListedDirectNatListAppendTwoValuesPublicBounds
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate

private abbrev appendTwoFixedValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.zeroValuation

def appendTwoFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridFiveConjunctionGeneralPayloadEnvelope
    (appendTwoExactFullFormulaCodePolynomial bitBound + 1)
    (appendTwoEqualityFixedPayloadPolynomial bitBound)
    (appendTwoEqualityFixedPayloadPolynomial bitBound)
    (appendTwoSliceFixedPayloadPolynomial numericBound bitBound)
    (appendTwoExactRowFixedPayloadPolynomial numericBound bitBound)
    (appendTwoExactRowFixedPayloadPolynomial numericBound bitBound)

theorem
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateDirectOfGraph_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount
      first second numericBound bitBound : Nat)
    (firstTerm secondTerm : ValuationTerm)
    (hfirstValue : termValue appendTwoFixedValuation firstTerm = first)
    (hsecondValue : termValue appendTwoFixedValuation secondTerm = second)
    (hfirstClosed : firstTerm.freeVariables = ∅)
    (hsecondClosed : secondTerm.freeVariables = ∅)
    (hgraph : CompactAdditiveNatListAppendTwoValues tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount first second)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (hsourceFinishSize : Nat.size sourceFinish <= bitBound)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound)
    (htargetFinishSize : Nat.size targetFinish <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (htargetCountSize : Nat.size targetCount <= bitBound)
    (hfirstSize : Nat.size first <= bitBound)
    (hsecondSize : Nat.size second <= bitBound)
    (hfirstCode : (binaryTermCode firstTerm).length <=
      appendTwoExactTermCodePolynomial bitBound)
    (hsecondCode : (binaryTermCode secondTerm).length <=
      appendTwoExactTermCodePolynomial bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (htargetCountBound : targetCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateDirectOfGraph
          tokenTable width tokenCount sourceStart sourceFinish sourceCount
          targetStart targetFinish targetBoundary targetCount first second
          firstTerm secondTerm hfirstValue hsecondValue hgraph) <=
      appendTwoFullyFixedPayloadPolynomial numericBound bitBound := by
  rcases hgraph with
    ⟨htargetFinish, htargetCount, hslices, hfirstRows, hsecondRows⟩
  let sliceCount := Classical.choose hslices
  have hsliceSpec :
      sliceCount <= tokenCount ∧
      sourceFinish = sourceStart + 1 + sliceCount ∧
      targetStart + 1 + sourceCount = targetStart + 1 + sliceCount ∧
      sourceFinish <= tokenCount ∧
      targetStart + 1 + sourceCount <= tokenCount ∧
      ∀ offset < sliceCount, ∀ bitIndex < width,
        tokenTable.testBit
            ((sourceStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + offset) * width + bitIndex) := by
    simpa [sliceCount, Nat.add_assoc] using Classical.choose_spec hslices
  have hsourceStartBound : sourceStart + 1 <= numericBound :=
    (show sourceStart + 1 <= tokenCount by omega).trans htokenCountBound
  have htargetStartBound : targetStart + 1 <= numericBound :=
    (show targetStart + 1 <= tokenCount by omega).trans htokenCountBound
  have hfirstIndexValue :
      termValue
        FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
        (shortBinaryNumeralTerm sourceCount) = sourceCount := by
    simp [termValue_shortBinaryNumeralTerm]
  have hsecondIndexValue :
      termValue
        FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
        (successorTerm (shortBinaryNumeralTerm sourceCount)) =
          sourceCount + 1 := by
    simp [termValue_shortBinaryNumeralTerm]
  have hfirstValue' :
      termValue
        FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
        firstTerm = first := by
    change termValue (fun _ => 0) firstTerm = first
    change termValue (fun _ => 0) firstTerm = first at hfirstValue
    exact hfirstValue
  have hsecondValue' :
      termValue
        FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
        secondTerm = second := by
    change termValue (fun _ => 0) secondTerm = second
    change termValue (fun _ => 0) secondTerm = second at hsecondValue
    exact hsecondValue
  let finishFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetFinish) =
      !!(addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm targetCount))”
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(addTerm (shortBinaryNumeralTerm sourceCount)
        (‘2’ : ValuationTerm))”
  let sliceFormula := compactFixedWidthTokenSlicesEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (successorTerm (shortBinaryNumeralTerm sourceStart))
    (shortBinaryNumeralTerm sourceFinish)
    (successorTerm (shortBinaryNumeralTerm targetStart))
    (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
      (shortBinaryNumeralTerm sourceCount))
  let firstFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexValueFormula tokenTable width
      tokenCount targetBoundary targetCount
      (shortBinaryNumeralTerm sourceCount) firstTerm
  let secondFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexValueFormula tokenTable width
      tokenCount targetBoundary targetCount
      (successorTerm (shortBinaryNumeralTerm sourceCount)) secondTerm
  let fullFormula := finishFormula ⋏
    (countFormula ⋏ (sliceFormula ⋏ (firstFormula ⋏ secondFormula)))
  let syntaxResource := appendTwoExactFullFormulaCodePolynomial bitBound + 1
  let equalityResource := appendTwoEqualityFixedPayloadPolynomial bitBound
  let sliceResource :=
    appendTwoSliceFixedPayloadPolynomial numericBound bitBound
  let rowResource :=
    appendTwoExactRowFixedPayloadPolynomial numericBound bitBound
  have hfullAlignment : fullFormula =
      compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount firstTerm
        secondTerm := by
    rw [
      compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula_alignment]
    rfl
  have hfullClosed : fullFormula.freeVariables = ∅ := by
    rw [hfullAlignment]
    exact
      compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula_closed
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount firstTerm
        secondTerm hfirstClosed hsecondClosed
  have hfullCode :
      (binaryFormulaCode fullFormula).length <= syntaxResource := by
    rw [hfullAlignment]
    have hcode :=
      compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula_code_length_le_fixed
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount bitBound firstTerm
        secondTerm htableSize hwidthSize htokenCountSize hsourceStartSize
        hsourceFinishSize hsourceCountSize htargetStartSize htargetFinishSize
        htargetBoundarySize htargetCountSize hfirstCode hsecondCode
    dsimp only [syntaxResource]
    omega
  have hsyntaxPositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    omega
  have hfinishValue : termValue appendTwoFixedValuation
      (shortBinaryNumeralTerm targetFinish) =
        termValue appendTwoFixedValuation
          (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
            (shortBinaryNumeralTerm targetCount)) := by
    simpa [termValue_shortBinaryNumeralTerm] using htargetFinish
  have hcountValue : termValue appendTwoFixedValuation
      (shortBinaryNumeralTerm targetCount) =
        termValue appendTwoFixedValuation
          (addTerm (shortBinaryNumeralTerm sourceCount)
            (‘2’ : ValuationTerm)) := by
    simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticTwo] using
      htargetCount
  let finishCertificate := valuationEqCertificate
    (shortBinaryNumeralTerm targetFinish)
    (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
      (shortBinaryNumeralTerm targetCount)) hfinishValue
  let countCertificate := valuationEqCertificate
    (shortBinaryNumeralTerm targetCount)
    (addTerm (shortBinaryNumeralTerm sourceCount) (‘2’ : ValuationTerm))
    hcountValue
  let sliceCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      appendTwoFixedValuation
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm sourceFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm sourceCount))
      sliceCount
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using
        hsliceSpec.2.2.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using
        hsliceSpec.2.2.2.2.1)
      (by
        intro offset hoffset bitIndex hbitIndex
        have hbitIndex' : bitIndex < width := by
          simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
        simpa [termValue_shortBinaryNumeralTerm] using
          hsliceSpec.2.2.2.2.2 offset hoffset bitIndex hbitIndex')
  let firstCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph
      FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
      tokenTable width tokenCount targetBoundary targetCount sourceCount first
      (shortBinaryNumeralTerm sourceCount) firstTerm hfirstIndexValue
      hfirstValue' hfirstRows
  let secondCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph
      FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
      tokenTable width tokenCount targetBoundary targetCount
      (sourceCount + 1) second
      (successorTerm (shortBinaryNumeralTerm sourceCount)) secondTerm
      hsecondIndexValue hsecondValue' hsecondRows
  have hfinishLeftCode :=
    appendTwoShortNumeralCode_le targetFinish bitBound htargetFinishSize
  have hfinishRightCode :=
    appendTwoAddSuccessorAndShort_code_le targetStart targetCount bitBound
      htargetStartSize htargetCountSize
  have hfinishLeftClosed :
      (shortBinaryNumeralTerm targetFinish : ValuationTerm).freeVariables =
        ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have hfinishRightClosed :=
    appendTwoAddSuccessorAndShort_closed targetStart targetCount
  have hcountLeftCode :=
    appendTwoShortNumeralCode_le targetCount bitBound htargetCountSize
  have hcountRightCode :=
    appendTwoAddShortAndTwo_code_le sourceCount bitBound hsourceCountSize
  have hcountLeftClosed :
      (shortBinaryNumeralTerm targetCount : ValuationTerm).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have hcountRightClosed := appendTwoAddShortAndTwo_closed sourceCount
  have hfinishResource :
      hybridFormulaStructuralPayloadBound finishCertificate <=
        equalityResource := by
    have htransparent :=
      valuationEqCertificate_structuralPayloadBound_le_transparent
        (shortBinaryNumeralTerm targetFinish)
        (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
          (shortBinaryNumeralTerm targetCount)) hfinishValue
    exact htransparent.trans
      (appendTwoEqualityPayloadEnvelope_le_fixed _ _ bitBound
        hfinishLeftClosed hfinishRightClosed hfinishLeftCode hfinishRightCode)
  have hcountResource :
      hybridFormulaStructuralPayloadBound countCertificate <=
        equalityResource := by
    have htransparent :=
      valuationEqCertificate_structuralPayloadBound_le_transparent
        (shortBinaryNumeralTerm targetCount)
        (addTerm (shortBinaryNumeralTerm sourceCount)
          (‘2’ : ValuationTerm)) hcountValue
    exact htransparent.trans
      (appendTwoEqualityPayloadEnvelope_le_fixed _ _ bitBound
        hcountLeftClosed hcountRightClosed hcountLeftCode hcountRightCode)
  have hsliceResource :
      hybridFormulaStructuralPayloadBound sliceCertificate <=
        sliceResource := by
    have hraw :=
      appendOneTokenSliceCertificate_structuralPayloadBound_le_fixed
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart sliceCount numericBound bitBound hsliceSpec.1
        hsliceSpec.2.1 hsliceSpec.2.2.1 hsliceSpec.2.2.2.1
        hsliceSpec.2.2.2.2.1 hsliceSpec.2.2.2.2.2 htableSize hwidthSize
        htokenCountSize hsourceStartSize hsourceFinishSize hsourceCountSize
        htargetStartSize hwidthBound hsourceStartBound htargetStartBound
        htokenCountBound hnumericSize
    unfold sliceResource appendTwoSliceFixedPayloadPolynomial
    convert hraw using 1 <;>
      (try simp only [sliceCertificate,
      FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.successorTerm,
      FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.addTerm,
      FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm,
      FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.appendOneTargetFinishTerm]) <;>
      (try congr 1)
  have hfirstIndexClosed :
      (shortBinaryNumeralTerm sourceCount : ValuationTerm).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have hsecondIndexClosed :
      (successorTerm
        (shortBinaryNumeralTerm sourceCount)).freeVariables = ∅ := by
    simpa only [
      FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.successorTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.successorTerm]
      using appendSourcePrefixSuccessorShortNumeral_closed sourceCount
  have hfirstIndexCode :=
    appendTwoShortNumeralCode_le sourceCount bitBound hsourceCountSize
  have hsecondIndexCode :
      (binaryTermCode
        (successorTerm
          (shortBinaryNumeralTerm sourceCount))).length <=
        appendTwoExactTermCodePolynomial bitBound := by
    have hraw := appendSourcePrefixSuccessorShortNumeral_code_le sourceCount
      bitBound hsourceCountSize
    have hsame :
        (binaryTermCode
          (successorTerm
            (shortBinaryNumeralTerm sourceCount))).length <=
          appendSourcePrefixCompositeTermCodePolynomial bitBound := by
      simpa only [
        FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.successorTerm,
        FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.successorTerm]
        using hraw
    exact hsame.trans
      (appendSourcePrefixTermCode_le_appendTwoExact bitBound)
  have hsecondIndexSize : Nat.size (sourceCount + 1) <= bitBound :=
    (Nat.size_le_size (Nat.le_of_lt hsecondRows.1)).trans htargetCountSize
  have hfirstResource :
      hybridFormulaStructuralPayloadBound firstCertificate <= rowResource := by
    simpa only [firstCertificate, rowResource] using
      compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_appendTwoFixed
        tokenTable width tokenCount targetBoundary targetCount sourceCount first
        numericBound bitBound (shortBinaryNumeralTerm sourceCount) firstTerm
        hfirstRows hfirstIndexValue hfirstValue' hfirstIndexClosed hfirstClosed
        hwidthBound htokenCountBound htargetCountBound htableSize hwidthSize
        htokenCountSize htargetBoundarySize htargetCountSize hsourceCountSize
        hfirstSize hfirstIndexCode hfirstCode
  have hsecondResource :
      hybridFormulaStructuralPayloadBound secondCertificate <= rowResource := by
    simpa only [secondCertificate, rowResource] using
      compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_appendTwoFixed
        tokenTable width tokenCount targetBoundary targetCount
        (sourceCount + 1) second numericBound bitBound
        (successorTerm (shortBinaryNumeralTerm sourceCount)) secondTerm
        hsecondRows hsecondIndexValue hsecondValue' hsecondIndexClosed
        hsecondClosed hwidthBound htokenCountBound htargetCountBound htableSize
        hwidthSize htokenCountSize htargetBoundarySize htargetCountSize
        hsecondIndexSize hsecondSize hsecondIndexCode hsecondCode
  let rowsCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      firstCertificate secondCertificate
  let sliceRowsCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      sliceCertificate rowsCertificate
  let countTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      countCertificate sliceRowsCertificate
  let directCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      finishCertificate countTailCertificate
  have hrowsRaw := transparentHybridConjunctionPayloadBound_le
    firstCertificate secondCertificate rowResource rowResource
    hfirstResource hsecondResource
  have hsliceRowsRaw := transparentHybridConjunctionPayloadBound_le
    sliceCertificate rowsCertificate sliceResource
    (transparentHybridConjunctionPayloadEnvelope appendTwoFixedValuation
      firstFormula secondFormula rowResource rowResource)
    hsliceResource hrowsRaw
  have hcountTailRaw := transparentHybridConjunctionPayloadBound_le
    countCertificate sliceRowsCertificate equalityResource
    (transparentHybridConjunctionPayloadEnvelope appendTwoFixedValuation
      sliceFormula (firstFormula ⋏ secondFormula) sliceResource
      (transparentHybridConjunctionPayloadEnvelope appendTwoFixedValuation
        firstFormula secondFormula rowResource rowResource))
    hcountResource hsliceRowsRaw
  have hfullRaw := transparentHybridConjunctionPayloadBound_le
    finishCertificate countTailCertificate equalityResource
    (transparentHybridConjunctionPayloadEnvelope appendTwoFixedValuation
      countFormula (sliceFormula ⋏ (firstFormula ⋏ secondFormula))
      equalityResource
      (transparentHybridConjunctionPayloadEnvelope appendTwoFixedValuation
        sliceFormula (firstFormula ⋏ secondFormula) sliceResource
        (transparentHybridConjunctionPayloadEnvelope appendTwoFixedValuation
          firstFormula secondFormula rowResource rowResource)))
    hfinishResource hcountTailRaw
  have hassembly :=
    transparentHybridFiveConjunctionPayloadEnvelope_le_closedGeneral
      appendTwoFixedValuation finishFormula countFormula sliceFormula
      firstFormula secondFormula equalityResource equalityResource
      sliceResource rowResource rowResource syntaxResource hsyntaxPositive
      hfullClosed hfullCode
  have hfixed := hfullRaw.trans hassembly
  convert hfixed using 1 <;>
    (try simp only [
      compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateDirectOfGraph,
      hybridFormulaStructuralPayloadBound, appendTwoFullyFixedPayloadPolynomial,
      sliceCount, syntaxResource, equalityResource,
      sliceResource, rowResource, finishCertificate, countCertificate,
      sliceCertificate, firstCertificate, secondCertificate, rowsCertificate,
      sliceRowsCertificate, countTailCertificate]) <;>
    (try congr 1)

theorem
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount
      first second numericBound bitBound : Nat)
    (firstTerm secondTerm : ValuationTerm)
    (hfirstValue : termValue appendTwoFixedValuation firstTerm = first)
    (hsecondValue : termValue appendTwoFixedValuation secondTerm = second)
    (hfirstClosed : firstTerm.freeVariables = ∅)
    (hsecondClosed : secondTerm.freeVariables = ∅)
    (hgraph : CompactAdditiveNatListAppendTwoValues tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount first second)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (hsourceFinishSize : Nat.size sourceFinish <= bitBound)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound)
    (htargetFinishSize : Nat.size targetFinish <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (htargetCountSize : Nat.size targetCount <= bitBound)
    (hfirstSize : Nat.size first <= bitBound)
    (hsecondSize : Nat.size second <= bitBound)
    (hfirstCode : (binaryTermCode firstTerm).length <=
      appendTwoExactTermCodePolynomial bitBound)
    (hsecondCode : (binaryTermCode secondTerm).length <=
      appendTwoExactTermCodePolynomial bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (htargetCountBound : targetCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceStart sourceFinish sourceCount
          targetStart targetFinish targetBoundary targetCount first second
          firstTerm secondTerm hfirstValue hsecondValue hgraph) <=
      appendTwoFullyFixedPayloadPolynomial numericBound bitBound := by
  simpa only [
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph,
    hybridFormulaStructuralPayloadBound] using
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateDirectOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount first second
      numericBound bitBound firstTerm secondTerm hfirstValue hsecondValue
      hfirstClosed hsecondClosed hgraph htableSize hwidthSize htokenCountSize
      hsourceStartSize hsourceFinishSize hsourceCountSize htargetStartSize
      htargetFinishSize htargetBoundarySize htargetCountSize hfirstSize
      hsecondSize hfirstCode hsecondCode hwidthBound htokenCountBound
      htargetCountBound hnumericSize

#print axioms
  compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateDirectOfGraph_structuralPayloadBound_le_fullyFixed
#print axioms
  compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectNatListAppendTwoValuesFullyFixedBounds
