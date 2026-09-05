import integration.FoundationCompactNumericListedDirectNatListAppendOneValueLeafFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueFullyFixedBounds
import integration.FoundationCompactPAHybridFourConjunctionClosedGeneralBounds

/-! # Fully fixed structural payload for the append-one certificate -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 240000

namespace FoundationCompactNumericListedDirectNatListAppendOneValueFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridFourConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectNatListAppendOneValue
open FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendOneValuePublicBounds
open FoundationCompactNumericListedDirectNatListAppendOneValueFormulaFixedBounds
open FoundationCompactNumericListedDirectNatListAppendOneValueLeafFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueFullyFixedBounds

private abbrev appendOneFixedValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.zeroValuation

def appendOneFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridFourConjunctionGeneralPayloadEnvelope
    (appendOneFullFormulaCodePolynomial bitBound + 1)
    (appendOneEqualityFixedPayloadPolynomial bitBound)
    (appendOneEqualityFixedPayloadPolynomial bitBound)
    (appendOneSliceFixedPayloadPolynomial numericBound bitBound)
    (compactAdditiveNatListAtRowsExactValueFullyFixedPayloadPolynomial
      numericBound bitBound)

theorem
    compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value
      numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListAppendOneValue tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount value)
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
    (hvalueSize : Nat.size value <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (htargetCountBound : targetCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceStart sourceFinish sourceCount
          targetStart targetFinish targetBoundary targetCount value hgraph) <=
      appendOneFullyFixedPayloadPolynomial numericBound bitBound := by
  have htargetFinish := hgraph.1
  have htargetCount := hgraph.2.1
  have hslices := hgraph.2.2.1
  have hrows := hgraph.2.2.2
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
  let targetFinishFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetFinish) =
      !!(appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm targetCount))”
  let targetCountFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm
        (shortBinaryNumeralTerm sourceCount))”
  let sliceFormula := compactFixedWidthTokenSlicesEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm
      (shortBinaryNumeralTerm sourceStart))
    (shortBinaryNumeralTerm sourceFinish)
    (FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm
      (shortBinaryNumeralTerm targetStart))
    (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
      (shortBinaryNumeralTerm sourceCount))
  let rowFormula := compactAdditiveNatListAtRowsAtValuationIndexFormula
    tokenTable width tokenCount targetBoundary targetCount value
    (shortBinaryNumeralTerm sourceCount)
  let fullFormula := targetFinishFormula ⋏
    (targetCountFormula ⋏ (sliceFormula ⋏ rowFormula))
  let syntaxResource := appendOneFullFormulaCodePolynomial bitBound + 1
  let equalityResource := appendOneEqualityFixedPayloadPolynomial bitBound
  let sliceResource := appendOneSliceFixedPayloadPolynomial numericBound
    bitBound
  let rowResource :=
    compactAdditiveNatListAtRowsExactValueFullyFixedPayloadPolynomial
      numericBound bitBound
  have hfullAlignment : fullFormula =
      compactAdditiveNatListAppendOneValueExplicitFormula tokenTable width
        tokenCount sourceStart sourceFinish sourceCount targetStart targetFinish
        targetBoundary targetCount value := by
    rfl
  have hfullClosed : fullFormula.freeVariables = ∅ := by
    rw [hfullAlignment]
    exact compactAdditiveNatListAppendOneValueExplicitFormula_closed tokenTable
      width tokenCount sourceStart sourceFinish sourceCount targetStart
      targetFinish targetBoundary targetCount value
  have hfullCode : (binaryFormulaCode fullFormula).length <= syntaxResource := by
    have hraw :=
      compactAdditiveNatListAppendOneValueClosedFormula_code_length_le_fixed
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount value bitBound
        htableSize hwidthSize htokenCountSize hsourceStartSize hsourceFinishSize
        hsourceCountSize htargetStartSize htargetFinishSize htargetBoundarySize
        htargetCountSize hvalueSize
    rw [compactAdditiveNatListAppendOneValueClosedFormula_alignment] at hraw
    rw [hfullAlignment]
    dsimp only [syntaxResource]
    omega
  have hsyntaxPositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    omega
  let targetFinishCertificate := equalityCertificate
    (shortBinaryNumeralTerm targetFinish)
    (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
      (shortBinaryNumeralTerm targetCount)) (by
        simpa [termValue_shortBinaryNumeralTerm] using htargetFinish)
  let targetCountCertificate := equalityCertificate
    (shortBinaryNumeralTerm targetCount)
    (FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm
      (shortBinaryNumeralTerm sourceCount)) (by
        simpa [termValue_shortBinaryNumeralTerm] using htargetCount)
  let sliceCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
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
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.2.2.1)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.2.2.2.1)
      (by
        intro offset hoffset bitIndex hbitIndex
        have hbitIndex' : bitIndex < width := by
          simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
        simpa [termValue_shortBinaryNumeralTerm] using
          hsliceSpec.2.2.2.2.2 offset hoffset bitIndex hbitIndex')
  let rowCertificateExact :=
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph
      appendOneFixedValuation tokenTable width tokenCount targetBoundary
      targetCount sourceCount value (shortBinaryNumeralTerm sourceCount)
      (shortBinaryNumeralTerm value)
      (by simp [termValue_shortBinaryNumeralTerm])
      (by simp [termValue_shortBinaryNumeralTerm]) hrows
  let rowCertificate : CheckedHybridValuationBoundedFormulaCertificate
      appendOneFixedValuation rowFormula :=
    .cast
      (compactAdditiveNatListAtRowsAtValuationIndexValue_shortNumeral_alignment
        tokenTable width tokenCount targetBoundary targetCount value
        (shortBinaryNumeralTerm sourceCount))
      rowCertificateExact
  let sliceRowCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      sliceCertificate rowCertificate
  let countTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      targetCountCertificate sliceRowCertificate
  let directCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      targetFinishCertificate countTailCertificate
  have htargetFinishLeftCode := appendSourcePrefixShortNumeral_code_le
    targetFinish bitBound htargetFinishSize
  have htargetFinishRightCode :
      (binaryTermCode
        (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
          (shortBinaryNumeralTerm targetCount))).length <=
        appendOneTermCodePolynomial bitBound := by
    unfold appendOneTermCodePolynomial
    simpa only [appendOneTargetFinishTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.addTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.successorTerm]
      using appendSourcePrefixAddSuccessorAndShort_code_le targetStart
        targetCount bitBound htargetStartSize htargetCountSize
  have htargetFinishLeftClosed :
      (shortBinaryNumeralTerm targetFinish : ValuationTerm).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have htargetFinishRightClosed :
      (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm targetCount)).freeVariables = ∅ := by
    simpa only [appendOneTargetFinishTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.addTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.successorTerm]
      using appendSourcePrefixAddSuccessorAndShort_closed targetStart
        targetCount
  have htargetCountLeftCode := appendSourcePrefixShortNumeral_code_le
    targetCount bitBound htargetCountSize
  have htargetCountRightCode :
      (binaryTermCode
        (FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm
          (shortBinaryNumeralTerm sourceCount))).length <=
        appendOneTermCodePolynomial bitBound := by
    unfold appendOneTermCodePolynomial
    simpa only [
      FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.successorTerm]
      using appendSourcePrefixSuccessorShortNumeral_code_le sourceCount
        bitBound hsourceCountSize
  have htargetCountLeftClosed :
      (shortBinaryNumeralTerm targetCount : ValuationTerm).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have htargetCountRightClosed :
      (FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm
        (shortBinaryNumeralTerm sourceCount)).freeVariables = ∅ := by
    simpa only [
      FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm,
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.successorTerm]
      using appendSourcePrefixSuccessorShortNumeral_closed sourceCount
  have htargetFinishResource :
      hybridFormulaStructuralPayloadBound targetFinishCertificate <=
        equalityResource := by
    have htransparent := equalityCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm targetFinish)
      (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm targetCount)) (by
          simpa [termValue_shortBinaryNumeralTerm] using htargetFinish)
    exact htransparent.trans (appendOneEqualityPayloadEnvelope_le_fixed _ _
      bitBound htargetFinishLeftClosed htargetFinishRightClosed
      htargetFinishLeftCode htargetFinishRightCode)
  have htargetCountResource :
      hybridFormulaStructuralPayloadBound targetCountCertificate <=
        equalityResource := by
    have htransparent := equalityCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm targetCount)
      (FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.successorTerm
        (shortBinaryNumeralTerm sourceCount)) (by
          simpa [termValue_shortBinaryNumeralTerm] using htargetCount)
    exact htransparent.trans (appendOneEqualityPayloadEnvelope_le_fixed _ _
      bitBound htargetCountLeftClosed htargetCountRightClosed
      htargetCountLeftCode htargetCountRightCode)
  have hsliceResource :
      hybridFormulaStructuralPayloadBound sliceCertificate <= sliceResource := by
    simpa only [sliceCertificate, sliceCount, sliceResource] using
      appendOneTokenSliceCertificate_structuralPayloadBound_le_fixed
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart sliceCount numericBound bitBound hsliceSpec.1
        hsliceSpec.2.1 hsliceSpec.2.2.1 hsliceSpec.2.2.2.1
        hsliceSpec.2.2.2.2.1 hsliceSpec.2.2.2.2.2 htableSize hwidthSize
        htokenCountSize hsourceStartSize hsourceFinishSize hsourceCountSize
        htargetStartSize hwidthBound hsourceStartBound htargetStartBound
        htokenCountBound hnumericSize
  have hrowResource :
      hybridFormulaStructuralPayloadBound rowCertificate <= rowResource := by
    have hindexCode :
        (binaryTermCode (shortBinaryNumeralTerm sourceCount)).length <=
          natListAtRowsExactIndexCodeEnvelope bitBound := by
      exact binaryNumeralTerm_code_length_le_envelope sourceCount bitBound
        hsourceCountSize
    have hvalueCode :
        (binaryTermCode (shortBinaryNumeralTerm value)).length <=
          binaryNumeralTermCodeEnvelope bitBound :=
      binaryNumeralTerm_code_length_le_envelope value bitBound hvalueSize
    have hfixed :=
      compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount targetBoundary targetCount sourceCount value
        numericBound bitBound (shortBinaryNumeralTerm sourceCount)
        (shortBinaryNumeralTerm value) hrows
        (by simp [termValue_shortBinaryNumeralTerm])
        (by simp [termValue_shortBinaryNumeralTerm])
        (shortBinaryNumeralTerm_freeVariables_eq_empty sourceCount)
        (shortBinaryNumeralTerm_freeVariables_eq_empty value) hwidthBound
        htokenCountBound htargetCountBound htableSize hwidthSize
        htokenCountSize htargetBoundarySize htargetCountSize hsourceCountSize
        hvalueSize hindexCode hvalueCode
    change hybridFormulaStructuralPayloadBound rowCertificateExact <=
      rowResource at hfixed
    change hybridFormulaStructuralPayloadBound rowCertificateExact <= _
    exact hfixed
  have hsliceRowRaw := transparentHybridConjunctionPayloadBound_le
    sliceCertificate rowCertificate sliceResource rowResource hsliceResource
    hrowResource
  have hcountTailRaw := transparentHybridConjunctionPayloadBound_le
    targetCountCertificate sliceRowCertificate equalityResource
    (transparentHybridConjunctionPayloadEnvelope appendOneFixedValuation
      sliceFormula rowFormula sliceResource rowResource)
    htargetCountResource hsliceRowRaw
  have hfullRaw := transparentHybridConjunctionPayloadBound_le
    targetFinishCertificate countTailCertificate equalityResource
    (transparentHybridConjunctionPayloadEnvelope appendOneFixedValuation
      targetCountFormula (sliceFormula ⋏ rowFormula) equalityResource
      (transparentHybridConjunctionPayloadEnvelope appendOneFixedValuation
        sliceFormula rowFormula sliceResource rowResource))
    htargetFinishResource hcountTailRaw
  have hassembly :=
    transparentHybridFourConjunctionPayloadEnvelope_le_closedGeneral
      appendOneFixedValuation targetFinishFormula targetCountFormula
      sliceFormula rowFormula equalityResource equalityResource sliceResource
      rowResource syntaxResource hsyntaxPositive hfullClosed hfullCode
  have hfixed := hfullRaw.trans hassembly
  convert hfixed using 1 <;>
    (try simp only [
      compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph,
      compactAdditiveNatListAppendOneValueExplicitHybridCertificateDirectOfGraph,
      hybridFormulaStructuralPayloadBound, appendOneFullyFixedPayloadPolynomial,
      sliceCount, targetFinishFormula, targetCountFormula, sliceFormula,
      rowFormula, fullFormula, syntaxResource, equalityResource, sliceResource,
      rowResource, targetFinishCertificate, targetCountCertificate,
      sliceCertificate, rowCertificate, sliceRowCertificate,
      countTailCertificate, directCertificate]) <;>
    (try (congr 1 <;> apply proof_irrel_heq))

#print axioms
  compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectNatListAppendOneValueFullyFixedBounds
