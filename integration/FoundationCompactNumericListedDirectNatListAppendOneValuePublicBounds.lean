import integration.FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectTokenSlicePublicBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resources for appending one natural-list value

The graph fixes the copied slice and final row.  This file charges the two
arithmetic equalities, the actual slice certificate, and the actual row
certificate without accepting a payload resource from the caller.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListAppendOneValuePublicBounds

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListAppendOneValue
open FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsPublicBounds

private abbrev appendOneZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate.zeroValuation

def appendOneEqualityPayloadEnvelope
    (left right : ValuationTerm) : Nat :=
  compilePositiveRelationPayloadResource appendOneZeroValuation
    Language.Eq.eq ![left, right]

theorem equalityCertificate_structuralPayloadBound_le_transparent
    (left right : ValuationTerm)
    (hequality : termValue appendOneZeroValuation left =
      termValue appendOneZeroValuation right) :
    hybridFormulaStructuralPayloadBound
        (equalityCertificate left right hequality) <=
      appendOneEqualityPayloadEnvelope left right := by
  simp only [equalityCertificate, appendOneEqualityPayloadEnvelope]
  exact le_rfl

noncomputable def compactAdditiveNatListAppendOneValueGraphPayloadEnvelope
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value : Nat)
    (hgraph : CompactAdditiveNatListAppendOneValue tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount value) : Nat :=
  let sliceCount := Classical.choose hgraph.2.2.1
  let targetFinishFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetFinish) =
      !!(appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm targetCount))”
  let targetCountFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(successorTerm (shortBinaryNumeralTerm sourceCount))”
  let sliceFormula := compactFixedWidthTokenSlicesEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (successorTerm (shortBinaryNumeralTerm sourceStart))
    (shortBinaryNumeralTerm sourceFinish)
    (successorTerm (shortBinaryNumeralTerm targetStart))
    (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
      (shortBinaryNumeralTerm sourceCount))
  let rowFormula := compactAdditiveNatListAtRowsAtValuationIndexFormula
    tokenTable width tokenCount targetBoundary targetCount value
    (shortBinaryNumeralTerm sourceCount)
  let targetFinishResource := appendOneEqualityPayloadEnvelope
    (shortBinaryNumeralTerm targetFinish)
    (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
      (shortBinaryNumeralTerm targetCount))
  let targetCountResource := appendOneEqualityPayloadEnvelope
    (shortBinaryNumeralTerm targetCount)
    (successorTerm (shortBinaryNumeralTerm sourceCount))
  let sliceResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope
      appendOneZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm sourceFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm sourceCount)) sliceCount
  let hindexValue : termValue
      FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
      (shortBinaryNumeralTerm sourceCount) = sourceCount := by
    simp [termValue_shortBinaryNumeralTerm]
  let rowResource :=
    compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope
      tokenTable width tokenCount targetBoundary targetCount sourceCount value
      (shortBinaryNumeralTerm sourceCount) hindexValue hgraph.2.2.2
  let sliceRowResource := transparentHybridConjunctionPayloadEnvelope
    appendOneZeroValuation sliceFormula rowFormula sliceResource rowResource
  let countTailResource := transparentHybridConjunctionPayloadEnvelope
    appendOneZeroValuation targetCountFormula (sliceFormula ⋏ rowFormula)
    targetCountResource sliceRowResource
  transparentHybridConjunctionPayloadEnvelope appendOneZeroValuation
    targetFinishFormula (targetCountFormula ⋏ (sliceFormula ⋏ rowFormula))
    targetFinishResource countTailResource

theorem
    compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value : Nat)
    (hgraph : CompactAdditiveNatListAppendOneValue tokenTable width tokenCount
      sourceStart sourceFinish sourceCount targetStart targetFinish
      targetBoundary targetCount value) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceStart sourceFinish sourceCount
          targetStart targetFinish targetBoundary targetCount value hgraph) <=
      compactAdditiveNatListAppendOneValueGraphPayloadEnvelope tokenTable width
        tokenCount sourceStart sourceFinish sourceCount targetStart targetFinish
        targetBoundary targetCount value hgraph := by
  rcases hgraph with ⟨htargetFinish, htargetCount, hslices, hrows⟩
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
  have hsliceCountBound : sliceCount <= termValue appendOneZeroValuation
      (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.1
  have hsourceEndpoint : termValue appendOneZeroValuation
      (shortBinaryNumeralTerm sourceFinish) =
        termValue appendOneZeroValuation
          (successorTerm (shortBinaryNumeralTerm sourceStart)) + sliceCount := by
    simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.1
  have htargetEndpoint : termValue appendOneZeroValuation
      (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm sourceCount)) =
        termValue appendOneZeroValuation
          (successorTerm (shortBinaryNumeralTerm targetStart)) + sliceCount := by
    simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.2.1
  have hsourceFinishBound : termValue appendOneZeroValuation
      (shortBinaryNumeralTerm sourceFinish) <=
        termValue appendOneZeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.2.2.1
  have htargetFinishBound : termValue appendOneZeroValuation
      (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm sourceCount)) <=
        termValue appendOneZeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hsliceSpec.2.2.2.2.1
  have hbits : ∀ offset < sliceCount,
      ∀ bitIndex < termValue appendOneZeroValuation
        (shortBinaryNumeralTerm width),
        (termValue appendOneZeroValuation
          (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue appendOneZeroValuation
                (successorTerm (shortBinaryNumeralTerm sourceStart)) + offset) *
              termValue appendOneZeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) =
          (termValue appendOneZeroValuation
            (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue appendOneZeroValuation
                (successorTerm (shortBinaryNumeralTerm targetStart)) + offset) *
              termValue appendOneZeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) := by
    intro offset hoffset bitIndex hbitIndex
    have hbitIndex' : bitIndex < width := by
      simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
    simpa [termValue_shortBinaryNumeralTerm] using
      hsliceSpec.2.2.2.2.2 offset hoffset bitIndex hbitIndex'
  have hindexClosed :
      (shortBinaryNumeralTerm sourceCount).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hindexValue : termValue
      FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
      (shortBinaryNumeralTerm sourceCount) = sourceCount := by
    simp [termValue_shortBinaryNumeralTerm]
  let sliceCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      appendOneZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm sourceFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm sourceCount)) sliceCount hsliceCountBound
      hsourceEndpoint htargetEndpoint hsourceFinishBound htargetFinishBound hbits
  let rowCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount targetBoundary targetCount sourceCount value
      (shortBinaryNumeralTerm sourceCount) hindexValue hrows
  have htargetFinishValue : termValue appendOneZeroValuation
      (shortBinaryNumeralTerm targetFinish) =
        termValue appendOneZeroValuation
          (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
            (shortBinaryNumeralTerm targetCount)) := by
    simpa [termValue_shortBinaryNumeralTerm] using htargetFinish
  have htargetCountValue : termValue appendOneZeroValuation
      (shortBinaryNumeralTerm targetCount) =
        termValue appendOneZeroValuation
          (successorTerm (shortBinaryNumeralTerm sourceCount)) := by
    simpa [termValue_shortBinaryNumeralTerm] using htargetCount
  let targetFinishCertificate := equalityCertificate
    (shortBinaryNumeralTerm targetFinish)
    (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
      (shortBinaryNumeralTerm targetCount)) htargetFinishValue
  let targetCountCertificate := equalityCertificate
    (shortBinaryNumeralTerm targetCount)
    (successorTerm (shortBinaryNumeralTerm sourceCount)) htargetCountValue
  have hsliceResource :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_transparent
      appendOneZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm sourceFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm sourceCount)) sliceCount hsliceCountBound
      hsourceEndpoint htargetEndpoint hsourceFinishBound htargetFinishBound hbits
  have hrowResource :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount targetBoundary targetCount sourceCount value
      (shortBinaryNumeralTerm sourceCount) hindexClosed hindexValue hrows
  have htargetFinishResource :=
    equalityCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm targetFinish)
      (appendOneTargetFinishTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm targetCount)) htargetFinishValue
  have htargetCountResource :=
    equalityCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm targetCount)
      (successorTerm (shortBinaryNumeralTerm sourceCount)) htargetCountValue
  let sliceRow := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    sliceCertificate rowCertificate
  have hsliceRow := transparentHybridConjunctionPayloadBound_le
    sliceCertificate rowCertificate _ _ hsliceResource hrowResource
  let countTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    targetCountCertificate sliceRow
  have hcountTail := transparentHybridConjunctionPayloadBound_le
    targetCountCertificate sliceRow _ _ htargetCountResource hsliceRow
  let direct := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    targetFinishCertificate countTail
  have hdirect := transparentHybridConjunctionPayloadBound_le
    targetFinishCertificate countTail _ _ htargetFinishResource hcountTail
  unfold compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph
  simp only [hybridFormulaStructuralPayloadBound]
  change hybridFormulaStructuralPayloadBound direct <= _
  simpa only [compactAdditiveNatListAppendOneValueGraphPayloadEnvelope,
    sliceCount] using hdirect

#print axioms equalityCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent

end FoundationCompactNumericListedDirectNatListAppendOneValuePublicBounds
