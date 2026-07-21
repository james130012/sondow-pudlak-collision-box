import integration.FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectTokenSlicePublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resources for appending two natural-list slices

The graph supplies both concrete slice witnesses.  The public envelope charges
the count equality and the two actual slice certificates without accepting a
payload resource from the caller.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListAppendSlicesPublicBounds

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds

private abbrev appendSlicesZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate.zeroValuation

def appendSlicesCountPayloadEnvelope
    (leftCount rightCount targetCount : Nat) : Nat :=
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm leftCount) +
      !!(shortBinaryNumeralTerm rightCount)’
  compilePositiveRelationPayloadResource appendSlicesZeroValuation
    Language.Eq.eq ![shortBinaryNumeralTerm targetCount, rightTerm]

theorem appendCountCertificate_structuralPayloadBound_le_transparent
    (leftCount rightCount targetCount : Nat)
    (hcount : targetCount = leftCount + rightCount) :
    hybridFormulaStructuralPayloadBound
        (appendCountCertificate leftCount rightCount targetCount hcount) <=
      appendSlicesCountPayloadEnvelope leftCount rightCount targetCount := by
  simp only [appendCountCertificate, hybridFormulaStructuralPayloadBound,
    appendSlicesCountPayloadEnvelope]
  exact le_rfl

noncomputable def compactAdditiveNatListAppendSlicesGraphPayloadEnvelope
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSlices tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount) : Nat :=
  let leftSliceCount := Classical.choose hgraph.2.1
  let rightSliceCount := Classical.choose hgraph.2.2
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm leftCount) +
        !!(shortBinaryNumeralTerm rightCount)”
  let leftFormula := compactFixedWidthTokenSlicesEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (successorTerm (shortBinaryNumeralTerm leftStart))
    (shortBinaryNumeralTerm leftFinish)
    (successorTerm (shortBinaryNumeralTerm targetStart))
    (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
      (shortBinaryNumeralTerm leftCount))
  let rightFormula := compactFixedWidthTokenSlicesEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (successorTerm (shortBinaryNumeralTerm rightStart))
    (shortBinaryNumeralTerm rightFinish)
    (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
      (shortBinaryNumeralTerm leftCount))
    (shortBinaryNumeralTerm targetFinish)
  let countResource := appendSlicesCountPayloadEnvelope leftCount rightCount
    targetCount
  let leftResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope
      appendSlicesZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm leftCount)) leftSliceCount
  let rightResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope
      appendSlicesZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm rightStart))
      (shortBinaryNumeralTerm rightFinish)
      (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish) rightSliceCount
  let slicesResource := transparentHybridConjunctionPayloadEnvelope
    appendSlicesZeroValuation leftFormula rightFormula leftResource rightResource
  transparentHybridConjunctionPayloadEnvelope appendSlicesZeroValuation
    countFormula (leftFormula ⋏ rightFormula) countResource slicesResource

theorem
    compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSlices tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph
          tokenTable width tokenCount leftStart leftFinish leftCount rightStart
          rightFinish rightCount targetStart targetFinish targetCount hgraph) <=
      compactAdditiveNatListAppendSlicesGraphPayloadEnvelope tokenTable width
        tokenCount leftStart leftFinish leftCount rightStart rightFinish
        rightCount targetStart targetFinish targetCount hgraph := by
  rcases hgraph with ⟨hcount, hleft, hright⟩
  let leftSliceCount := Classical.choose hleft
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
    simpa [leftSliceCount, Nat.add_assoc] using Classical.choose_spec hleft
  let rightSliceCount := Classical.choose hright
  have hrightSpec :
      rightSliceCount <= tokenCount ∧
      rightFinish = rightStart + 1 + rightSliceCount ∧
      targetFinish = targetStart + 1 + leftCount + rightSliceCount ∧
      rightFinish <= tokenCount ∧
      targetFinish <= tokenCount ∧
      ∀ offset < rightSliceCount, ∀ bitIndex < width,
        tokenTable.testBit ((rightStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + leftCount + offset) * width + bitIndex) := by
    simpa [rightSliceCount, Nat.add_assoc] using Classical.choose_spec hright
  have hleftCountBound : leftSliceCount <= termValue appendSlicesZeroValuation
      (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.1
  have hleftSourceEndpoint : termValue appendSlicesZeroValuation
      (shortBinaryNumeralTerm leftFinish) =
        termValue appendSlicesZeroValuation
          (successorTerm (shortBinaryNumeralTerm leftStart)) +
          leftSliceCount := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.1
  have hleftTargetEndpoint : termValue appendSlicesZeroValuation
      (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm leftCount)) =
        termValue appendSlicesZeroValuation
          (successorTerm (shortBinaryNumeralTerm targetStart)) +
          leftSliceCount := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.2.1
  have hleftSourceFinish : termValue appendSlicesZeroValuation
      (shortBinaryNumeralTerm leftFinish) <=
        termValue appendSlicesZeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.2.2.1
  have hleftTargetFinish : termValue appendSlicesZeroValuation
      (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm leftCount)) <=
        termValue appendSlicesZeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.2.2.2.1
  have hleftBits : ∀ offset < leftSliceCount,
      ∀ bitIndex < termValue appendSlicesZeroValuation
        (shortBinaryNumeralTerm width),
        (termValue appendSlicesZeroValuation
          (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue appendSlicesZeroValuation
                (successorTerm (shortBinaryNumeralTerm leftStart)) + offset) *
              termValue appendSlicesZeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) =
          (termValue appendSlicesZeroValuation
            (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue appendSlicesZeroValuation
                (successorTerm (shortBinaryNumeralTerm targetStart)) + offset) *
              termValue appendSlicesZeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) := by
    intro offset hoffset bitIndex hbitIndex
    have hbitIndex' : bitIndex < width := by
      simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
    simpa [termValue_shortBinaryNumeralTerm] using
      hleftSpec.2.2.2.2.2 offset hoffset bitIndex hbitIndex'
  have hrightCountBound : rightSliceCount <= termValue appendSlicesZeroValuation
      (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hrightSpec.1
  have hrightSourceEndpoint : termValue appendSlicesZeroValuation
      (shortBinaryNumeralTerm rightFinish) =
        termValue appendSlicesZeroValuation
          (successorTerm (shortBinaryNumeralTerm rightStart)) +
          rightSliceCount := by
    simpa [termValue_shortBinaryNumeralTerm] using hrightSpec.2.1
  have hrightTargetEndpoint : termValue appendSlicesZeroValuation
      (shortBinaryNumeralTerm targetFinish) =
        termValue appendSlicesZeroValuation
          (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
            (shortBinaryNumeralTerm leftCount)) + rightSliceCount := by
    simpa [termValue_shortBinaryNumeralTerm] using hrightSpec.2.2.1
  have hrightSourceFinish : termValue appendSlicesZeroValuation
      (shortBinaryNumeralTerm rightFinish) <=
        termValue appendSlicesZeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hrightSpec.2.2.2.1
  have hrightTargetFinish : termValue appendSlicesZeroValuation
      (shortBinaryNumeralTerm targetFinish) <=
        termValue appendSlicesZeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hrightSpec.2.2.2.2.1
  have hrightBits : ∀ offset < rightSliceCount,
      ∀ bitIndex < termValue appendSlicesZeroValuation
        (shortBinaryNumeralTerm width),
        (termValue appendSlicesZeroValuation
          (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue appendSlicesZeroValuation
                (successorTerm (shortBinaryNumeralTerm rightStart)) + offset) *
              termValue appendSlicesZeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) =
          (termValue appendSlicesZeroValuation
            (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue appendSlicesZeroValuation
                (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
                  (shortBinaryNumeralTerm leftCount)) + offset) *
              termValue appendSlicesZeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) := by
    intro offset hoffset bitIndex hbitIndex
    have hbitIndex' : bitIndex < width := by
      simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
    simpa [termValue_shortBinaryNumeralTerm] using
      hrightSpec.2.2.2.2.2 offset hoffset bitIndex hbitIndex'
  let leftCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      appendSlicesZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm leftCount)) leftSliceCount hleftCountBound
      hleftSourceEndpoint hleftTargetEndpoint hleftSourceFinish
      hleftTargetFinish hleftBits
  let rightCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      appendSlicesZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm rightStart))
      (shortBinaryNumeralTerm rightFinish)
      (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish) rightSliceCount hrightCountBound
      hrightSourceEndpoint hrightTargetEndpoint hrightSourceFinish
      hrightTargetFinish hrightBits
  let countCertificate := appendCountCertificate leftCount rightCount targetCount
    hcount
  have hleftResource :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_transparent
      appendSlicesZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm leftCount)) leftSliceCount hleftCountBound
      hleftSourceEndpoint hleftTargetEndpoint hleftSourceFinish
      hleftTargetFinish hleftBits
  have hrightResource :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_transparent
      appendSlicesZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm rightStart))
      (shortBinaryNumeralTerm rightFinish)
      (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish) rightSliceCount hrightCountBound
      hrightSourceEndpoint hrightTargetEndpoint hrightSourceFinish
      hrightTargetFinish hrightBits
  have hcountResource :=
    appendCountCertificate_structuralPayloadBound_le_transparent leftCount
      rightCount targetCount hcount
  let slices := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    leftCertificate rightCertificate
  have hslices := transparentHybridConjunctionPayloadBound_le
    leftCertificate rightCertificate _ _ hleftResource hrightResource
  let direct := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    countCertificate slices
  have hdirect := transparentHybridConjunctionPayloadBound_le
    countCertificate slices _ _ hcountResource hslices
  unfold compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph
  simp only [hybridFormulaStructuralPayloadBound]
  change hybridFormulaStructuralPayloadBound direct <= _
  simpa only [compactAdditiveNatListAppendSlicesGraphPayloadEnvelope,
    leftSliceCount, rightSliceCount] using hdirect

#print axioms appendCountCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent

end FoundationCompactNumericListedDirectNatListAppendSlicesPublicBounds
