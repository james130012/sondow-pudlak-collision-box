import integration.FoundationCompactNumericListedDirectNatListAppendSlicesGeneralPayloadBound

/-! # Fixed local resources for the named append-slices envelope -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 250000

namespace FoundationCompactNumericListedDirectNatListAppendSlicesNamedFixedResourceBound

open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesFormulaFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesNamedResources
open FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedPolynomial

theorem compactAdditiveNatListAppendSlicesNamedGeneralEnvelope_le_fixed
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
    (hrightCountBound : rightCount <= numericBound)
    (htargetCountBound : targetCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListAppendSlicesNamedGeneralEnvelope tokenTable width
        tokenCount leftStart leftFinish leftCount rightStart rightFinish
        rightCount targetStart targetFinish targetCount hgraph
        (appendSlicesFullFormulaCodePolynomial bitBound + 1) <=
      appendSlicesFullyFixedPayloadPolynomial numericBound bitBound := by
  let leftSliceCount := Classical.choose hgraph.2.1
  let rightSliceCount := Classical.choose hgraph.2.2
  let countResource := appendSlicesCountPayloadEnvelope leftCount rightCount
    targetCount
  let leftResource := appendSlicesNamedLeftResource tokenTable width tokenCount
    leftStart leftFinish leftCount targetStart leftSliceCount
  let rightResource := appendSlicesNamedRightResource tokenTable width tokenCount
    rightStart rightFinish leftCount targetStart targetFinish rightSliceCount
  let countFixed := appendSlicesCountFixedPayloadPolynomial bitBound
  let slicesFixed :=
    appendSlicesTokenSlicesFixedPayloadPolynomial numericBound bitBound
  have hleftSpec := Classical.choose_spec hgraph.2.1
  have hleftCountSize : Nat.size leftCount <= bitBound :=
    (Nat.size_le_size (show leftCount <= numericBound by omega)).trans
      hnumericSize
  have hrightCountSize : Nat.size rightCount <= bitBound :=
    (Nat.size_le_size hrightCountBound).trans hnumericSize
  have htargetCountSize : Nat.size targetCount <= bitBound :=
    (Nat.size_le_size htargetCountBound).trans hnumericSize
  have hcount : countResource <= countFixed := by
    exact appendSlicesCountPayloadEnvelope_le_fixed leftCount rightCount
      targetCount bitBound hleftCountSize hrightCountSize htargetCountSize
  have hslices : leftResource + rightResource <= slicesFixed := by
    simpa only [leftSliceCount, rightSliceCount, leftResource, rightResource,
      appendSlicesNamedLeftResource, appendSlicesNamedRightResource,
      slicesFixed] using
      appendSlicesTokenSlicesResource_le_fixed tokenTable width tokenCount
        leftStart leftFinish leftCount rightStart rightFinish rightCount
        targetStart targetFinish targetCount numericBound bitBound hgraph
        htableSize hwidthBound htokenCountBound hnumericSize
  have hleft : leftResource <= slicesFixed := by omega
  have hright : rightResource <= slicesFixed := by omega
  have hmono :
      hybridThreeConjunctionGeneralPayloadEnvelope
          (appendSlicesFullFormulaCodePolynomial bitBound + 1) countResource
          leftResource rightResource <=
        hybridThreeConjunctionGeneralPayloadEnvelope
          (appendSlicesFullFormulaCodePolynomial bitBound + 1) countFixed
          slicesFixed slicesFixed :=
    appendSlicesHybridThreeConjunctionGeneralPayloadEnvelope_mono hcount hleft
      hright
  unfold compactAdditiveNatListAppendSlicesNamedGeneralEnvelope
    appendSlicesFullyFixedPayloadPolynomial
  simpa only [leftSliceCount, rightSliceCount, countResource, leftResource,
    rightResource, countFixed, slicesFixed] using hmono

#print axioms compactAdditiveNatListAppendSlicesNamedGeneralEnvelope_le_fixed

end FoundationCompactNumericListedDirectNatListAppendSlicesNamedFixedResourceBound
