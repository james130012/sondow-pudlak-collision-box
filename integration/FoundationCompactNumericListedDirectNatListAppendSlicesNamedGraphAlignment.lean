import integration.FoundationCompactNumericListedDirectNatListAppendSlicesNamedResources

/-! # Alignment of the original append-slices graph envelope -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 250000

namespace FoundationCompactNumericListedDirectNatListAppendSlicesNamedGraphAlignment

open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesNamedResources

theorem compactAdditiveNatListAppendSlicesGraphPayloadEnvelope_eq_named
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSlices tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount) :
    compactAdditiveNatListAppendSlicesGraphPayloadEnvelope tokenTable width
        tokenCount leftStart leftFinish leftCount rightStart rightFinish
        rightCount targetStart targetFinish targetCount hgraph =
      compactAdditiveNatListAppendSlicesNamedTransparentEnvelope tokenTable width
        tokenCount leftStart leftFinish leftCount rightStart rightFinish
        rightCount targetStart targetFinish targetCount hgraph := by
  unfold compactAdditiveNatListAppendSlicesGraphPayloadEnvelope
    compactAdditiveNatListAppendSlicesNamedTransparentEnvelope
    appendSlicesNamedCountFormula appendSlicesNamedLeftFormula
    appendSlicesNamedRightFormula appendSlicesNamedLeftResource
    appendSlicesNamedRightResource
  rfl

#print axioms compactAdditiveNatListAppendSlicesGraphPayloadEnvelope_eq_named

end FoundationCompactNumericListedDirectNatListAppendSlicesNamedGraphAlignment
