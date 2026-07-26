import integration.FoundationCompactNumericListedDirectNatListAppendSlicesNamedGraphAlignment
import integration.FoundationCompactNumericListedDirectNatListAppendSlicesNamedFormulaAlignment

/-! # General three-conjunction envelope for the append-slices graph -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 250000

namespace FoundationCompactNumericListedDirectNatListAppendSlicesGeneralPayloadBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAppendSlicesPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesNamedResources
open FoundationCompactNumericListedDirectNatListAppendSlicesNamedGraphAlignment
open FoundationCompactNumericListedDirectNatListAppendSlicesNamedFormulaAlignment

theorem compactAdditiveNatListAppendSlicesGraphPayloadEnvelope_le_general
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount syntaxResource : Nat)
    (hgraph : CompactAdditiveNatListAppendSlices tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount)
    (hpositive : 1 <= syntaxResource)
    (hcode :
      (binaryFormulaCode
        (appendSlicesNamedCountFormula leftCount rightCount targetCount ⋏
          (appendSlicesNamedLeftFormula tokenTable width tokenCount leftStart
              leftFinish leftCount targetStart ⋏
            appendSlicesNamedRightFormula tokenTable width tokenCount rightStart
              rightFinish leftCount targetStart targetFinish))).length <=
        syntaxResource) :
    compactAdditiveNatListAppendSlicesGraphPayloadEnvelope tokenTable width
        tokenCount leftStart leftFinish leftCount rightStart rightFinish
        rightCount targetStart targetFinish targetCount hgraph <=
      compactAdditiveNatListAppendSlicesNamedGeneralEnvelope tokenTable width
        tokenCount leftStart leftFinish leftCount rightStart rightFinish
        rightCount targetStart targetFinish targetCount hgraph syntaxResource := by
  rw [compactAdditiveNatListAppendSlicesGraphPayloadEnvelope_eq_named]
  unfold compactAdditiveNatListAppendSlicesNamedTransparentEnvelope
    compactAdditiveNatListAppendSlicesNamedGeneralEnvelope
  exact transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
    _ _ _ _ _ _ _ syntaxResource hpositive
      (appendSlicesNamedFormula_closed tokenTable width tokenCount leftStart
        leftFinish leftCount rightStart rightFinish rightCount targetStart
        targetFinish targetCount)
      hcode

#print axioms compactAdditiveNatListAppendSlicesGraphPayloadEnvelope_le_general

end FoundationCompactNumericListedDirectNatListAppendSlicesGeneralPayloadBound
