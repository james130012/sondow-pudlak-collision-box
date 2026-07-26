import integration.FoundationCompactNumericListedDirectNatListAppendSlicesNamedFixedResourceBound

/-! # Fully fixed resource for the append-slices graph -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 250000

namespace FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAppendSlicesPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesFormulaFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesNamedResources
open FoundationCompactNumericListedDirectNatListAppendSlicesNamedFormulaAlignment
open FoundationCompactNumericListedDirectNatListAppendSlicesGeneralPayloadBound
open FoundationCompactNumericListedDirectNatListAppendSlicesNamedFixedResourceBound
open FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedPolynomial

theorem compactAdditiveNatListAppendSlicesGraphPayloadEnvelope_le_fixed
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
    compactAdditiveNatListAppendSlicesGraphPayloadEnvelope tokenTable width
        tokenCount leftStart leftFinish leftCount rightStart rightFinish
        rightCount targetStart targetFinish targetCount hgraph <=
      appendSlicesFullyFixedPayloadPolynomial numericBound bitBound := by
  have hclosedCode :=
    compactAdditiveNatListAppendSlicesClosedFormula_code_length_le_fixed_of_graph
      tokenTable width tokenCount leftStart leftFinish leftCount rightStart
      rightFinish rightCount targetStart targetFinish targetCount numericBound
      bitBound hgraph htableSize hwidthBound htokenCountBound hrightCountBound
      htargetCountBound hnumericSize
  have hnamedCode :
      (binaryFormulaCode
        (appendSlicesNamedCountFormula leftCount rightCount targetCount ⋏
          (appendSlicesNamedLeftFormula tokenTable width tokenCount leftStart
              leftFinish leftCount targetStart ⋏
            appendSlicesNamedRightFormula tokenTable width tokenCount rightStart
              rightFinish leftCount targetStart targetFinish))).length <=
        appendSlicesFullFormulaCodePolynomial bitBound + 1 := by
    rw [appendSlicesNamedFormula_eq_closedFormula]
    exact hclosedCode.trans (Nat.le_add_right _ 1)
  have hgeneral :=
    compactAdditiveNatListAppendSlicesGraphPayloadEnvelope_le_general
      tokenTable width tokenCount leftStart leftFinish leftCount rightStart
      rightFinish rightCount targetStart targetFinish targetCount
      (appendSlicesFullFormulaCodePolynomial bitBound + 1) hgraph (by omega)
      hnamedCode
  have hfixed :=
    compactAdditiveNatListAppendSlicesNamedGeneralEnvelope_le_fixed tokenTable
      width tokenCount leftStart leftFinish leftCount rightStart rightFinish
      rightCount targetStart targetFinish targetCount numericBound bitBound
      hgraph htableSize hwidthBound htokenCountBound hrightCountBound
      htargetCountBound hnumericSize
  exact hgeneral.trans hfixed

#print axioms compactAdditiveNatListAppendSlicesGraphPayloadEnvelope_le_fixed

end FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedBound
