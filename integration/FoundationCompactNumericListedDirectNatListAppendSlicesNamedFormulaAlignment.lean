import integration.FoundationCompactNumericListedDirectNatListAppendSlicesNamedResources

/-! # Alignment and closedness of the named append-slices formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 250000

namespace FoundationCompactNumericListedDirectNatListAppendSlicesNamedFormulaAlignment

open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesFormulaFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesNamedResources

theorem appendSlicesNamedFormula_eq_closedFormula
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat) :
    appendSlicesNamedCountFormula leftCount rightCount targetCount ⋏
        (appendSlicesNamedLeftFormula tokenTable width tokenCount leftStart
          leftFinish leftCount targetStart ⋏
        appendSlicesNamedRightFormula tokenTable width tokenCount rightStart
          rightFinish leftCount targetStart targetFinish) =
      compactAdditiveNatListAppendSlicesClosedFormula tokenTable width tokenCount
        leftStart leftFinish leftCount rightStart rightFinish rightCount
        targetStart targetFinish targetCount := by
  unfold appendSlicesNamedCountFormula appendSlicesNamedLeftFormula
    appendSlicesNamedRightFormula
  rw [compactAdditiveNatListAppendSlicesClosedFormula_alignment]
  rfl

theorem appendSlicesNamedFormula_closed
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat) :
    (appendSlicesNamedCountFormula leftCount rightCount targetCount ⋏
      (appendSlicesNamedLeftFormula tokenTable width tokenCount leftStart
        leftFinish leftCount targetStart ⋏
      appendSlicesNamedRightFormula tokenTable width tokenCount rightStart
        rightFinish leftCount targetStart targetFinish)).freeVariables = ∅ := by
  rw [appendSlicesNamedFormula_eq_closedFormula]
  rw [compactAdditiveNatListAppendSlicesClosedFormula_alignment]
  exact compactAdditiveNatListAppendSlicesExplicitFormula_closed tokenTable
    width tokenCount leftStart leftFinish leftCount rightStart rightFinish
    rightCount targetStart targetFinish targetCount

#print axioms appendSlicesNamedFormula_eq_closedFormula
#print axioms appendSlicesNamedFormula_closed

end FoundationCompactNumericListedDirectNatListAppendSlicesNamedFormulaAlignment
