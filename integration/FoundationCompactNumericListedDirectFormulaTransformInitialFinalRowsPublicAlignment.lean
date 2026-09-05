import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsPublicFormula

/-! # Alignment of the closed endpoint formula with its public seven leaves -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsDirectSyntax

open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalExplicitHybridCertificate
open FoundationCompactPAValuationTermCompiler

private theorem conjunctionSeven_replace_third
    {first second third third' fourth fifth sixth seventh :
      ValuationFormula}
    (hthird : third = third') :
    first ⋏ (second ⋏ (third ⋏ (fourth ⋏ (fifth ⋏ (sixth ⋏ seventh))))) =
      first ⋏
        (second ⋏ (third' ⋏ (fourth ⋏ (fifth ⋏ (sixth ⋏ seventh))))) := by
  rw [hthird]

theorem compactFormulaTransformInitialFinalRowsClosedFormula_alignment_public
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    compactFormulaTransformInitialFinalRowsClosedFormula
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity witness =
      compactFormulaTransformInitialFinalRowsPublicExplicitFormula
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity witness := by
  refine (compactFormulaTransformInitialFinalRowsClosedFormula_alignment
    tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
    inputCount expectedOutputBoundary expectedOutputCount
    expectedSuffixBoundary expectedSuffixCount binderArity witness).trans ?_
  unfold compactFormulaTransformInitialFinalRowsExplicitFormula
  unfold compactFormulaTransformInitialFinalRowsPublicExplicitFormula
  apply conjunctionSeven_replace_third
  unfold compactFormulaTransformInitialParserSourcePublicFormula
  rfl

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsDirectSyntax
