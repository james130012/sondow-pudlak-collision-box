import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectOriginalRawSyntax

/-! # Equality of the original and split thirty-one-witness matrices -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectOriginalSplitAlignment

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectOriginalRawSyntax

theorem compactFormulaTransformInitialFinalBoundedDirectOriginalRawTerminal_eq_split
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat) :
    compactFormulaTransformInitialFinalBoundedDirectOriginalRawTerminal
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity =
      compactFormulaTransformInitialFinalBoundedDirectRawTerminal tokenTable
        width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity := by
  unfold compactFormulaTransformInitialFinalBoundedDirectOriginalRawTerminal
    compactFormulaTransformInitialFinalBoundedDirectRawTerminal
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [compactFormulaTransformInitialFinalBoundedDirectOriginalRawTerms,
      compactFormulaTransformInitialFinalBoundedDirectRawTerms,
      compactFormulaTransformInitialFinalBoundedDirectRawPublicTerms,
      compactFormulaTransformInitialFinalBoundedDirectPublicTerms,
      compactFormulaTransformInitialFinalBoundedDirectRawWitnessTerms,
      compactFormulaTransformInitialFinalBoundedDirectReverseIndex,
      Matrix.vecAppend_eq_ite]

theorem compactFormulaTransformInitialFinalBoundedClosedFormula_alignment_split
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    compactFormulaTransformInitialFinalBoundedClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity valueBound =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 31
        (compactFormulaTransformInitialFinalBoundedDirectRawTerminal tokenTable
          width tokenCount stateBoundary stateCount fuel inputBoundary
          inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity) := by
  calc
    _ = explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 31
        (compactFormulaTransformInitialFinalBoundedDirectOriginalRawTerminal
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity) :=
      compactFormulaTransformInitialFinalBoundedClosedFormula_alignment_originalRaw
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound
    _ = _ := congrArg
      (explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 31)
      (compactFormulaTransformInitialFinalBoundedDirectOriginalRawTerminal_eq_split
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity)

#print axioms
  compactFormulaTransformInitialFinalBoundedDirectOriginalRawTerminal_eq_split
#print axioms
  compactFormulaTransformInitialFinalBoundedClosedFormula_alignment_split

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectOriginalSplitAlignment
