import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectRawFreeVariables
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectAlignment
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsDirectSyntax

/-! # Closedness after installing the thirty-one endpoint witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectFreeVariables

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsDirectSyntax
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectAlignment

theorem compactFormulaTransformInitialFinalRowsClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    (compactFormulaTransformInitialFinalRowsClosedFormula tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity witness).freeVariables = ∅ := by
  rw [compactFormulaTransformInitialFinalRowsClosedFormula_alignment_public]
  exact
    compactFormulaTransformInitialFinalRowsPublicExplicitFormula_freeVariables_eq_empty
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity witness

theorem compactFormulaTransformInitialFinalBoundedDirectInstalledTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    (compactFormulaTransformInitialFinalBoundedDirectRawTerminal tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity ⇜
        (fun coordinate => shortBinaryNumeralTerm
          (compactFormulaTransformInitialFinalBoundedDirectWitnessValues
            witness coordinate))).freeVariables = ∅ := by
  rw [compactFormulaTransformInitialFinalBoundedDirectRawTerminal_alignment]
  exact compactFormulaTransformInitialFinalRowsClosedFormula_freeVariables_eq_empty
    tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
    inputCount expectedOutputBoundary expectedOutputCount
    expectedSuffixBoundary expectedSuffixCount binderArity witness

#print axioms
  compactFormulaTransformInitialFinalBoundedDirectInstalledTerminal_freeVariables_eq_empty

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectFreeVariables
