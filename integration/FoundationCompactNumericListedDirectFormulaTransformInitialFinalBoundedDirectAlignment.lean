import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectTermAlignment

/-! # Alignment of the thirty-one endpoint witnesses with the closed matrix -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectAlignment

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectAlignmentSupport
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectTermAlignment

theorem compactFormulaTransformInitialFinalBoundedDirectRawTerminal_alignment
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    compactFormulaTransformInitialFinalBoundedDirectRawTerminal
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity ⇜
      (fun index => shortBinaryNumeralTerm
        (compactFormulaTransformInitialFinalBoundedDirectWitnessValues
          witness index)) =
    compactFormulaTransformInitialFinalRowsClosedFormula
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity witness := by
  change Rew.subst (fun index => shortBinaryNumeralTerm
      (compactFormulaTransformInitialFinalBoundedDirectWitnessValues
        witness index)) ▹
    compactFormulaTransformInitialFinalBoundedDirectRawTerminal
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity = _
  unfold compactFormulaTransformInitialFinalBoundedDirectRawTerminal
  rw [rewriting_embeddedFormulaSubstitution]
  rw [compactFormulaTransformInitialFinalRowsClosedFormula_eq_directTerms]
  congr 1
  exact compactFormulaTransformInitialFinalBoundedDirectRawTerms_alignment
    tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
    inputCount expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
    expectedSuffixCount binderArity witness

#print axioms
  compactFormulaTransformInitialFinalBoundedDirectRawTerminal_alignment

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectAlignment
