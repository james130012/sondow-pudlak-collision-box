import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectAlignmentSupport

/-! # Coordinate alignment for the thirty-one endpoint witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectTermAlignment

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectAlignmentSupport

theorem compactFormulaTransformInitialFinalBoundedDirectReverseIndex_involutive
    (coordinate : Fin 31) :
    compactFormulaTransformInitialFinalBoundedDirectReverseIndex
        (compactFormulaTransformInitialFinalBoundedDirectReverseIndex
          coordinate) = coordinate := by
  apply Fin.ext
  simp only [compactFormulaTransformInitialFinalBoundedDirectReverseIndex]
  omega

theorem compactFormulaTransformInitialFinalBoundedDirectRawTerms_alignment
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    (fun coordinate =>
      Rew.subst (fun index => shortBinaryNumeralTerm
        (compactFormulaTransformInitialFinalBoundedDirectWitnessValues
          witness index))
        (compactFormulaTransformInitialFinalBoundedDirectRawTerms
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity coordinate)) =
      compactFormulaTransformInitialFinalBoundedDirectClosedTerms tokenTable
        width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity witness := by
  funext coordinate
  unfold compactFormulaTransformInitialFinalBoundedDirectRawTerms
    compactFormulaTransformInitialFinalBoundedDirectClosedTerms
  simp only [Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · exact substitute_sourceSubstitutionLift31
      (fun index => shortBinaryNumeralTerm
        (compactFormulaTransformInitialFinalBoundedDirectWitnessValues
          witness index))
      (compactFormulaTransformInitialFinalBoundedDirectPublicTerms tokenTable
        width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity ⟨coordinate, hcoordinate⟩)
  · simp only [compactFormulaTransformInitialFinalBoundedDirectRawWitnessTerms,
      compactFormulaTransformInitialFinalBoundedDirectClosedWitnessTerms,
      compactFormulaTransformInitialFinalBoundedDirectWitnessValues,
      Rew.subst_bvar]
    rw [compactFormulaTransformInitialFinalBoundedDirectReverseIndex_involutive]

#print axioms
  compactFormulaTransformInitialFinalBoundedDirectRawTerms_alignment

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectTermAlignment
