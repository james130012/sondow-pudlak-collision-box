import integration.FoundationCompactNumericListedDirectFormulaTransformInitialDefaultFinalFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound

/-!
# Public bounds for formula-transform endpoint witnesses

The total initial/default-final relation fixes two checked state rows and sets
its three reserved parser-output coordinates to zero.  Consequently all
thirty-one endpoint fields fit the same public width used by adjacent rows.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformEndpointWitnessBound

open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialDefaultFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound

theorem CompactFormulaTransformInitialDefaultFinalRows.endpointValuesFit
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound : Nat}
    {witness : CompactFormulaTransformInitialFinalWitnessCoordinates}
    (hrows : CompactFormulaTransformInitialDefaultFinalRows
      tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedOutputBoundary expectedOutputCount
        emptyBoundary binderArity tableWidth valueBound witness) :
    ∀ value ∈ compactFormulaTransformInitialFinalWitnessValues witness,
      Nat.size value ≤
        compactFormulaTransformAdjacentStepPublicWidth width tokenCount := by
  rcases hrows with
    ⟨_hstateCount, hinitial, _hinitialParser, _hinitialOutput,
      hfinal, _hfinalOutput, hreservedStart, hreservedBoundary,
      hreservedBoundarySize⟩
  have hinitialFit :=
    CompactFormulaTransformStateAtRows.coordinateFits hinitial
  have hfinalFit :=
    CompactFormulaTransformStateAtRows.coordinateFits hfinal
  intro value hvalue
  simp only [compactFormulaTransformInitialFinalWitnessValues,
    List.mem_cons] at hvalue
  rcases hvalue with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h
  · simpa [h] using hinitialFit.start
  · simpa [h] using hinitialFit.finish
  · simpa [h] using hinitialFit.parserFinish
  · simpa [h] using hinitialFit.parserTokensFinish
  · simpa [h] using hinitialFit.parserTasksFinish
  · simpa [h] using hinitialFit.parserTokensBoundary
  · simpa [h] using hinitialFit.parserTokensCount
  · simpa [h] using hinitialFit.parserTasksBoundary
  · simpa [h] using hinitialFit.parserTasksCount
  · simpa [h] using hinitialFit.outputBoundary
  · simpa [h] using hinitialFit.outputCount
  · simpa [h] using hinitialFit.parserTokensBoundarySize
  · simpa [h] using hinitialFit.parserTasksBoundarySize
  · simpa [h] using hinitialFit.outputBoundarySize
  · simpa [h] using hfinalFit.start
  · simpa [h] using hfinalFit.finish
  · simpa [h] using hfinalFit.parserFinish
  · simpa [h] using hfinalFit.parserTokensFinish
  · simpa [h] using hfinalFit.parserTasksFinish
  · simpa [h] using hfinalFit.parserTokensBoundary
  · simpa [h] using hfinalFit.parserTokensCount
  · simpa [h] using hfinalFit.parserTasksBoundary
  · simpa [h] using hfinalFit.parserTasksCount
  · simpa [h] using hfinalFit.outputBoundary
  · simpa [h] using hfinalFit.outputCount
  · simpa [h] using hfinalFit.parserTokensBoundarySize
  · simpa [h] using hfinalFit.parserTasksBoundarySize
  · simpa [h] using hfinalFit.outputBoundarySize
  · subst value
    simp [hreservedStart]
  · subst value
    simp [hreservedBoundary]
  · rcases h with h | h
    · subst value
      simp [hreservedBoundarySize]
    · simp at h

#print axioms CompactFormulaTransformInitialDefaultFinalRows.endpointValuesFit

end FoundationCompactNumericListedDirectFormulaTransformEndpointWitnessBound
