import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpoint
import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactCompleteness
import integration.FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute

/-!
# Canonical constructor for a total exact transform endpoint

Given canonical rows in one shared table, the executable transform trace
constructs the endpoint coordinates and its bounded graph.  No endpoint or
graph existence is an input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpointCompleteness

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
open FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpoint
open FoundationCompactNumericListedDirectFormulaTransformTotalExactCompleteness
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute

theorem exists_compactFormulaTransformTotalExactEndpoint_of_canonical_trace
    {tokenTable width tokenCount stateBoundary mode binderArity : Nat}
    {witnessStart witnessFinish witnessBoundary witnessBoundarySize
      inputStart inputFinish inputBoundary inputBoundarySize
      outputStart outputFinish outputBoundary outputBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize : Nat}
    {witness input output : List Nat}
    (hwitnessRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount witnessStart witness.length witnessFinish
        witnessBoundary witnessBoundarySize)
    (hinputRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart input.length inputFinish
        inputBoundary inputBoundarySize)
    (houtputRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount outputStart output.length outputFinish
        outputBoundary outputBoundarySize)
    (hemptyRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount emptyStart 0 emptyFinish
        emptyBoundary emptyBoundarySize)
    (hwitnessLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hinputElements : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (houtputElements : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        outputBoundary output)
    (hemptyElements : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary [])
    (hstateRows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary
        (compactFormulaTransformStateTrace (mode, witness)
          (compactSyntaxRunFuelBound input)
          (compactFormulaTransformInitialState binderArity input)))
    (hresult : output =
      (compactExactFormulaTransformResult
        (compactFormulaTransformResult
          (mode, witness) (binderArity, input))).getD []) :
    ∃ trace : CompactFormulaTransformTraceSlot,
      CompactFormulaTransformTotalExactEndpoint
        tokenTable width tokenCount mode binderArity
        witnessStart witnessFinish witnessBoundary witness.length
          witnessBoundarySize
        inputStart inputFinish inputBoundary input.length inputBoundarySize
        outputStart outputFinish outputBoundary output.length
          outputBoundarySize
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        trace.stateBoundary trace.stateCount trace.tableWidth
          trace.valueBound := by
  rcases CompactFormulaTransformTotalExactBoundedGraph.of_canonical_trace
      hstateRows hwitnessLayout rfl hinputElements houtputElements
      hemptyElements hresult with
    ⟨tableWidth, hgraph⟩
  let trace : CompactFormulaTransformTraceSlot :=
    { stateBoundary := stateBoundary
      stateCount := compactSyntaxRunFuelBound input + 1
      tableWidth := tableWidth
      valueBound := 2 ^ tableWidth }
  refine ⟨trace, hwitnessRows, hinputRows, houtputRows, hemptyRows, ?_⟩
  simpa [trace] using hgraph

#print axioms
  exists_compactFormulaTransformTotalExactEndpoint_of_canonical_trace

end FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpointCompleteness
