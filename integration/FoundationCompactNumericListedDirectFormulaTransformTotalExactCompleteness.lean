import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula

/-!
# Converse constructor for the total exact formula-transform graph

A canonical executable trace, together with direct layouts for its control,
input, exact defaulted output, and empty default, constructs the bounded graph.
No graph-existence premise is used.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformTotalExactCompleteness

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula

theorem CompactFormulaTransformTotalExactBoundedGraph.of_canonical_trace_with_width_bound
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary emptyBoundary binderArity : Nat}
    {witness input expectedOutput : List Nat}
    (hrows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary
        (compactFormulaTransformStateTrace (mode, witness)
          (compactSyntaxRunFuelBound input)
          (compactFormulaTransformInitialState binderArity input)))
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hwitnessCount : witnessCount = witness.length)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpectedOutput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedOutputBoundary expectedOutput)
    (hempty : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary [])
    (hresult : expectedOutput =
      (compactExactFormulaTransformResult
        (compactFormulaTransformResult
          (mode, witness) (binderArity, input))).getD []) :
    ∃ tableWidth,
      CompactFormulaTransformTotalExactBoundedGraph
        tokenTable width tokenCount stateBoundary
          ((compactSyntaxRunFuelBound input) + 1) mode
        witnessStart witnessFinish witnessCount
        inputBoundary input.length expectedOutputBoundary expectedOutput.length
        emptyBoundary binderArity tableWidth (2 ^ tableWidth) ∧
      tableWidth ≤ compactFormulaTransformCanonicalTableWidthBound
        width tokenCount (compactSyntaxRunFuelBound input) := by
  rcases
      totalResult_exists_compactFormulaTransformTotalExactBoundedFormula_with_width_bound
      hrows hwitness hwitnessCount hinput hexpectedOutput hempty hresult with
    ⟨tableWidth, hformula, htableWidth⟩
  exact ⟨tableWidth,
    (compactFormulaTransformTotalExactBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary
      (compactSyntaxRunFuelBound input + 1) mode
      witnessStart witnessFinish witnessCount
      inputBoundary input.length
      expectedOutputBoundary expectedOutput.length
      emptyBoundary binderArity tableWidth (2 ^ tableWidth)).mp hformula,
    htableWidth⟩

theorem CompactFormulaTransformTotalExactBoundedGraph.of_canonical_trace
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount
      inputBoundary expectedOutputBoundary emptyBoundary binderArity : Nat}
    {witness input expectedOutput : List Nat}
    (hrows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary
        (compactFormulaTransformStateTrace (mode, witness)
          (compactSyntaxRunFuelBound input)
          (compactFormulaTransformInitialState binderArity input)))
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hwitnessCount : witnessCount = witness.length)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpectedOutput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedOutputBoundary expectedOutput)
    (hempty : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary [])
    (hresult : expectedOutput =
      (compactExactFormulaTransformResult
        (compactFormulaTransformResult
          (mode, witness) (binderArity, input))).getD []) :
    ∃ tableWidth,
      CompactFormulaTransformTotalExactBoundedGraph
        tokenTable width tokenCount stateBoundary
          ((compactSyntaxRunFuelBound input) + 1) mode
        witnessStart witnessFinish witnessCount
        inputBoundary input.length expectedOutputBoundary expectedOutput.length
        emptyBoundary binderArity tableWidth (2 ^ tableWidth) := by
  rcases
      CompactFormulaTransformTotalExactBoundedGraph.of_canonical_trace_with_width_bound
        hrows hwitness hwitnessCount hinput hexpectedOutput hempty hresult with
    ⟨tableWidth, hgraph, _htableWidth⟩
  exact ⟨tableWidth, hgraph⟩

#print axioms
  CompactFormulaTransformTotalExactBoundedGraph.of_canonical_trace_with_width_bound
#print axioms
  CompactFormulaTransformTotalExactBoundedGraph.of_canonical_trace

end FoundationCompactNumericListedDirectFormulaTransformTotalExactCompleteness
