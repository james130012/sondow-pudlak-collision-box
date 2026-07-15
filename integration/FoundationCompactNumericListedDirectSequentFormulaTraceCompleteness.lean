import integration.FoundationCompactNumericListedDirectSequentFormulaTraceFormula
import integration.FoundationCompactNumericListedDirectParserStateListLayout

/-!
# Completeness of the exact sequent formula-list trace

Typed suffix rows, value rows, and one real formula-parser trace per row are
assembled into the same bounded arithmetic trace graph.  The only chosen
objects are the finitely many rows already constructed by the direct data.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSequentFormulaTraceCompleteness

open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedInstallation
open FoundationCompactNumericListedDirectSequentFormulaTraceFormula

theorem exists_compactSequentFormulaTraceBoundedGraph_of_directData
    {tokenTable width tokenCount suffixBoundary valueBoundary : Nat}
    {suffixes values : List (List Nat)}
    {parserTraces : List CompactFormulaTokenParserDirectTrace}
    (hsuffixCount : suffixes.length = values.length + 1)
    (hparserCount : parserTraces.length = values.length)
    (hsuffixRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        suffixBoundary suffixes)
    (hvalueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        valueBoundary values)
    (hparserRows : ∀ index < values.length,
      ∃ parserStateBoundary,
        CompactUnifiedParserStateListRowLayouts
          tokenTable width tokenCount parserStateBoundary
            (parserTraces.getI index))
    (hsteps : ∀ index < values.length,
      CompactFormulaTokenParserDirectTraceValid
        0 (suffixes.getI index) (suffixes.getI (index + 1))
          (parserTraces.getI index) ∧
      suffixes.getI index =
        values.getI index ++ suffixes.getI (index + 1)) :
    ∃ tableWidth,
      CompactSequentFormulaTraceBoundedGraph
        tokenTable width tokenCount suffixBoundary suffixes.length
          valueBoundary values.length tableWidth (2 ^ tableWidth) := by
  have hexists (index : Fin values.length) :
      ∃ row : CompactSequentFormulaStepCoordinates,
        CompactSequentFormulaStepGraph
          tokenTable width tokenCount suffixBoundary suffixes.length
            valueBoundary values.length index row := by
    have hindex : index.1 < values.length := index.2
    have hcurrentIndex : index.1 < suffixes.length := by
      rw [hsuffixCount]
      omega
    have hnextIndex : index.1 + 1 < suffixes.length := by
      rw [hsuffixCount]
      omega
    rcases hsuffixRows index.1 hcurrentIndex with
      ⟨currentStart, _hcurrentStartBound,
        currentFinish, _hcurrentFinishBound,
        hcurrentStartEntry, hcurrentFinishEntry, hcurrentLayout⟩
    rcases hsuffixRows (index.1 + 1) hnextIndex with
      ⟨nextStart, _hnextStartBound,
        nextFinish, _hnextFinishBound,
        hnextStartEntry, hnextFinishEntry, hnextLayout⟩
    rcases hvalueRows index.1 hindex with
      ⟨valueStart, _hvalueStartBound,
        valueFinish, _hvalueFinishBound,
        hvalueStartEntry, hvalueFinishEntry, hvalueLayout⟩
    rcases hparserRows index.1 hindex with
      ⟨parserStateBoundary, hparserStateRows⟩
    rcases hsteps index.1 hindex with ⟨hparserTrace, hcurrentEq⟩
    exact exists_compactSequentFormulaStepGraph_of_directTrace
      hcurrentLayout hnextLayout hvalueLayout
      parserStateBoundary hparserStateRows hparserTrace hcurrentEq
      hcurrentStartEntry hcurrentFinishEntry
      hnextStartEntry hnextFinishEntry
      hvalueStartEntry hvalueFinishEntry hsuffixCount
  let rowAt (index : Fin values.length) :
      CompactSequentFormulaStepCoordinates :=
    Classical.choose (hexists index)
  have hrowAt (index : Fin values.length) :
      CompactSequentFormulaStepGraph
        tokenTable width tokenCount suffixBoundary suffixes.length
          valueBoundary values.length index (rowAt index) :=
    Classical.choose_spec (hexists index)
  let rows : List CompactSequentFormulaStepCoordinates := List.ofFn rowAt
  have hrows : ∀ index < values.length,
      ∃ row ∈ rows,
        CompactSequentFormulaStepGraph
          tokenTable width tokenCount suffixBoundary suffixes.length
            valueBoundary values.length index row := by
    intro index hindex
    let finiteIndex : Fin values.length := ⟨index, hindex⟩
    refine ⟨rowAt finiteIndex, ?_, ?_⟩
    · simp [rows, finiteIndex]
    · simpa [finiteIndex] using hrowAt finiteIndex
  exact exists_compactSequentFormulaTraceBoundedGraph_of_rows
    hsuffixCount rfl rfl hsuffixRows hvalueRows rows hrows

#print axioms exists_compactSequentFormulaTraceBoundedGraph_of_directData

end FoundationCompactNumericListedDirectSequentFormulaTraceCompleteness
