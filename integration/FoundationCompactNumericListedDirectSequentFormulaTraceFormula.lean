import integration.FoundationCompactNumericListedDirectSequentFormulaStepBoundedInstallation
import integration.FoundationCompactNumericListedDirectNatListListRowsRealization
import integration.FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy

/-!
# Exact bounded trace for a sequent formula list

The graph carries every formula-parser row under one power-of-two witness
bound.  Its two boundary tables independently reconstruct all token suffixes
and all parsed formula values.  Soundness then identifies each reconstructed
row with the corresponding exact parser step, including the final suffix.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSequentFormulaTraceFormula

open FoundationCompactParserDirectTrace
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectNatListListRowsRealization
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedInstallation

def CompactSequentFormulaTraceBoundedGraph
    (tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount tableWidth valueBound : Nat) : Prop :=
  suffixCount = valueCount + 1 ∧
    CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount suffixBoundary suffixCount ∧
    CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount valueBoundary valueCount ∧
    CompactSequentFormulaStepRowsBoundedGraph
      tokenTable width tokenCount suffixBoundary suffixCount
        valueBoundary valueCount valueCount tableWidth valueBound

def compactSequentFormulaTraceBoundedGraphDef : 𝚺₀.Semisentence 9 := .mkSigma
  “tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount tableWidth valueBound.
    suffixCount = valueCount + 1 ∧
    !(compactAdditiveNatListListRowsWellFormedDef)
      tokenTable width tokenCount suffixBoundary suffixCount ∧
    !(compactAdditiveNatListListRowsWellFormedDef)
      tokenTable width tokenCount valueBoundary valueCount ∧
    !(compactSequentFormulaStepRowsBoundedGraphDef)
      tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount valueCount tableWidth valueBound”

@[simp] theorem compactSequentFormulaTraceBoundedGraphDef_spec
    (tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount tableWidth valueBound : Nat) :
    compactSequentFormulaTraceBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, suffixBoundary, suffixCount,
          valueBoundary, valueCount, tableWidth, valueBound] ↔
      CompactSequentFormulaTraceBoundedGraph
        tokenTable width tokenCount suffixBoundary suffixCount
          valueBoundary valueCount tableWidth valueBound := by
  let env : Fin 9 → Nat :=
    ![tokenTable, width, tokenCount, suffixBoundary, suffixCount,
      valueBoundary, valueCount, tableWidth, valueBound]
  change compactSequentFormulaTraceBoundedGraphDef.val.Evalb env ↔ _
  have hsuffixEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 9), #1, #2, #3, #4]) =
        ![tokenTable, width, tokenCount, suffixBoundary, suffixCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hvalueEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 9), #1, #2, #5, #6]) =
        ![tokenTable, width, tokenCount, valueBoundary, valueCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hstepEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 9), #1, #2, #3, #4,
          #5, #6, #6, #7, #8]) =
        ![tokenTable, width, tokenCount, suffixBoundary, suffixCount,
          valueBoundary, valueCount, valueCount, tableWidth, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsuffixCountValue : env 4 = suffixCount := rfl
  have hvalueCountValue : env 6 = valueCount := rfl
  simp [compactSequentFormulaTraceBoundedGraphDef,
    CompactSequentFormulaTraceBoundedGraph,
    hsuffixEnv, hvalueEnv, hstepEnv,
    hsuffixCountValue, hvalueCountValue]

theorem compactSequentFormulaTraceBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactSequentFormulaTraceBoundedGraphDef.val := by
  simp [compactSequentFormulaTraceBoundedGraphDef]

theorem CompactSequentFormulaTraceBoundedGraph.realize
    {tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount tableWidth valueBound : Nat}
    (hgraph : CompactSequentFormulaTraceBoundedGraph
      tokenTable width tokenCount suffixBoundary suffixCount
        valueBoundary valueCount tableWidth valueBound) :
    ∃ suffixes values : List (List Nat),
      suffixes.length = suffixCount ∧
      values.length = valueCount ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          suffixBoundary suffixes ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          valueBoundary values ∧
      ∀ index < valueCount,
        compactFormulaTokenValueParser 0 (suffixes.getI index) =
          some (values.getI index, suffixes.getI (index + 1)) := by
  rcases hgraph with
    ⟨hsuffixCount, hsuffixWellFormed, hvalueWellFormed, hsteps⟩
  rcases
      FoundationCompactNumericListedDirectNatListListRowsRealization.CompactAdditiveNatListListRowsWellFormed.realizeRows
        hsuffixWellFormed with
    ⟨suffixes, hsuffixesLength, hsuffixRows⟩
  rcases
      FoundationCompactNumericListedDirectNatListListRowsRealization.CompactAdditiveNatListListRowsWellFormed.realizeRows
        hvalueWellFormed with
    ⟨values, hvaluesLength, hvalueRows⟩
  refine ⟨suffixes, values, hsuffixesLength, hvaluesLength,
    hsuffixRows, hvalueRows, ?_⟩
  intro index hindex
  have hbounded := hsteps.2 index hindex
  rcases CompactSequentFormulaStepRowBounded.exists_row hbounded with
    ⟨row, hrowGraph⟩
  have hrowSound := CompactSequentFormulaStepGraph.sound hrowGraph
  rcases hrowSound with
    ⟨current, next, value, parserStates,
      hcurrentLayout, hnextLayout, hvalueLayout,
      _hparserTrace, _happend, hparserResult⟩
  rcases hrowGraph with
    ⟨_hcurrentStart, _hcurrentFinish, _hcurrentCount,
      _hnextStart, _hnextFinish, _hnextCount,
      _hvalueStart, _hvalueFinish, _hvalueCount,
      hcurrentStartEntry, _hcurrentFinishEntry,
      hnextStartEntry, _hnextFinishEntry,
      hvalueStartEntry, _hvalueFinishEntry,
      _hcurrentWitness, _hnextWitness, _hvalueWitness,
      _hparserGraph, _happendGraph, _hsuffixCountRow⟩
  have hcurrentIndex : index < suffixes.length := by
    rw [hsuffixesLength, hsuffixCount]
    omega
  have hnextIndex : index + 1 < suffixes.length := by
    rw [hsuffixesLength, hsuffixCount]
    omega
  have hvalueIndex : index < values.length := by
    simpa only [hvaluesLength] using hindex
  rcases hsuffixRows index hcurrentIndex with
    ⟨actualCurrentStart, _hactualCurrentStartBound,
      actualCurrentFinish, _hactualCurrentFinishBound,
      hactualCurrentStartEntry, _hactualCurrentFinishEntry,
      hactualCurrentLayout⟩
  rcases hsuffixRows (index + 1) hnextIndex with
    ⟨actualNextStart, _hactualNextStartBound,
      actualNextFinish, _hactualNextFinishBound,
      hactualNextStartEntry, _hactualNextFinishEntry,
      hactualNextLayout⟩
  rcases hvalueRows index hvalueIndex with
    ⟨actualValueStart, _hactualValueStartBound,
      actualValueFinish, _hactualValueFinishBound,
      hactualValueStartEntry, _hactualValueFinishEntry,
      hactualValueLayout⟩
  have hcurrentStartEq : row.current.start = actualCurrentStart :=
    (CompactFixedWidthEntry.value_eq_tableValue
      hcurrentStartEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          hactualCurrentStartEntry).symm
  have hnextStartEq : row.next.start = actualNextStart :=
    (CompactFixedWidthEntry.value_eq_tableValue
      hnextStartEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          hactualNextStartEntry).symm
  have hvalueStartEq : row.value.start = actualValueStart :=
    (CompactFixedWidthEntry.value_eq_tableValue
      hvalueStartEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          hactualValueStartEntry).symm
  subst actualCurrentStart
  subst actualNextStart
  subst actualValueStart
  have hcurrentEq : suffixes.getI index = current :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hcurrentLayout hactualCurrentLayout).1
  have hnextEq : suffixes.getI (index + 1) = next :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hnextLayout hactualNextLayout).1
  have hvalueEq : values.getI index = value :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hvalueLayout hactualValueLayout).1
  rw [hcurrentEq, hvalueEq, hnextEq]
  exact hparserResult

theorem compactFormulaTokenValuesRepeat_eq_some_of_indexed_steps
    {count : Nat} {suffixes values : List (List Nat)}
    (hvaluesLength : values.length = count)
    (hsteps : ∀ index < count,
      compactFormulaTokenValueParser 0 (suffixes.getI index) =
        some (values.getI index, suffixes.getI (index + 1))) :
    compactFormulaTokenValuesRepeat count (suffixes.getI 0) =
      some (values, suffixes.getI count) := by
  have hiterate : ∀ stepIndex ≤ count,
      (compactFormulaTokenValuesStep^[stepIndex])
          (compactFormulaTokenValuesInitial (suffixes.getI 0)) =
        some (values.take stepIndex, suffixes.getI stepIndex) := by
    intro stepIndex hstepIndex
    induction stepIndex with
    | zero =>
        rfl
    | succ stepIndex ih =>
        have hindex : stepIndex < count := by omega
        have hvalueIndex : stepIndex < values.length := by
          simpa only [hvaluesLength] using hindex
        have htake :
            values.take stepIndex ++ [values.getI stepIndex] =
              values.take (stepIndex + 1) := by
          simpa only [List.getI_eq_getElem values hvalueIndex] using
            (List.take_concat_get' values stepIndex hvalueIndex)
        rw [Function.iterate_succ_apply', ih (Nat.le_of_lt hindex)]
        simp only [compactFormulaTokenValuesStep, Option.bind_some,
          hsteps stepIndex hindex, Option.map_some]
        rw [htake]
  unfold compactFormulaTokenValuesRepeat
  have hfinal := hiterate count (Nat.le_refl count)
  have htakeAll : values.take count = values := by
    rw [← hvaluesLength, List.take_length]
  rw [htakeAll] at hfinal
  exact hfinal

theorem CompactSequentFormulaTraceBoundedGraph.sound_repeat
    {tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount tableWidth valueBound : Nat}
    (hgraph : CompactSequentFormulaTraceBoundedGraph
      tokenTable width tokenCount suffixBoundary suffixCount
        valueBoundary valueCount tableWidth valueBound) :
    ∃ suffixes values : List (List Nat),
      suffixes.length = suffixCount ∧
      values.length = valueCount ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          suffixBoundary suffixes ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          valueBoundary values ∧
      compactFormulaTokenValuesRepeat valueCount (suffixes.getI 0) =
        some (values, suffixes.getI valueCount) := by
  rcases hgraph.realize with
    ⟨suffixes, values, hsuffixesLength, hvaluesLength,
      hsuffixRows, hvalueRows, hsteps⟩
  refine ⟨suffixes, values, hsuffixesLength, hvaluesLength,
    hsuffixRows, hvalueRows, ?_⟩
  exact compactFormulaTokenValuesRepeat_eq_some_of_indexed_steps
    hvaluesLength hsteps

def compactSequentFormulaTraceDynamicWidth
    (rows : List CompactSequentFormulaStepCoordinates) : Nat :=
  (rows.map compactSequentFormulaStepDynamicWidth).sum

theorem compactSequentFormulaStep_dynamicWidth_le_trace
    {rows : List CompactSequentFormulaStepCoordinates}
    {row : CompactSequentFormulaStepCoordinates}
    (hrow : row ∈ rows) :
    compactSequentFormulaStepDynamicWidth row ≤
      compactSequentFormulaTraceDynamicWidth rows := by
  have hmem : compactSequentFormulaStepDynamicWidth row ∈
      rows.map compactSequentFormulaStepDynamicWidth :=
    List.mem_map.mpr ⟨row, hrow, rfl⟩
  simpa [compactSequentFormulaTraceDynamicWidth] using
    List.single_le_sum (by simp) _ hmem

theorem exists_compactSequentFormulaTraceBoundedGraph_of_rows
    {tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount : Nat}
    {suffixes values : List (List Nat)}
    (hsuffixCount : suffixCount = valueCount + 1)
    (hsuffixesLength : suffixes.length = suffixCount)
    (hvaluesLength : values.length = valueCount)
    (hsuffixRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        suffixBoundary suffixes)
    (hvalueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        valueBoundary values)
    (rows : List CompactSequentFormulaStepCoordinates)
    (hrows : ∀ index < valueCount,
      ∃ row ∈ rows,
        CompactSequentFormulaStepGraph
          tokenTable width tokenCount suffixBoundary suffixCount
            valueBoundary valueCount index row) :
    ∃ tableWidth,
      CompactSequentFormulaTraceBoundedGraph
        tokenTable width tokenCount suffixBoundary suffixCount
          valueBoundary valueCount tableWidth (2 ^ tableWidth) := by
  let tableWidth := compactSequentFormulaTraceDynamicWidth rows
  have hsuffixWellFormed : CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount suffixBoundary suffixCount := by
    simpa only [hsuffixesLength] using
      FoundationCompactNumericListedDirectNatListListRowsFormula.CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
        hsuffixRows
  have hvalueWellFormed : CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount valueBoundary valueCount := by
    simpa only [hvaluesLength] using
      FoundationCompactNumericListedDirectNatListListRowsFormula.CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
        hvalueRows
  have hbounded : CompactSequentFormulaStepRowsBoundedGraph
      tokenTable width tokenCount suffixBoundary suffixCount
        valueBoundary valueCount valueCount tableWidth (2 ^ tableWidth) := by
    refine ⟨rfl, ?_⟩
    intro index hindex
    rcases hrows index hindex with ⟨row, hrowMem, hrowGraph⟩
    apply CompactSequentFormulaStepGraph.toBounded hrowGraph
    intro value hvalue
    have hsize := compactSequentFormulaStep_value_size_le_dynamic
      row hvalue
    have htraceWidth :=
      compactSequentFormulaStep_dynamicWidth_le_trace hrowMem
    exact (Nat.size_le.mp (hsize.trans htraceWidth)).le
  exact ⟨tableWidth, hsuffixCount, hsuffixWellFormed,
    hvalueWellFormed, hbounded⟩

#print axioms compactSequentFormulaTraceBoundedGraphDef_spec
#print axioms compactSequentFormulaTraceBoundedGraphDef_sigmaZero
#print axioms CompactSequentFormulaTraceBoundedGraph.realize
#print axioms compactFormulaTokenValuesRepeat_eq_some_of_indexed_steps
#print axioms CompactSequentFormulaTraceBoundedGraph.sound_repeat
#print axioms compactSequentFormulaStep_dynamicWidth_le_trace
#print axioms exists_compactSequentFormulaTraceBoundedGraph_of_rows

end FoundationCompactNumericListedDirectSequentFormulaTraceFormula
