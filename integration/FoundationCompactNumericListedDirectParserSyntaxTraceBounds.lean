import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessBound
import integration.FoundationCompactNumericListedDirectParserSyntaxBoundedRowsPublicInstallation
import integration.FoundationCompactNumericListedDirectParserSyntaxExactFormula
import integration.FoundationCompactNumericListedDirectParserInitialFinalInstallation

/-!
# Public aggregation bounds for syntax-parser traces

Adjacent syntax-parser rows contain exactly twenty-seven numeric fields and the
initial/final witness contains exactly twenty-three.  Uniform field bounds are
aggregated here into an explicit width for the complete bounded trace formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxTraceBounds

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectParserInitialFinalInstallation
open FoundationCompactNumericListedDirectParserSyntaxTraceInstallation
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedInstallation
open FoundationCompactNumericListedDirectParserSyntaxTraceFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectParserSyntaxBoundedRowsPublicInstallation

private theorem list_sum_map_le_length_mul
    {α : Type*} {values : List α} {weight : α → Nat} {bound : Nat}
    (hbound : ∀ value ∈ values, weight value <= bound) :
    (values.map weight).sum <= values.length * bound := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      have hhead : weight head <= bound := hbound head (by simp)
      have htail : ∀ value ∈ tail, weight value <= bound := by
        intro value hvalue
        exact hbound value (by simp [hvalue])
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        weight head + (tail.map weight).sum <=
            bound + tail.length * bound :=
          Nat.add_le_add hhead (ih htail)
        _ = (tail.length + 1) * bound := by ring

@[simp] theorem compactParserInitialFinalWitnessValues_length
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    (compactParserInitialFinalWitnessValues witness).length = 23 := by
  simp [compactParserInitialFinalWitnessValues]

theorem compactParserSyntaxAdjacentStepDynamicWidth_le
    {rows : List CompactParserSyntaxAdjacentStepRow}
    {width tokenCount : Nat}
    (hfit : CompactParserSyntaxAdjacentStepRowsFit
      (compactParserSyntaxAdjacentStepPublicWidth width tokenCount) rows) :
    compactParserSyntaxAdjacentStepDynamicWidth rows <=
      rows.length * compactParserSyntaxAdjacentStepWitnessColumnCount *
        compactParserSyntaxAdjacentStepPublicWidth width tokenCount := by
  induction rows with
  | nil => simp [compactParserSyntaxAdjacentStepDynamicWidth]
  | cons row tail ih =>
      have hrowFit := hfit row (by simp)
      have hrow :
          ((compactParserSyntaxAdjacentStepRowValues row).map Nat.size).sum <=
            compactParserSyntaxAdjacentStepWitnessColumnCount *
              compactParserSyntaxAdjacentStepPublicWidth width tokenCount := by
        apply list_sum_map_le_length_mul
        intro value hvalue
        exact hrowFit.value_size_le hvalue
      have htail : CompactParserSyntaxAdjacentStepRowsFit
          (compactParserSyntaxAdjacentStepPublicWidth width tokenCount) tail := by
        intro tailRow htailRow
        exact hfit tailRow (by simp [htailRow])
      simp only [compactParserSyntaxAdjacentStepDynamicWidth,
        List.flatMap_cons, List.map_append, List.sum_append, List.length_cons]
      calc
        ((compactParserSyntaxAdjacentStepRowValues row).map Nat.size).sum +
            ((tail.flatMap compactParserSyntaxAdjacentStepRowValues).map
              Nat.size).sum <=
          compactParserSyntaxAdjacentStepWitnessColumnCount *
              compactParserSyntaxAdjacentStepPublicWidth width tokenCount +
            tail.length * compactParserSyntaxAdjacentStepWitnessColumnCount *
              compactParserSyntaxAdjacentStepPublicWidth width tokenCount :=
          Nat.add_le_add hrow (ih htail)
        _ = (tail.length + 1) *
            compactParserSyntaxAdjacentStepWitnessColumnCount *
              compactParserSyntaxAdjacentStepPublicWidth width tokenCount := by
          ring

theorem CompactUnifiedParserInitialFinalRows.witness_value_size_le
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat}
    {witness : CompactParserInitialFinalWitnessCoordinates}
    (hrows : CompactUnifiedParserInitialFinalRows
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount witness)
    {value : Nat}
    (hvalue : value ∈ compactParserInitialFinalWitnessValues witness) :
    Nat.size value <=
      compactParserSyntaxAdjacentStepPublicWidth width tokenCount := by
  rcases hrows with
    ⟨_hstateCount, hinitialAt, _hinitialRows, hfinalAt, hfinalRows⟩
  have hinitialFit :=
    CompactUnifiedParserStateAtRows.coordinateFits hinitialAt
  have hfinalFit :=
    CompactUnifiedParserStateAtRows.coordinateFits hfinalAt
  rcases hfinalRows with ⟨houtputSame, houtputSizeEq, houtputSize⟩
  rcases houtputSame with ⟨_hstatus, houtputLayout, _hsameRows⟩
  have houtputStart : witness.outputStart <= tokenCount := by
    rcases houtputLayout with ⟨_bodyStart, _hbodyStart, hheader, _hboundary⟩
    exact Nat.le_of_lt hheader.1.1
  have houtputCount : expectedCount <= tokenCount :=
    structuredListLayout_count_le_tokenCount houtputLayout
  have houtputArea : witness.outputBoundarySize <=
      (tokenCount + 1) * tokenCount :=
    houtputSize.trans (listBoundaryArea_le_publicArea houtputCount)
  have houtputBoundary :
      Nat.size witness.outputBoundary <=
        compactParserSyntaxAdjacentStepPublicWidth width tokenCount := by
    rw [← houtputSizeEq]
    exact houtputArea.trans
      (boundaryArea_le_streamStepWidth tokenCount |>.trans
        (streamWidth_le_compactFormulaTransformAdjacentStepPublicWidth
          width tokenCount))
  have houtputBoundarySize :
      Nat.size witness.outputBoundarySize <=
        compactParserSyntaxAdjacentStepPublicWidth width tokenCount :=
    natSize_le_parserStepWidth_of_le_boundaryArea houtputArea
  simp only [compactParserInitialFinalWitnessValues, List.mem_cons] at hvalue
  rcases hvalue with
    h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h |
    h | h | h
  · simpa [h] using hinitialFit.start
  · simpa [h] using hinitialFit.finish
  · simpa [h] using hinitialFit.tokensFinish
  · simpa [h] using hinitialFit.tasksFinish
  · simpa [h] using hinitialFit.tokensBoundary
  · simpa [h] using hinitialFit.tokensCount
  · simpa [h] using hinitialFit.tasksBoundary
  · simpa [h] using hinitialFit.tasksCount
  · simpa [h] using hinitialFit.tokensBoundarySize
  · simpa [h] using hinitialFit.tasksBoundarySize
  · simpa [h] using hfinalFit.start
  · simpa [h] using hfinalFit.finish
  · simpa [h] using hfinalFit.tokensFinish
  · simpa [h] using hfinalFit.tasksFinish
  · simpa [h] using hfinalFit.tokensBoundary
  · simpa [h] using hfinalFit.tokensCount
  · simpa [h] using hfinalFit.tasksBoundary
  · simpa [h] using hfinalFit.tasksCount
  · simpa [h] using hfinalFit.tokensBoundarySize
  · simpa [h] using hfinalFit.tasksBoundarySize
  · simpa [h] using
      natSize_le_parserStepWidth_of_le_tokenCount
        (width := width) houtputStart
  · simpa [h] using houtputBoundary
  · rcases h with h | h
    · simpa [h] using houtputBoundarySize
    · simp at h

theorem compactParserInitialFinalWitnessDynamicWidth_le
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat}
    {witness : CompactParserInitialFinalWitnessCoordinates}
    (hrows : CompactUnifiedParserInitialFinalRows
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount witness) :
    compactParserInitialFinalWitnessDynamicWidth witness <=
      23 * compactParserSyntaxAdjacentStepPublicWidth width tokenCount := by
  simpa only [compactParserInitialFinalWitnessDynamicWidth,
    compactParserInitialFinalWitnessValues_length] using
      (list_sum_map_le_length_mul
        (values := compactParserInitialFinalWitnessValues witness)
        (weight := Nat.size)
        (bound := compactParserSyntaxAdjacentStepPublicWidth width tokenCount)
        (fun value hvalue =>
          CompactUnifiedParserInitialFinalRows.witness_value_size_le
            hrows hvalue))

def compactParserSyntaxCanonicalTableWidthBound
    (width tokenCount fuel : Nat) : Nat :=
  fuel * compactParserSyntaxAdjacentStepWitnessColumnCount *
      compactParserSyntaxAdjacentStepPublicWidth width tokenCount +
    (tokenCount + 1) * tokenCount +
    23 * compactParserSyntaxAdjacentStepPublicWidth width tokenCount

set_option maxHeartbeats 1500000 in
theorem localTrace_exists_compactParserSyntaxExactBoundedGraph_with_publicWidth
    {tokenTable width tokenCount stateBoundary
      inputBoundary expectedBoundary taskKind taskBinderArity taskRepeatCount :
      Nat}
    {states : List CompactUnifiedParserState}
    {input expected : List Nat}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpected : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedBoundary expected)
    (hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(taskKind, taskBinderArity, taskRepeatCount)])
    (hvalid : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      (some expected) states) :
    ∃ tableWidth,
      tableWidth <= compactParserSyntaxCanonicalTableWidthBound
        width tokenCount (compactSyntaxRunFuelBound input) ∧
      CompactParserSyntaxExactBoundedGraph
        tokenTable width tokenCount stateBoundary states.length
        inputBoundary input.length expectedBoundary expected.length
        taskKind taskBinderArity taskRepeatCount tableWidth (2 ^ tableWidth) := by
  have hendpoints := compactParserOutputLocalTraceValid_initial_final hvalid
  rcases (exists_compactUnifiedParserInitialFinalRows_iff
      (Eq.refl states.length) hrows hinput hexpected).mpr hendpoints with
    ⟨endpointWitness, hendpointRows⟩
  have hfitSource :=
    stateListAdjacentStepRowsWithFit_of_localTrace
      hrows hvalid.1 hstartWell
  let rows := compactParserSyntaxPublicFittingAdjacentStepRows hfitSource
  have hrowsValid : CompactParserSyntaxAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary states.length rows := by
    simpa only [rows] using
      compactParserSyntaxPublicFittingAdjacentStepRows_valid hfitSource
  have hrowsPublicFit : CompactParserSyntaxAdjacentStepRowsFit
      (compactParserSyntaxAdjacentStepPublicWidth width tokenCount) rows := by
    simpa only [rows] using
      compactParserSyntaxPublicFittingAdjacentStepRows_fit hfitSource
  have hrowsDynamic :=
    compactParserSyntaxAdjacentStepDynamicWidth_le hrowsPublicFit
  have hendpointDynamic :=
    compactParserInitialFinalWitnessDynamicWidth_le hendpointRows
  let tableWidth :=
    compactParserSyntaxAdjacentStepDynamicWidth rows +
      (tokenCount + 1) * tokenCount +
      compactParserInitialFinalWitnessDynamicWidth endpointWitness
  have hfit : CompactParserSyntaxAdjacentStepRowsFit tableWidth rows := by
    have hdynamic := compactParserSyntaxAdjacentStepRowsFit_dynamic rows
    intro row hrow column hcolumn
    exact (hdynamic row hrow column hcolumn).trans (by
      dsimp only [tableWidth]
      omega)
  have harea : (tokenCount + 1) * tokenCount <= tableWidth := by
    dsimp only [tableWidth]
    omega
  have hendpointWidth :
      compactParserInitialFinalWitnessDynamicWidth endpointWitness <=
        tableWidth := by
    dsimp only [tableWidth]
    omega
  have hendpointBounded : CompactParserInitialFinalBounded
      tokenTable width tokenCount stateBoundary states.length
      (compactSyntaxRunFuelBound input)
      inputBoundary input.length expectedBoundary expected.length
      taskKind taskBinderArity taskRepeatCount (2 ^ tableWidth) :=
    CompactParserInitialFinalBounded.of_witness
      hendpointWidth hendpointRows
  have hrowsLength : rows.length =
      compactSyntaxRunFuelBound input := by
    simp only [rows, compactParserSyntaxPublicFittingAdjacentStepRows_length]
    rw [hvalid.1.1]
    omega
  have hadjacentBounded : CompactParserSyntaxAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary states.length
        (compactSyntaxRunFuelBound input) tableWidth (2 ^ tableWidth) := by
    rw [← hrowsLength]
    exact compactParserSyntaxAdjacentRowsBoundedGraph_of_valid_fit
      hrows hrowsValid hfit harea
  have htableWidth :
      tableWidth <= compactParserSyntaxCanonicalTableWidthBound
        width tokenCount (compactSyntaxRunFuelBound input) := by
    dsimp only [tableWidth]
    unfold compactParserSyntaxCanonicalTableWidthBound
    rw [hrowsLength] at hrowsDynamic
    omega
  refine ⟨tableWidth, htableWidth, ?_⟩
  unfold CompactParserSyntaxExactBoundedGraph
  exact ⟨hvalid.1.1, hendpointBounded, hadjacentBounded⟩

#print axioms compactParserSyntaxAdjacentStepDynamicWidth_le
#print axioms CompactUnifiedParserInitialFinalRows.witness_value_size_le
#print axioms compactParserInitialFinalWitnessDynamicWidth_le
#print axioms
  localTrace_exists_compactParserSyntaxExactBoundedGraph_with_publicWidth

end FoundationCompactNumericListedDirectParserSyntaxTraceBounds
