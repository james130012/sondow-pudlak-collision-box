import integration.FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointFormula
import integration.FoundationCompactNumericListedDirectParserSyntaxExactEndpointPublicBounds

/-!
# Public bounds for exact no-output syntax-parser endpoints

A failed formula or term parse still has one complete deterministic parser
trace.  This file bounds the twenty initial/final witness fields, every
adjacent transition row, and all seven exposed endpoint coordinates by explicit
functions of the shared table width and token count.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointPublicBounds

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxTraceInstallation
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedInstallation
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectParserSyntaxBoundedRowsPublicInstallation
open FoundationCompactNumericListedDirectParserNoOutputInitialFinalFormula
open FoundationCompactNumericListedDirectParserNoOutputInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxNoOutputTraceFormula
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactFormula
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointFormula
open FoundationCompactNumericListedDirectParserSyntaxTraceBounds
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointPublicBounds
open FoundationCompactNumericListedDirectSequentFormulaTracePublicBounds
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

private theorem list_sum_map_le_length_mul
    {alpha : Type*} {values : List alpha} {weight : alpha -> Nat}
    {bound : Nat}
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

@[simp] theorem compactParserNoOutputInitialFinalWitnessValues_length
    (witness : CompactParserNoOutputInitialFinalWitnessCoordinates) :
    (compactParserNoOutputInitialFinalWitnessValues witness).length = 20 := by
  simp [compactParserNoOutputInitialFinalWitnessValues]

theorem CompactUnifiedParserNoOutputInitialFinalRows.witness_value_size_le
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount : Nat}
    {witness : CompactParserNoOutputInitialFinalWitnessCoordinates}
    (hrows : CompactUnifiedParserNoOutputInitialFinalRows
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      witness)
    {value : Nat}
    (hvalue :
      value ∈ compactParserNoOutputInitialFinalWitnessValues witness) :
    Nat.size value <=
      compactParserSyntaxAdjacentStepPublicWidth width tokenCount := by
  rcases hrows with
    ⟨_hstateCount, hinitialAt, _hinitialRows, hfinalAt, _hfinalRows⟩
  have hinitialFit :=
    CompactUnifiedParserStateAtRows.coordinateFits hinitialAt
  have hfinalFit :=
    CompactUnifiedParserStateAtRows.coordinateFits hfinalAt
  simp only [compactParserNoOutputInitialFinalWitnessValues,
    List.mem_cons, List.not_mem_nil, or_false] at hvalue
  rcases hvalue with
    h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h
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

theorem compactParserNoOutputInitialFinalWitnessDynamicWidth_le
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount : Nat}
    {witness : CompactParserNoOutputInitialFinalWitnessCoordinates}
    (hrows : CompactUnifiedParserNoOutputInitialFinalRows
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      witness) :
    compactParserNoOutputInitialFinalWitnessDynamicWidth witness <=
      20 * compactParserSyntaxAdjacentStepPublicWidth width tokenCount := by
  simpa only [compactParserNoOutputInitialFinalWitnessDynamicWidth,
    compactParserNoOutputInitialFinalWitnessValues_length] using
      (list_sum_map_le_length_mul
        (values := compactParserNoOutputInitialFinalWitnessValues witness)
        (weight := Nat.size)
        (bound := compactParserSyntaxAdjacentStepPublicWidth width tokenCount)
        (fun value hvalue =>
          CompactUnifiedParserNoOutputInitialFinalRows.witness_value_size_le
            hrows hvalue))

private theorem traceState?_eq_some_getI
    {states : List CompactUnifiedParserState} {index : Nat}
    (hindex : index < states.length) :
    compactParserTraceState? states index = some (states.getI index) := by
  unfold compactParserTraceState?
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨hindex, ?_⟩
  rw [List.getI_eq_getElem _ hindex]

private theorem parserNoOutputLocalTraceValid_endpoints
    {fuel taskKind taskBinderArity taskRepeatCount : Nat}
    {input : List Nat} {states : List CompactUnifiedParserState}
    (hvalid : CompactParserOutputLocalTraceValid compactSyntaxParserStep fuel
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      none states) :
    states.length = fuel + 1 /\
      states.getI 0 =
        (input, [(taskKind, taskBinderArity, taskRepeatCount)], none) /\
      compactSyntaxParserStateOutput (states.getI fuel) = none := by
  have hlocal := hvalid.1
  have hlength : states.length = fuel + 1 := hlocal.1
  have hinitial := CompactParserLocalTraceValid.getI_eq_stateAt
    hlocal (Nat.zero_le fuel)
  have hfuelIndex : fuel < states.length := by omega
  have hfinalTrace := traceState?_eq_some_getI hfuelIndex
  have houtput := hvalid.2
  rw [hfinalTrace] at houtput
  have hstateOutput :
      compactSyntaxParserStateOutput (states.getI fuel) = none := by
    simpa [compactParserStateOutputOption] using houtput
  exact ⟨hlength,
    (by simpa [compactParserStateAt] using hinitial), hstateOutput⟩

/- The ordinary no-output trace has a public table width.  The same canonical
width used for successful syntax traces is sufficient because its endpoint
allowance has twenty fields while the success allowance already reserves
twenty-three. -/
set_option maxHeartbeats 1500000 in
theorem
    localTrace_exists_compactParserSyntaxNoOutputExactBoundedGraph_with_publicWidth
    {tokenTable width tokenCount stateBoundary inputBoundary
      taskKind taskBinderArity taskRepeatCount : Nat}
    {states : List CompactUnifiedParserState}
    {input : List Nat}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(taskKind, taskBinderArity, taskRepeatCount)])
    (hvalid : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      none states) :
    exists tableWidth,
      tableWidth <= compactParserSyntaxCanonicalTableWidthBound
        width tokenCount (compactSyntaxRunFuelBound input) /\
      CompactParserSyntaxNoOutputExactBoundedGraph
        tokenTable width tokenCount stateBoundary states.length
        inputBoundary input.length taskKind taskBinderArity taskRepeatCount
        tableWidth (2 ^ tableWidth) := by
  have hendpoints := parserNoOutputLocalTraceValid_endpoints hvalid
  rcases (exists_compactUnifiedParserNoOutputInitialFinalRows_iff
      (Eq.refl states.length) hrows hinput).mpr hendpoints with
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
    compactParserNoOutputInitialFinalWitnessDynamicWidth_le hendpointRows
  let tableWidth :=
    compactParserSyntaxAdjacentStepDynamicWidth rows +
      (tokenCount + 1) * tokenCount +
      compactParserNoOutputInitialFinalWitnessDynamicWidth endpointWitness
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
      compactParserNoOutputInitialFinalWitnessDynamicWidth endpointWitness <=
        tableWidth := by
    dsimp only [tableWidth]
    omega
  have hendpointBounded : CompactParserNoOutputInitialFinalBounded
      tokenTable width tokenCount stateBoundary states.length
      (compactSyntaxRunFuelBound input)
      inputBoundary input.length taskKind taskBinderArity taskRepeatCount
      (2 ^ tableWidth) :=
    CompactParserNoOutputInitialFinalBounded.of_witness
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
  unfold CompactParserSyntaxNoOutputExactBoundedGraph
  exact ⟨hvalid.1.1, hendpointBounded, hadjacentBounded⟩

def compactParserSyntaxNoOutputExactEndpointCoordinateValues
    (coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates) :
    List Nat :=
  [coordinates.inputBoundary,
    coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.stateBoundary,
    coordinates.stateCount,
    coordinates.tableWidth,
    coordinates.valueBound]

def compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound
    (width tokenCount : Nat) : Nat :=
  compactParserSyntaxExactEndpointPublicCoordinateSizeBound width tokenCount

structure CompactParserSyntaxNoOutputExactEndpointPublicBounds
    (coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates)
    (bound : Nat) : Prop where
  value_size_le :
    ∀ value ∈
      compactParserSyntaxNoOutputExactEndpointCoordinateValues coordinates,
      Nat.size value <= bound

private theorem compactSyntaxRunFuelBound_le_public
    {input : List Nat} {tokenCount : Nat}
    (hcount : input.length <= tokenCount) :
    compactSyntaxRunFuelBound input <=
      compactSequentFormulaPublicParserFuelBound tokenCount := by
  have hplus : input.length + 1 <= tokenCount + 1 := by omega
  have hsquare :
      (input.length + 1) * (input.length + 1) <=
        (tokenCount + 1) * (tokenCount + 1) :=
    Nat.mul_le_mul hplus hplus
  have hscaled :
      16 * (input.length + 1) * (input.length + 1) <=
        16 * (tokenCount + 1) * (tokenCount + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 16 hplus) hplus
  unfold compactSyntaxRunFuelBound
    compactSequentFormulaPublicParserFuelBound
  omega

private theorem compactParserSyntaxCanonicalTableWidthBound_mono_fuel
    {width tokenCount leftFuel rightFuel : Nat}
    (hfuel : leftFuel <= rightFuel) :
    compactParserSyntaxCanonicalTableWidthBound width tokenCount leftFuel <=
      compactParserSyntaxCanonicalTableWidthBound
        width tokenCount rightFuel := by
  have hcolumns :
      leftFuel * compactParserSyntaxAdjacentStepWitnessColumnCount <=
        rightFuel * compactParserSyntaxAdjacentStepWitnessColumnCount :=
    Nat.mul_le_mul_right
      compactParserSyntaxAdjacentStepWitnessColumnCount hfuel
  have hrows :=
    Nat.mul_le_mul_right
      (FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessBound.compactParserSyntaxAdjacentStepPublicWidth
        width tokenCount)
      hcolumns
  unfold compactParserSyntaxCanonicalTableWidthBound
  omega

/-- Install an already laid-out no-output parser trace while retaining public
bounds for all seven endpoint coordinates. -/
theorem
    exists_compactParserSyntaxNoOutputExactEndpointGraph_of_rows_with_publicBounds
    {tokenTable width tokenCount inputStart inputFinish stateBoundary : Nat}
    {input : List Nat}
    {states : List CompactUnifiedParserState}
    {taskKind taskBinderArity taskRepeatCount : Nat}
    (hinputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hstateRows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hstateBoundarySize :
      Nat.size stateBoundary <= (states.length + 1) * tokenCount)
    (hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(taskKind, taskBinderArity, taskRepeatCount)])
    (hvalid : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      none states) :
    exists coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates,
      CompactParserSyntaxNoOutputExactEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            taskKind taskBinderArity taskRepeatCount coordinates /\
        CompactParserSyntaxNoOutputExactEndpointPublicBounds coordinates
          (compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound
            width tokenCount) /\
        coordinates.stateBoundary = stateBoundary := by
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputRows, hinputSize⟩
  rcases
      localTrace_exists_compactParserSyntaxNoOutputExactBoundedGraph_with_publicWidth
        hstateRows hinputRows hstartWell hvalid with
    ⟨tableWidth, htableWidth, hexact⟩
  have hinputWitness :
      CompactAdditiveNatListWitnessRows
        tokenTable width tokenCount inputStart input.length inputFinish
          inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputRows,
      rfl, hinputSize⟩
  let coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      stateBoundary := stateBoundary
      stateCount := states.length
      tableWidth := tableWidth
      valueBound := 2 ^ tableWidth }
  have hgraph :
      CompactParserSyntaxNoOutputExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          taskKind taskBinderArity taskRepeatCount coordinates := by
    unfold CompactParserSyntaxNoOutputExactEndpointGraph
    dsimp only [coordinates]
    exact ⟨hinputWitness, hexact⟩
  have hinputCount : input.length <= tokenCount :=
    structuredListLayout_count_le_tokenCount hinputStructure
  have htokenCountPos : 0 < tokenCount :=
    Nat.lt_of_le_of_lt (Nat.zero_le inputStart)
      (FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound.structuredListLayout_start_lt_tokenCount
        hinputStructure)
  have hfuel :
      compactSyntaxRunFuelBound input <=
        compactSequentFormulaPublicParserFuelBound tokenCount :=
    compactSyntaxRunFuelBound_le_public hinputCount
  have hstateCount :
      states.length <=
        compactSequentFormulaPublicParserFuelBound tokenCount + 1 := by
    rw [hvalid.1.1]
    omega
  have hstateCountPublic :
      states.length <=
        (compactSequentFormulaPublicParserFuelBound tokenCount + 2) *
          tokenCount := by
    have hone : 1 <= tokenCount := Nat.succ_le_iff.mpr htokenCountPos
    have hscaled :
        (compactSequentFormulaPublicParserFuelBound tokenCount + 2) * 1 <=
          (compactSequentFormulaPublicParserFuelBound tokenCount + 2) *
            tokenCount :=
      Nat.mul_le_mul_left
        (compactSequentFormulaPublicParserFuelBound tokenCount + 2) hone
    exact hstateCount.trans (by
      exact (show
        compactSequentFormulaPublicParserFuelBound tokenCount + 1 <=
          (compactSequentFormulaPublicParserFuelBound tokenCount + 2) * 1
        by omega) |>.trans hscaled)
  have hinputBoundary :
      Nat.size inputBoundary <= (tokenCount + 1) * tokenCount :=
    hinputSize.trans
      (Nat.mul_le_mul_right tokenCount
        (Nat.add_le_add_right hinputCount 1))
  have hstateBoundary :
      Nat.size stateBoundary <=
        (compactSequentFormulaPublicParserFuelBound tokenCount + 2) *
          tokenCount :=
    hstateBoundarySize.trans
      (Nat.mul_le_mul_right tokenCount
        (Nat.add_le_add_right hstateCount 1))
  have htableWidthPublic :
      tableWidth <=
        compactParserSyntaxCanonicalTableWidthBound
          width tokenCount
            (compactSequentFormulaPublicParserFuelBound tokenCount) :=
    htableWidth.trans
      (compactParserSyntaxCanonicalTableWidthBound_mono_fuel hfuel)
  let coordinateBound :=
    compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound
      width tokenCount
  have hpublic :
      CompactParserSyntaxNoOutputExactEndpointPublicBounds
        coordinates coordinateBound := by
    refine ⟨?_⟩
    intro value hvalue
    simp only [compactParserSyntaxNoOutputExactEndpointCoordinateValues,
      List.mem_cons, List.not_mem_nil, or_false] at hvalue
    rcases hvalue with h | h | h | h | h | h | h
    all_goals
      subst value
      dsimp only [coordinates, coordinateBound,
        compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound,
        compactParserSyntaxExactEndpointPublicCoordinateSizeBound,
        compactSequentFormulaStepPublicCoordinateSizeBound]
    · exact hinputBoundary.trans (by omega)
    · exact (natSize_le_of_le hinputCount).trans (by omega)
    · exact (natSize_le_of_le hinputBoundary).trans (by omega)
    · exact hstateBoundary.trans (by omega)
    · exact (natSize_le_of_le hstateCountPublic).trans (by omega)
    · exact (natSize_le_of_le htableWidthPublic).trans (by omega)
    · rw [Nat.size_pow]
      exact Nat.add_le_add_right htableWidthPublic 1 |>.trans (by omega)
  exact ⟨coordinates, hgraph, hpublic, rfl⟩

#print axioms
  localTrace_exists_compactParserSyntaxNoOutputExactBoundedGraph_with_publicWidth
#print axioms
  exists_compactParserSyntaxNoOutputExactEndpointGraph_of_rows_with_publicBounds

end FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointPublicBounds
