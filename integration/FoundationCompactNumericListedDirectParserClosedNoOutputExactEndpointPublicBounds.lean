import integration.FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointFormula
import integration.FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointPublicBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound

/-!
# Public bounds for exact no-output closed-parser endpoints

The closed parser has one additional free-variable failure transition.  This
file constructs a publicly fitted witness for both the ordinary safe branch and
that extra failure branch, then aggregates the complete closed trace into the
same explicit width budget used by the ordinary syntax parser.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointPublicBounds

open FoundationCompactSyntaxTokenMachine
open FoundationCompactClosedFormulaTokenMachine
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
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTraceInstallation
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectParserNoOutputInitialFinalFormula
open FoundationCompactNumericListedDirectParserNoOutputInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectParserClosedSuccessBridge
open FoundationCompactNumericListedDirectParserClosedSuccessStepFormula
open FoundationCompactNumericListedDirectParserClosedStepFormula
open FoundationCompactNumericListedDirectParserClosedAdjacentStepFormula
open FoundationCompactNumericListedDirectParserClosedAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserClosedAdjacentStepBoundedInstallation
open FoundationCompactNumericListedDirectParserClosedNoOutputTraceFormula
open FoundationCompactNumericListedDirectParserClosedNoOutputExactFormula
open FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectParserSyntaxTraceBounds
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointPublicBounds
open FoundationCompactNumericListedDirectSequentFormulaTracePublicBounds
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

private theorem
    CompactUnifiedParserClosedFreeVariableFailureRows.exists_fittingWitness
    {tokenTable width tokenCount : Nat}
    {current next : CompactUnifiedParserStateRowCoordinates}
    {witness : CompactUnifiedParserSyntaxStepWitnessCoordinates}
    (hcurrentCount : current.tasksCount <= tokenCount)
    (hrows : CompactUnifiedParserClosedFreeVariableFailureRows
      tokenTable width tokenCount current next witness) :
    exists fittingWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates,
      CompactUnifiedParserClosedFreeVariableFailureRows
          tokenTable width tokenCount current next fittingWitness /\
        CompactUnifiedParserSyntaxStepWitnessFits
          width tokenCount fittingWitness := by
  rcases hrows with
    ⟨hcurrentRunning, huncons, hlength, htagRows, hfailureRows⟩
  have hunconsFit :=
    CompactAdditiveSyntaxTaskListUnconsRowsWithSize.coordinateFits
      hcurrentCount huncons
  let termWitness : CompactSyntaxTermTaskWitnessCoordinates :=
    { tailBoundary := witness.term.tailBoundary
      tailCount := witness.term.tailCount
      tailBoundarySize := witness.term.tailBoundarySize
      tag := 0
      argument := 0
      functionCode := 0 }
  let fittingWitness :=
    CompactUnifiedParserSyntaxStepWitnessCoordinates.ofTerm
      witness.slot0 termWitness
  refine ⟨fittingWitness, ?_, ?_⟩
  · refine ⟨hcurrentRunning, ?_, hlength, htagRows, ?_⟩
    · simpa only [fittingWitness, termWitness,
        CompactUnifiedParserSyntaxStepWitnessCoordinates.term_ofTerm,
        CompactUnifiedParserSyntaxStepWitnessCoordinates.slot0_ofTerm]
        using huncons
    · simpa only [fittingWitness, termWitness,
        CompactUnifiedParserSyntaxStepWitnessCoordinates.term_ofTerm]
        using hfailureRows
  · exact
      { slot0_size := hunconsFit.headBinderArity_size
        slot1_size := hunconsFit.tailBoundary_size
        slot2_size := hunconsFit.tailCount_size
        slot3_size := hunconsFit.tailBoundarySize_size
        slot4_size := by
          simp [fittingWitness, termWitness,
            CompactUnifiedParserSyntaxStepWitnessCoordinates.ofTerm,
            compactFormulaTransformAdjacentStepPublicWidth,
            compactBinaryNatStreamStepWitnessPublicWidth]
        slot5_size := by
          simp [fittingWitness, termWitness,
            CompactUnifiedParserSyntaxStepWitnessCoordinates.ofTerm,
            compactFormulaTransformAdjacentStepPublicWidth,
            compactBinaryNatStreamStepWitnessPublicWidth]
        slot6_size := by
          simp [fittingWitness, termWitness,
            CompactUnifiedParserSyntaxStepWitnessCoordinates.ofTerm,
            compactFormulaTransformAdjacentStepPublicWidth,
            compactBinaryNatStreamStepWitnessPublicWidth] }

private theorem compactUnifiedParserClosedStepRows_complete_with_fit
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hwell : CompactSyntaxTaskStackFieldsWellFormed current.2.1)
    (hstep : next = compactClosedSyntaxParserStep current) :
    exists witness : CompactUnifiedParserSyntaxStepWitnessCoordinates,
      CompactUnifiedParserClosedStepRows
          tokenTable width tokenCount currentCoordinates nextCoordinates
            witness /\
        CompactUnifiedParserSyntaxStepWitnessFits
          width tokenCount witness := by
  by_cases hsafe : CompactClosedSyntaxStepSafe current
  · have hordinary : next = compactSyntaxParserStep current := by
      calc
        next = compactClosedSyntaxParserStep current := hstep
        _ = compactSyntaxParserStep current :=
          compactClosedSyntaxParserStep_eq_compactSyntaxParserStep_of_safe
            current hsafe
    rcases compactUnifiedParserSyntaxStepRows_complete_with_fit
        hcurrent hnext hwell hordinary with
      ⟨witness, hsyntaxRows, hfit⟩
    refine ⟨witness, Or.inl ⟨hsyntaxRows, ?_⟩, hfit⟩
    intro hterm
    exact CompactUnifiedParserSyntaxTermRows.guard_of_safe
      hcurrent hterm hsafe
  · rcases compactUnifiedParserClosedFreeVariableFailureRows_complete
        hcurrent hnext hwell hsafe hstep with
      ⟨witness, hfailureRows⟩
    have hcurrentCount : currentCoordinates.tasksCount <= tokenCount :=
      structuredListLayout_count_le_tokenCount hcurrent.tasksLayout
    rcases
        CompactUnifiedParserClosedFreeVariableFailureRows.exists_fittingWitness
          hcurrentCount hfailureRows with
      ⟨fittingWitness, hfittingRows, hfit⟩
    exact ⟨fittingWitness, Or.inr hfittingRows, hfit⟩

def CompactUnifiedParserClosedStateListAdjacentStepRowsWithFit
    (tokenTable width tokenCount stateBoundary : Nat)
    (states : List CompactUnifiedParserState) : Prop :=
  ∀ index < states.length - 1,
    ∃ row : CompactParserSyntaxAdjacentStepRow,
      CompactParserClosedAdjacentStepRowGraph
          tokenTable width tokenCount stateBoundary states.length index row /\
        CompactParserSyntaxAdjacentStepRowFits
          (compactParserSyntaxAdjacentStepPublicWidth width tokenCount) row

private theorem closedStateListAdjacentStepRowsWithFit_of_localTrace
    {tokenTable width tokenCount stateBoundary fuel : Nat}
    {start : CompactUnifiedParserState}
    {states : List CompactUnifiedParserState}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hvalid : CompactParserLocalTraceValid
      compactClosedSyntaxParserStep fuel start states)
    (hstart : CompactSyntaxTaskStackFieldsWellFormed start.2.1) :
    CompactUnifiedParserClosedStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary states := by
  intro index hindex
  have hstepIndex : index < fuel := by
    rw [hvalid.1] at hindex
    omega
  have hcurrentIndex : index < states.length := by
    rw [hvalid.1]
    omega
  have hnextIndex : index + 1 < states.length := by
    rw [hvalid.1]
    omega
  rcases exists_compactUnifiedParserStateAtRows_with_fixed_layout
      hrows hcurrentIndex with
    ⟨currentCoordinates, currentSize, hcurrentRows, hcurrentFixed⟩
  rcases exists_compactUnifiedParserStateAtRows_with_fixed_layout
      hrows hnextIndex with
    ⟨nextCoordinates, nextSize, hnextRows, hnextFixed⟩
  have hwell : CompactSyntaxTaskStackFieldsWellFormed
      (states.getI index).2.1 :=
    CompactParserLocalTraceValid.getI_closed_task_fields_well_formed
      hvalid hstart (Nat.le_of_lt hstepIndex)
  have hstep : states.getI (index + 1) =
      compactClosedSyntaxParserStep (states.getI index) :=
    CompactParserLocalTraceValid.getI_step hvalid hstepIndex
  rcases compactUnifiedParserClosedStepRows_complete_with_fit
      hcurrentFixed hnextFixed hwell hstep with
    ⟨stepWitness, hstepRows, hstepFit⟩
  let row : CompactParserSyntaxAdjacentStepRow :=
    { currentCoordinates := currentCoordinates
      currentSize := currentSize
      nextCoordinates := nextCoordinates
      nextSize := nextSize
      stepWitness := stepWitness }
  have hrowGraph :
      CompactParserClosedAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary states.length index row := by
    exact ⟨hcurrentRows, hnextRows, hstepRows⟩
  have hrowFit :
      CompactParserSyntaxAdjacentStepRowFits
        (compactParserSyntaxAdjacentStepPublicWidth width tokenCount) row :=
    CompactParserSyntaxAdjacentStepRowFits.of_componentFits
      (CompactUnifiedParserStateAtRows.coordinateFits hcurrentRows)
      (CompactUnifiedParserStateAtRows.coordinateFits hnextRows)
      hstepFit
  exact ⟨row, hrowGraph, hrowFit⟩

noncomputable def compactParserClosedPublicFittingAdjacentStepRowAt
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hadjacent : CompactUnifiedParserClosedStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary states)
    (index : Nat) : CompactParserSyntaxAdjacentStepRow :=
  if hindex : index < states.length - 1 then
    Classical.choose (hadjacent index hindex)
  else
    default

private theorem compactParserClosedPublicFittingAdjacentStepRowAt_spec
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hadjacent : CompactUnifiedParserClosedStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary states)
    {index : Nat} (hindex : index < states.length - 1) :
    CompactParserClosedAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary states.length index
          (compactParserClosedPublicFittingAdjacentStepRowAt
            hadjacent index) /\
      CompactParserSyntaxAdjacentStepRowFits
        (compactParserSyntaxAdjacentStepPublicWidth width tokenCount)
          (compactParserClosedPublicFittingAdjacentStepRowAt
            hadjacent index) := by
  rw [compactParserClosedPublicFittingAdjacentStepRowAt, dif_pos hindex]
  exact Classical.choose_spec (hadjacent index hindex)

noncomputable def compactParserClosedPublicFittingAdjacentStepRows
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hadjacent : CompactUnifiedParserClosedStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary states) :
    List CompactParserSyntaxAdjacentStepRow :=
  (List.range (states.length - 1)).map
    (compactParserClosedPublicFittingAdjacentStepRowAt hadjacent)

@[simp] private theorem compactParserClosedPublicFittingAdjacentStepRows_length
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hadjacent : CompactUnifiedParserClosedStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary states) :
    (compactParserClosedPublicFittingAdjacentStepRows hadjacent).length =
      states.length - 1 := by
  simp [compactParserClosedPublicFittingAdjacentStepRows]

private theorem compactParserClosedPublicFittingAdjacentStepRows_valid
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hadjacent : CompactUnifiedParserClosedStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary states) :
    CompactParserClosedAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary states.length
        (compactParserClosedPublicFittingAdjacentStepRows hadjacent) := by
  intro rowIndex hrowIndex
  have hindex : rowIndex < states.length - 1 := by
    simpa using hrowIndex
  rw [List.getI_eq_getElem _ hrowIndex]
  simpa [compactParserClosedPublicFittingAdjacentStepRows] using
    (compactParserClosedPublicFittingAdjacentStepRowAt_spec
      hadjacent hindex).1

private theorem compactParserClosedPublicFittingAdjacentStepRows_fit
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hadjacent : CompactUnifiedParserClosedStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary states) :
    CompactParserSyntaxAdjacentStepRowsFit
      (compactParserSyntaxAdjacentStepPublicWidth width tokenCount)
        (compactParserClosedPublicFittingAdjacentStepRows hadjacent) := by
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨index, hindexRange, rfl⟩
  have hsourceIndex : index < states.length - 1 :=
    List.mem_range.mp hindexRange
  exact
    (compactParserClosedPublicFittingAdjacentStepRowAt_spec
      hadjacent hsourceIndex).2

/- The complete closed no-output trace has the same public width budget as the
ordinary syntax trace, including the explicit free-variable failure row. -/
set_option maxHeartbeats 1500000 in
theorem
    localTrace_exists_compactParserClosedNoOutputExactBoundedGraph_with_publicWidth
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
    (hvalid : CompactParserOutputLocalTraceValid compactClosedSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      none states) :
    exists tableWidth,
      tableWidth <= compactParserSyntaxCanonicalTableWidthBound
        width tokenCount (compactSyntaxRunFuelBound input) /\
      CompactParserClosedNoOutputExactBoundedGraph
        tokenTable width tokenCount stateBoundary states.length
        inputBoundary input.length taskKind taskBinderArity taskRepeatCount
        tableWidth (2 ^ tableWidth) := by
  have hendpoints : states.length = compactSyntaxRunFuelBound input + 1 /\
      states.getI 0 =
        (input, [(taskKind, taskBinderArity, taskRepeatCount)], none) /\
      compactSyntaxParserStateOutput
        (states.getI (compactSyntaxRunFuelBound input)) = none := by
    have hlocal := hvalid.1
    have hlength := hlocal.1
    have hinitial := CompactParserLocalTraceValid.getI_eq_stateAt
      hlocal (Nat.zero_le (compactSyntaxRunFuelBound input))
    have hfinalIndex :
        compactSyntaxRunFuelBound input < states.length := by omega
    have htrace :
        compactParserTraceState? states (compactSyntaxRunFuelBound input) =
          some (states.getI (compactSyntaxRunFuelBound input)) := by
      unfold compactParserTraceState?
      apply List.getElem?_eq_some_iff.mpr
      refine ⟨hfinalIndex, ?_⟩
      rw [List.getI_eq_getElem _ hfinalIndex]
    have houtput := hvalid.2
    rw [htrace] at houtput
    exact ⟨hlength,
      (by simpa [compactParserStateAt] using hinitial),
      (by simpa [compactParserStateOutputOption] using houtput)⟩
  rcases (exists_compactUnifiedParserNoOutputInitialFinalRows_iff
      (Eq.refl states.length) hrows hinput).mpr hendpoints with
    ⟨endpointWitness, hendpointRows⟩
  have hfitSource :=
    closedStateListAdjacentStepRowsWithFit_of_localTrace
      hrows hvalid.1 hstartWell
  let rows := compactParserClosedPublicFittingAdjacentStepRows hfitSource
  have hrowsValid : CompactParserClosedAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary states.length rows := by
    simpa only [rows] using
      compactParserClosedPublicFittingAdjacentStepRows_valid hfitSource
  have hrowsPublicFit : CompactParserSyntaxAdjacentStepRowsFit
      (compactParserSyntaxAdjacentStepPublicWidth width tokenCount) rows := by
    simpa only [rows] using
      compactParserClosedPublicFittingAdjacentStepRows_fit hfitSource
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
    simp only [rows, compactParserClosedPublicFittingAdjacentStepRows_length]
    rw [hvalid.1.1]
    omega
  have hadjacentBounded : CompactParserClosedAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary states.length
      (compactSyntaxRunFuelBound input) tableWidth (2 ^ tableWidth) := by
    refine ⟨rfl, ?_⟩
    intro rowIndex hrowIndex
    have hrowIndex' : rowIndex < rows.length := by
      rw [hrowsLength]
      exact hrowIndex
    have hrowGraph := hrowsValid rowIndex hrowIndex'
    have hrowMem : rows.getI rowIndex ∈ rows := by
      rw [List.getI_eq_getElem _ hrowIndex']
      exact List.getElem_mem hrowIndex'
    have hcurrentStatusLayout : CompactBinaryNatStreamStatusDirectLayout
        tokenTable width tokenCount
          (rows.getI rowIndex).currentCoordinates.tasksFinish
          (rows.getI rowIndex).currentCoordinates.finish
          (states.getI rowIndex).2.2 :=
      (CompactUnifiedParserStateAtRows.fixedLayout_of_rows
        rfl hrows hrowGraph.1).statusLayout
    have hnextStatusLayout : CompactBinaryNatStreamStatusDirectLayout
        tokenTable width tokenCount
          (rows.getI rowIndex).nextCoordinates.tasksFinish
          (rows.getI rowIndex).nextCoordinates.finish
          (states.getI (rowIndex + 1)).2.2 :=
      (CompactUnifiedParserStateAtRows.fixedLayout_of_rows
        rfl hrows hrowGraph.2.1).statusLayout
    exact CompactParserClosedAdjacentStepRowGraph.toBounded
      hrowGraph (hfit (rows.getI rowIndex) hrowMem)
      (CompactBinaryNatStreamStatusDirectLayout.validBounded
        hcurrentStatusLayout harea)
      (CompactBinaryNatStreamStatusDirectLayout.validBounded
        hnextStatusLayout harea)
  have htableWidth :
      tableWidth <= compactParserSyntaxCanonicalTableWidthBound
        width tokenCount (compactSyntaxRunFuelBound input) := by
    dsimp only [tableWidth]
    unfold compactParserSyntaxCanonicalTableWidthBound
    rw [hrowsLength] at hrowsDynamic
    omega
  refine ⟨tableWidth, htableWidth, ?_⟩
  unfold CompactParserClosedNoOutputExactBoundedGraph
  exact ⟨hvalid.1.1, hendpointBounded, hadjacentBounded⟩

def compactParserClosedNoOutputExactEndpointCoordinateValues
    (coordinates : CompactParserClosedNoOutputExactEndpointCoordinates) :
    List Nat :=
  [coordinates.inputBoundary,
    coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.stateBoundary,
    coordinates.stateCount,
    coordinates.tableWidth,
    coordinates.valueBound]

def compactParserClosedNoOutputExactEndpointPublicCoordinateSizeBound
    (width tokenCount : Nat) : Nat :=
  compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound
    width tokenCount

structure CompactParserClosedNoOutputExactEndpointPublicBounds
    (coordinates : CompactParserClosedNoOutputExactEndpointCoordinates)
    (bound : Nat) : Prop where
  value_size_le :
    ∀ value ∈
      compactParserClosedNoOutputExactEndpointCoordinateValues coordinates,
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

/-- Install an already laid-out closed-parser failure trace while retaining
public bounds for all seven endpoint coordinates. -/
theorem
    exists_compactParserClosedNoOutputExactEndpointGraph_of_rows_with_publicBounds
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
    (hvalid : CompactParserOutputLocalTraceValid compactClosedSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      none states) :
    exists coordinates : CompactParserClosedNoOutputExactEndpointCoordinates,
      CompactParserClosedNoOutputExactEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            taskKind taskBinderArity taskRepeatCount coordinates /\
        CompactParserClosedNoOutputExactEndpointPublicBounds coordinates
          (compactParserClosedNoOutputExactEndpointPublicCoordinateSizeBound
            width tokenCount) /\
        coordinates.stateBoundary = stateBoundary := by
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputRows, hinputSize⟩
  rcases
      localTrace_exists_compactParserClosedNoOutputExactBoundedGraph_with_publicWidth
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
  let coordinates : CompactParserClosedNoOutputExactEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      stateBoundary := stateBoundary
      stateCount := states.length
      tableWidth := tableWidth
      valueBound := 2 ^ tableWidth }
  have hgraph :
      CompactParserClosedNoOutputExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          taskKind taskBinderArity taskRepeatCount coordinates := by
    unfold CompactParserClosedNoOutputExactEndpointGraph
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
    compactParserClosedNoOutputExactEndpointPublicCoordinateSizeBound
      width tokenCount
  have hpublic :
      CompactParserClosedNoOutputExactEndpointPublicBounds
        coordinates coordinateBound := by
    refine ⟨?_⟩
    intro value hvalue
    simp only [compactParserClosedNoOutputExactEndpointCoordinateValues,
      List.mem_cons, List.not_mem_nil, or_false] at hvalue
    rcases hvalue with h | h | h | h | h | h | h
    all_goals
      subst value
      dsimp only [coordinates, coordinateBound,
        compactParserClosedNoOutputExactEndpointPublicCoordinateSizeBound,
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
  localTrace_exists_compactParserClosedNoOutputExactBoundedGraph_with_publicWidth
#print axioms
  exists_compactParserClosedNoOutputExactEndpointGraph_of_rows_with_publicBounds

end FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointPublicBounds
