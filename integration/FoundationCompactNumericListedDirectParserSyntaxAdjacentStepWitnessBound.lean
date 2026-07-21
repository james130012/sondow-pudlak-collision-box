import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable

/-!
# Public bounds for syntax-parser adjacent-step witnesses

The formula-transform compiler already constructs bounded witnesses for every
underlying syntax-parser branch.  This file exposes the parser-only consequence:
both state rows and all seven step slots fit one public width depending only on
the shared token-table width and token count.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessBound

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxTraceInstallation
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound

def compactParserSyntaxAdjacentStepPublicWidth
    (width tokenCount : Nat) : Nat :=
  compactFormulaTransformAdjacentStepPublicWidth width tokenCount

theorem width_le_compactParserSyntaxAdjacentStepPublicWidth
    (width tokenCount : Nat) :
    width <= compactParserSyntaxAdjacentStepPublicWidth width tokenCount := by
  exact width_le_compactFormulaTransformAdjacentStepPublicWidth width tokenCount

theorem natSize_le_parserStepWidth_of_le_tokenCount
    {value width tokenCount : Nat} (hvalue : value <= tokenCount) :
    Nat.size value <=
      compactParserSyntaxAdjacentStepPublicWidth width tokenCount := by
  exact natSize_le_transformStepWidth_of_le_tokenCount hvalue

theorem natSize_le_parserStepWidth_of_le_boundaryArea
    {value width tokenCount : Nat}
    (hvalue : value <= (tokenCount + 1) * tokenCount) :
    Nat.size value <=
      compactParserSyntaxAdjacentStepPublicWidth width tokenCount := by
  exact natSize_le_transformStepWidth_of_le_boundaryArea hvalue

structure CompactUnifiedParserStateCoreCoordinateFits
    (width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness) : Prop where
  start : Nat.size coordinates.start <=
    compactParserSyntaxAdjacentStepPublicWidth width tokenCount
  finish : Nat.size coordinates.finish <=
    compactParserSyntaxAdjacentStepPublicWidth width tokenCount
  tokensFinish : Nat.size coordinates.tokensFinish <=
    compactParserSyntaxAdjacentStepPublicWidth width tokenCount
  tasksFinish : Nat.size coordinates.tasksFinish <=
    compactParserSyntaxAdjacentStepPublicWidth width tokenCount
  tokensBoundary : Nat.size coordinates.tokensBoundary <=
    compactParserSyntaxAdjacentStepPublicWidth width tokenCount
  tokensCount : Nat.size coordinates.tokensCount <=
    compactParserSyntaxAdjacentStepPublicWidth width tokenCount
  tasksBoundary : Nat.size coordinates.tasksBoundary <=
    compactParserSyntaxAdjacentStepPublicWidth width tokenCount
  tasksCount : Nat.size coordinates.tasksCount <=
    compactParserSyntaxAdjacentStepPublicWidth width tokenCount
  tokensBoundarySize : Nat.size sizeWitness.tokensBoundarySize <=
    compactParserSyntaxAdjacentStepPublicWidth width tokenCount
  tasksBoundarySize : Nat.size sizeWitness.tasksBoundarySize <=
    compactParserSyntaxAdjacentStepPublicWidth width tokenCount
  finish_le_tokenCount : coordinates.finish <= tokenCount
  tokensCount_le_tokenCount : coordinates.tokensCount <= tokenCount
  tasksCount_le_tokenCount : coordinates.tasksCount <= tokenCount

theorem CompactUnifiedParserStateCoreGraph.coordinateFits
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactUnifiedParserStateRowCoordinates}
    {sizeWitness : CompactUnifiedParserStateCoreSizeWitness}
    (hgraph : CompactUnifiedParserStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    CompactUnifiedParserStateCoreCoordinateFits
      width tokenCount coordinates sizeWitness := by
  rcases hgraph with
    ⟨houter, htokensLayout, _htokensRows,
      hinner, htasksLayout, _htasksRows,
      htokensSizeEq, htokensSize,
      htasksSizeEq, htasksSize⟩
  have hfinish : coordinates.finish <= tokenCount := houter.2.2
  have hstart : coordinates.start <= tokenCount :=
    (Nat.le_of_lt houter.1).trans
      ((Nat.le_of_lt houter.2.1).trans hfinish)
  have htokensFinish : coordinates.tokensFinish <= tokenCount :=
    (Nat.le_of_lt houter.2.1).trans hfinish
  have htasksFinish : coordinates.tasksFinish <= tokenCount :=
    (Nat.le_of_lt hinner.2.1).trans hfinish
  have htokensCount : coordinates.tokensCount <= tokenCount :=
    structuredListLayout_count_le_tokenCount htokensLayout
  have htasksCount : coordinates.tasksCount <= tokenCount :=
    structuredListLayout_count_le_tokenCount htasksLayout
  have htokensArea : sizeWitness.tokensBoundarySize <=
      (tokenCount + 1) * tokenCount :=
    htokensSize.trans (listBoundaryArea_le_publicArea htokensCount)
  have htasksArea : sizeWitness.tasksBoundarySize <=
      (tokenCount + 1) * tokenCount :=
    htasksSize.trans (listBoundaryArea_le_publicArea htasksCount)
  refine
    { start := natSize_le_parserStepWidth_of_le_tokenCount hstart
      finish := natSize_le_parserStepWidth_of_le_tokenCount hfinish
      tokensFinish :=
        natSize_le_parserStepWidth_of_le_tokenCount htokensFinish
      tasksFinish :=
        natSize_le_parserStepWidth_of_le_tokenCount htasksFinish
      tokensBoundary := ?_
      tokensCount :=
        natSize_le_parserStepWidth_of_le_tokenCount htokensCount
      tasksBoundary := ?_
      tasksCount :=
        natSize_le_parserStepWidth_of_le_tokenCount htasksCount
      tokensBoundarySize :=
        natSize_le_parserStepWidth_of_le_boundaryArea htokensArea
      tasksBoundarySize :=
        natSize_le_parserStepWidth_of_le_boundaryArea htasksArea
      finish_le_tokenCount := hfinish
      tokensCount_le_tokenCount := htokensCount
      tasksCount_le_tokenCount := htasksCount }
  · rw [← htokensSizeEq]
    exact htokensArea.trans
      (boundaryArea_le_streamStepWidth tokenCount |>.trans
        (streamWidth_le_compactFormulaTransformAdjacentStepPublicWidth
          width tokenCount))
  · rw [← htasksSizeEq]
    exact htasksArea.trans
      (boundaryArea_le_streamStepWidth tokenCount |>.trans
        (streamWidth_le_compactFormulaTransformAdjacentStepPublicWidth
          width tokenCount))

theorem CompactUnifiedParserStateAtRows.coordinateFits
    {tokenTable width tokenCount stateBoundary stateCount index : Nat}
    {coordinates : CompactUnifiedParserStateRowCoordinates}
    {sizeWitness : CompactUnifiedParserStateCoreSizeWitness}
    (hrows : CompactUnifiedParserStateAtRows
      tokenTable width tokenCount stateBoundary stateCount index
        coordinates sizeWitness) :
    CompactUnifiedParserStateCoreCoordinateFits
      width tokenCount coordinates sizeWitness :=
  CompactUnifiedParserStateCoreGraph.coordinateFits hrows.2.2.2

theorem CompactParserSyntaxAdjacentStepRowFits.of_componentFits
    {width tokenCount : Nat}
    {row : CompactParserSyntaxAdjacentStepRow}
    (hcurrent : CompactUnifiedParserStateCoreCoordinateFits
      width tokenCount row.currentCoordinates row.currentSize)
    (hnext : CompactUnifiedParserStateCoreCoordinateFits
      width tokenCount row.nextCoordinates row.nextSize)
    (hstep : CompactUnifiedParserSyntaxStepWitnessFits
      width tokenCount row.stepWitness) :
    CompactParserSyntaxAdjacentStepRowFits
      (compactParserSyntaxAdjacentStepPublicWidth width tokenCount) row := by
  intro column hcolumn
  have hindex : column <
      (compactParserSyntaxAdjacentStepRowValues row).length := by
    simpa using hcolumn
  let value := (compactParserSyntaxAdjacentStepRowValues row).getI column
  change Nat.size value <= _
  have hmem : value ∈ compactParserSyntaxAdjacentStepRowValues row := by
    change (compactParserSyntaxAdjacentStepRowValues row).getI column ∈ _
    rw [List.getI_eq_getElem _ hindex]
    exact List.getElem_mem hindex
  simp only [compactParserSyntaxAdjacentStepRowValues, List.mem_cons] at hmem
  rcases hmem with
    h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h
  · simpa [h] using hcurrent.start
  · simpa [h] using hcurrent.finish
  · simpa [h] using hcurrent.tokensFinish
  · simpa [h] using hcurrent.tasksFinish
  · simpa [h] using hcurrent.tokensBoundary
  · simpa [h] using hcurrent.tokensCount
  · simpa [h] using hcurrent.tasksBoundary
  · simpa [h] using hcurrent.tasksCount
  · simpa [h] using hcurrent.tokensBoundarySize
  · simpa [h] using hcurrent.tasksBoundarySize
  · simpa [h] using hnext.start
  · simpa [h] using hnext.finish
  · simpa [h] using hnext.tokensFinish
  · simpa [h] using hnext.tasksFinish
  · simpa [h] using hnext.tokensBoundary
  · simpa [h] using hnext.tokensCount
  · simpa [h] using hnext.tasksBoundary
  · simpa [h] using hnext.tasksCount
  · simpa [h] using hnext.tokensBoundarySize
  · simpa [h] using hnext.tasksBoundarySize
  · simpa [h, compactParserSyntaxAdjacentStepPublicWidth] using
      hstep.slot0_size
  · simpa [h, compactParserSyntaxAdjacentStepPublicWidth] using
      hstep.slot1_size
  · simpa [h, compactParserSyntaxAdjacentStepPublicWidth] using
      hstep.slot2_size
  · simpa [h, compactParserSyntaxAdjacentStepPublicWidth] using
      hstep.slot3_size
  · simpa [h, compactParserSyntaxAdjacentStepPublicWidth] using
      hstep.slot4_size
  · simpa [h, compactParserSyntaxAdjacentStepPublicWidth] using
      hstep.slot5_size
  · rcases h with h | h
    · simpa [h, compactParserSyntaxAdjacentStepPublicWidth] using
        hstep.slot6_size
    · simp at h

def CompactUnifiedParserSyntaxStateListAdjacentStepRowsWithFit
    (tokenTable width tokenCount stateBoundary : Nat)
    (states : List CompactUnifiedParserState) : Prop :=
  ∀ index < states.length - 1,
    ∃ row : CompactParserSyntaxAdjacentStepRow,
      CompactParserSyntaxAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary states.length index row ∧
      CompactParserSyntaxAdjacentStepRowFits
        (compactParserSyntaxAdjacentStepPublicWidth width tokenCount) row

theorem stateListAdjacentStepRowsWithFit_of_localTrace
    {tokenTable width tokenCount stateBoundary fuel : Nat}
    {start : CompactUnifiedParserState}
    {states : List CompactUnifiedParserState}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hvalid : CompactParserLocalTraceValid
      compactSyntaxParserStep fuel start states)
    (hstart : CompactSyntaxTaskStackFieldsWellFormed start.2.1) :
    CompactUnifiedParserSyntaxStateListAdjacentStepRowsWithFit
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
    CompactParserLocalTraceValid.getI_task_fields_well_formed
      hvalid hstart (Nat.le_of_lt hstepIndex)
  have hstep : states.getI (index + 1) =
      compactSyntaxParserStep (states.getI index) :=
    CompactParserLocalTraceValid.getI_step hvalid hstepIndex
  rcases compactUnifiedParserSyntaxStepRows_complete_with_fit
      hcurrentFixed hnextFixed hwell hstep with
    ⟨stepWitness, hstepRows, hstepFit⟩
  let row : CompactParserSyntaxAdjacentStepRow :=
    { currentCoordinates := currentCoordinates
      currentSize := currentSize
      nextCoordinates := nextCoordinates
      nextSize := nextSize
      stepWitness := stepWitness }
  have hcurrentFit :=
    CompactUnifiedParserStateAtRows.coordinateFits hcurrentRows
  have hnextFit :=
    CompactUnifiedParserStateAtRows.coordinateFits hnextRows
  refine ⟨row, ?_, ?_⟩
  · exact ⟨hcurrentRows, hnextRows, hstepRows⟩
  · exact CompactParserSyntaxAdjacentStepRowFits.of_componentFits
      hcurrentFit hnextFit hstepFit

noncomputable def compactParserSyntaxPublicFittingAdjacentStepRowAt
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hfit : CompactUnifiedParserSyntaxStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary states)
    (index : Nat) : CompactParserSyntaxAdjacentStepRow :=
  if hindex : index < states.length - 1 then
    Classical.choose (hfit index hindex)
  else
    default

theorem compactParserSyntaxPublicFittingAdjacentStepRowAt_graph
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hfit : CompactUnifiedParserSyntaxStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary states)
    {index : Nat} (hindex : index < states.length - 1) :
    CompactParserSyntaxAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary states.length index
        (compactParserSyntaxPublicFittingAdjacentStepRowAt hfit index) := by
  rw [compactParserSyntaxPublicFittingAdjacentStepRowAt, dif_pos hindex]
  exact (Classical.choose_spec (hfit index hindex)).1

theorem compactParserSyntaxPublicFittingAdjacentStepRowAt_fits
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hfit : CompactUnifiedParserSyntaxStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary states)
    {index : Nat} (hindex : index < states.length - 1) :
    CompactParserSyntaxAdjacentStepRowFits
      (compactParserSyntaxAdjacentStepPublicWidth width tokenCount)
      (compactParserSyntaxPublicFittingAdjacentStepRowAt hfit index) := by
  rw [compactParserSyntaxPublicFittingAdjacentStepRowAt, dif_pos hindex]
  exact (Classical.choose_spec (hfit index hindex)).2

noncomputable def compactParserSyntaxPublicFittingAdjacentStepRows
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hfit : CompactUnifiedParserSyntaxStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary states) :
    List CompactParserSyntaxAdjacentStepRow :=
  (List.range (states.length - 1)).map
    (compactParserSyntaxPublicFittingAdjacentStepRowAt hfit)

@[simp] theorem compactParserSyntaxPublicFittingAdjacentStepRows_length
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hfit : CompactUnifiedParserSyntaxStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary states) :
    (compactParserSyntaxPublicFittingAdjacentStepRows hfit).length =
      states.length - 1 := by
  simp [compactParserSyntaxPublicFittingAdjacentStepRows]

theorem compactParserSyntaxPublicFittingAdjacentStepRows_valid
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hfit : CompactUnifiedParserSyntaxStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary states) :
    CompactParserSyntaxAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary states.length
        (compactParserSyntaxPublicFittingAdjacentStepRows hfit) := by
  intro rowIndex hrowIndex
  have hindex : rowIndex < states.length - 1 := by
    simpa using hrowIndex
  rw [List.getI_eq_getElem _ hrowIndex]
  simpa [compactParserSyntaxPublicFittingAdjacentStepRows] using
    compactParserSyntaxPublicFittingAdjacentStepRowAt_graph hfit hindex

theorem compactParserSyntaxPublicFittingAdjacentStepRows_fit
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hfit : CompactUnifiedParserSyntaxStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary states) :
    CompactParserSyntaxAdjacentStepRowsFit
      (compactParserSyntaxAdjacentStepPublicWidth width tokenCount)
        (compactParserSyntaxPublicFittingAdjacentStepRows hfit) := by
  intro row hrow column hcolumn
  rcases List.mem_map.mp hrow with ⟨index, hindexRange, rfl⟩
  have hindex : index < states.length - 1 := List.mem_range.mp hindexRange
  exact compactParserSyntaxPublicFittingAdjacentStepRowAt_fits
    hfit hindex column hcolumn

#print axioms CompactUnifiedParserStateCoreGraph.coordinateFits
#print axioms CompactUnifiedParserStateAtRows.coordinateFits
#print axioms CompactParserSyntaxAdjacentStepRowFits.of_componentFits
#print axioms stateListAdjacentStepRowsWithFit_of_localTrace
#print axioms compactParserSyntaxPublicFittingAdjacentStepRows_valid
#print axioms compactParserSyntaxPublicFittingAdjacentStepRows_fit

end FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessBound
