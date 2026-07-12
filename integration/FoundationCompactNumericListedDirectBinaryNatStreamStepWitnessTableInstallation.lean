import integration.FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
import integration.FoundationCompactNumericListedDirectBinaryNatStreamStepInstallation

/-!
# Installation of bounded stream-step witness tables

Every adjacent state pair is converted to one normalized 32-column row.  The
canonical fixed-width table of these rows satisfies the 35-variable Delta-zero
step formula at every row and has a public bit-size bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableInstallation

open FoundationCompactAdditiveTokenCodec
open FoundationCompactBinaryNatStreamMachine
open FoundationCompactPackedTokenStreamDirectTrace
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTraceComponentTableau
open FoundationCompactNumericListedDirectBinaryNatStreamStepRows
open FoundationCompactNumericListedDirectBinaryNatStreamStepFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStateFormula
open CompactBinaryNatStreamStateFixedLayout
open CompactBinaryNatStreamStateCoreFixedLayout
open FoundationCompactNumericListedDirectBinaryNatStreamStepRealization
open FoundationCompactNumericListedDirectBinaryNatStreamStepInstallation
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTable
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound

theorem adjacentStepGraphRows_exists_fittingRow
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List BinaryNatStreamState}
    (hadjacent : CompactBinaryNatStreamStateListAdjacentStepGraphRows
      tokenTable width tokenCount stateBoundary states)
    {index : Nat} (hindex : index < states.length - 1) :
    ∃ row : CompactBinaryNatStreamStepStateRow,
      CompactBinaryNatStreamStepStateGraph tokenTable width tokenCount
        row.currentCoordinates row.nextCoordinates
        row.currentSize row.nextSize row.witness ∧
      CompactBinaryNatStreamStepStateRowFits
        (compactBinaryNatStreamStepWitnessPublicWidth tokenCount) row := by
  rcases hadjacent index hindex with
    ⟨_currentLeft, _hcurrentLeft,
      _currentRight, _hcurrentRight,
      _nextLeft, _hnextLeft, _nextRight, _hnextRight,
      _hcurrentLeftEntry, _hcurrentRightEntry,
      _hnextLeftEntry, _hnextRightEntry,
      currentCoordinates, nextCoordinates, witness,
      _hcurrentStart, _hcurrentFinish, _hnextStart, _hnextFinish,
      hcurrentFixed, hnextFixed, hstep⟩
  rcases toCoreGraph (coreFixedLayout hcurrentFixed) with
    ⟨currentSize, hcurrentGraph⟩
  rcases toCoreGraph (coreFixedLayout hnextFixed) with
    ⟨nextSize, hnextGraph⟩
  have hstateGraph : CompactBinaryNatStreamStepStateGraph
      tokenTable width tokenCount currentCoordinates nextCoordinates
        currentSize nextSize witness :=
    ⟨hcurrentGraph, hnextGraph, hstep⟩
  rcases CompactBinaryNatStreamStepStateGraph.exists_fittingWitness
      hstateGraph with
    ⟨fittingWitness, hfittingGraph, hfittingWitness⟩
  let row : CompactBinaryNatStreamStepStateRow :=
    { currentCoordinates := currentCoordinates
      currentSize := currentSize
      nextCoordinates := nextCoordinates
      nextSize := nextSize
      witness := fittingWitness }
  refine ⟨row, ?_, ?_⟩
  · exact hfittingGraph
  · exact CompactBinaryNatStreamStepStateRow.rowFits
      (CompactBinaryNatStreamStateCoreGraph.coordinateFits hcurrentGraph)
      (CompactBinaryNatStreamStateCoreGraph.coordinateFits hnextGraph)
      hfittingWitness

noncomputable def compactBinaryNatStreamFittingStepRowAt
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List BinaryNatStreamState}
    (hadjacent : CompactBinaryNatStreamStateListAdjacentStepGraphRows
      tokenTable width tokenCount stateBoundary states)
    (index : Nat) : CompactBinaryNatStreamStepStateRow :=
  if hindex : index < states.length - 1 then
    Classical.choose
      (adjacentStepGraphRows_exists_fittingRow hadjacent hindex)
  else default

theorem compactBinaryNatStreamFittingStepRowAt_graph
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List BinaryNatStreamState}
    (hadjacent : CompactBinaryNatStreamStateListAdjacentStepGraphRows
      tokenTable width tokenCount stateBoundary states)
    {index : Nat} (hindex : index < states.length - 1) :
    let row := compactBinaryNatStreamFittingStepRowAt hadjacent index
    CompactBinaryNatStreamStepStateGraph tokenTable width tokenCount
      row.currentCoordinates row.nextCoordinates
      row.currentSize row.nextSize row.witness := by
  rw [compactBinaryNatStreamFittingStepRowAt, dif_pos hindex]
  exact (Classical.choose_spec
    (adjacentStepGraphRows_exists_fittingRow hadjacent hindex)).1

theorem compactBinaryNatStreamFittingStepRowAt_fits
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List BinaryNatStreamState}
    (hadjacent : CompactBinaryNatStreamStateListAdjacentStepGraphRows
      tokenTable width tokenCount stateBoundary states)
    {index : Nat} (hindex : index < states.length - 1) :
    CompactBinaryNatStreamStepStateRowFits
      (compactBinaryNatStreamStepWitnessPublicWidth tokenCount)
      (compactBinaryNatStreamFittingStepRowAt hadjacent index) := by
  rw [compactBinaryNatStreamFittingStepRowAt, dif_pos hindex]
  exact (Classical.choose_spec
    (adjacentStepGraphRows_exists_fittingRow hadjacent hindex)).2

noncomputable def compactBinaryNatStreamFittingStepRows
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List BinaryNatStreamState}
    (hadjacent : CompactBinaryNatStreamStateListAdjacentStepGraphRows
      tokenTable width tokenCount stateBoundary states) :
    List CompactBinaryNatStreamStepStateRow :=
  (List.range (states.length - 1)).map
    (compactBinaryNatStreamFittingStepRowAt hadjacent)

@[simp] theorem compactBinaryNatStreamFittingStepRows_length
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List BinaryNatStreamState}
    (hadjacent : CompactBinaryNatStreamStateListAdjacentStepGraphRows
      tokenTable width tokenCount stateBoundary states) :
    (compactBinaryNatStreamFittingStepRows hadjacent).length =
      states.length - 1 := by
  simp [compactBinaryNatStreamFittingStepRows]

theorem compactBinaryNatStreamFittingStepRows_valid
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List BinaryNatStreamState}
    (hadjacent : CompactBinaryNatStreamStateListAdjacentStepGraphRows
      tokenTable width tokenCount stateBoundary states) :
    CompactBinaryNatStreamStepStateRowsValid tokenTable width tokenCount
      (compactBinaryNatStreamFittingStepRows hadjacent) := by
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨index, hindex, rfl⟩
  exact compactBinaryNatStreamFittingStepRowAt_graph hadjacent
    (List.mem_range.mp hindex)

theorem compactBinaryNatStreamFittingStepRows_fit
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List BinaryNatStreamState}
    (hadjacent : CompactBinaryNatStreamStateListAdjacentStepGraphRows
      tokenTable width tokenCount stateBoundary states) :
    CompactBinaryNatStreamStepStateRowsFit
      (compactBinaryNatStreamStepWitnessPublicWidth tokenCount)
      (compactBinaryNatStreamFittingStepRows hadjacent) := by
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨index, hindex, rfl⟩
  exact compactBinaryNatStreamFittingStepRowAt_fits hadjacent
    (List.mem_range.mp hindex)

theorem adjacentStepGraphRows_exists_boundedWitnessTable
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List BinaryNatStreamState}
    (hadjacent : CompactBinaryNatStreamStateListAdjacentStepGraphRows
      tokenTable width tokenCount stateBoundary states) :
    ∃ table,
      Nat.size table ≤
        (states.length - 1) *
          compactBinaryNatStreamStepWitnessColumnCount *
          compactBinaryNatStreamStepWitnessPublicWidth tokenCount ∧
      CompactBinaryNatStreamStepWitnessTableGraph
        tokenTable width tokenCount
        (compactBinaryNatStreamStepWitnessPublicWidth tokenCount)
        table (states.length - 1) := by
  let rows := compactBinaryNatStreamFittingStepRows hadjacent
  let tableWidth := compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  let table := compactBinaryNatStreamStepWitnessTableCode tableWidth rows
  have hfit : CompactBinaryNatStreamStepStateRowsFit tableWidth rows :=
    compactBinaryNatStreamFittingStepRows_fit hadjacent
  have hvalid : CompactBinaryNatStreamStepStateRowsValid
      tokenTable width tokenCount rows :=
    compactBinaryNatStreamFittingStepRows_valid hadjacent
  refine ⟨table, ?_, ?_⟩
  · simpa [table, tableWidth, rows] using
      compactBinaryNatStreamStepWitnessTableCode_size_le tableWidth rows
  · simpa [table, tableWidth, rows] using
      compactBinaryNatStreamStepWitnessTableCode_graph hfit hvalid

theorem compactNumericListedDirectTrace_packedStream_boundedWitnessTables
    (code formulaCode : Nat) (trace : CompactNumericListedDirectTrace)
    (hvalid : CompactNumericListedDirectTraceValid
      code formulaCode trace) :
    let tokens := compactNumericListedDirectTraceTokens trace
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    let tableWidth :=
      compactBinaryNatStreamStepWitnessPublicWidth tokens.length
    let proofStates :=
      (compactNumericDirectTraceCertifiedStreamTrace trace).2
    let formulaStates :=
      (compactNumericDirectTraceFormulaStreamTrace trace).2
    ∃ proofStepTable formulaStepTable,
      Nat.size proofStepTable ≤
          (proofStates.length - 1) *
            compactBinaryNatStreamStepWitnessColumnCount * tableWidth ∧
      CompactBinaryNatStreamStepWitnessTableGraph
        tokenTable width tokens.length tableWidth proofStepTable
          (proofStates.length - 1) ∧
      Nat.size formulaStepTable ≤
          (formulaStates.length - 1) *
            compactBinaryNatStreamStepWitnessColumnCount * tableWidth ∧
      CompactBinaryNatStreamStepWitnessTableGraph
        tokenTable width tokens.length tableWidth formulaStepTable
          (formulaStates.length - 1) := by
  let tokens := compactNumericListedDirectTraceTokens trace
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  let tableWidth :=
    compactBinaryNatStreamStepWitnessPublicWidth tokens.length
  let proofStates :=
    (compactNumericDirectTraceCertifiedStreamTrace trace).2
  let formulaStates :=
    (compactNumericDirectTraceFormulaStreamTrace trace).2
  rcases
      compactNumericListedDirectTrace_packedStream_step_graph_rows
        code formulaCode trace hvalid with
    ⟨_proofStateBoundaryTable, _formulaStateBoundaryTable,
      _hproofLayout, hproofAdjacent, _hproofBoundarySize,
      _hformulaLayout, hformulaAdjacent, _hformulaBoundarySize⟩
  rcases adjacentStepGraphRows_exists_boundedWitnessTable hproofAdjacent with
    ⟨proofStepTable, hproofSize, hproofGraph⟩
  rcases adjacentStepGraphRows_exists_boundedWitnessTable hformulaAdjacent with
    ⟨formulaStepTable, hformulaSize, hformulaGraph⟩
  exact ⟨proofStepTable, formulaStepTable,
    hproofSize, hproofGraph, hformulaSize, hformulaGraph⟩

#print axioms adjacentStepGraphRows_exists_fittingRow
#print axioms compactBinaryNatStreamFittingStepRows_valid
#print axioms compactBinaryNatStreamFittingStepRows_fit
#print axioms adjacentStepGraphRows_exists_boundedWitnessTable
#print axioms compactNumericListedDirectTrace_packedStream_boundedWitnessTables

end FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableInstallation
