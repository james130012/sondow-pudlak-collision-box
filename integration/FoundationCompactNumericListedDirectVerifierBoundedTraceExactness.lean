import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceExactness
import integration.FoundationCompactNumericListedDirectVerifierBoundedTraceSelection

/-!
# Accepted-trace completeness for the uniformly bounded row selection

This is the canonical completeness proof with the row source replaced by the
bounded selector.  It preserves the exact initial and final states while also
retaining the coordinate bound needed for quantitative compilation.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierBoundedTraceExactness

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableAdjacencyFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge
open FoundationCompactNumericListedDirectVerifierInitialEnvironmentFormula
open FoundationCompactNumericListedDirectVerifierInitialWitnessTableRowFormula
open FoundationCompactNumericListedDirectVerifierFinalEnvironmentFormula
open FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowFormula
open FoundationCompactNumericListedDirectVerifierAcceptedTraceFormula
open FoundationCompactNumericListedDirectVerifierBoundedTraceSelection

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem acceptedTraceTable_complete_boundedRows
    {fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    (coordinateBound : Nat)
    (hrows : forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          offset /\
        row.nextState = compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          (offset + 1) /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <= coordinateBound)
    (hfuel : 0 < fuel)
    (hproofSource : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount proofStart proofFinish proofTokens)
    (hcertificateSource : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish certificateTokens)
    (haccepted :
      (compactNumericVerifierStateAt
        (compactNumericVerifierInitialState proofTokens certificateTokens)
        fuel).2 = some true) :
    let start := compactNumericVerifierInitialState
      proofTokens certificateTokens
    let rows := compactNumericVerifierBoundedStepFormulaRows fuel start
      coordinateBound hrows
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    CompactNumericVerifierAcceptedTraceTable
      tableWidth table (2 ^ tableWidth) fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish := by
  let start := compactNumericVerifierInitialState
    proofTokens certificateTokens
  let checkedRows := compactNumericVerifierBoundedCheckedStepRows fuel start
    coordinateBound hrows
  let rows := compactNumericVerifierBoundedStepFormulaRows fuel start
    coordinateBound hrows
  let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
  let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
  change CompactNumericVerifierAcceptedTraceTable
    tableWidth table (2 ^ tableWidth) fuel
    proofTable proofWidth proofTokenCount proofStart proofFinish
    certificateTable certificateWidth certificateTokenCount
    certificateStart certificateFinish
  refine ⟨rfl, hfuel, ?_, ?_, ?_, ?_⟩
  · simpa only [start, rows, tableWidth, table] using
      compactNumericVerifierBoundedStepWitnessTable_boundedGraph fuel start
        coordinateBound hrows
  · simpa only [start, rows, tableWidth, table] using
      compactNumericVerifierBoundedStepWitnessTable_rowsAdjacent fuel start
        coordinateBound hrows
  · let initialRow := checkedRows.getI 0
    have hinitialSpec := compactNumericVerifierBoundedCheckedStepRows_spec
      fuel 0 start coordinateBound hrows hfuel
    have hinitialCurrent : initialRow.currentState = start := by
      simpa only [initialRow, checkedRows, compactNumericVerifierStateAt,
        Function.iterate_zero_apply] using hinitialSpec.1
    have hinitialLayout : CompactNumericVerifierStateDirectLayout
        (initialRow.environment 0) (initialRow.environment 1)
        (initialRow.environment 2) (initialRow.environment 3)
        (initialRow.environment 4) start := by
      simpa only [hinitialCurrent] using initialRow.currentLayout
    have hinitialEnvironment : CompactNumericVerifierInitialEnvironment
        initialRow.environment
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish := by
      apply CompactNumericVerifierInitialEnvironment.ofInitialState
        initialRow.formula hinitialLayout hproofSource hcertificateSource
    have hinitialTableEnvironment : CompactNumericVerifierInitialEnvironment
        (compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table 0)
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish := by
      have henvironment :=
        compactNumericVerifierBoundedStepWitnessTable_environment_eq fuel 0
          start coordinateBound hrows hfuel
      change compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table 0 = initialRow.environment at henvironment
      rw [henvironment]
      exact hinitialEnvironment
    apply CompactNumericVerifierInitialEnvironment.to_witnessTableRow
      (fun coordinate =>
        compactNumericVerifierStepWitnessTableColumnValue_le_pow
          tableWidth table 0 coordinate.val)
      (fun coordinate =>
        compactNumericVerifierStepWitnessTableColumnValue_entry
          tableWidth table 0 coordinate.val)
      hinitialTableEnvironment
  · let lastRow := fuel - 1
    have hlastRow : lastRow < fuel := by omega
    have hlastNext : lastRow + 1 = fuel := by omega
    refine ⟨lastRow, hlastRow, hlastNext, ?_⟩
    let finalRow := checkedRows.getI lastRow
    have hfinalSpec := compactNumericVerifierBoundedCheckedStepRows_spec
      fuel lastRow start coordinateBound hrows hlastRow
    have hfinalNext : finalRow.nextState =
        compactNumericVerifierStateAt start fuel := by
      exact hfinalSpec.2.1.trans (by rw [hlastNext])
    have hfinalLayout : CompactNumericVerifierStateDirectLayout
        (finalRow.environment 0) (finalRow.environment 1)
        (finalRow.environment 2) (finalRow.environment 24)
        (finalRow.environment 25)
        (compactNumericVerifierStateAt start fuel) := by
      simpa only [hfinalNext] using finalRow.nextLayout
    have haccepted' :
        (compactNumericVerifierStateAt start fuel).2 = some true := by
      simpa only [start] using haccepted
    have hfinalEnvironment : CompactNumericVerifierAcceptedEnvironment
        finalRow.environment := by
      exact CompactNumericVerifierAcceptedEnvironment.ofAcceptedState
        finalRow.formula hfinalLayout haccepted'
    have hfinalTableEnvironment : CompactNumericVerifierAcceptedEnvironment
        (compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table lastRow) := by
      have henvironment :=
        compactNumericVerifierBoundedStepWitnessTable_environment_eq fuel
          lastRow start coordinateBound hrows hlastRow
      change compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table lastRow = finalRow.environment at henvironment
      rw [henvironment]
      exact hfinalEnvironment
    apply CompactNumericVerifierAcceptedEnvironment.to_witnessTableRow
      (fun coordinate =>
        compactNumericVerifierStepWitnessTableColumnValue_entry
          tableWidth table lastRow coordinate.val)
      hfinalTableEnvironment

#print axioms acceptedTraceTable_complete_boundedRows

end FoundationCompactNumericListedDirectVerifierBoundedTraceExactness
