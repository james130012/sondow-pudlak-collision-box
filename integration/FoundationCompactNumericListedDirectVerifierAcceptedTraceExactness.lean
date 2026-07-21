import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceFormula

/-!
# Exactness of the accepted verifier-trace formula

An accepted witness table exists exactly when the public deterministic
verifier reaches `some true` after the same number of steps.  The soundness
direction decodes every arbitrary table row and uses the arithmetic adjacency
relation to recover the unique public run.  The completeness direction packs
the canonical public run into one fixed-width table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedTraceExactness

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectVerifierStateCrossTableEquality
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepEnvironmentSurjectivity
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierCheckedStepRows
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableAdjacencyFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge
open FoundationCompactNumericListedDirectVerifierCheckedTraceWitnessTable
open FoundationCompactNumericListedDirectVerifierInitialEnvironmentFormula
open FoundationCompactNumericListedDirectVerifierInitialWitnessTableRowFormula
open FoundationCompactNumericListedDirectVerifierFinalEnvironmentFormula
open FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowFormula
open FoundationCompactNumericListedDirectVerifierAcceptedTraceFormula

theorem exists_checkedStepRow_of_formula
    (environment : Fin 429 -> Nat)
    (hformula : compactNumericVerifierStepGraphDef.val.Evalb environment) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.environment = environment := by
  rcases compactNumericVerifierStepGraphDef_evalb_realizeExactStep
      environment hformula with
    ⟨currentState, nextState, hcurrent, hnext, hstep⟩
  exact ⟨{
    environment := environment
    currentState := currentState
    nextState := nextState
    currentLayout := hcurrent
    nextLayout := hnext
    formula := hformula
  }, rfl⟩

noncomputable def checkedStepRowOfFormula
    (environment : Fin 429 -> Nat)
    (hformula : compactNumericVerifierStepGraphDef.val.Evalb environment) :
    CompactNumericVerifierCheckedStepRow :=
  Classical.choose (exists_checkedStepRow_of_formula environment hformula)

@[simp] theorem checkedStepRowOfFormula_environment
    (environment : Fin 429 -> Nat)
    (hformula : compactNumericVerifierStepGraphDef.val.Evalb environment) :
    (checkedStepRowOfFormula environment hformula).environment = environment :=
  Classical.choose_spec (exists_checkedStepRow_of_formula environment hformula)

private theorem checkedStepRow_currentState_eq_of_layout
    (row : CompactNumericVerifierCheckedStepRow)
    {state : CompactNumericVerifierState}
    (hlayout : CompactNumericVerifierStateDirectLayout
      (row.environment 0) (row.environment 1) (row.environment 2)
      (row.environment 3) (row.environment 4) state) :
    row.currentState = state := by
  rcases
      FoundationCompactNumericListedDirectVerifierStateCrossTableEquality.CompactNumericVerifierStateDirectLayout.toSliceCarries
        row.currentLayout with
    ⟨_hfinish, hbound, _hentries⟩
  have hslices : CompactFixedWidthTokenSlicesEq
      (row.environment 0) (row.environment 1) (row.environment 2)
      (row.environment 3) (row.environment 4)
      (row.environment 3) (row.environment 4) :=
    CompactFixedWidthTokenSlicesEq.refl (by omega) hbound
  exact (CompactFixedWidthTokenSlicesEq.verifierStateValue_eq
    hslices row.currentLayout hlayout).symm

private theorem checkedStepRow_nextState_eq_of_layout
    (row : CompactNumericVerifierCheckedStepRow)
    {state : CompactNumericVerifierState}
    (hlayout : CompactNumericVerifierStateDirectLayout
      (row.environment 0) (row.environment 1) (row.environment 2)
      (row.environment 24) (row.environment 25) state) :
    row.nextState = state := by
  rcases
      FoundationCompactNumericListedDirectVerifierStateCrossTableEquality.CompactNumericVerifierStateDirectLayout.toSliceCarries
        row.nextLayout with
    ⟨_hfinish, hbound, _hentries⟩
  have hslices : CompactFixedWidthTokenSlicesEq
      (row.environment 0) (row.environment 1) (row.environment 2)
      (row.environment 24) (row.environment 25)
      (row.environment 24) (row.environment 25) :=
    CompactFixedWidthTokenSlicesEq.refl (by omega) hbound
  exact (CompactFixedWidthTokenSlicesEq.verifierStateValue_eq
    hslices row.nextLayout hlayout).symm

theorem acceptedTraceTable_sound
    {tableWidth table valueBound fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    (htrace : CompactNumericVerifierAcceptedTraceTable
      tableWidth table valueBound fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish)
    (hproofSource : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount proofStart proofFinish proofTokens)
    (hcertificateSource : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish certificateTokens) :
    (compactNumericVerifierStateAt
      (compactNumericVerifierInitialState proofTokens certificateTokens)
      fuel).2 = some true := by
  rcases htrace with
    ⟨hvalueBound, hfuel, hbounded, hadjacent, hinitial,
      lastRow, hlastRow, hlastNext, hfinal⟩
  have hboundedPow : CompactNumericVerifierStepWitnessTableBoundedGraph
      tableWidth table fuel (2 ^ tableWidth) := by
    simpa [hvalueBound] using hbounded
  have hadjacentPow : CompactNumericVerifierStepWitnessTableRowsAdjacent
      tableWidth table fuel (2 ^ tableWidth) := by
    simpa [hvalueBound] using hadjacent
  have hformula (rowIndex : Nat) (hrowIndex : rowIndex < fuel) :
      compactNumericVerifierStepGraphDef.val.Evalb
        (compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table rowIndex) :=
    (compactNumericVerifierStepWitnessTableBoundedRow_iff_formula
      tableWidth table rowIndex).mp
        (hboundedPow rowIndex hrowIndex)
  let row (rowIndex : Nat) (hrowIndex : rowIndex < fuel) :=
    checkedStepRowOfFormula
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table rowIndex)
      (hformula rowIndex hrowIndex)
  have hrowEnvironment (rowIndex : Nat) (hrowIndex : rowIndex < fuel) :
      (row rowIndex hrowIndex).environment =
        compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table rowIndex := by
    simp [row]
  have hrowInitial :
      (row 0 hfuel).currentState =
        compactNumericVerifierInitialState proofTokens certificateTokens := by
    have hinitialEnvironment := hinitial.canonical_environment
    rcases hinitialEnvironment.realizeInitialState
        (hformula 0 hfuel) hproofSource hcertificateSource with
      ⟨initialState, hinitialLayout, hinitialState⟩
    have hinitialLayout' : CompactNumericVerifierStateDirectLayout
        ((row 0 hfuel).environment 0)
        ((row 0 hfuel).environment 1)
        ((row 0 hfuel).environment 2)
        ((row 0 hfuel).environment 3)
        ((row 0 hfuel).environment 4) initialState := by
      simpa only [hrowEnvironment 0 hfuel] using hinitialLayout
    exact (checkedStepRow_currentState_eq_of_layout
      (row 0 hfuel) hinitialLayout').trans
      hinitialState
  have hrowsAdjacent (rowIndex : Nat) (hnext : rowIndex + 1 < fuel) :
      CompactNumericVerifierCheckedStepRowsAdjacent
        (row rowIndex (by omega)) (row (rowIndex + 1) hnext) := by
    have hcanonical :=
      (compactNumericVerifierStepWitnessTableAdjacentRow_iff_canonical
        tableWidth table rowIndex).mp
        (hadjacentPow rowIndex (by omega) hnext)
    unfold CompactNumericVerifierStepWitnessTableCanonicalAdjacent at hcanonical
    unfold CompactNumericVerifierCheckedStepRowsAdjacent
    simpa only [hrowEnvironment rowIndex (by omega),
      hrowEnvironment (rowIndex + 1) hnext] using hcanonical
  have hrowState (rowIndex : Nat) (hrowIndex : rowIndex < fuel) :
      (row rowIndex hrowIndex).currentState =
        compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          rowIndex := by
    induction rowIndex with
    | zero =>
        simpa [compactNumericVerifierStateAt] using hrowInitial
    | succ previous ih =>
        have hprevious : previous < fuel := by omega
        have htransition :=
          (hrowsAdjacent previous (by omega)).exact_transition
        rw [htransition, ih hprevious]
        simp [compactNumericVerifierStateAt, Function.iterate_succ_apply']
  have hfinalEnvironment := hfinal.canonical_environment
  rcases hfinalEnvironment.realizeAcceptedState
      (hformula lastRow hlastRow) with
    ⟨finalState, hfinalLayout, hfinalAccepted⟩
  have hfinalLayout' : CompactNumericVerifierStateDirectLayout
      ((row lastRow hlastRow).environment 0)
      ((row lastRow hlastRow).environment 1)
      ((row lastRow hlastRow).environment 2)
      ((row lastRow hlastRow).environment 24)
      ((row lastRow hlastRow).environment 25) finalState := by
    simpa only [hrowEnvironment lastRow hlastRow] using hfinalLayout
  have hrowFinal : (row lastRow hlastRow).nextState.2 = some true := by
    rw [checkedStepRow_nextState_eq_of_layout
      (row lastRow hlastRow) hfinalLayout']
    exact hfinalAccepted
  have hstateFinal :
      compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          fuel =
        (row lastRow hlastRow).nextState := by
    calc
      compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          fuel =
          compactNumericVerifierStateAt
            (compactNumericVerifierInitialState proofTokens certificateTokens)
            (lastRow + 1) := by rw [hlastNext]
      _ = compactNumericVerifierStep
          (compactNumericVerifierStateAt
            (compactNumericVerifierInitialState proofTokens certificateTokens)
            lastRow) := by
          simp [compactNumericVerifierStateAt, Function.iterate_succ_apply']
      _ = compactNumericVerifierStep
          (row lastRow hlastRow).currentState := by
          rw [hrowState lastRow hlastRow]
      _ = (row lastRow hlastRow).nextState :=
          (row lastRow hlastRow).exact_step.symm
  rw [hstateFinal]
  exact hrowFinal

theorem acceptedTraceTable_exact_finalLayout
    {tableWidth table valueBound fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    (htrace : CompactNumericVerifierAcceptedTraceTable
      tableWidth table valueBound fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish)
    (hproofSource : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount proofStart proofFinish proofTokens)
    (hcertificateSource : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish certificateTokens) :
    let lastRow := fuel - 1
    let environment :=
      compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table lastRow
    compactNumericVerifierStepGraphDef.val.Evalb environment /\
      CompactNumericVerifierStateDirectLayout
        (environment 0) (environment 1) (environment 2)
        (environment 24) (environment 25)
        (compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          fuel) := by
  rcases htrace with
    ⟨hvalueBound, hfuel, hbounded, hadjacent, hinitial,
      lastRow, hlastRow, hlastNext, _hfinal⟩
  have hboundedPow : CompactNumericVerifierStepWitnessTableBoundedGraph
      tableWidth table fuel (2 ^ tableWidth) := by
    simpa [hvalueBound] using hbounded
  have hadjacentPow : CompactNumericVerifierStepWitnessTableRowsAdjacent
      tableWidth table fuel (2 ^ tableWidth) := by
    simpa [hvalueBound] using hadjacent
  have hformula (rowIndex : Nat) (hrowIndex : rowIndex < fuel) :
      compactNumericVerifierStepGraphDef.val.Evalb
        (compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table rowIndex) :=
    (compactNumericVerifierStepWitnessTableBoundedRow_iff_formula
      tableWidth table rowIndex).mp (hboundedPow rowIndex hrowIndex)
  let row (rowIndex : Nat) (hrowIndex : rowIndex < fuel) :=
    checkedStepRowOfFormula
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table rowIndex)
      (hformula rowIndex hrowIndex)
  have hrowEnvironment (rowIndex : Nat) (hrowIndex : rowIndex < fuel) :
      (row rowIndex hrowIndex).environment =
        compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table rowIndex := by
    simp [row]
  have hrowInitial :
      (row 0 hfuel).currentState =
        compactNumericVerifierInitialState proofTokens certificateTokens := by
    have hinitialEnvironment := hinitial.canonical_environment
    rcases hinitialEnvironment.realizeInitialState
        (hformula 0 hfuel) hproofSource hcertificateSource with
      ⟨initialState, hinitialLayout, hinitialState⟩
    have hinitialLayout' : CompactNumericVerifierStateDirectLayout
        ((row 0 hfuel).environment 0)
        ((row 0 hfuel).environment 1)
        ((row 0 hfuel).environment 2)
        ((row 0 hfuel).environment 3)
        ((row 0 hfuel).environment 4) initialState := by
      simpa only [hrowEnvironment 0 hfuel] using hinitialLayout
    exact (checkedStepRow_currentState_eq_of_layout
      (row 0 hfuel) hinitialLayout').trans hinitialState
  have hrowsAdjacent (rowIndex : Nat) (hnext : rowIndex + 1 < fuel) :
      CompactNumericVerifierCheckedStepRowsAdjacent
        (row rowIndex (by omega)) (row (rowIndex + 1) hnext) := by
    have hcanonical :=
      (compactNumericVerifierStepWitnessTableAdjacentRow_iff_canonical
        tableWidth table rowIndex).mp
        (hadjacentPow rowIndex (by omega) hnext)
    unfold CompactNumericVerifierStepWitnessTableCanonicalAdjacent at hcanonical
    unfold CompactNumericVerifierCheckedStepRowsAdjacent
    simpa only [hrowEnvironment rowIndex (by omega),
      hrowEnvironment (rowIndex + 1) hnext] using hcanonical
  have hrowState (rowIndex : Nat) (hrowIndex : rowIndex < fuel) :
      (row rowIndex hrowIndex).currentState =
        compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          rowIndex := by
    induction rowIndex with
    | zero =>
        simpa [compactNumericVerifierStateAt] using hrowInitial
    | succ previous ih =>
        have hprevious : previous < fuel := by omega
        have htransition :=
          (hrowsAdjacent previous (by omega)).exact_transition
        rw [htransition, ih hprevious]
        simp [compactNumericVerifierStateAt, Function.iterate_succ_apply']
  have hstateFinal :
      compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          fuel =
        (row lastRow hlastRow).nextState := by
    calc
      compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          fuel =
          compactNumericVerifierStateAt
            (compactNumericVerifierInitialState proofTokens certificateTokens)
            (lastRow + 1) := by rw [hlastNext]
      _ = compactNumericVerifierStep
          (compactNumericVerifierStateAt
            (compactNumericVerifierInitialState proofTokens certificateTokens)
            lastRow) := by
          simp [compactNumericVerifierStateAt, Function.iterate_succ_apply']
      _ = compactNumericVerifierStep
          (row lastRow hlastRow).currentState := by
          rw [hrowState lastRow hlastRow]
      _ = (row lastRow hlastRow).nextState :=
          (row lastRow hlastRow).exact_step.symm
  have hfinalLayout : CompactNumericVerifierStateDirectLayout
      ((row lastRow hlastRow).environment 0)
      ((row lastRow hlastRow).environment 1)
      ((row lastRow hlastRow).environment 2)
      ((row lastRow hlastRow).environment 24)
      ((row lastRow hlastRow).environment 25)
      (compactNumericVerifierStateAt
        (compactNumericVerifierInitialState proofTokens certificateTokens)
        fuel) := by
    rw [hstateFinal]
    exact (row lastRow hlastRow).nextLayout
  have hlastRowEq : lastRow = fuel - 1 := by omega
  subst lastRow
  exact ⟨hformula (fuel - 1) hlastRow,
    by simpa only [hrowEnvironment (fuel - 1) hlastRow] using hfinalLayout⟩

theorem acceptedTraceTable_complete_canonical
    {fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    {proofTokens certificateTokens : List Nat}
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
    let rows := compactNumericVerifierCanonicalStepFormulaRows fuel start
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    CompactNumericVerifierAcceptedTraceTable
      tableWidth table (2 ^ tableWidth) fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish := by
  let start := compactNumericVerifierInitialState
    proofTokens certificateTokens
  let rows := compactNumericVerifierCanonicalStepFormulaRows fuel start
  let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
  let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
  change CompactNumericVerifierAcceptedTraceTable
    tableWidth table (2 ^ tableWidth) fuel
    proofTable proofWidth proofTokenCount proofStart proofFinish
    certificateTable certificateWidth certificateTokenCount
    certificateStart certificateFinish
  refine ⟨rfl, hfuel, ?_, ?_, ?_, ?_⟩
  · simpa only [start, rows, tableWidth, table] using
      compactNumericVerifierCanonicalStepWitnessTable_boundedGraph fuel start
  · simpa only [start, rows, tableWidth, table] using
      compactNumericVerifierCanonicalStepWitnessTable_rowsAdjacent fuel start
  · let initialRow :=
      (compactNumericVerifierCanonicalCheckedStepRows fuel start).getI 0
    have hinitialCurrent : initialRow.currentState = start := by
      exact compactNumericVerifierCanonicalCheckedStepRows_currentState
        fuel 0 start hfuel
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
        compactNumericVerifierCanonicalStepWitnessTable_environment_eq
          fuel 0 start hfuel
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
    let finalRow :=
      (compactNumericVerifierCanonicalCheckedStepRows fuel start).getI lastRow
    have hfinalNext : finalRow.nextState =
        compactNumericVerifierStateAt start fuel := by
      calc
        finalRow.nextState =
            compactNumericVerifierStateAt start (lastRow + 1) := by
          exact compactNumericVerifierCanonicalCheckedStepRows_nextState
            fuel lastRow start hlastRow
        _ = compactNumericVerifierStateAt start fuel := by rw [hlastNext]
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
        compactNumericVerifierCanonicalStepWitnessTable_environment_eq
          fuel lastRow start hlastRow
      change compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table lastRow = finalRow.environment at henvironment
      rw [henvironment]
      exact hfinalEnvironment
    apply CompactNumericVerifierAcceptedEnvironment.to_witnessTableRow
      (fun coordinate =>
        compactNumericVerifierStepWitnessTableColumnValue_entry
          tableWidth table lastRow coordinate.val)
      hfinalTableEnvironment

theorem acceptedTraceTable_complete
    {fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    {proofTokens certificateTokens : List Nat}
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
    exists tableWidth table,
      CompactNumericVerifierAcceptedTraceTable
        tableWidth table (2 ^ tableWidth) fuel
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish := by
  let start := compactNumericVerifierInitialState
    proofTokens certificateTokens
  let rows := compactNumericVerifierCanonicalStepFormulaRows fuel start
  let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
  let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
  refine ⟨tableWidth, table, ?_⟩
  simpa only [start, rows, tableWidth, table] using
    acceptedTraceTable_complete_canonical
      hfuel hproofSource hcertificateSource haccepted

/-- Rebase an accepted trace onto the two list layouts recovered from its own
row zero.  The returned trace has no external source-list coordinates. -/
theorem acceptedTraceTable_rebase_initialLists
    {tableWidth table valueBound fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    (htrace : CompactNumericVerifierAcceptedTraceTable
      tableWidth table valueBound fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish) :
    let environment :=
      compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0
    exists proofTokens certificateTokens : List Nat,
      CompactAdditiveNatListDirectLayout
          (environment 0) (environment 1) (environment 2)
          (environment 3) (environment 5) proofTokens /\
        CompactAdditiveNatListDirectLayout
          (environment 0) (environment 1) (environment 2)
          (environment 5) (environment 7) certificateTokens /\
        CompactNumericVerifierAcceptedTraceTable
          tableWidth table valueBound fuel
          (environment 0) (environment 1) (environment 2)
            (environment 3) (environment 5)
          (environment 0) (environment 1) (environment 2)
            (environment 5) (environment 7) := by
  rcases htrace with
    ⟨hvalueBound, hfuel, hbounded, hadjacent, hinitial,
      lastRow, hlastRow, hlastNext, hfinal⟩
  let environment :=
    compactNumericVerifierStepWitnessTableFormulaEnvironment
      tableWidth table 0
  have hboundedPow : CompactNumericVerifierStepWitnessTableBoundedGraph
      tableWidth table fuel (2 ^ tableWidth) := by
    simpa [hvalueBound] using hbounded
  have hformula : compactNumericVerifierStepGraphDef.val.Evalb environment := by
    exact (compactNumericVerifierStepWitnessTableBoundedRow_iff_formula
      tableWidth table 0).mp (hboundedPow 0 hfuel)
  have hinitialEnvironment : CompactNumericVerifierInitialEnvironment
      environment
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish := by
    simpa only [environment] using hinitial.canonical_environment
  rcases hinitialEnvironment.realizeInitialShape hformula with
    ⟨proofTokens, certificateTokens, initialState,
      hinitialLayout, hproofLayout, hcertificateLayout, hinitialState⟩
  have hinitialLayout' : CompactNumericVerifierStateDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 3) (environment 4)
      (compactNumericVerifierInitialState proofTokens certificateTokens) := by
    simpa only [hinitialState] using hinitialLayout
  have hselfInitialEnvironment : CompactNumericVerifierInitialEnvironment
      environment
      (environment 0) (environment 1) (environment 2)
        (environment 3) (environment 5)
      (environment 0) (environment 1) (environment 2)
        (environment 5) (environment 7) :=
    CompactNumericVerifierInitialEnvironment.ofInitialState
      hformula hinitialLayout' hproofLayout hcertificateLayout
  have hselfInitial : CompactNumericVerifierInitialWitnessTableRow
      tableWidth table valueBound 0
      (environment 0) (environment 1) (environment 2)
        (environment 3) (environment 5)
      (environment 0) (environment 1) (environment 2)
        (environment 5) (environment 7) := by
    apply CompactNumericVerifierInitialEnvironment.to_witnessTableRow
      (environment := environment)
    · intro coordinate
      rw [hvalueBound]
      exact compactNumericVerifierStepWitnessTableColumnValue_le_pow
        tableWidth table 0 coordinate.val
    · intro coordinate
      exact compactNumericVerifierStepWitnessTableColumnValue_entry
        tableWidth table 0 coordinate.val
    · exact hselfInitialEnvironment
  have hselfTrace : CompactNumericVerifierAcceptedTraceTable
      tableWidth table valueBound fuel
      (environment 0) (environment 1) (environment 2)
        (environment 3) (environment 5)
      (environment 0) (environment 1) (environment 2)
        (environment 5) (environment 7) :=
    ⟨hvalueBound, hfuel, hbounded, hadjacent, hselfInitial,
      lastRow, hlastRow, hlastNext, hfinal⟩
  exact ⟨proofTokens, certificateTokens,
    hproofLayout, hcertificateLayout, hselfTrace⟩

/-- An accepted arithmetic trace determines its own two initial input lists.
No typed source-list witness is supplied to this theorem: both lists and both
layouts are recovered from row zero of the trace table itself. -/
theorem acceptedTraceTable_sound_exists_initialLists
    {tableWidth table valueBound fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    (htrace : CompactNumericVerifierAcceptedTraceTable
      tableWidth table valueBound fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish) :
    let environment :=
      compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table 0
    exists proofTokens certificateTokens : List Nat,
      CompactAdditiveNatListDirectLayout
          (environment 0) (environment 1) (environment 2)
          (environment 3) (environment 5) proofTokens /\
        CompactAdditiveNatListDirectLayout
          (environment 0) (environment 1) (environment 2)
          (environment 5) (environment 7) certificateTokens /\
        (compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          fuel).2 = some true := by
  rcases acceptedTraceTable_rebase_initialLists htrace with
    ⟨proofTokens, certificateTokens,
      hproofLayout, hcertificateLayout, hselfTrace⟩
  exact ⟨proofTokens, certificateTokens,
    hproofLayout, hcertificateLayout,
    acceptedTraceTable_sound hselfTrace hproofLayout hcertificateLayout⟩

theorem exists_acceptedTraceTable_iff_stateAccepted
    {fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    (hfuel : 0 < fuel)
    (hproofSource : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount proofStart proofFinish proofTokens)
    (hcertificateSource : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish certificateTokens) :
    (exists tableWidth table valueBound,
      CompactNumericVerifierAcceptedTraceTable
        tableWidth table valueBound fuel
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish) ↔
      (compactNumericVerifierStateAt
        (compactNumericVerifierInitialState proofTokens certificateTokens)
        fuel).2 = some true := by
  constructor
  · rintro ⟨tableWidth, table, valueBound, htrace⟩
    exact acceptedTraceTable_sound htrace hproofSource hcertificateSource
  · intro haccepted
    rcases acceptedTraceTable_complete hfuel hproofSource
        hcertificateSource haccepted with
      ⟨tableWidth, table, htrace⟩
    exact ⟨tableWidth, table, 2 ^ tableWidth, htrace⟩

theorem exists_acceptedTraceFormula_iff_stateAccepted
    {fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    (hfuel : 0 < fuel)
    (hproofSource : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount proofStart proofFinish proofTokens)
    (hcertificateSource : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish certificateTokens) :
    (exists tableWidth table valueBound,
      compactNumericVerifierAcceptedTraceTableDef.val.Evalb
        ![tableWidth, table, valueBound, fuel,
          proofTable, proofWidth, proofTokenCount, proofStart, proofFinish,
          certificateTable, certificateWidth, certificateTokenCount,
          certificateStart, certificateFinish]) ↔
      (compactNumericVerifierStateAt
        (compactNumericVerifierInitialState proofTokens certificateTokens)
        fuel).2 = some true := by
  simpa only [compactNumericVerifierAcceptedTraceTableDef_spec] using
    exists_acceptedTraceTable_iff_stateAccepted
      hfuel hproofSource hcertificateSource

theorem stateAccepted_iff_verifierResult_true
    (proofTokens certificateTokens : List Nat) :
    (compactNumericVerifierStateAt
      (compactNumericVerifierInitialState proofTokens certificateTokens)
      (compactNumericVerifierFuelBound proofTokens certificateTokens)).2 =
        some true ↔
      compactNumericVerifierResult proofTokens certificateTokens = true := by
  unfold compactNumericVerifierStateAt compactNumericVerifierResult
    compactNumericVerifierRun
  generalize hstatus :
    (compactNumericVerifierStep^[
      compactNumericVerifierFuelBound proofTokens certificateTokens]
      (compactNumericVerifierInitialState proofTokens certificateTokens)).2 =
        status
  cases status with
  | none => simp
  | some result => cases result <;> simp

theorem exists_publicAcceptedTraceFormula_iff_verifierResult_true
    {proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    (hproofSource : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount proofStart proofFinish proofTokens)
    (hcertificateSource : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish certificateTokens) :
    (exists tableWidth table valueBound,
      compactNumericVerifierAcceptedTraceTableDef.val.Evalb
        ![tableWidth, table, valueBound,
          compactNumericVerifierFuelBound proofTokens certificateTokens,
          proofTable, proofWidth, proofTokenCount, proofStart, proofFinish,
          certificateTable, certificateWidth, certificateTokenCount,
          certificateStart, certificateFinish]) ↔
      compactNumericVerifierResult proofTokens certificateTokens = true := by
  rw [← stateAccepted_iff_verifierResult_true]
  apply exists_acceptedTraceFormula_iff_stateAccepted
    (proofTokens := proofTokens) (certificateTokens := certificateTokens)
    (by
      unfold compactNumericVerifierFuelBound
      omega)
    hproofSource hcertificateSource

#print axioms exists_checkedStepRow_of_formula
#print axioms checkedStepRowOfFormula_environment
#print axioms acceptedTraceTable_sound
#print axioms acceptedTraceTable_exact_finalLayout
#print axioms acceptedTraceTable_complete_canonical
#print axioms acceptedTraceTable_complete
#print axioms acceptedTraceTable_rebase_initialLists
#print axioms acceptedTraceTable_sound_exists_initialLists
#print axioms exists_acceptedTraceTable_iff_stateAccepted
#print axioms exists_acceptedTraceFormula_iff_stateAccepted
#print axioms stateAccepted_iff_verifierResult_true
#print axioms exists_publicAcceptedTraceFormula_iff_verifierResult_true

end FoundationCompactNumericListedDirectVerifierAcceptedTraceExactness
