import integration.FoundationCompactNumericListedDirectVerifierAcceptedControlledTraceSelection
import integration.FoundationCompactNumericListedDirectVerifierStepStateListCountControlBounds
import integration.FoundationCompactNumericListedVerifierRunExactness

/-!
# Accepted trace table retaining terminal numeric controls

This table uses the controlled row selector.  It has the same checked execution
semantics and global coordinate-size bounds as the older bounded table, but its
actual final row also carries polynomial numeric bounds for state width and
state token count.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedControlledTraceTable

open FoundationCompactAdditiveTokenCodec
open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge
open FoundationCompactNumericListedDirectVerifierInitialEnvironmentFormula
open FoundationCompactNumericListedDirectVerifierInitialWitnessTableRowFormula
open FoundationCompactNumericListedDirectVerifierFinalEnvironmentFormula
open FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowFormula
open FoundationCompactNumericListedDirectVerifierAcceptedTraceFormula
open FoundationCompactNumericListedDirectVerifierAcceptedBoundedTraceTable
open FoundationCompactNumericListedDirectVerifierAcceptedTerminalRowsControlBounds
open FoundationCompactNumericListedDirectVerifierAcceptedStateTableControlBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
open FoundationCompactNumericListedDirectVerifierAcceptedControlledTraceSelection
open FoundationCompactNumericListedDirectVerifierStepStateListCountControlBounds
open FoundationCompactNumericListedDirectVerifierCombineActiveCountBounds

noncomputable def compactNumericVerifierAcceptedControlledTraceWidth
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (streamWeight : Nat)
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) : Nat :=
  compactNumericVerifierStepFormulaDynamicWidth
    (compactNumericVerifierAcceptedControlledStepFormulaRows tree certificate
      hvalid streamWeight hproof hcertificate)

noncomputable def compactNumericVerifierAcceptedControlledTraceTable
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (streamWeight : Nat)
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) : Nat :=
  compactNumericVerifierStepWitnessTableCode
    (compactNumericVerifierAcceptedControlledTraceWidth tree certificate hvalid
      streamWeight hproof hcertificate)
    (compactNumericVerifierAcceptedControlledStepFormulaRows tree certificate
      hvalid streamWeight hproof hcertificate)

theorem compactNumericVerifierAcceptedControlledFinalRow_controlBounds
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    let fuel := compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)
    let lastRow := fuel - 1
    let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
    let finalRow :=
      (compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
        hvalid streamWeight hproof hcertificate).getI lastRow
    CompactNumericVerifierAcceptedRowControlBounds finalRow rowWeight := by
  dsimp only
  have hfuel : 0 < compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate) := by
    simp [compactNumericVerifierFuelBound]
  have hlast : compactNumericVerifierFuelBound
        (compactListedProofTokens tree)
        (compactStructuralCertificateTokens certificate) - 1 <
      compactNumericVerifierFuelBound
        (compactListedProofTokens tree)
        (compactStructuralCertificateTokens certificate) := by
    omega
  have hspec :=
    compactNumericVerifierAcceptedControlledCheckedStepRows_spec
      tree certificate hvalid (streamWeight := streamWeight)
      (offset := compactNumericVerifierFuelBound
        (compactListedProofTokens tree)
        (compactStructuralCertificateTokens certificate) - 1)
      hproof hcertificate hlast
  exact hspec.2.2.2.2.1 rfl

theorem
    compactNumericVerifierAcceptedControlledTraceEnvironment_controlBounds
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight rowIndex : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight)
    (hrowIndex : rowIndex < compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)) :
    let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
    let tableWidth := compactNumericVerifierAcceptedControlledTraceWidth
      tree certificate hvalid streamWeight hproof hcertificate
    let table := compactNumericVerifierAcceptedControlledTraceTable
      tree certificate hvalid streamWeight hproof hcertificate
    let environment :=
      compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table rowIndex
    environment 1 <=
        compactNumericVerifierAcceptedStateWidthBound rowWeight /\
      environment 2 <=
        compactNumericVerifierAcceptedStateTokenCountBound rowWeight := by
  dsimp only
  have henvironment :=
    compactNumericVerifierAcceptedControlledStepWitnessTable_environment_eq
      tree certificate hvalid (streamWeight := streamWeight)
        (rowIndex := rowIndex) hproof hcertificate hrowIndex
  have hspec :=
    compactNumericVerifierAcceptedControlledCheckedStepRows_spec
      tree certificate hvalid (streamWeight := streamWeight)
        (offset := rowIndex) hproof hcertificate hrowIndex
  have hcontrol := hspec.2.2.2.1
  simp only [compactNumericVerifierAcceptedControlledTraceWidth,
    compactNumericVerifierAcceptedControlledTraceTable]
  rw [henvironment]
  exact ⟨hcontrol.stateWidth_le, hcontrol.stateTokenCount_le⟩

theorem
    compactNumericVerifierAcceptedControlledTraceEnvironment_stateListCountBounds
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight rowIndex : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight)
    (hrowIndex : rowIndex < compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)) :
    let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
    let tableWidth := compactNumericVerifierAcceptedControlledTraceWidth
      tree certificate hvalid streamWeight hproof hcertificate
    let table := compactNumericVerifierAcceptedControlledTraceTable
      tree certificate hvalid streamWeight hproof hcertificate
    let environment :=
      compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table rowIndex
    CompactNumericVerifierStepStateListCountBounds environment
      (compactNumericVerifierAcceptedStateTokenCountBound rowWeight) := by
  dsimp only
  have henvironment :=
    compactNumericVerifierAcceptedControlledStepWitnessTable_environment_eq
      tree certificate hvalid (streamWeight := streamWeight)
        (rowIndex := rowIndex) hproof hcertificate hrowIndex
  let row :=
    (compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
      hvalid streamWeight hproof hcertificate).getI rowIndex
  have hspec :=
    compactNumericVerifierAcceptedControlledCheckedStepRows_spec
      tree certificate hvalid (streamWeight := streamWeight)
        (offset := rowIndex) hproof hcertificate hrowIndex
  have hcounts :=
    compactNumericVerifierStepGraphDef_stateListCountControlBounds
      row.environment row.formula
  have hbounded := hcounts.to_bound hspec.2.2.2.1.stateTokenCount_le
  simp only [compactNumericVerifierAcceptedControlledTraceWidth,
    compactNumericVerifierAcceptedControlledTraceTable]
  rw [henvironment]
  exact hbounded

/-- On every actual parse row, the table environment retains numeric bounds for
the proof/certificate widths and token counts used by the parser loops. -/
theorem
    compactNumericVerifierAcceptedControlledTraceEnvironment_parserControlBounds
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight rowIndex : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight)
    (hrowIndex : rowIndex < compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)) :
    let start := compactNumericVerifierInitialState
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)
    let tableWidth := compactNumericVerifierAcceptedControlledTraceWidth
      tree certificate hvalid streamWeight hproof hcertificate
    let table := compactNumericVerifierAcceptedControlledTraceTable
      tree certificate hvalid streamWeight hproof hcertificate
    let environment :=
      compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table rowIndex
    (compactNumericVerifierStateAt start rowIndex).2 = none ->
      forall restTasks,
        (compactNumericVerifierStateAt start rowIndex).1.2.1 =
            compactNumericParseTask :: restTasks ->
          CompactNumericVerifierParseSuccessParserControlBounds
            environment
              (compactNumericVerifierAcceptedCoordinateSizeBound
                streamWeight) := by
  dsimp only
  intro hstatus restTasks htask
  have henvironment :=
    compactNumericVerifierAcceptedControlledStepWitnessTable_environment_eq
      tree certificate hvalid (streamWeight := streamWeight)
        (rowIndex := rowIndex) hproof hcertificate hrowIndex
  have hspec :=
    compactNumericVerifierAcceptedControlledCheckedStepRows_spec
      tree certificate hvalid (streamWeight := streamWeight)
        (offset := rowIndex) hproof hcertificate hrowIndex
  have hrowStatus :
      ((compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
        hvalid streamWeight hproof hcertificate).getI rowIndex).currentState.2 =
          none := by
    rw [hspec.1]
    exact hstatus
  have hrowTask :
      ((compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
        hvalid streamWeight hproof hcertificate).getI rowIndex).currentState.1.2.1 =
          compactNumericParseTask :: restTasks := by
    rw [hspec.1]
    exact htask
  have hcontrol := hspec.2.2.2.2.2.1 hrowStatus restTasks hrowTask
  simp only [compactNumericVerifierAcceptedControlledTraceWidth,
    compactNumericVerifierAcceptedControlledTraceTable]
  rw [henvironment]
  exact hcontrol

/-- On every actual non-parse row, the table environment retains the task,
active-rule-list, and formula-transform state-count bounds used by combine. -/
theorem
    compactNumericVerifierAcceptedControlledTraceEnvironment_combineControlBounds
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight rowIndex : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight)
    (hrowIndex : rowIndex < compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)) :
    let start := compactNumericVerifierInitialState
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)
    let tableWidth := compactNumericVerifierAcceptedControlledTraceWidth
      tree certificate hvalid streamWeight hproof hcertificate
    let table := compactNumericVerifierAcceptedControlledTraceTable
      tree certificate hvalid streamWeight hproof hcertificate
    let environment :=
      compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table rowIndex
    (compactNumericVerifierStateAt start rowIndex).2 = none ->
      forall task restTasks,
        (compactNumericVerifierStateAt start rowIndex).1.2.1 =
            task :: restTasks ->
        task.1 ≠ 10 ->
          CompactNumericVerifierCombineEnvironmentCountControls
            environment := by
  dsimp only
  intro hstatus task restTasks htask htaskNe
  have henvironment :=
    compactNumericVerifierAcceptedControlledStepWitnessTable_environment_eq
      tree certificate hvalid (streamWeight := streamWeight)
        (rowIndex := rowIndex) hproof hcertificate hrowIndex
  have hspec :=
    compactNumericVerifierAcceptedControlledCheckedStepRows_spec
      tree certificate hvalid (streamWeight := streamWeight)
        (offset := rowIndex) hproof hcertificate hrowIndex
  have hrowStatus :
      ((compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
        hvalid streamWeight hproof hcertificate).getI rowIndex).currentState.2 =
          none := by
    rw [hspec.1]
    exact hstatus
  have hrowTask :
      ((compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
        hvalid streamWeight hproof hcertificate).getI rowIndex).currentState.1.2.1 =
          task :: restTasks := by
    rw [hspec.1]
    exact htask
  have hcontrol := hspec.2.2.2.2.2.2
    hrowStatus task restTasks hrowTask htaskNe
  simp only [compactNumericVerifierAcceptedControlledTraceWidth,
    compactNumericVerifierAcceptedControlledTraceTable]
  rw [henvironment]
  exact hcontrol

theorem
    compactNumericVerifierAcceptedControlledTraceFinalEnvironment_controlBounds
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    let fuel := compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)
    let lastRow := fuel - 1
    let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
    let tableWidth := compactNumericVerifierAcceptedControlledTraceWidth
      tree certificate hvalid streamWeight hproof hcertificate
    let table := compactNumericVerifierAcceptedControlledTraceTable
      tree certificate hvalid streamWeight hproof hcertificate
    let environment :=
      compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table lastRow
    environment 1 <= 4 * rowWeight /\
      environment 2 <= 2 * rowWeight := by
  dsimp only
  let fuel := compactNumericVerifierFuelBound
    (compactListedProofTokens tree)
    (compactStructuralCertificateTokens certificate)
  let lastRow := fuel - 1
  have hfuel : 0 < fuel := by
    simp [fuel, compactNumericVerifierFuelBound]
  have hlast : lastRow < fuel := by omega
  have henvironment :=
    compactNumericVerifierAcceptedControlledStepWitnessTable_environment_eq
      tree certificate hvalid (streamWeight := streamWeight)
        (rowIndex := lastRow) hproof hcertificate (by
          simpa only [fuel, lastRow] using hlast)
  have hcontrol :=
    compactNumericVerifierAcceptedControlledFinalRow_controlBounds
      tree certificate hvalid hproof hcertificate
  simp only [compactNumericVerifierAcceptedControlledTraceWidth,
    compactNumericVerifierAcceptedControlledTraceTable]
  rw [henvironment]
  exact ⟨hcontrol.stateWidth_le, hcontrol.stateTokenCount_le⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem compactNumericVerifierAcceptedControlledTraceTable_complete
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight)
    (hproofSource : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount proofStart proofFinish
        (compactListedProofTokens tree))
    (hcertificateSource : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish
        (compactStructuralCertificateTokens certificate)) :
    CompactNumericVerifierAcceptedTraceTable
      (compactNumericVerifierAcceptedControlledTraceWidth tree certificate
        hvalid streamWeight hproof hcertificate)
      (compactNumericVerifierAcceptedControlledTraceTable tree certificate
        hvalid streamWeight hproof hcertificate)
      (2 ^ compactNumericVerifierAcceptedControlledTraceWidth tree certificate
        hvalid streamWeight hproof hcertificate)
      (compactNumericVerifierFuelBound (compactListedProofTokens tree)
        (compactStructuralCertificateTokens certificate))
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish := by
  let proofTokens := compactListedProofTokens tree
  let certificateTokens := compactStructuralCertificateTokens certificate
  let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
  let start := compactNumericVerifierInitialState proofTokens certificateTokens
  let checkedRows :=
    compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
      hvalid streamWeight hproof hcertificate
  let rows := compactNumericVerifierAcceptedControlledStepFormulaRows tree
    certificate hvalid streamWeight hproof hcertificate
  let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
  let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
  change CompactNumericVerifierAcceptedTraceTable
    tableWidth table (2 ^ tableWidth) fuel
    proofTable proofWidth proofTokenCount proofStart proofFinish
    certificateTable certificateWidth certificateTokenCount
    certificateStart certificateFinish
  have hfuel : 0 < fuel := by
    simp [fuel, compactNumericVerifierFuelBound]
  have hrun := compactNumericVerifierRun_canonical_of_valid tree certificate
    hvalid
  have haccepted :
      (compactNumericVerifierStateAt start fuel).2 = some true := by
    have hstatus := congrArg Prod.snd hrun
    simpa only [start, fuel, proofTokens, certificateTokens,
      compactNumericVerifierRun, compactNumericVerifierStateAt] using hstatus
  refine ⟨rfl, hfuel, ?_, ?_, ?_, ?_⟩
  · simpa only [proofTokens, certificateTokens, fuel, rows, tableWidth, table]
      using compactNumericVerifierAcceptedControlledStepWitnessTable_boundedGraph
        tree certificate hvalid streamWeight hproof hcertificate
  · simpa only [proofTokens, certificateTokens, fuel, rows, tableWidth, table]
      using compactNumericVerifierAcceptedControlledStepWitnessTable_rowsAdjacent
        tree certificate hvalid streamWeight hproof hcertificate
  · let initialRow := checkedRows.getI 0
    have hinitialSpec :=
      compactNumericVerifierAcceptedControlledCheckedStepRows_spec
        tree certificate hvalid (streamWeight := streamWeight) (offset := 0)
          hproof hcertificate (by simpa only [fuel, proofTokens,
            certificateTokens] using hfuel)
    have hinitialCurrent : initialRow.currentState = start := by
      simpa only [initialRow, checkedRows, start,
        compactNumericVerifierStateAt, Function.iterate_zero_apply] using
          hinitialSpec.1
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
        compactNumericVerifierAcceptedControlledStepWitnessTable_environment_eq
          tree certificate hvalid (streamWeight := streamWeight) (rowIndex := 0)
            hproof hcertificate (by simpa only [fuel, proofTokens,
              certificateTokens] using hfuel)
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
    have hfinalSpec :=
      compactNumericVerifierAcceptedControlledCheckedStepRows_spec
        tree certificate hvalid (streamWeight := streamWeight)
          (offset := lastRow) hproof hcertificate (by
            simpa only [fuel, proofTokens, certificateTokens, lastRow] using
              hlastRow)
    have hfinalNext : finalRow.nextState =
        compactNumericVerifierStateAt start fuel := by
      exact hfinalSpec.2.1.trans (by rw [hlastNext])
    have hfinalLayout : CompactNumericVerifierStateDirectLayout
        (finalRow.environment 0) (finalRow.environment 1)
        (finalRow.environment 2) (finalRow.environment 24)
        (finalRow.environment 25)
        (compactNumericVerifierStateAt start fuel) := by
      simpa only [hfinalNext] using finalRow.nextLayout
    have hfinalEnvironment : CompactNumericVerifierAcceptedEnvironment
        finalRow.environment := by
      exact CompactNumericVerifierAcceptedEnvironment.ofAcceptedState
        finalRow.formula hfinalLayout haccepted
    have hfinalTableEnvironment : CompactNumericVerifierAcceptedEnvironment
        (compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table lastRow) := by
      have henvironment :=
        compactNumericVerifierAcceptedControlledStepWitnessTable_environment_eq
          tree certificate hvalid (streamWeight := streamWeight)
            (rowIndex := lastRow) hproof hcertificate (by
              simpa only [fuel, proofTokens, certificateTokens, lastRow] using
                hlastRow)
      change compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table lastRow = finalRow.environment at henvironment
      rw [henvironment]
      exact hfinalEnvironment
    apply CompactNumericVerifierAcceptedEnvironment.to_witnessTableRow
      (fun coordinate =>
        compactNumericVerifierStepWitnessTableColumnValue_entry
          tableWidth table lastRow coordinate.val)
      hfinalTableEnvironment

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem compactNumericVerifierAcceptedControlledTraceTable_size_le
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    let fuel := compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)
    let coordinateBound :=
      compactNumericVerifierAcceptedCoordinateSizeBound streamWeight
    let width := compactNumericVerifierAcceptedControlledTraceWidth tree
      certificate hvalid streamWeight hproof hcertificate
    let table := compactNumericVerifierAcceptedControlledTraceTable tree
      certificate hvalid streamWeight hproof hcertificate
    width <=
        fuel * (compactNumericVerifierStepWitnessColumnCount * coordinateBound) /\
      Nat.size table <=
        fuel * compactNumericVerifierStepWitnessColumnCount *
          (fuel *
            (compactNumericVerifierStepWitnessColumnCount * coordinateBound)) /\
      Nat.size (2 ^ width) <=
        fuel * (compactNumericVerifierStepWitnessColumnCount * coordinateBound) +
          1 := by
  simpa only [compactNumericVerifierAcceptedControlledTraceWidth,
    compactNumericVerifierAcceptedControlledTraceTable] using
      compactNumericVerifierAcceptedControlledTraceCoordinates_size_le
        tree certificate hvalid streamWeight hproof hcertificate

#print axioms compactNumericVerifierAcceptedControlledFinalRow_controlBounds
#print axioms
  compactNumericVerifierAcceptedControlledTraceEnvironment_controlBounds
#print axioms
  compactNumericVerifierAcceptedControlledTraceEnvironment_stateListCountBounds
#print axioms
  compactNumericVerifierAcceptedControlledTraceEnvironment_parserControlBounds
#print axioms
  compactNumericVerifierAcceptedControlledTraceEnvironment_combineControlBounds
#print axioms
  compactNumericVerifierAcceptedControlledTraceFinalEnvironment_controlBounds
#print axioms compactNumericVerifierAcceptedControlledTraceTable_complete
#print axioms compactNumericVerifierAcceptedControlledTraceTable_size_le

end FoundationCompactNumericListedDirectVerifierAcceptedControlledTraceTable
