import integration.FoundationCompactNumericListedDirectVerifierAcceptedBoundedTraceTable
import integration.FoundationCompactNumericListedDirectVerifierAcceptedTerminalRowsControlBounds
import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceRowsStateTableControlBounds

/-!
# Accepted trace selection retaining terminal numeric controls

The older bounded selector records only binary-size bounds.  This selector keeps
the same canonical state equalities and coordinate bounds, while retaining
numeric bounds for state width and token count at the final trace row.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedControlledTraceSelection

open FoundationCompactAdditiveTokenCodec
open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierCheckedStepRows
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableAdjacencyFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge
open FoundationCompactNumericListedDirectCanonicalTraceBounds
open FoundationCompactNumericListedDirectVerifierAcceptedBoundedTraceTable
open FoundationCompactNumericListedDirectVerifierAcceptedTerminalRowsControlBounds
open FoundationCompactNumericListedDirectVerifierAcceptedStateTableControlBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
open FoundationCompactNumericListedDirectVerifierAcceptedTreeRowStateTableControlBounds
open FoundationCompactNumericListedDirectVerifierAcceptedTerminalRowsStateTableControlBounds
open FoundationCompactNumericListedDirectVerifierAcceptedTraceRowsStateTableControlBounds
open FoundationCompactNumericListedDirectVerifierCombineActiveCountBounds

/-- The canonical fuel leaves at least one halted row after the finish step. -/
theorem compactNumericTreeTaskSteps_add_one_le_fuel_sub_one
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    compactNumericTreeTaskSteps tree certificate + 1 <=
      compactNumericVerifierFuelBound
          (compactListedProofTokens tree)
          (compactStructuralCertificateTokens certificate) - 1 := by
  have hsteps := compactNumericTreeTaskSteps_le_two_mul_proofTokenLength
    tree certificate
  simp only [compactNumericVerifierFuelBound]
  omega

/- Every selected row retains both the global coordinate bound and the common
numeric state-table controls.  The final row additionally keeps its tighter
terminal controls. -/
set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem compactNumericVerifierAcceptedControlledRowExists
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    let proofTokens := compactListedProofTokens tree
    let certificateTokens := compactStructuralCertificateTokens certificate
    let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
    let start := compactNumericVerifierInitialState proofTokens certificateTokens
    let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
    forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState =
            compactNumericVerifierStateAt start (offset + 1) /\
          (forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <=
              compactNumericVerifierAcceptedCoordinateSizeBound
                streamWeight) /\
          CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight /\
          (offset = fuel - 1 ->
            CompactNumericVerifierAcceptedRowControlBounds row rowWeight) /\
          (row.currentState.2 = none ->
            forall restTasks,
              row.currentState.1.2.1 = compactNumericParseTask :: restTasks ->
                CompactNumericVerifierParseSuccessParserControlBounds
                  row.environment
                    (compactNumericVerifierAcceptedCoordinateSizeBound
                      streamWeight)) /\
          (row.currentState.2 = none ->
            forall task restTasks,
              row.currentState.1.2.1 = task :: restTasks ->
              task.1 ≠ 10 ->
                CompactNumericVerifierCombineEnvironmentCountControls
                  row.environment) := by
  let proofTokens := compactListedProofTokens tree
  let certificateTokens := compactStructuralCertificateTokens certificate
  let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
  let start := compactNumericVerifierInitialState proofTokens certificateTokens
  let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
  dsimp only
  intro offset hoffset
  by_cases hlast : offset = fuel - 1
  · have hterminal : compactNumericTreeTaskSteps tree certificate + 1 <=
        offset := by
      rw [hlast]
      simpa only [fuel, proofTokens, certificateTokens] using
        compactNumericTreeTaskSteps_add_one_le_fuel_sub_one tree certificate
    have hstrong :=
      exists_canonicalAcceptedHaltedCheckedStepRow_with_controlBounds
        tree certificate hvalid hproof hcertificate hterminal (by
          simpa only [fuel, proofTokens, certificateTokens] using hoffset)
    rcases hstrong with
      ⟨row, hcurrent, hnext, hcontrols, hcoordinates, hstatus⟩
    refine ⟨row, hcurrent, hnext, ?_, ?_, ?_, ?_, ?_⟩
    · intro coordinate
      simpa only [compactNumericVerifierAcceptedCoordinateSizeBound,
        rowWeight] using hcoordinates coordinate
    · exact acceptedStateTableControlBounds_of_terminalControl
        row rowWeight hcontrols
    · intro _
      exact hcontrols
    · intro hnone
      exact (hstatus hnone).elim
    · intro hnone
      exact (hstatus hnone).elim
  · rcases
        exists_canonicalAcceptedCheckedStepRow_at_offset_with_globalControlBound
          tree certificate hvalid hproof hcertificate (by
            simpa only [fuel, proofTokens, certificateTokens] using hoffset) with
      ⟨row, hcurrent, hnext, hbound⟩
    refine ⟨row, hcurrent, hnext, ?_, hbound.stateTable, ?_, ?_, ?_⟩
    · intro coordinate
      simpa only [compactNumericVerifierAcceptedCoordinateSizeBound,
        rowWeight] using hbound.coordinates coordinate
    · intro h
      exact (hlast h).elim
    · intro hnone restTasks htask
      simpa only [compactNumericVerifierAcceptedCoordinateSizeBound,
        rowWeight] using hbound.parserControls hnone restTasks htask
    · intro hnone task restTasks htask htaskNe
      exact hbound.combineControls hnone task restTasks htask htaskNe

noncomputable def compactNumericVerifierAcceptedControlledCheckedStepRow
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (streamWeight : Nat)
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight)
    (offset : Nat) : CompactNumericVerifierCheckedStepRow :=
  let proofTokens := compactListedProofTokens tree
  let certificateTokens := compactStructuralCertificateTokens certificate
  let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
  let start := compactNumericVerifierInitialState proofTokens certificateTokens
  if hoffset : offset < fuel then
    Classical.choose
      (compactNumericVerifierAcceptedControlledRowExists tree certificate
        hvalid hproof hcertificate offset hoffset)
  else
    compactNumericVerifierCanonicalCheckedStepRow
      (compactNumericVerifierStateAt start offset)

theorem compactNumericVerifierAcceptedControlledCheckedStepRow_spec
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight)
    (offset : Nat)
    (hoffset : offset < compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)) :
    let proofTokens := compactListedProofTokens tree
    let certificateTokens := compactStructuralCertificateTokens certificate
    let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
    let start := compactNumericVerifierInitialState proofTokens certificateTokens
    let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
    let row := compactNumericVerifierAcceptedControlledCheckedStepRow
      tree certificate hvalid streamWeight hproof hcertificate offset
    row.currentState = compactNumericVerifierStateAt start offset /\
      row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
      (forall coordinate : Fin 429,
        Nat.size (row.environment coordinate) <=
          compactNumericVerifierAcceptedCoordinateSizeBound streamWeight) /\
      CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight /\
      (offset = fuel - 1 ->
        CompactNumericVerifierAcceptedRowControlBounds row rowWeight) /\
      (row.currentState.2 = none ->
        forall restTasks,
          row.currentState.1.2.1 = compactNumericParseTask :: restTasks ->
            CompactNumericVerifierParseSuccessParserControlBounds
              row.environment
                (compactNumericVerifierAcceptedCoordinateSizeBound
                  streamWeight)) /\
      (row.currentState.2 = none ->
        forall task restTasks,
          row.currentState.1.2.1 = task :: restTasks ->
          task.1 ≠ 10 ->
            CompactNumericVerifierCombineEnvironmentCountControls
              row.environment) := by
  dsimp only
  rw [compactNumericVerifierAcceptedControlledCheckedStepRow,
    dif_pos hoffset]
  exact Classical.choose_spec
    (compactNumericVerifierAcceptedControlledRowExists tree certificate
      hvalid hproof hcertificate offset hoffset)

noncomputable def compactNumericVerifierAcceptedControlledCheckedStepRows
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (streamWeight : Nat)
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    List CompactNumericVerifierCheckedStepRow :=
  let fuel := compactNumericVerifierFuelBound
    (compactListedProofTokens tree)
    (compactStructuralCertificateTokens certificate)
  (List.range fuel).map fun offset =>
    compactNumericVerifierAcceptedControlledCheckedStepRow tree certificate
      hvalid streamWeight hproof hcertificate offset

@[simp] theorem compactNumericVerifierAcceptedControlledCheckedStepRows_length
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (streamWeight : Nat)
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    (compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
      hvalid streamWeight hproof hcertificate).length =
      compactNumericVerifierFuelBound
        (compactListedProofTokens tree)
        (compactStructuralCertificateTokens certificate) := by
  simp [compactNumericVerifierAcceptedControlledCheckedStepRows]

theorem compactNumericVerifierAcceptedControlledCheckedStepRows_getI
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight offset : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight)
    (hoffset : offset < compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)) :
    (compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
      hvalid streamWeight hproof hcertificate).getI offset =
      compactNumericVerifierAcceptedControlledCheckedStepRow tree certificate
        hvalid streamWeight hproof hcertificate offset := by
  have hindex : offset <
      (compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
        hvalid streamWeight hproof hcertificate).length := by
    simpa using hoffset
  rw [List.getI_eq_getElem _ hindex]
  simp [compactNumericVerifierAcceptedControlledCheckedStepRows]

theorem compactNumericVerifierAcceptedControlledCheckedStepRows_spec
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight offset : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight)
    (hoffset : offset < compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)) :
    let proofTokens := compactListedProofTokens tree
    let certificateTokens := compactStructuralCertificateTokens certificate
    let fuel := compactNumericVerifierFuelBound proofTokens certificateTokens
    let start := compactNumericVerifierInitialState proofTokens certificateTokens
    let rowWeight := compactNumericVerifierPublicRowWeightBound streamWeight
    let row :=
      (compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
        hvalid streamWeight hproof hcertificate).getI offset
    row.currentState = compactNumericVerifierStateAt start offset /\
      row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
      (forall coordinate : Fin 429,
        Nat.size (row.environment coordinate) <=
          compactNumericVerifierAcceptedCoordinateSizeBound streamWeight) /\
      CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight /\
      (offset = fuel - 1 ->
        CompactNumericVerifierAcceptedRowControlBounds row rowWeight) /\
      (row.currentState.2 = none ->
        forall restTasks,
          row.currentState.1.2.1 = compactNumericParseTask :: restTasks ->
            CompactNumericVerifierParseSuccessParserControlBounds
              row.environment
                (compactNumericVerifierAcceptedCoordinateSizeBound
                  streamWeight)) /\
      (row.currentState.2 = none ->
        forall task restTasks,
          row.currentState.1.2.1 = task :: restTasks ->
          task.1 ≠ 10 ->
            CompactNumericVerifierCombineEnvironmentCountControls
              row.environment) := by
  dsimp only
  rw [compactNumericVerifierAcceptedControlledCheckedStepRows_getI
    tree certificate hvalid hproof hcertificate hoffset]
  exact compactNumericVerifierAcceptedControlledCheckedStepRow_spec
    tree certificate hvalid hproof hcertificate offset hoffset

theorem compactNumericVerifierAcceptedControlledCheckedStepRows_adjacent
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight offset : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight)
    (hoffset : offset + 1 < compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)) :
    CompactNumericVerifierCheckedStepRowsAdjacent
      ((compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
        hvalid streamWeight hproof hcertificate).getI offset)
      ((compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
        hvalid streamWeight hproof hcertificate).getI (offset + 1)) := by
  apply CompactNumericVerifierCheckedStepRowsAdjacent.of_state_eq
  have hsource :=
    compactNumericVerifierAcceptedControlledCheckedStepRows_spec
      tree certificate hvalid (streamWeight := streamWeight)
        (offset := offset) hproof hcertificate (by omega)
  have htarget :=
    compactNumericVerifierAcceptedControlledCheckedStepRows_spec
      tree certificate hvalid (streamWeight := streamWeight)
        (offset := offset + 1) hproof hcertificate hoffset
  exact hsource.2.1.trans htarget.1.symm

noncomputable def compactNumericVerifierAcceptedControlledStepFormulaRows
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (streamWeight : Nat)
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    List CompactNumericVerifierStepFormulaRow :=
  (compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
    hvalid streamWeight hproof hcertificate).map
      CompactNumericVerifierCheckedStepRow.toFormulaRow

@[simp] theorem compactNumericVerifierAcceptedControlledStepFormulaRows_length
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (streamWeight : Nat)
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    (compactNumericVerifierAcceptedControlledStepFormulaRows tree certificate
      hvalid streamWeight hproof hcertificate).length =
      compactNumericVerifierFuelBound
        (compactListedProofTokens tree)
        (compactStructuralCertificateTokens certificate) := by
  simp [compactNumericVerifierAcceptedControlledStepFormulaRows]

theorem compactNumericVerifierAcceptedControlledStepFormulaRows_valid
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (streamWeight : Nat)
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    compactNumericVerifierStepFormulaRowsValid
      (compactNumericVerifierAcceptedControlledStepFormulaRows tree certificate
        hvalid streamWeight hproof hcertificate) := by
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨checkedRow, _hcheckedRow, rfl⟩
  exact checkedRow.formula

theorem
    compactNumericVerifierAcceptedControlledStepFormulaRows_rowBitWeight_le
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (streamWeight : Nat)
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    forall row,
      row ∈ compactNumericVerifierAcceptedControlledStepFormulaRows
          tree certificate hvalid streamWeight hproof hcertificate ->
        compactNumericVerifierStepFormulaRowBitWeight row <=
          compactNumericVerifierStepWitnessColumnCount *
            compactNumericVerifierAcceptedCoordinateSizeBound streamWeight := by
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨checkedRow, hcheckedRow, rfl⟩
  rw [compactNumericVerifierAcceptedControlledCheckedStepRows] at hcheckedRow
  rcases List.mem_map.mp hcheckedRow with
    ⟨offset, hoffsetRange, rfl⟩
  have hoffset : offset < compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate) :=
    List.mem_range.mp hoffsetRange
  apply compactNumericVerifierStepFormulaRowBitWeight_le
  intro coordinate
  exact
    (compactNumericVerifierAcceptedControlledCheckedStepRow_spec
      tree certificate hvalid hproof hcertificate offset hoffset).2.2.1
      coordinate

theorem compactNumericVerifierAcceptedControlledStepFormulaDynamicWidth_le
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (streamWeight : Nat)
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    compactNumericVerifierStepFormulaDynamicWidth
        (compactNumericVerifierAcceptedControlledStepFormulaRows tree
          certificate hvalid streamWeight hproof hcertificate) <=
      compactNumericVerifierFuelBound
          (compactListedProofTokens tree)
          (compactStructuralCertificateTokens certificate) *
        (compactNumericVerifierStepWitnessColumnCount *
          compactNumericVerifierAcceptedCoordinateSizeBound streamWeight) := by
  have hbound :=
    compactNumericVerifierStepFormulaDynamicWidth_le_of_rowBitWeight
      (compactNumericVerifierAcceptedControlledStepFormulaRows_rowBitWeight_le
        tree certificate hvalid streamWeight hproof hcertificate)
  simpa only [compactNumericVerifierAcceptedControlledStepFormulaRows_length]
    using hbound

theorem compactNumericVerifierAcceptedControlledTraceCoordinates_size_le
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (streamWeight : Nat)
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    let fuel := compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)
    let coordinateBound :=
      compactNumericVerifierAcceptedCoordinateSizeBound streamWeight
    let rows := compactNumericVerifierAcceptedControlledStepFormulaRows tree
      certificate hvalid streamWeight hproof hcertificate
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    tableWidth <=
        fuel * (compactNumericVerifierStepWitnessColumnCount * coordinateBound) /\
      Nat.size table <=
        fuel * compactNumericVerifierStepWitnessColumnCount *
          (fuel *
            (compactNumericVerifierStepWitnessColumnCount * coordinateBound)) /\
      Nat.size (2 ^ tableWidth) <=
        fuel * (compactNumericVerifierStepWitnessColumnCount * coordinateBound) +
          1 := by
  dsimp only
  let fuel := compactNumericVerifierFuelBound
    (compactListedProofTokens tree)
    (compactStructuralCertificateTokens certificate)
  let coordinateBound :=
    compactNumericVerifierAcceptedCoordinateSizeBound streamWeight
  let rows := compactNumericVerifierAcceptedControlledStepFormulaRows tree
    certificate hvalid streamWeight hproof hcertificate
  let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
  have hwidth : tableWidth <=
      fuel * (compactNumericVerifierStepWitnessColumnCount * coordinateBound) := by
    simpa only [tableWidth, rows, fuel, coordinateBound] using
      compactNumericVerifierAcceptedControlledStepFormulaDynamicWidth_le
        tree certificate hvalid streamWeight hproof hcertificate
  have htable := compactNumericVerifierStepWitnessTableCode_size_le
    tableWidth rows
  have htableScale :
      rows.length * compactNumericVerifierStepWitnessColumnCount * tableWidth <=
        fuel * compactNumericVerifierStepWitnessColumnCount *
          (fuel *
            (compactNumericVerifierStepWitnessColumnCount * coordinateBound)) := by
    have hlength : rows.length = fuel := by
      simpa only [rows, fuel] using
        compactNumericVerifierAcceptedControlledStepFormulaRows_length
          tree certificate hvalid streamWeight hproof hcertificate
    rw [hlength]
    exact Nat.mul_le_mul_left
      (fuel * compactNumericVerifierStepWitnessColumnCount) hwidth
  have hvalue : Nat.size (2 ^ tableWidth) <=
      fuel * (compactNumericVerifierStepWitnessColumnCount * coordinateBound) +
        1 := by
    rw [Nat.size_pow]
    omega
  exact ⟨hwidth, htable.trans htableScale, hvalue⟩

theorem compactNumericVerifierAcceptedControlledStepFormulaRows_getI
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
    (compactNumericVerifierAcceptedControlledStepFormulaRows tree certificate
      hvalid streamWeight hproof hcertificate).getI rowIndex =
      ((compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
        hvalid streamWeight hproof hcertificate).getI rowIndex).toFormulaRow := by
  have hchecked : rowIndex <
      (compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
        hvalid streamWeight hproof hcertificate).length := by
    simpa using hrowIndex
  have hformula : rowIndex <
      (compactNumericVerifierAcceptedControlledStepFormulaRows tree certificate
        hvalid streamWeight hproof hcertificate).length := by
    simpa using hrowIndex
  rw [List.getI_eq_getElem _ hformula, List.getI_eq_getElem _ hchecked]
  simp [compactNumericVerifierAcceptedControlledStepFormulaRows]

theorem compactNumericVerifierAcceptedControlledStepWitnessTable_environment_eq
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
    let rows := compactNumericVerifierAcceptedControlledStepFormulaRows tree
      certificate hvalid streamWeight hproof hcertificate
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table rowIndex =
      ((compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
        hvalid streamWeight hproof hcertificate).getI rowIndex).environment := by
  dsimp only
  let rows := compactNumericVerifierAcceptedControlledStepFormulaRows tree
    certificate hvalid streamWeight hproof hcertificate
  let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
  have hfit : CompactNumericVerifierStepFormulaRowsFit tableWidth rows :=
    compactNumericVerifierStepFormulaRowsFit_dynamic rows
  have hcarries : CompactNumericVerifierStepWitnessTableCarriesRows
      tableWidth (compactNumericVerifierStepWitnessTableCode tableWidth rows)
        rows :=
    compactNumericVerifierStepWitnessTableCode_carriesRows hfit
  have hrowIndexRows : rowIndex < rows.length := by
    have hlength : rows.length = compactNumericVerifierFuelBound
        (compactListedProofTokens tree)
        (compactStructuralCertificateTokens certificate) := by
      simpa only [rows] using
        compactNumericVerifierAcceptedControlledStepFormulaRows_length
          tree certificate hvalid streamWeight hproof hcertificate
    rw [hlength]
    exact hrowIndex
  rw [compactNumericVerifierStepWitnessTableFormulaEnvironment_eq
    hcarries rowIndex hrowIndexRows]
  change (rows.getI rowIndex).environment = _
  rw [show rows.getI rowIndex =
      ((compactNumericVerifierAcceptedControlledCheckedStepRows tree certificate
        hvalid streamWeight hproof hcertificate).getI rowIndex).toFormulaRow by
    exact compactNumericVerifierAcceptedControlledStepFormulaRows_getI
      tree certificate hvalid hproof hcertificate hrowIndex]
  rfl

theorem compactNumericVerifierAcceptedControlledStepWitnessTable_boundedGraph
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (streamWeight : Nat)
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    let fuel := compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)
    let rows := compactNumericVerifierAcceptedControlledStepFormulaRows tree
      certificate hvalid streamWeight hproof hcertificate
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    CompactNumericVerifierStepWitnessTableBoundedGraph
      tableWidth table fuel (2 ^ tableWidth) := by
  dsimp only
  intro rowIndex hrowIndex
  apply
    (compactNumericVerifierStepWitnessTableBoundedRow_iff_formula
      (compactNumericVerifierStepFormulaDynamicWidth
        (compactNumericVerifierAcceptedControlledStepFormulaRows tree
          certificate hvalid streamWeight hproof hcertificate))
      (compactNumericVerifierStepWitnessTableCode
        (compactNumericVerifierStepFormulaDynamicWidth
          (compactNumericVerifierAcceptedControlledStepFormulaRows tree
            certificate hvalid streamWeight hproof hcertificate))
        (compactNumericVerifierAcceptedControlledStepFormulaRows tree
          certificate hvalid streamWeight hproof hcertificate)) rowIndex).mpr
  apply compactNumericVerifierStepWitnessTableCode_formula
    (compactNumericVerifierStepFormulaRowsFit_dynamic _)
    (compactNumericVerifierAcceptedControlledStepFormulaRows_valid
      tree certificate hvalid streamWeight hproof hcertificate)
  simpa using hrowIndex

theorem
    compactNumericVerifierAcceptedControlledStepWitnessTable_canonicalAdjacent
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    {streamWeight rowIndex : Nat}
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight)
    (hrowIndex : rowIndex + 1 < compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)) :
    let rows := compactNumericVerifierAcceptedControlledStepFormulaRows tree
      certificate hvalid streamWeight hproof hcertificate
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    CompactNumericVerifierStepWitnessTableCanonicalAdjacent
      tableWidth table rowIndex := by
  dsimp only
  have hadjacent :=
    compactNumericVerifierAcceptedControlledCheckedStepRows_adjacent
      tree certificate hvalid hproof hcertificate hrowIndex
  have hsource :=
    compactNumericVerifierAcceptedControlledStepWitnessTable_environment_eq
      tree certificate hvalid (streamWeight := streamWeight)
        (rowIndex := rowIndex) hproof hcertificate (by omega)
  have htarget :=
    compactNumericVerifierAcceptedControlledStepWitnessTable_environment_eq
      tree certificate hvalid (streamWeight := streamWeight)
        (rowIndex := rowIndex + 1) hproof hcertificate hrowIndex
  unfold CompactNumericVerifierStepWitnessTableCanonicalAdjacent
  rw [hsource, htarget]
  exact hadjacent

theorem compactNumericVerifierAcceptedControlledStepWitnessTable_rowsAdjacent
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (hvalid : listedCertificateValid tree certificate)
    (streamWeight : Nat)
    (hproof : compactAdditiveValueWeight (compactListedProofTokens tree) <=
      streamWeight)
    (hcertificate : compactAdditiveValueWeight
      (compactStructuralCertificateTokens certificate) <= streamWeight) :
    let fuel := compactNumericVerifierFuelBound
      (compactListedProofTokens tree)
      (compactStructuralCertificateTokens certificate)
    let rows := compactNumericVerifierAcceptedControlledStepFormulaRows tree
      certificate hvalid streamWeight hproof hcertificate
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    CompactNumericVerifierStepWitnessTableRowsAdjacent
      tableWidth table fuel (2 ^ tableWidth) := by
  dsimp only
  intro rowIndex _hrowIndex hnextRow
  apply
    (compactNumericVerifierStepWitnessTableAdjacentRow_iff_canonical
      (compactNumericVerifierStepFormulaDynamicWidth
        (compactNumericVerifierAcceptedControlledStepFormulaRows tree
          certificate hvalid streamWeight hproof hcertificate))
      (compactNumericVerifierStepWitnessTableCode
        (compactNumericVerifierStepFormulaDynamicWidth
          (compactNumericVerifierAcceptedControlledStepFormulaRows tree
            certificate hvalid streamWeight hproof hcertificate))
        (compactNumericVerifierAcceptedControlledStepFormulaRows tree
          certificate hvalid streamWeight hproof hcertificate)) rowIndex).mpr
  exact
    compactNumericVerifierAcceptedControlledStepWitnessTable_canonicalAdjacent
      tree certificate hvalid hproof hcertificate hnextRow

#print axioms compactNumericTreeTaskSteps_add_one_le_fuel_sub_one
#print axioms compactNumericVerifierAcceptedControlledRowExists
#print axioms compactNumericVerifierAcceptedControlledCheckedStepRow_spec
#print axioms compactNumericVerifierAcceptedControlledCheckedStepRows_spec
#print axioms compactNumericVerifierAcceptedControlledCheckedStepRows_adjacent
#print axioms
  compactNumericVerifierAcceptedControlledStepFormulaRows_rowBitWeight_le
#print axioms
  compactNumericVerifierAcceptedControlledStepFormulaDynamicWidth_le
#print axioms compactNumericVerifierAcceptedControlledTraceCoordinates_size_le
#print axioms
  compactNumericVerifierAcceptedControlledStepWitnessTable_environment_eq
#print axioms
  compactNumericVerifierAcceptedControlledStepWitnessTable_boundedGraph
#print axioms
  compactNumericVerifierAcceptedControlledStepWitnessTable_canonicalAdjacent
#print axioms
  compactNumericVerifierAcceptedControlledStepWitnessTable_rowsAdjacent

end FoundationCompactNumericListedDirectVerifierAcceptedControlledTraceSelection
