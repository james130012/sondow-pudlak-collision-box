import integration.FoundationCompactNumericListedDirectCrossTableFormulaSetSingleton
import integration.FoundationCompactNumericListedDirectChildResultBoundedRowExposedFormula
import integration.FoundationCompactNumericListedDirectChildResultRowEquality
import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceExactness

/-!
# The accepted trace row exposes the checked conclusion formula set

The last verifier row stores the accepted next state in columns `0,1,2` and
`34,35`.  This graph reads its unique child result, requires the result Boolean
to be true, and compares the stored conclusion context with the raw token
stream decoded from the public formula code.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedConclusionRow

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierStateRealization
open FoundationCompactNumericListedDirectVerifierChildResultFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepEnvironmentSurjectivity
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge
open FoundationCompactNumericListedDirectChildResultRowEquality
open FoundationCompactNumericListedDirectChildResultBoundedRowExposedFormula
open FoundationCompactNumericListedDirectCrossTableFormulaSetSingleton

def CompactNumericVerifierAcceptedConclusionRow
    (traceWidth traceTable traceValueBound lastRow
      formulaTable formulaWidth formulaTokenCount : Nat) : Prop :=
  1 <= traceValueBound /\
    exists stateTable, stateTable <= traceValueBound /\
    exists stateWidth, stateWidth <= traceValueBound /\
    exists stateTokenCount, stateTokenCount <= traceValueBound /\
    exists valueBoundary, valueBoundary <= traceValueBound /\
    exists valueValueBound, valueValueBound <= traceValueBound /\
    exists valueStart, valueStart <= valueValueBound /\
    exists valueFinish, valueFinish <= valueValueBound /\
    exists gammaFinish, gammaFinish <= valueValueBound /\
    exists gammaCount, gammaCount <= valueValueBound /\
    exists gammaBoundary, gammaBoundary <= valueValueBound /\
    exists gammaBoundarySize, gammaBoundarySize <= valueValueBound /\
      CompactFixedWidthEntry traceTable traceWidth
        (lastRow * 429 + 0) stateTable /\
      CompactFixedWidthEntry traceTable traceWidth
        (lastRow * 429 + 1) stateWidth /\
      CompactFixedWidthEntry traceTable traceWidth
        (lastRow * 429 + 2) stateTokenCount /\
      CompactFixedWidthEntry traceTable traceWidth
        (lastRow * 429 + 34) 1 /\
      CompactFixedWidthEntry traceTable traceWidth
        (lastRow * 429 + 35) valueBoundary /\
      CompactFixedWidthEntry traceTable traceWidth
        (lastRow * 429 + 44) valueValueBound /\
      CompactFixedWidthEntry valueBoundary stateTokenCount 0 valueStart /\
      CompactFixedWidthEntry valueBoundary stateTokenCount 1 valueFinish /\
      CompactNumericChildResultCoreGraph
        stateTable stateWidth stateTokenCount
        (compactNumericChildResultRowCoordinatesOf
          valueStart valueFinish gammaFinish gammaCount gammaBoundary 1)
        { gammaBoundarySize := gammaBoundarySize } /\
      CompactCrossTableFormulaSetEqSingleton
        stateTable stateWidth stateTokenCount gammaBoundary gammaCount
        formulaTable formulaWidth formulaTokenCount

def compactNumericVerifierAcceptedConclusionRowDef :
    HierarchySymbol.sigmaZero.Semisentence 7 := .mkSigma
  “traceWidth traceTable traceValueBound lastRow
      formulaTable formulaWidth formulaTokenCount.
    1 ≤ traceValueBound ∧
    ∃ stateTable <⁺ traceValueBound,
    ∃ stateWidth <⁺ traceValueBound,
    ∃ stateTokenCount <⁺ traceValueBound,
    ∃ valueBoundary <⁺ traceValueBound,
    ∃ valueValueBound <⁺ traceValueBound,
    ∃ valueStart <⁺ valueValueBound,
    ∃ valueFinish <⁺ valueValueBound,
    ∃ gammaFinish <⁺ valueValueBound,
    ∃ gammaCount <⁺ valueValueBound,
    ∃ gammaBoundary <⁺ valueValueBound,
    ∃ gammaBoundarySize <⁺ valueValueBound,
      !(compactFixedWidthEntryDef)
        traceTable traceWidth (lastRow * 429 + 0) stateTable ∧
      !(compactFixedWidthEntryDef)
        traceTable traceWidth (lastRow * 429 + 1) stateWidth ∧
      !(compactFixedWidthEntryDef)
        traceTable traceWidth (lastRow * 429 + 2) stateTokenCount ∧
      !(compactFixedWidthEntryDef)
        traceTable traceWidth (lastRow * 429 + 34) 1 ∧
      !(compactFixedWidthEntryDef)
        traceTable traceWidth (lastRow * 429 + 35) valueBoundary ∧
      !(compactFixedWidthEntryDef)
        traceTable traceWidth (lastRow * 429 + 44) valueValueBound ∧
      !(compactFixedWidthEntryDef)
        valueBoundary stateTokenCount 0 valueStart ∧
      !(compactFixedWidthEntryDef)
        valueBoundary stateTokenCount 1 valueFinish ∧
      !(compactNumericChildResultCoreGraphDef)
        stateTable stateWidth stateTokenCount
        valueStart valueFinish gammaFinish gammaCount gammaBoundary 1
        gammaBoundarySize ∧
      !(compactCrossTableFormulaSetEqSingletonDef)
        stateTable stateWidth stateTokenCount gammaBoundary gammaCount
        formulaTable formulaWidth formulaTokenCount”

@[simp] theorem compactNumericVerifierAcceptedConclusionRowDef_spec
    (traceWidth traceTable traceValueBound lastRow
      formulaTable formulaWidth formulaTokenCount : Nat) :
    compactNumericVerifierAcceptedConclusionRowDef.val.Evalb
        ![traceWidth, traceTable, traceValueBound, lastRow,
          formulaTable, formulaWidth, formulaTokenCount] ↔
      CompactNumericVerifierAcceptedConclusionRow
        traceWidth traceTable traceValueBound lastRow
        formulaTable formulaWidth formulaTokenCount := by
  have hcore
      (gammaBoundarySize gammaBoundary gammaCount gammaFinish
        valueFinish valueStart valueValueBound valueBoundary
        stateTokenCount stateWidth stateTable : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![gammaBoundarySize, gammaBoundary, gammaCount, gammaFinish,
                valueFinish, valueStart, valueValueBound, valueBoundary,
                stateTokenCount, stateWidth, stateTable,
                traceWidth, traceTable, traceValueBound, lastRow,
                formulaTable, formulaWidth, formulaTokenCount]
              Empty.elim ∘
            ![(#10 : Semiterm ℒₒᵣ Empty 18), #9, #8, #5, #4,
              #3, #2, #1, (↑(1 : Nat)), #0])
          Empty.elim) compactNumericChildResultCoreGraphDef.val ↔
        CompactNumericChildResultCoreGraph
          stateTable stateWidth stateTokenCount
          (compactNumericChildResultRowCoordinatesOf
            valueStart valueFinish gammaFinish gammaCount gammaBoundary 1)
          { gammaBoundarySize := gammaBoundarySize } := by
    have henv :
        (Semiterm.val
            ![gammaBoundarySize, gammaBoundary, gammaCount, gammaFinish,
              valueFinish, valueStart, valueValueBound, valueBoundary,
              stateTokenCount, stateWidth, stateTable,
              traceWidth, traceTable, traceValueBound, lastRow,
              formulaTable, formulaWidth, formulaTokenCount]
            Empty.elim ∘
          ![(#10 : Semiterm ℒₒᵣ Empty 18), #9, #8, #5, #4,
            #3, #2, #1, (↑(1 : Nat)), #0]) =
          compactNumericChildResultCoreFormulaEnvironment
            stateTable stateWidth stateTokenCount
            valueStart valueFinish gammaFinish gammaCount gammaBoundary 1
            gammaBoundarySize := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactNumericChildResultCoreGraphDef_spec
      stateTable stateWidth stateTokenCount
      valueStart valueFinish gammaFinish gammaCount gammaBoundary 1
      gammaBoundarySize
  have hsingleton
      (gammaBoundarySize gammaBoundary gammaCount gammaFinish
        valueFinish valueStart valueValueBound valueBoundary
        stateTokenCount stateWidth stateTable : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![gammaBoundarySize, gammaBoundary, gammaCount, gammaFinish,
                valueFinish, valueStart, valueValueBound, valueBoundary,
                stateTokenCount, stateWidth, stateTable,
                traceWidth, traceTable, traceValueBound, lastRow,
                formulaTable, formulaWidth, formulaTokenCount]
              Empty.elim ∘
            ![(#10 : Semiterm ℒₒᵣ Empty 18), #9, #8, #1, #2,
              #15, #16, #17])
          Empty.elim) compactCrossTableFormulaSetEqSingletonDef.val ↔
        CompactCrossTableFormulaSetEqSingleton
          stateTable stateWidth stateTokenCount gammaBoundary gammaCount
          formulaTable formulaWidth formulaTokenCount := by
    have henv :
        (Semiterm.val
            ![gammaBoundarySize, gammaBoundary, gammaCount, gammaFinish,
              valueFinish, valueStart, valueValueBound, valueBoundary,
              stateTokenCount, stateWidth, stateTable,
              traceWidth, traceTable, traceValueBound, lastRow,
              formulaTable, formulaWidth, formulaTokenCount]
            Empty.elim ∘
          ![(#10 : Semiterm ℒₒᵣ Empty 18), #9, #8, #1, #2,
            #15, #16, #17]) =
          ![stateTable, stateWidth, stateTokenCount,
            gammaBoundary, gammaCount,
            formulaTable, formulaWidth, formulaTokenCount] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactCrossTableFormulaSetEqSingletonDef_spec
      stateTable stateWidth stateTokenCount gammaBoundary gammaCount
      formulaTable formulaWidth formulaTokenCount
  simp [compactNumericVerifierAcceptedConclusionRowDef,
    CompactNumericVerifierAcceptedConclusionRow, hcore, hsingleton]
  intro _hvalueBound
  rfl

theorem compactNumericVerifierAcceptedConclusionRowDef_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactNumericVerifierAcceptedConclusionRowDef.val :=
  compactNumericVerifierAcceptedConclusionRowDef.sigma_prop

theorem CompactNumericVerifierAcceptedConclusionRow.realize_formulaSet
    {traceWidth traceTable traceValueBound lastRow
      formulaTable formulaWidth formulaTokenCount : Nat}
    {formulaTokens : List Nat}
    (hstep : compactNumericVerifierStepGraphDef.val.Evalb
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        traceWidth traceTable lastRow))
    (hconclusion : CompactNumericVerifierAcceptedConclusionRow
      traceWidth traceTable traceValueBound lastRow
      formulaTable formulaWidth formulaTokenCount)
    (hformulaLength : formulaTokens.length = formulaTokenCount)
    (hformulaEntry : forall index, index < formulaTokens.length ->
      CompactFixedWidthEntry formulaTable formulaWidth
        index (formulaTokens.getI index)) :
    let environment :=
      compactNumericVerifierStepWitnessTableFormulaEnvironment
        traceWidth traceTable lastRow
    exists state : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
          (environment 0) (environment 1) (environment 2)
          (environment 24) (environment 25) state /\
        state.1.2.2.length = 1 /\
        (state.1.2.2.getI 0).1.toFinset = {formulaTokens} := by
  let environment :=
    compactNumericVerifierStepWitnessTableFormulaEnvironment
      traceWidth traceTable lastRow
  rcases hconclusion with
    ⟨_hvalueBound,
      stateTable, _hstateTableBound,
      stateWidth, _hstateWidthBound,
      stateTokenCount, _hstateTokenCountBound,
      valueBoundary, _hvalueBoundaryBound,
      valueValueBound, _hvalueValueBoundBound,
      valueStart, _hvalueStartBound,
      valueFinish, _hvalueFinishBound,
      gammaFinish, _hgammaFinishBound,
      gammaCount, _hgammaCountBound,
      gammaBoundary, _hgammaBoundaryBound,
      gammaBoundarySize, _hgammaBoundarySizeBound,
      hstateTableEntry, hstateWidthEntry, hstateTokenCountEntry,
      hvalueCountEntry, hvalueBoundaryEntry,
      _hvalueValueBoundEntry,
      hvalueStartEntry, hvalueFinishEntry, hchildCore, hsingleton⟩
  have hstateTable : stateTable = environment 0 := by
    change stateTable = compactNumericVerifierStepWitnessTableColumnValue
      traceWidth traceTable lastRow 0
    exact CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue
      hstateTableEntry
  have hstateWidth : stateWidth = environment 1 := by
    change stateWidth = compactNumericVerifierStepWitnessTableColumnValue
      traceWidth traceTable lastRow 1
    exact CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue
      hstateWidthEntry
  have hstateTokenCount : stateTokenCount = environment 2 := by
    change stateTokenCount = compactNumericVerifierStepWitnessTableColumnValue
      traceWidth traceTable lastRow 2
    exact CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue
      hstateTokenCountEntry
  have hvalueCount : environment 34 = 1 := by
    exact (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue
      hvalueCountEntry).symm
  have hvalueBoundary : valueBoundary = environment 35 := by
    change valueBoundary =
      compactNumericVerifierStepWitnessTableColumnValue
        traceWidth traceTable lastRow 35
    exact CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue
      hvalueBoundaryEntry
  simp only [hstateTable, hstateWidth, hstateTokenCount, hvalueBoundary]
    at hvalueStartEntry hvalueFinishEntry hchildCore hsingleton
  let coordinates := compactNumericVerifierStepNextCoordinates environment
  let sizeWitness := compactNumericVerifierStepNextSizeWitness environment
  have hstateCore : CompactNumericVerifierStateCoreGraph
      (environment 0) (environment 1) (environment 2)
      coordinates sizeWitness :=
    compactNumericVerifierStepGraphDef_evalb_nextCore environment hstep
  have hcoordinateFields :=
    compactNumericVerifierStepNextCoordinates_fields environment
  change
    coordinates.start = environment 24 /\
      coordinates.finish = environment 25 /\
      coordinates.proofFinish = environment 26 /\
      coordinates.proofCount = environment 27 /\
      coordinates.certificateFinish = environment 28 /\
      coordinates.certificateCount = environment 29 /\
      coordinates.tasksFinish = environment 30 /\
      coordinates.taskCount = environment 31 /\
      coordinates.taskBoundary = environment 32 /\
      coordinates.valuesFinish = environment 33 /\
      coordinates.valueCount = environment 34 /\
      coordinates.valueBoundary = environment 35 /\
      coordinates.statusTag = environment 36 /\
      coordinates.statusPayloadStart = environment 37 /\
      coordinates.statusBool = environment 38 at hcoordinateFields
  rcases hcoordinateFields with
    ⟨hstart, hfinish, _hproofFinish, _hproofCount,
      _hcertificateFinish, _hcertificateCount,
      _htasksFinish, _htaskCount, _htaskBoundary,
      _hvaluesFinish, hcoordinateValueCount, hcoordinateValueBoundary,
      _hstatusTag, _hstatusPayloadStart, _hstatusBool⟩
  rcases
      FoundationCompactNumericListedDirectVerifierStateRealization.CompactNumericVerifierStateCoreGraph.realizeDirectLayout
        hstateCore with
    ⟨proofTokens, certificateTokens, tasks, values, status,
      _hproofLength, _hcertificateLength, _htasksLength, hvaluesLength,
      hstateLayout, _hproofLayout, _hcertificateLayout,
      _htaskListLayout, _htaskRows,
      _hvalueListLayout, hvalueRows, _hstatusCase⟩
  have hvaluesLength' : values.length = 1 := by
    omega
  have hvalueRows' : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 35) values := by
    simpa only [hcoordinateValueBoundary] using hvalueRows
  have hzero : 0 < values.length := by omega
  rcases hvalueRows' 0 hzero with
    ⟨actualStart, _hactualStart,
      actualFinish, _hactualFinish,
      hactualStartEntry, hactualFinishEntry, hactualLayout⟩
  have hstartEq : valueStart = actualStart :=
    (CompactFixedWidthEntry.value_eq_tableValue hvalueStartEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue hactualStartEntry).symm
  have hfinishEq : valueFinish = actualFinish :=
    (CompactFixedWidthEntry.value_eq_tableValue hvalueFinishEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue hactualFinishEntry).symm
  have hactualLayout' : CompactNumericChildResultDirectLayout
      (environment 0) (environment 1) (environment 2)
      valueStart valueFinish (values.getI 0) := by
    simpa only [hstartEq, hfinishEq] using hactualLayout
  rcases
      FoundationCompactNumericListedDirectChildResultRowEquality.CompactNumericChildResultCoreGraph.realizeDirectLayoutWithRows
        hchildCore with
    ⟨realizedValue, hrealizedLayout, hgammaRows,
      hgammaLength, _hboolValue⟩
  have hrealizedEq : realizedValue = values.getI 0 :=
    FoundationCompactNumericListedDirectChildResultRowEquality.CompactNumericChildResultCoreGraph.realizedValue_eq
      hchildCore hactualLayout' hrealizedLayout
  have hset : realizedValue.1.toFinset = {formulaTokens} := by
    apply (compactCrossTableFormulaSetEqSingleton_iff
      hgammaRows hformulaLength hformulaEntry).mp
    simpa only [compactNumericChildResultRowCoordinatesOf,
      hgammaLength] using hsingleton
  rw [hrealizedEq] at hset
  have hstateLayout' : CompactNumericVerifierStateDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 24) (environment 25)
      (((proofTokens, certificateTokens), (tasks, values)), status) := by
    simpa only [hstart, hfinish] using hstateLayout
  exact ⟨(((proofTokens, certificateTokens), (tasks, values)), status),
    hstateLayout', hvaluesLength', hset⟩

theorem CompactNumericVerifierAcceptedConclusionRow.of_formulaSet
    {traceWidth traceTable traceValueBound lastRow
      formulaTable formulaWidth formulaTokenCount : Nat}
    {formulaTokens : List Nat}
    {state : CompactNumericVerifierState}
    (htraceValueBound : traceValueBound = 2 ^ traceWidth)
    (hstep : compactNumericVerifierStepGraphDef.val.Evalb
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        traceWidth traceTable lastRow))
    (hstateLayout :
      let environment :=
        compactNumericVerifierStepWitnessTableFormulaEnvironment
          traceWidth traceTable lastRow
      CompactNumericVerifierStateDirectLayout
        (environment 0) (environment 1) (environment 2)
        (environment 24) (environment 25) state)
    (hvaluesLength : state.1.2.2.length = 1)
    (hchildTrue : (state.1.2.2.getI 0).2 = true)
    (hformulaSet :
      (state.1.2.2.getI 0).1.toFinset = {formulaTokens})
    (hformulaLength : formulaTokens.length = formulaTokenCount)
    (hformulaEntry : forall index, index < formulaTokens.length ->
      CompactFixedWidthEntry formulaTable formulaWidth
        index (formulaTokens.getI index)) :
    CompactNumericVerifierAcceptedConclusionRow
      traceWidth traceTable traceValueBound lastRow
      formulaTable formulaWidth formulaTokenCount := by
  let environment :=
    compactNumericVerifierStepWitnessTableFormulaEnvironment
      traceWidth traceTable lastRow
  let coordinates := compactNumericVerifierStepNextCoordinates environment
  let sizeWitness := compactNumericVerifierStepNextSizeWitness environment
  have hstateCore : CompactNumericVerifierStateCoreGraph
      (environment 0) (environment 1) (environment 2)
      coordinates sizeWitness :=
    compactNumericVerifierStepGraphDef_evalb_nextCore environment hstep
  have hcoordinateFields :=
    compactNumericVerifierStepNextCoordinates_fields environment
  change
    coordinates.start = environment 24 /\
      coordinates.finish = environment 25 /\
      coordinates.proofFinish = environment 26 /\
      coordinates.proofCount = environment 27 /\
      coordinates.certificateFinish = environment 28 /\
      coordinates.certificateCount = environment 29 /\
      coordinates.tasksFinish = environment 30 /\
      coordinates.taskCount = environment 31 /\
      coordinates.taskBoundary = environment 32 /\
      coordinates.valuesFinish = environment 33 /\
      coordinates.valueCount = environment 34 /\
      coordinates.valueBoundary = environment 35 /\
      coordinates.statusTag = environment 36 /\
      coordinates.statusPayloadStart = environment 37 /\
      coordinates.statusBool = environment 38 at hcoordinateFields
  rcases hcoordinateFields with
    ⟨hstart, hfinish, _hproofFinish, _hproofCount,
      _hcertificateFinish, _hcertificateCount,
      _htasksFinish, _htaskCount, _htaskBoundary,
      _hvaluesFinish, hcoordinateValueCount, hcoordinateValueBoundary,
      _hstatusTag, _hstatusPayloadStart, _hstatusBool⟩
  have hsizeFields :=
    compactNumericVerifierStepNextSizeWitness_fields environment
  change
    sizeWitness.taskBoundarySize = environment 39 /\
      sizeWitness.valueBoundarySize = environment 40 /\
      sizeWitness.taskTableWidth = environment 41 /\
      sizeWitness.taskValueBound = environment 42 /\
      sizeWitness.valueTableWidth = environment 43 /\
      sizeWitness.valueValueBound = environment 44 at hsizeFields
  rcases hsizeFields with
    ⟨_htaskBoundarySize, _hvalueBoundarySize,
      _htaskTableWidth, _htaskValueBound,
      hvalueTableWidth, hvalueValueBound⟩
  rcases
      FoundationCompactNumericListedDirectVerifierStateRealization.CompactNumericVerifierStateCoreGraph.realizeDirectLayout
        hstateCore with
    ⟨proofTokens, certificateTokens, tasks, values, status,
      _hproofLength, _hcertificateLength, _htasksLength,
      hvaluesCoordinateLength, hrealizedLayout,
      _hproofLayout, _hcertificateLayout,
      _htaskListLayout, _htaskRows,
      _hvalueListLayout, hvalueRows, _hstatusCase⟩
  have hrealizedLayout' : CompactNumericVerifierStateDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 24) (environment 25)
      (((proofTokens, certificateTokens), (tasks, values)), status) := by
    simpa only [hstart, hfinish] using hrealizedLayout
  rcases
      FoundationCompactNumericListedDirectVerifierStateCrossTableEquality.CompactNumericVerifierStateDirectLayout.toSliceCarries
        hrealizedLayout' with
    ⟨_hrealizedFinish, hrealizedBound, _hrealizedEntries⟩
  have hslices : CompactFixedWidthTokenSlicesEq
      (environment 0) (environment 1) (environment 2)
      (environment 24) (environment 25)
      (environment 24) (environment 25) :=
    CompactFixedWidthTokenSlicesEq.refl (by omega) hrealizedBound
  have hstateEq : state =
      (((proofTokens, certificateTokens), (tasks, values)), status) :=
    CompactFixedWidthTokenSlicesEq.verifierStateValue_eq
      hslices hrealizedLayout' hstateLayout
  have hvaluesLength' : values.length = 1 := by
    simpa only [hstateEq] using hvaluesLength
  have henvironmentValueCount : environment 34 = 1 := by
    omega
  have hvalueRows' : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
      (environment 0) (environment 1) (environment 2)
      (environment 35) values := by
    simpa only [hcoordinateValueBoundary] using hvalueRows
  have hvalueGraphRaw : CompactNumericChildResultListRowsGraph
      (environment 0) (environment 1) (environment 2)
      coordinates.valueBoundary coordinates.valueCount
      sizeWitness.valueTableWidth sizeWitness.valueValueBound :=
    hstateCore.2.2.2.2.2.2.2.1
  have hvalueGraph : CompactNumericChildResultListRowsGraph
      (environment 0) (environment 1) (environment 2)
      (environment 35) 1 (environment 43) (environment 44) := by
    simpa only [hcoordinateValueBoundary, hcoordinateValueCount,
      hvalueTableWidth, hvalueValueBound, henvironmentValueCount] using
      hvalueGraphRaw
  rcases
      FoundationCompactNumericListedDirectChildResultBoundedRowExposedFormula.CompactNumericChildResultListRowsGraph.exists_exposed
        hvalueGraph (rowIndex := 0) (by omega) with
    ⟨valueStart, valueFinish, gammaFinish, gammaCount, gammaBoundary,
      boolValue, gammaBoundarySize, hexposed⟩
  have hexposedCopy := hexposed
  rcases
      FoundationCompactNumericListedDirectChildResultBoundedRowExposedFormula.CompactNumericChildResultBoundedRowExposed.realize_actual
        hexposed (by omega) hvalueRows' with
    ⟨value, hactualValue, _hvalueLayout, hgammaRows,
      hgammaLength, hvalueBool⟩
  have hchildTrue' : (values.getI 0).2 = true := by
    simpa only [hstateEq] using hchildTrue
  have hformulaSet' :
      (values.getI 0).1.toFinset = {formulaTokens} := by
    simpa only [hstateEq] using hformulaSet
  have hvalueTrue : value.2 = true := by
    rw [← hactualValue]
    exact hchildTrue'
  have hboolValue : boolValue = 1 := by
    simpa [compactAdditiveBoolTag, hvalueTrue] using hvalueBool.symm
  have hvalueSet : value.1.toFinset = {formulaTokens} := by
    rw [← hactualValue]
    exact hformulaSet'
  have hsingletonRaw : CompactCrossTableFormulaSetEqSingleton
      (environment 0) (environment 1) (environment 2)
      gammaBoundary value.1.length
      formulaTable formulaWidth formulaTokenCount :=
    (compactCrossTableFormulaSetEqSingleton_iff
      hgammaRows hformulaLength hformulaEntry).mpr hvalueSet
  have hsingleton : CompactCrossTableFormulaSetEqSingleton
      (environment 0) (environment 1) (environment 2)
      gammaBoundary gammaCount
      formulaTable formulaWidth formulaTokenCount := by
    simpa only [hgammaLength] using hsingletonRaw
  rcases hexposedCopy with
    ⟨hvalueStartBound, hvalueFinishBound,
      hgammaFinishBound, hgammaCountBound, hgammaBoundaryBound,
      _hboolBound, hgammaBoundarySizeBound,
      hvalueStartEntry, hvalueFinishEntry, hchildCore⟩
  have hchildCore' : CompactNumericChildResultCoreGraph
      (environment 0) (environment 1) (environment 2)
      (compactNumericChildResultRowCoordinatesOf
        valueStart valueFinish gammaFinish gammaCount gammaBoundary 1)
      { gammaBoundarySize := gammaBoundarySize } := by
    simpa only [hboolValue] using hchildCore
  have henvironmentBound (column : Fin 429) :
      environment column <= traceValueBound := by
    change compactNumericVerifierStepWitnessTableColumnValue
      traceWidth traceTable lastRow column.val <= traceValueBound
    rw [htraceValueBound]
    exact compactNumericVerifierStepWitnessTableColumnValue_le_pow
      traceWidth traceTable lastRow column.val
  have henvironmentEntry (column : Fin 429) :
      CompactFixedWidthEntry traceTable traceWidth
        (lastRow * 429 + column.val) (environment column) := by
    exact compactNumericVerifierStepWitnessTableColumnValue_entry
      traceWidth traceTable lastRow column.val
  have htracePositive : 1 <= traceValueBound := by
    rw [htraceValueBound]
    exact Nat.one_le_two_pow
  refine ⟨htracePositive,
    environment 0, henvironmentBound 0,
    environment 1, henvironmentBound 1,
    environment 2, henvironmentBound 2,
    environment 35, henvironmentBound 35,
    environment 44, henvironmentBound 44,
    valueStart, hvalueStartBound,
    valueFinish, hvalueFinishBound,
    gammaFinish, hgammaFinishBound,
    gammaCount, hgammaCountBound,
    gammaBoundary, hgammaBoundaryBound,
    gammaBoundarySize, hgammaBoundarySizeBound,
    henvironmentEntry 0, henvironmentEntry 1, henvironmentEntry 2, ?_,
    henvironmentEntry 35, henvironmentEntry 44,
    hvalueStartEntry, hvalueFinishEntry, hchildCore', hsingleton⟩
  simpa [henvironmentValueCount] using henvironmentEntry 34

#print axioms compactNumericVerifierAcceptedConclusionRowDef_spec
#print axioms compactNumericVerifierAcceptedConclusionRowDef_sigmaZero
#print axioms
  CompactNumericVerifierAcceptedConclusionRow.realize_formulaSet
#print axioms
  CompactNumericVerifierAcceptedConclusionRow.of_formulaSet

end FoundationCompactNumericListedDirectVerifierAcceptedConclusionRow
