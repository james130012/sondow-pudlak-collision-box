import integration.FoundationCompactNumericListedDirectVerifierStateLayout
import integration.FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
import integration.FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula

/-!
# Bounded arithmetic core for one central verifier state

The 24 free coordinates expose both remaining token streams, both typed
stacks, and the optional Boolean status.  Task and child-result rows use their
already checked bounded row formulas with explicit exponential value bounds.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStateFormula

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula

structure CompactNumericVerifierStateRowCoordinates where
  start : Nat
  finish : Nat
  proofFinish : Nat
  proofCount : Nat
  certificateFinish : Nat
  certificateCount : Nat
  tasksFinish : Nat
  taskCount : Nat
  taskBoundary : Nat
  valuesFinish : Nat
  valueCount : Nat
  valueBoundary : Nat
  statusTag : Nat
  statusPayloadStart : Nat
  statusBool : Nat

structure CompactNumericVerifierStateSizeWitness where
  taskBoundarySize : Nat
  valueBoundarySize : Nat
  taskTableWidth : Nat
  taskValueBound : Nat
  valueTableWidth : Nat
  valueValueBound : Nat

def compactNumericVerifierStateRowCoordinatesOf
    (start finish proofFinish proofCount certificateFinish certificateCount
      tasksFinish taskCount taskBoundary valuesFinish valueCount valueBoundary
      statusTag statusPayloadStart statusBool : Nat) :
    CompactNumericVerifierStateRowCoordinates where
  start := start
  finish := finish
  proofFinish := proofFinish
  proofCount := proofCount
  certificateFinish := certificateFinish
  certificateCount := certificateCount
  tasksFinish := tasksFinish
  taskCount := taskCount
  taskBoundary := taskBoundary
  valuesFinish := valuesFinish
  valueCount := valueCount
  valueBoundary := valueBoundary
  statusTag := statusTag
  statusPayloadStart := statusPayloadStart
  statusBool := statusBool

def CompactNumericVerifierStateCoreGraph
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericVerifierStateRowCoordinates)
    (sizeWitness : CompactNumericVerifierStateSizeWitness) : Prop :=
  CompactAdditiveNatListSlice tokenTable width tokenCount
      coordinates.start coordinates.proofCount coordinates.proofFinish ∧
    CompactAdditiveNatListSlice tokenTable width tokenCount
      coordinates.proofFinish coordinates.certificateCount
      coordinates.certificateFinish ∧
    CompactAdditiveStructuredListLayout tokenTable width tokenCount
      coordinates.certificateFinish coordinates.taskCount
      coordinates.tasksFinish coordinates.taskBoundary ∧
    CompactNumericVerifierTaskListRowsGraph tokenTable width tokenCount
      coordinates.taskBoundary coordinates.taskCount
      sizeWitness.taskTableWidth sizeWitness.taskValueBound ∧
    sizeWitness.taskBoundarySize = Nat.size coordinates.taskBoundary ∧
    sizeWitness.taskBoundarySize ≤
      (coordinates.taskCount + 1) * tokenCount ∧
    CompactAdditiveStructuredListLayout tokenTable width tokenCount
      coordinates.tasksFinish coordinates.valueCount
      coordinates.valuesFinish coordinates.valueBoundary ∧
    CompactNumericChildResultListRowsGraph tokenTable width tokenCount
      coordinates.valueBoundary coordinates.valueCount
      sizeWitness.valueTableWidth sizeWitness.valueValueBound ∧
    sizeWitness.valueBoundarySize = Nat.size coordinates.valueBoundary ∧
    sizeWitness.valueBoundarySize ≤
      (coordinates.valueCount + 1) * tokenCount ∧
    CompactAdditiveOptionLayout tokenTable width tokenCount
      coordinates.valuesFinish coordinates.statusTag
      coordinates.statusPayloadStart coordinates.finish ∧
    ((coordinates.statusTag = 0 ∧
        coordinates.finish = coordinates.statusPayloadStart) ∨
      (coordinates.statusTag = 1 ∧
        CompactAdditiveBoolSlice tokenTable width tokenCount
          coordinates.statusPayloadStart coordinates.statusBool
          coordinates.finish))

def compactNumericVerifierStateCoreGraphDef :
    𝚺₀.Semisentence 24 := .mkSigma
  “tokenTable width tokenCount
      start finish proofFinish proofCount certificateFinish certificateCount
      tasksFinish taskCount taskBoundary valuesFinish valueCount valueBoundary
      statusTag statusPayloadStart statusBool
      taskBoundarySize valueBoundarySize
      taskTableWidth taskValueBound valueTableWidth valueValueBound.
    !(compactAdditiveNatListSliceDef)
      tokenTable width tokenCount start proofCount proofFinish ∧
    !(compactAdditiveNatListSliceDef)
      tokenTable width tokenCount proofFinish certificateCount
        certificateFinish ∧
    !(compactAdditiveStructuredListLayoutDef)
      tokenTable width tokenCount certificateFinish taskCount
        tasksFinish taskBoundary ∧
    !(compactNumericVerifierTaskListRowsGraphDef)
      tokenTable width tokenCount taskBoundary taskCount
        taskTableWidth taskValueBound ∧
    !(compactNatSizeDef) taskBoundarySize taskBoundary ∧
    taskBoundarySize ≤ (taskCount + 1) * tokenCount ∧
    !(compactAdditiveStructuredListLayoutDef)
      tokenTable width tokenCount tasksFinish valueCount
        valuesFinish valueBoundary ∧
    !(compactNumericChildResultListRowsGraphDef)
      tokenTable width tokenCount valueBoundary valueCount
        valueTableWidth valueValueBound ∧
    !(compactNatSizeDef) valueBoundarySize valueBoundary ∧
    valueBoundarySize ≤ (valueCount + 1) * tokenCount ∧
    !(compactAdditiveOptionLayoutDef)
      tokenTable width tokenCount valuesFinish statusTag
        statusPayloadStart finish ∧
    ((statusTag = 0 ∧ finish = statusPayloadStart) ∨
      (statusTag = 1 ∧
        !(compactAdditiveBoolSliceDef)
          tokenTable width tokenCount statusPayloadStart statusBool finish))”

def compactNumericVerifierStateCoreFormulaEnvironment
    (tokenTable width tokenCount
      start finish proofFinish proofCount certificateFinish certificateCount
      tasksFinish taskCount taskBoundary valuesFinish valueCount valueBoundary
      statusTag statusPayloadStart statusBool
      taskBoundarySize valueBoundarySize
      taskTableWidth taskValueBound valueTableWidth valueValueBound : Nat) :
    Fin 24 → Nat :=
  ![tokenTable, width, tokenCount,
    start, finish, proofFinish, proofCount, certificateFinish,
    certificateCount, tasksFinish, taskCount, taskBoundary,
    valuesFinish, valueCount, valueBoundary,
    statusTag, statusPayloadStart, statusBool,
    taskBoundarySize, valueBoundarySize,
    taskTableWidth, taskValueBound, valueTableWidth, valueValueBound]

@[simp] theorem compactNumericVerifierStateCoreGraphDef_spec
    (tokenTable width tokenCount
      start finish proofFinish proofCount certificateFinish certificateCount
      tasksFinish taskCount taskBoundary valuesFinish valueCount valueBoundary
      statusTag statusPayloadStart statusBool
      taskBoundarySize valueBoundarySize
      taskTableWidth taskValueBound valueTableWidth valueValueBound : Nat) :
    compactNumericVerifierStateCoreGraphDef.val.Evalb
        (compactNumericVerifierStateCoreFormulaEnvironment
          tokenTable width tokenCount
          start finish proofFinish proofCount certificateFinish certificateCount
          tasksFinish taskCount taskBoundary valuesFinish valueCount valueBoundary
          statusTag statusPayloadStart statusBool
          taskBoundarySize valueBoundarySize
          taskTableWidth taskValueBound valueTableWidth valueValueBound) ↔
      CompactNumericVerifierStateCoreGraph tokenTable width tokenCount
        (compactNumericVerifierStateRowCoordinatesOf
          start finish proofFinish proofCount certificateFinish certificateCount
          tasksFinish taskCount taskBoundary valuesFinish valueCount valueBoundary
          statusTag statusPayloadStart statusBool)
        { taskBoundarySize := taskBoundarySize
          valueBoundarySize := valueBoundarySize
          taskTableWidth := taskTableWidth
          taskValueBound := taskValueBound
          valueTableWidth := valueTableWidth
          valueValueBound := valueValueBound } := by
  let env := compactNumericVerifierStateCoreFormulaEnvironment
    tokenTable width tokenCount
    start finish proofFinish proofCount certificateFinish certificateCount
    tasksFinish taskCount taskBoundary valuesFinish valueCount valueBoundary
    statusTag statusPayloadStart statusBool
    taskBoundarySize valueBoundarySize
    taskTableWidth taskValueBound valueTableWidth valueValueBound
  change compactNumericVerifierStateCoreGraphDef.val.Evalb env ↔ _
  have hproofEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #3, #6, #5]) =
        ![tokenTable, width, tokenCount, start, proofCount, proofFinish] := by
    funext index
    fin_cases index <;> rfl
  have hcertificateEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #5, #8, #7]) =
        ![tokenTable, width, tokenCount,
          proofFinish, certificateCount, certificateFinish] := by
    funext index
    fin_cases index <;> rfl
  have htaskLayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #7, #10, #9, #11]) =
        ![tokenTable, width, tokenCount,
          certificateFinish, taskCount, tasksFinish, taskBoundary] := by
    funext index
    fin_cases index <;> rfl
  have htaskRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #11, #10, #20, #21]) =
        ![tokenTable, width, tokenCount, taskBoundary,
          taskCount, taskTableWidth, taskValueBound] := by
    funext index
    fin_cases index <;> rfl
  have htaskSizeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#18 : Semiterm ℒₒᵣ Empty 24), #11]) =
        ![taskBoundarySize, taskBoundary] := by
    funext index
    fin_cases index <;> rfl
  have hvalueLayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #9, #13, #12, #14]) =
        ![tokenTable, width, tokenCount,
          tasksFinish, valueCount, valuesFinish, valueBoundary] := by
    funext index
    fin_cases index <;> rfl
  have hvalueRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #14, #13, #22, #23]) =
        ![tokenTable, width, tokenCount, valueBoundary,
          valueCount, valueTableWidth, valueValueBound] := by
    funext index
    fin_cases index <;> rfl
  have hvalueSizeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#19 : Semiterm ℒₒᵣ Empty 24), #14]) =
        ![valueBoundarySize, valueBoundary] := by
    funext index
    fin_cases index <;> rfl
  have hstatusEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #12, #15, #16, #4]) =
        ![tokenTable, width, tokenCount, valuesFinish,
          statusTag, statusPayloadStart, finish] := by
    funext index
    fin_cases index <;> rfl
  have hboolEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #16, #17, #4]) =
        ![tokenTable, width, tokenCount,
          statusPayloadStart, statusBool, finish] := by
    funext index
    fin_cases index <;> rfl
  have htokenCountValue : env 2 = tokenCount := rfl
  have htaskCountValue : env 10 = taskCount := rfl
  have htaskBoundarySizeValue : env 18 = taskBoundarySize := rfl
  have hvalueCountValue : env 13 = valueCount := rfl
  have hvalueBoundarySizeValue : env 19 = valueBoundarySize := rfl
  have hstatusTagValue : env 15 = statusTag := rfl
  have hfinishValue : env 4 = finish := rfl
  have hstatusPayloadStartValue : env 16 = statusPayloadStart := rfl
  simp [compactNumericVerifierStateCoreGraphDef,
    compactNumericVerifierStateRowCoordinatesOf,
    CompactNumericVerifierStateCoreGraph,
    hproofEnv, hcertificateEnv, htaskLayoutEnv, htaskRowsEnv,
    htaskSizeEnv, hvalueLayoutEnv, hvalueRowsEnv, hvalueSizeEnv,
    hstatusEnv, hboolEnv, htokenCountValue, htaskCountValue,
    htaskBoundarySizeValue, hvalueCountValue,
    hvalueBoundarySizeValue, hstatusTagValue,
    hfinishValue, hstatusPayloadStartValue]

theorem compactNumericVerifierStateCoreGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierStateCoreGraphDef.val := by
  simp [compactNumericVerifierStateCoreGraphDef]

private theorem CompactNumericVerifierStateDirectLayout.toCoreGraph_none
    {tokenTable width tokenCount start finish : Nat}
    {state : CompactNumericVerifierState}
    (hlayout : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount start finish state)
    (hstatus : state.2 = none) :
    ∃ coordinates sizeWitness,
      coordinates.start = start ∧
      coordinates.finish = finish ∧
      CompactNumericVerifierStateCoreGraph
        tokenTable width tokenCount coordinates sizeWitness := by
  rcases hlayout with
    ⟨proofFinish, certificateFinish, tasksFinish, valuesFinish,
      taskBoundary, valueBoundary,
      hproof, hcertificate, htaskLayout, htaskRows, htaskSize,
      hvalueLayout, hvalueRows, hvalueSize, hstatusLayout⟩
  rcases hstatusLayout with
    ⟨statusTag, statusPayloadStart, hoption, hstatusCase⟩
  rcases hstatusCase with hnone | hsome
  · rcases hnone with ⟨_hstate, htag, hfinish⟩
    let taskTableWidth :=
      compactNumericVerifierTaskRowTableWidth width tokenCount
    let taskValueBound := 2 ^ taskTableWidth
    let valueTableWidth :=
      compactNumericChildResultRowTableWidth width tokenCount
    let valueValueBound := 2 ^ valueTableWidth
    let coordinates : CompactNumericVerifierStateRowCoordinates :=
      { start := start
        finish := finish
        proofFinish := proofFinish
        proofCount := state.1.1.1.length
        certificateFinish := certificateFinish
        certificateCount := state.1.1.2.length
        tasksFinish := tasksFinish
        taskCount := state.1.2.1.length
        taskBoundary := taskBoundary
        valuesFinish := valuesFinish
        valueCount := state.1.2.2.length
        valueBoundary := valueBoundary
        statusTag := statusTag
        statusPayloadStart := statusPayloadStart
        statusBool := 0 }
    let sizeWitness : CompactNumericVerifierStateSizeWitness :=
      { taskBoundarySize := Nat.size taskBoundary
        valueBoundarySize := Nat.size valueBoundary
        taskTableWidth := taskTableWidth
        taskValueBound := taskValueBound
        valueTableWidth := valueTableWidth
        valueValueBound := valueValueBound }
    refine ⟨coordinates, sizeWitness, rfl, rfl, ?_⟩
    exact ⟨CompactAdditiveNatListDirectLayout.toSlice hproof,
      CompactAdditiveNatListDirectLayout.toSlice hcertificate,
      htaskLayout,
      CompactAdditiveStructuredListElementRowLayouts.taskListRowsGraph
        htaskRows,
      rfl, htaskSize, hvalueLayout,
      CompactAdditiveStructuredListElementRowLayouts.childResultListRowsGraph
        hvalueRows,
      rfl, hvalueSize, hoption, Or.inl ⟨htag, hfinish⟩⟩
  · rcases hsome with ⟨result, hstateSome, _htag, _hbool⟩
    rw [hstatus] at hstateSome
    simp at hstateSome

private theorem CompactNumericVerifierStateDirectLayout.toCoreGraph_some
    {tokenTable width tokenCount start finish : Nat}
    {state : CompactNumericVerifierState}
    (hlayout : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount start finish state)
    {result : Bool} (hstatus : state.2 = some result) :
    ∃ coordinates sizeWitness,
      coordinates.start = start ∧
      coordinates.finish = finish ∧
      CompactNumericVerifierStateCoreGraph
        tokenTable width tokenCount coordinates sizeWitness := by
  rcases hlayout with
    ⟨proofFinish, certificateFinish, tasksFinish, valuesFinish,
      taskBoundary, valueBoundary,
      hproof, hcertificate, htaskLayout, htaskRows, htaskSize,
      hvalueLayout, hvalueRows, hvalueSize, hstatusLayout⟩
  rcases hstatusLayout with
    ⟨statusTag, statusPayloadStart, hoption, hstatusCase⟩
  rcases hstatusCase with hnone | hsome
  · rcases hnone with ⟨hstateNone, _htag, _hfinish⟩
    rw [hstatus] at hstateNone
    simp at hstateNone
  · rcases hsome with ⟨storedResult, hstateSome, htag, hbool⟩
    have hstored : storedResult = result := by
      rw [hstatus] at hstateSome
      exact (Option.some.inj hstateSome).symm
    subst storedResult
    let taskTableWidth :=
      compactNumericVerifierTaskRowTableWidth width tokenCount
    let taskValueBound := 2 ^ taskTableWidth
    let valueTableWidth :=
      compactNumericChildResultRowTableWidth width tokenCount
    let valueValueBound := 2 ^ valueTableWidth
    let coordinates : CompactNumericVerifierStateRowCoordinates :=
      { start := start
        finish := finish
        proofFinish := proofFinish
        proofCount := state.1.1.1.length
        certificateFinish := certificateFinish
        certificateCount := state.1.1.2.length
        tasksFinish := tasksFinish
        taskCount := state.1.2.1.length
        taskBoundary := taskBoundary
        valuesFinish := valuesFinish
        valueCount := state.1.2.2.length
        valueBoundary := valueBoundary
        statusTag := statusTag
        statusPayloadStart := statusPayloadStart
        statusBool := compactAdditiveBoolTag result }
    let sizeWitness : CompactNumericVerifierStateSizeWitness :=
      { taskBoundarySize := Nat.size taskBoundary
        valueBoundarySize := Nat.size valueBoundary
        taskTableWidth := taskTableWidth
        taskValueBound := taskValueBound
        valueTableWidth := valueTableWidth
        valueValueBound := valueValueBound }
    refine ⟨coordinates, sizeWitness, rfl, rfl, ?_⟩
    exact ⟨CompactAdditiveNatListDirectLayout.toSlice hproof,
      CompactAdditiveNatListDirectLayout.toSlice hcertificate,
      htaskLayout,
      CompactAdditiveStructuredListElementRowLayouts.taskListRowsGraph
        htaskRows,
      rfl, htaskSize, hvalueLayout,
      CompactAdditiveStructuredListElementRowLayouts.childResultListRowsGraph
        hvalueRows,
      rfl, hvalueSize, hoption, Or.inr ⟨htag, hbool⟩⟩

theorem CompactNumericVerifierStateDirectLayout.toCoreGraph
    {tokenTable width tokenCount start finish : Nat}
    {state : CompactNumericVerifierState}
    (hlayout : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount start finish state) :
    ∃ coordinates sizeWitness,
      coordinates.start = start ∧
      coordinates.finish = finish ∧
      CompactNumericVerifierStateCoreGraph
        tokenTable width tokenCount coordinates sizeWitness := by
  cases hstatus : state.2 with
  | none =>
      exact CompactNumericVerifierStateDirectLayout.toCoreGraph_none
        hlayout hstatus
  | some result =>
      exact CompactNumericVerifierStateDirectLayout.toCoreGraph_some
        hlayout hstatus

#print axioms compactNumericVerifierStateCoreGraphDef_spec
#print axioms compactNumericVerifierStateCoreGraphDef_sigmaZero
#print axioms CompactNumericVerifierStateDirectLayout.toCoreGraph

end FoundationCompactNumericListedDirectVerifierStateFormula
