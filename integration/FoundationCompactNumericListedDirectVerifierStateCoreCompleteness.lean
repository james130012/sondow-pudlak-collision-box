import integration.FoundationCompactNumericListedDirectVerifierStateFormula

/-!
# Canonical converse package for verifier-state cores

A typed direct state layout determines explicit core coordinates and the
canonical task/value row bounds.  The package retains the typed component rows
needed by later converse constructions instead of hiding them behind an
existence theorem.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStateCoreCompleteness

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierStateFormula

def CompactNumericVerifierStateCanonicalCorePackage
    (tokenTable width tokenCount start finish : Nat)
    (state : CompactNumericVerifierState)
    (coordinates : CompactNumericVerifierStateRowCoordinates)
    (sizeWitness : CompactNumericVerifierStateSizeWitness) : Prop :=
  coordinates.start = start ∧
    coordinates.finish = finish ∧
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount coordinates.start coordinates.proofFinish
        state.1.1.1 ∧
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount coordinates.proofFinish
        coordinates.certificateFinish state.1.1.2 ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount coordinates.certificateFinish
        state.1.2.1.length coordinates.tasksFinish coordinates.taskBoundary ∧
    CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        coordinates.taskBoundary state.1.2.1 ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount coordinates.tasksFinish
        state.1.2.2.length coordinates.valuesFinish coordinates.valueBoundary ∧
    CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        coordinates.valueBoundary state.1.2.2 ∧
    coordinates.taskCount = state.1.2.1.length ∧
    coordinates.valueCount = state.1.2.2.length ∧
    sizeWitness.taskTableWidth =
      compactNumericVerifierTaskRowTableWidth width tokenCount ∧
    sizeWitness.taskValueBound =
      2 ^ compactNumericVerifierTaskRowTableWidth width tokenCount ∧
    sizeWitness.valueTableWidth =
      compactNumericChildResultRowTableWidth width tokenCount ∧
    sizeWitness.valueValueBound =
      2 ^ compactNumericChildResultRowTableWidth width tokenCount ∧
    ((state.2 = none ∧ coordinates.statusTag = 0 ∧
        coordinates.statusBool = 0) ∨
      ∃ result : Bool,
        state.2 = some result ∧ coordinates.statusTag = 1 ∧
        coordinates.statusBool = compactAdditiveBoolTag result) ∧
    CompactNumericVerifierStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness

theorem CompactNumericVerifierStateDirectLayout.toCanonicalCorePackage
    {tokenTable width tokenCount start finish : Nat}
    {state : CompactNumericVerifierState}
    (hlayout : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount start finish state) :
    ∃ coordinates sizeWitness,
      CompactNumericVerifierStateCanonicalCorePackage
        tokenTable width tokenCount start finish state
        coordinates sizeWitness := by
  rcases hlayout with
    ⟨proofFinish, certificateFinish, tasksFinish, valuesFinish,
      taskBoundary, valueBoundary,
      hproof, hcertificate, htaskLayout, htaskRows, htaskSize,
      hvalueLayout, hvalueRows, hvalueSize, hstatusLayout⟩
  rcases hstatusLayout with
    ⟨statusTag, statusPayloadStart, hoption, hstatusCase⟩
  let taskTableWidth :=
    compactNumericVerifierTaskRowTableWidth width tokenCount
  let taskValueBound := 2 ^ taskTableWidth
  let valueTableWidth :=
    compactNumericChildResultRowTableWidth width tokenCount
  let valueValueBound := 2 ^ valueTableWidth
  rcases hstatusCase with hnone | hsome
  · rcases hnone with ⟨hstate, htag, hfinish⟩
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
    refine ⟨coordinates, sizeWitness,
      rfl, rfl, hproof, hcertificate, htaskLayout, htaskRows,
      hvalueLayout, hvalueRows, rfl, rfl, rfl, rfl, rfl, rfl,
      Or.inl ⟨hstate, htag, rfl⟩, ?_⟩
    exact ⟨CompactAdditiveNatListDirectLayout.toSlice hproof,
      CompactAdditiveNatListDirectLayout.toSlice hcertificate,
      htaskLayout,
      CompactAdditiveStructuredListElementRowLayouts.taskListRowsGraph
        htaskRows,
      rfl, htaskSize, hvalueLayout,
      CompactAdditiveStructuredListElementRowLayouts.childResultListRowsGraph
        hvalueRows,
      rfl, hvalueSize, hoption, Or.inl ⟨htag, hfinish⟩⟩
  · rcases hsome with ⟨result, hstate, htag, hbool⟩
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
    refine ⟨coordinates, sizeWitness,
      rfl, rfl, hproof, hcertificate, htaskLayout, htaskRows,
      hvalueLayout, hvalueRows, rfl, rfl, rfl, rfl, rfl, rfl,
      Or.inr ⟨result, hstate, htag, rfl⟩, ?_⟩
    exact ⟨CompactAdditiveNatListDirectLayout.toSlice hproof,
      CompactAdditiveNatListDirectLayout.toSlice hcertificate,
      htaskLayout,
      CompactAdditiveStructuredListElementRowLayouts.taskListRowsGraph
        htaskRows,
      rfl, htaskSize, hvalueLayout,
      CompactAdditiveStructuredListElementRowLayouts.childResultListRowsGraph
        hvalueRows,
      rfl, hvalueSize, hoption, Or.inr ⟨htag, hbool⟩⟩

theorem CompactNumericVerifierStateCanonicalCorePackage.core
    {tokenTable width tokenCount start finish : Nat}
    {state : CompactNumericVerifierState}
    {coordinates : CompactNumericVerifierStateRowCoordinates}
    {sizeWitness : CompactNumericVerifierStateSizeWitness}
    (hpackage : CompactNumericVerifierStateCanonicalCorePackage
      tokenTable width tokenCount start finish state
      coordinates sizeWitness) :
    CompactNumericVerifierStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness := by
  rcases hpackage with
    ⟨_hstart, _hfinish, _hproof, _hcertificate,
      _htaskLayout, _htaskRows, _hvalueLayout, _hvalueRows,
      _htaskCount, _hvalueCount,
      _htaskTableWidth, _htaskValueBound,
      _hvalueTableWidth, _hvalueValueBound,
      _hstatusCase, hcore⟩
  exact hcore

theorem CompactNumericVerifierStateCanonicalCorePackage.statusTag_eq_zero
    {tokenTable width tokenCount start finish : Nat}
    {state : CompactNumericVerifierState}
    {coordinates : CompactNumericVerifierStateRowCoordinates}
    {sizeWitness : CompactNumericVerifierStateSizeWitness}
    (hpackage : CompactNumericVerifierStateCanonicalCorePackage
      tokenTable width tokenCount start finish state
      coordinates sizeWitness)
    (hstatus : state.2 = none) :
    coordinates.statusTag = 0 := by
  rcases hpackage with
    ⟨_hstart, _hfinish, _hproof, _hcertificate,
      _htaskLayout, _htaskRows, _hvalueLayout, _hvalueRows,
      _htaskCount, _hvalueCount,
      _htaskTableWidth, _htaskValueBound,
      _hvalueTableWidth, _hvalueValueBound,
      hstatusCase, _hcore⟩
  rcases hstatusCase with hnone | hsome
  · exact hnone.2.1
  · rcases hsome with ⟨result, hsome, _htag, _hbool⟩
    rw [hstatus] at hsome
    simp at hsome

theorem CompactNumericVerifierStateCanonicalCorePackage.statusTagBool_eq_some
    {tokenTable width tokenCount start finish : Nat}
    {state : CompactNumericVerifierState}
    {coordinates : CompactNumericVerifierStateRowCoordinates}
    {sizeWitness : CompactNumericVerifierStateSizeWitness}
    {result : Bool}
    (hpackage : CompactNumericVerifierStateCanonicalCorePackage
      tokenTable width tokenCount start finish state
      coordinates sizeWitness)
    (hstatus : state.2 = some result) :
    coordinates.statusTag = 1 ∧
      coordinates.statusBool = compactAdditiveBoolTag result := by
  rcases hpackage with
    ⟨_hstart, _hfinish, _hproof, _hcertificate,
      _htaskLayout, _htaskRows, _hvalueLayout, _hvalueRows,
      _htaskCount, _hvalueCount,
      _htaskTableWidth, _htaskValueBound,
      _hvalueTableWidth, _hvalueValueBound,
      hstatusCase, _hcore⟩
  rcases hstatusCase with hnone | hsome
  · rw [hstatus] at hnone
    simp at hnone
  · rcases hsome with ⟨storedResult, hstored, htag, hbool⟩
    rw [hstatus] at hstored
    have hresult : storedResult = result := (Option.some.inj hstored).symm
    subst storedResult
    exact ⟨htag, hbool⟩

#print axioms CompactNumericVerifierStateDirectLayout.toCanonicalCorePackage
#print axioms CompactNumericVerifierStateCanonicalCorePackage.core
#print axioms
  CompactNumericVerifierStateCanonicalCorePackage.statusTag_eq_zero
#print axioms
  CompactNumericVerifierStateCanonicalCorePackage.statusTagBool_eq_some

end FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
