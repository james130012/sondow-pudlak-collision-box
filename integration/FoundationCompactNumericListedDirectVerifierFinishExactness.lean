import integration.FoundationCompactNumericListedDirectVerifierPayloadEquality

/-!
# Exact semantic realization of the verifier finish branch

The bounded finish rows preserve the complete running payload and change only
the option status.  This module proves that any two state graphs connected by
those rows realize an actual executable `compactNumericVerifierStep`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierFinishExactness

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierFinishFormula
open FoundationCompactNumericListedDirectVerifierValueRealization
open FoundationCompactNumericListedDirectVerifierFinishRealization
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectTokenSliceEquality

theorem CompactNumericVerifierFinishRows.realizeExactStep
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    (hcurrent : CompactNumericVerifierStateCoreGraph
      tokenTable width tokenCount currentCoordinates currentSizeWitness)
    (hnext : CompactNumericVerifierStateCoreGraph
      tokenTable width tokenCount nextCoordinates nextSizeWitness)
    (hfinish : CompactNumericVerifierFinishRows
      tokenTable width tokenCount
      currentCoordinates.start currentCoordinates.valuesFinish
      currentCoordinates.proofCount currentCoordinates.certificateCount
      currentCoordinates.taskCount currentCoordinates.valueCount
      currentCoordinates.valueBoundary currentSizeWitness.valueValueBound
      currentCoordinates.statusTag
      nextCoordinates.start nextCoordinates.valuesFinish
      nextCoordinates.proofCount nextCoordinates.certificateCount
      nextCoordinates.taskCount nextCoordinates.valueCount
      nextCoordinates.statusTag nextCoordinates.statusBool) :
    ∃ currentState nextState : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount currentCoordinates.start
          currentCoordinates.finish currentState ∧
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount nextCoordinates.start
          nextCoordinates.finish nextState ∧
      nextState = compactNumericVerifierStep currentState := by
  rcases hfinish with
    ⟨hcurrentTag, hcurrentTaskCount, hpayloadEq,
      hproofCountEq, hcertificateCountEq, htaskCountEq,
      hvalueCountEq, hnextTag, hcases⟩
  have hnextTaskCount : nextCoordinates.taskCount = 0 := by omega
  have hcurrentTaskLayout := hcurrent.2.2.1
  have hnextTaskLayout := hnext.2.2.1
  rcases CompactNumericVerifierStateCoreGraph.realizeEmptyTasks
      hcurrent hcurrentTaskCount with
    ⟨currentProofTokens, currentCertificateTokens, currentValues,
      currentStatus, hcurrentProofLength, hcurrentCertificateLength,
      hcurrentValuesLength, hcurrentStateLayout, hcurrentProofLayout,
      hcurrentCertificateLayout, hcurrentValueLayout, hcurrentValueRows,
      hcurrentStatus⟩
  rcases CompactNumericVerifierStateCoreGraph.realizeEmptyTasks
      hnext hnextTaskCount with
    ⟨nextProofTokens, nextCertificateTokens, nextValues,
      nextStatus, hnextProofLength, hnextCertificateLength,
      hnextValuesLength, hnextStateLayout, hnextProofLayout,
      hnextCertificateLayout, hnextValueLayout, hnextValueRows,
      hnextStatus⟩
  have hcurrentStatusNone : currentStatus = none := by
    rcases hcurrentStatus with hnone | hsome
    · exact hnone.1
    · rcases hsome with ⟨result, _hstatus, htag, _hresult⟩
      omega
  subst currentStatus
  rcases hnextStatus with hnone | hsome
  · rcases hnone with ⟨_hstatus, htag⟩
    omega
  · rcases hsome with
      ⟨nextResult, hnextStatusEq, _hnextStatusTag, hnextResultTag⟩
    subst nextStatus
    have hcurrentTaskLayoutZero : CompactAdditiveStructuredListLayout
        tokenTable width tokenCount currentCoordinates.certificateFinish 0
          currentCoordinates.tasksFinish currentCoordinates.taskBoundary := by
      simpa [hcurrentTaskCount] using hcurrentTaskLayout
    have hnextTaskLayoutZero : CompactAdditiveStructuredListLayout
        tokenTable width tokenCount nextCoordinates.certificateFinish 0
          nextCoordinates.tasksFinish nextCoordinates.taskBoundary := by
      simpa [hnextTaskCount] using hnextTaskLayout
    have hcurrentTasksFinish : currentCoordinates.tasksFinish =
        currentCoordinates.certificateFinish + 1 :=
      CompactAdditiveStructuredListLayout.finish_eq_start_add_one_of_count_zero
        hcurrentTaskLayoutZero
    have hnextTasksFinish : nextCoordinates.tasksFinish =
        nextCoordinates.certificateFinish + 1 :=
      CompactAdditiveStructuredListLayout.finish_eq_start_add_one_of_count_zero
        hnextTaskLayoutZero
    have hcurrentProofFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq hcurrentProofLayout
    have hnextProofFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq hnextProofLayout
    have hcurrentCertificateFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq
        hcurrentCertificateLayout
    have hnextCertificateFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq hnextCertificateLayout
    have hcurrentValuesStartFinish :=
      CompactAdditiveStructuredListLayout.start_lt_finish
        hcurrentValueLayout
    have hnextValuesStartFinish :=
      CompactAdditiveStructuredListLayout.start_lt_finish hnextValueLayout
    have hpayloadLength :
        currentCoordinates.valuesFinish - currentCoordinates.start =
          nextCoordinates.valuesFinish - nextCoordinates.start := by
      rcases hpayloadEq with
        ⟨count, _hcount, hcurrentCount, hnextCount,
          _hcurrentBound, _hnextBound, _hbits⟩
      omega
    rcases CompactFixedWidthTokenSlicesEq.natListPrefix_eq
        (offset := 0) hpayloadEq rfl rfl
        (by omega) (by omega) (by omega)
        hcurrentProofLayout hnextProofLayout with
      ⟨proofOffset, hcurrentProofAt, hnextProofAt, hproofEq⟩
    rcases CompactFixedWidthTokenSlicesEq.natListPrefix_eq
        (offset := proofOffset) hpayloadEq
        hcurrentProofAt hnextProofAt
        (by omega) (by omega) (by omega)
        hcurrentCertificateLayout hnextCertificateLayout with
      ⟨certificateOffset, hcurrentCertificateAt,
        hnextCertificateAt, hcertificateEq⟩
    let valueOffset := certificateOffset + 1
    have hcurrentValuesAt : currentCoordinates.tasksFinish =
        currentCoordinates.start + valueOffset := by
      dsimp only [valueOffset]
      omega
    have hnextValuesAt : nextCoordinates.tasksFinish =
        nextCoordinates.start + valueOffset := by
      dsimp only [valueOffset]
      omega
    let valueTokenCount :=
      currentCoordinates.valuesFinish - currentCoordinates.tasksFinish
    have hcurrentValuesFinishAt : currentCoordinates.valuesFinish =
        currentCoordinates.start + valueOffset + valueTokenCount := by
      dsimp only [valueTokenCount]
      omega
    have hnextValuesFinishAt : nextCoordinates.valuesFinish =
        nextCoordinates.start + valueOffset + valueTokenCount := by
      dsimp only [valueTokenCount]
      omega
    have hvalueWithin : valueOffset + valueTokenCount ≤
        currentCoordinates.valuesFinish - currentCoordinates.start := by
      omega
    have hvalueSlices := CompactFixedWidthTokenSlicesEq.subslice
      hpayloadEq valueOffset valueTokenCount hvalueWithin
    have hcurrentValueLayoutAligned : CompactAdditiveStructuredListLayout
        tokenTable width tokenCount
        (currentCoordinates.start + valueOffset) currentValues.length
        (currentCoordinates.start + valueOffset + valueTokenCount)
        currentCoordinates.valueBoundary := by
      simpa [hcurrentValuesAt, hcurrentValuesFinishAt] using
        hcurrentValueLayout
    have hnextValueLayoutAligned : CompactAdditiveStructuredListLayout
        tokenTable width tokenCount
        (nextCoordinates.start + valueOffset) nextValues.length
        (nextCoordinates.start + valueOffset + valueTokenCount)
        nextCoordinates.valueBoundary := by
      simpa [hnextValuesAt, hnextValuesFinishAt] using hnextValueLayout
    have hvaluesEq : nextValues = currentValues :=
      CompactFixedWidthTokenSlicesEq.childResultListValues_eq
        hvalueSlices hcurrentValueLayoutAligned hcurrentValueRows
          hnextValueLayoutAligned hnextValueRows
    let payload : CompactNumericRunningPayload :=
      ((currentProofTokens, currentCertificateTokens), ([], currentValues))
    have hcurrentLayout : CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount currentCoordinates.start
          currentCoordinates.finish (payload, none) := by
      simpa [payload] using hcurrentStateLayout
    have hnextLayout : CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount nextCoordinates.start
          nextCoordinates.finish (payload, some nextResult) := by
      simpa [payload, hproofEq, hcertificateEq, hvaluesEq] using
        hnextStateLayout
    have hfinishState : compactNumericFinishState payload =
        (payload, some nextResult) := by
      rcases hcases with hsuccess | hfailure
      · rcases hsuccess with
          ⟨hproofZero, hcertificateZero, _htaskZero,
            hvalueOne, hvalueBool⟩
        have hproofEmpty : currentProofTokens = [] := by
          apply List.eq_nil_of_length_eq_zero
          omega
        have hcertificateEmpty : currentCertificateTokens = [] := by
          apply List.eq_nil_of_length_eq_zero
          omega
        have hvaluesOne : currentValues.length = 1 := by omega
        have hvalueIndex : 0 < currentValues.length := by omega
        have hheadBool :
            (currentValues.head?.getD compactNumericDefaultChildResult).2 =
              (currentValues.getI 0).2 := by
          cases currentValues <;> simp_all
        have hstoredBool :=
          CompactNumericChildResultBoundedRowWithBool.matchesDirectRows
            hvalueIndex hcurrentValueRows hvalueBool
        have hheadTag : compactAdditiveBoolTag
              (currentValues.head?.getD compactNumericDefaultChildResult).2 =
            nextCoordinates.statusBool := by
          rw [hheadBool]
          exact hstoredBool
        have hresultEq : nextResult =
            (currentValues.head?.getD compactNumericDefaultChildResult).2 :=
          compactAdditiveBoolTag_injective
            (hnextResultTag.trans hheadTag.symm)
        simp [payload, compactNumericFinishState,
          hproofEmpty, hcertificateEmpty, hvaluesOne, hresultEq]
      · rcases hfailure with ⟨hbadCount, hnextFalse⟩
        have hnotGuard :
            ¬(currentProofTokens = [] ∧ currentCertificateTokens = [] ∧
              ([] : List CompactNumericVerifierTask) = [] ∧
              currentValues.length = 1) := by
          intro hguard
          rcases hguard with
            ⟨hproofEmpty, hcertificateEmpty, _htasksEmpty, hvaluesOne⟩
          have hproofZero : currentCoordinates.proofCount = 0 := by
            rw [← hcurrentProofLength, hproofEmpty]
            rfl
          have hcertificateZero :
              currentCoordinates.certificateCount = 0 := by
            rw [← hcurrentCertificateLength, hcertificateEmpty]
            rfl
          have hvalueOne : currentCoordinates.valueCount = 1 := by omega
          rcases hbadCount with hbad | hbad | hbad | hbad <;> omega
        have hresultFalse : nextResult = false :=
          compactAdditiveBoolTag_injective (by
            simpa [compactAdditiveBoolTag, hnextFalse] using hnextResultTag)
        have hnotGuardSimple :
            ¬(currentProofTokens = [] ∧ currentCertificateTokens = [] ∧
              currentValues.length = 1) := by
          intro hguard
          exact hnotGuard ⟨hguard.1, hguard.2.1, rfl, hguard.2.2⟩
        simp [payload, compactNumericFinishState,
          hnotGuardSimple, hresultFalse]
    refine ⟨(payload, none), (payload, some nextResult),
      hcurrentLayout, hnextLayout, ?_⟩
    simpa [compactNumericVerifierStep, compactNumericRunningStep, payload] using
      hfinishState.symm

#print axioms CompactNumericVerifierFinishRows.realizeExactStep

end FoundationCompactNumericListedDirectVerifierFinishExactness
