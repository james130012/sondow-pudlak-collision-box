import integration.FoundationCompactNumericListedDirectVerifierStateFormula
import integration.FoundationCompactNumericListedDirectVerifierFinishFormula
import integration.FoundationCompactNumericListedDirectVerifierValueRealization

/-!
# Realization support for the verifier finish branch

The finish branch has an empty task stack.  This permits a complete reverse
construction of both state rows before the general task decoder is available:
flat streams and child results are realized from their arithmetic graphs, and
the option status is reconstructed from its exact tag and Boolean slice.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierFinishRealization

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierValueRealization
open FoundationCompactNumericListedDirectVerifierFinishFormula

theorem CompactNumericVerifierStateCoreGraph.realizeEmptyTasks
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactNumericVerifierStateRowCoordinates}
    {sizeWitness : CompactNumericVerifierStateSizeWitness}
    (hgraph : CompactNumericVerifierStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (htaskCount : coordinates.taskCount = 0) :
    ∃ proofTokens certificateTokens : List Nat,
    ∃ values : List CompactNumericChildResult,
    ∃ status : Option Bool,
      proofTokens.length = coordinates.proofCount ∧
      certificateTokens.length = coordinates.certificateCount ∧
      values.length = coordinates.valueCount ∧
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount coordinates.start coordinates.finish
        (((proofTokens, certificateTokens), ([], values)), status) ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount coordinates.start
        coordinates.proofFinish proofTokens ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount coordinates.proofFinish
        coordinates.certificateFinish certificateTokens ∧
      CompactAdditiveStructuredListLayout
        tokenTable width tokenCount coordinates.tasksFinish
        values.length coordinates.valuesFinish coordinates.valueBoundary ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactNumericChildResultDirectLayout tokenTable width tokenCount
        coordinates.valueBoundary values ∧
      ((status = none ∧ coordinates.statusTag = 0) ∨
        ∃ result : Bool,
          status = some result ∧
          coordinates.statusTag = 1 ∧
          compactAdditiveBoolTag result = coordinates.statusBool) := by
  rcases hgraph with
    ⟨hproof, hcertificate,
      htaskLayout, htaskRows, htaskSizeEq, htaskSize,
      hvalueLayout, hvalueRows, hvalueSizeEq, hvalueSize,
      hoption, hstatus⟩
  have hproofFinishBound : coordinates.proofFinish ≤ tokenCount := by
    rcases hcertificate with
      ⟨bodyStart, _hbodyStart, hheader, _hfinish⟩
    exact Nat.le_of_lt hheader.1.1
  have hcertificateFinishBound :
      coordinates.certificateFinish ≤ tokenCount := by
    rcases htaskLayout with
      ⟨bodyStart, _hbodyStart, hheader, _hboundary⟩
    exact Nat.le_of_lt hheader.1.1
  rcases CompactAdditiveNatListSlice.realizeDirectLayout
      hproof hproofFinishBound with
    ⟨proofTokens, hproofLength, hproofLayout⟩
  rcases CompactAdditiveNatListSlice.realizeDirectLayout
      hcertificate hcertificateFinishBound with
    ⟨certificateTokens, hcertificateLength, hcertificateLayout⟩
  rcases CompactNumericChildResultListRowsGraph.realizeDirectRows
      hvalueLayout hvalueRows with
    ⟨values, hvaluesLength, hvaluesRows⟩
  have hemptyTaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
      coordinates.taskBoundary ([] : List CompactNumericVerifierTask) := by
    intro index hindex
    simp at hindex
  have htaskBoundarySize : Nat.size coordinates.taskBoundary ≤
      (([] : List CompactNumericVerifierTask).length + 1) * tokenCount := by
    rw [← htaskSizeEq]
    simpa [htaskCount] using htaskSize
  have hvalueBoundarySize : Nat.size coordinates.valueBoundary ≤
      (values.length + 1) * tokenCount := by
    rw [← hvalueSizeEq]
    simpa [hvaluesLength] using hvalueSize
  have hbuild (status : Option Bool)
      (hstatusLayout : CompactAdditiveOptionBoolDirectLayout
        tokenTable width tokenCount coordinates.valuesFinish
        coordinates.finish status) :
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount coordinates.start coordinates.finish
        (((proofTokens, certificateTokens), ([], values)), status) := by
    refine ⟨coordinates.proofFinish, coordinates.certificateFinish,
      coordinates.tasksFinish, coordinates.valuesFinish,
      coordinates.taskBoundary, coordinates.valueBoundary,
      ?_, ?_, ?_, hemptyTaskRows, htaskBoundarySize,
      ?_, hvaluesRows, hvalueBoundarySize, hstatusLayout⟩
    · simpa [hproofLength] using hproofLayout
    · simpa [hcertificateLength] using hcertificateLayout
    · simpa [htaskCount] using htaskLayout
    · simpa [hvaluesLength] using hvalueLayout
  rcases hstatus with hnone | hsome
  · rcases hnone with ⟨htag, hfinish⟩
    have hstatusLayout : CompactAdditiveOptionBoolDirectLayout
        tokenTable width tokenCount coordinates.valuesFinish
        coordinates.finish none :=
      ⟨coordinates.statusTag, coordinates.statusPayloadStart,
        hoption, Or.inl ⟨rfl, htag, hfinish⟩⟩
    exact ⟨proofTokens, certificateTokens, values, none,
      hproofLength, hcertificateLength, hvaluesLength,
      hbuild none hstatusLayout, hproofLayout, hcertificateLayout,
      by simpa [hvaluesLength] using hvalueLayout, hvaluesRows,
      Or.inl ⟨rfl, htag⟩⟩
  · rcases hsome with ⟨htag, hbool⟩
    rcases hbool.exists_bool with ⟨result, hresult⟩
    have hresultTag :
        coordinates.statusBool = compactAdditiveBoolTag result := by
      simpa [compactAdditiveBoolTag] using hresult
    have hboolLayout : CompactAdditiveBoolSlice
        tokenTable width tokenCount coordinates.statusPayloadStart
        (compactAdditiveBoolTag result) coordinates.finish := by
      simpa [hresultTag] using hbool
    have hstatusLayout : CompactAdditiveOptionBoolDirectLayout
        tokenTable width tokenCount coordinates.valuesFinish
        coordinates.finish (some result) :=
      ⟨coordinates.statusTag, coordinates.statusPayloadStart,
        hoption, Or.inr ⟨result, rfl, htag, hboolLayout⟩⟩
    exact ⟨proofTokens, certificateTokens, values, some result,
      hproofLength, hcertificateLength, hvaluesLength,
      hbuild (some result) hstatusLayout,
      hproofLayout, hcertificateLayout,
      by simpa [hvaluesLength] using hvalueLayout, hvaluesRows,
      Or.inr ⟨result, rfl, htag, hresultTag.symm⟩⟩

theorem CompactNumericVerifierFinishRows.realizeCurrentOutcome
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness : CompactNumericVerifierStateSizeWitness}
    (hcurrent : CompactNumericVerifierStateCoreGraph
      tokenTable width tokenCount currentCoordinates currentSizeWitness)
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
    ∃ payload : CompactNumericRunningPayload,
    ∃ result : Bool,
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount
        currentCoordinates.start currentCoordinates.finish
        (payload, none) ∧
      compactNumericFinishState payload = (payload, some result) ∧
      compactAdditiveBoolTag result = nextCoordinates.statusBool := by
  rcases hfinish with
    ⟨hcurrentTag, htaskCount, _hpayloadEq,
      _hproofCountEq, _hcertificateCountEq,
      _htaskCountEq, _hvalueCountEq,
      _hnextTag, hcases⟩
  rcases CompactNumericVerifierStateCoreGraph.realizeEmptyTasks
      hcurrent htaskCount with
    ⟨proofTokens, certificateTokens, values, status,
      hproofLength, hcertificateLength, hvaluesLength,
      hstate, _hproofDirect, _hcertificateDirect, _hvalueDirect,
      hactualValueRows, hstatus⟩
  have hstatusNone : status = none := by
    rcases hstatus with hnone | hsome
    · exact hnone.1
    · rcases hsome with ⟨result, _hstatus, htag, _hbool⟩
      omega
  subst status
  let payload : CompactNumericRunningPayload :=
    ((proofTokens, certificateTokens), ([], values))
  rcases hcases with hsuccess | hfailure
  · rcases hsuccess with
      ⟨hproofCount, hcertificateCount, _htaskCount,
        hvalueCount, hvalueBool⟩
    have hproofEmpty : proofTokens = [] := by
      apply List.eq_nil_of_length_eq_zero
      omega
    have hcertificateEmpty : certificateTokens = [] := by
      apply List.eq_nil_of_length_eq_zero
      omega
    have hvaluesOne : values.length = 1 := by omega
    have hvalueIndex : 0 < values.length := by omega
    have hheadBool :
        (values.head?.getD compactNumericDefaultChildResult).2 =
          (values.getI 0).2 := by
      cases values <;> simp_all
    have hstoredBool :=
      CompactNumericChildResultBoundedRowWithBool.matchesDirectRows
        hvalueIndex hactualValueRows hvalueBool
    have hresultBool :
        compactAdditiveBoolTag
            (values.head?.getD compactNumericDefaultChildResult).2 =
          nextCoordinates.statusBool := by
      rw [hheadBool]
      exact hstoredBool
    refine ⟨payload,
      (values.head?.getD compactNumericDefaultChildResult).2,
      ?_, ?_, hresultBool⟩
    · simpa [payload] using hstate
    · simp [payload, compactNumericFinishState,
        hproofEmpty, hcertificateEmpty, hvaluesOne]
  · rcases hfailure with ⟨hbadCount, hnextFalse⟩
    have hnotGuard :
        ¬(proofTokens = [] ∧ certificateTokens = [] ∧
          ([] : List CompactNumericVerifierTask) = [] ∧
          values.length = 1) := by
      intro hguard
      rcases hguard with
        ⟨hproofEmpty, hcertificateEmpty, _htasksEmpty, hvaluesOne⟩
      have hproofZero : currentCoordinates.proofCount = 0 := by
        rw [← hproofLength, hproofEmpty]
        rfl
      have hcertificateZero :
          currentCoordinates.certificateCount = 0 := by
        rw [← hcertificateLength, hcertificateEmpty]
        rfl
      have hvalueOne : currentCoordinates.valueCount = 1 := by
        omega
      rcases hbadCount with hbad | hbad | hbad | hbad <;> omega
    have hnotGuardSimple :
        ¬(proofTokens = [] ∧ certificateTokens = [] ∧
          values.length = 1) := by
      intro hguard
      exact hnotGuard ⟨hguard.1, hguard.2.1, rfl, hguard.2.2⟩
    refine ⟨payload, false, ?_, ?_, ?_⟩
    · simpa [payload] using hstate
    · simp [payload, compactNumericFinishState, hnotGuardSimple]
    · simpa [compactAdditiveBoolTag, hnextFalse]

#print axioms CompactNumericVerifierStateCoreGraph.realizeEmptyTasks
#print axioms CompactNumericVerifierFinishRows.realizeCurrentOutcome

end FoundationCompactNumericListedDirectVerifierFinishRealization
