import integration.FoundationCompactNumericListedDirectVerifierTaskRealization
import integration.FoundationCompactNumericListedDirectVerifierStateFormula

/-!
# Reverse realization of complete verifier states

Every arithmetic state core is decoded into the same five typed components used
by the executable verifier: proof tokens, certificate tokens, tasks, child
results, and optional status.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStateRealization

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
open FoundationCompactNumericListedDirectVerifierValueRealization
open FoundationCompactNumericListedDirectVerifierTaskRealization

theorem CompactNumericVerifierStateCoreGraph.realizeDirectLayout
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactNumericVerifierStateRowCoordinates}
    {sizeWitness : CompactNumericVerifierStateSizeWitness}
    (hgraph : CompactNumericVerifierStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    ∃ proofTokens certificateTokens : List Nat,
    ∃ tasks : List CompactNumericVerifierTask,
    ∃ values : List CompactNumericChildResult,
    ∃ status : Option Bool,
      proofTokens.length = coordinates.proofCount ∧
      certificateTokens.length = coordinates.certificateCount ∧
      tasks.length = coordinates.taskCount ∧
      values.length = coordinates.valueCount ∧
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount coordinates.start coordinates.finish
        (((proofTokens, certificateTokens), (tasks, values)), status) ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount coordinates.start
        coordinates.proofFinish proofTokens ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount coordinates.proofFinish
        coordinates.certificateFinish certificateTokens ∧
      CompactAdditiveStructuredListLayout
        tokenTable width tokenCount coordinates.certificateFinish
        tasks.length coordinates.tasksFinish coordinates.taskBoundary ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        coordinates.taskBoundary tasks ∧
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
      ⟨_bodyStart, _hbodyStart, hheader, _hfinish⟩
    exact Nat.le_of_lt hheader.1.1
  have hcertificateFinishBound :
      coordinates.certificateFinish ≤ tokenCount := by
    rcases htaskLayout with
      ⟨_bodyStart, _hbodyStart, hheader, _hboundary⟩
    exact Nat.le_of_lt hheader.1.1
  rcases CompactAdditiveNatListSlice.realizeDirectLayout
      hproof hproofFinishBound with
    ⟨proofTokens, hproofLength, hproofDirect⟩
  rcases CompactAdditiveNatListSlice.realizeDirectLayout
      hcertificate hcertificateFinishBound with
    ⟨certificateTokens, hcertificateLength, hcertificateDirect⟩
  rcases CompactNumericVerifierTaskListRowsGraph.realizeDirectRows
      htaskLayout htaskRows with
    ⟨tasks, htasksLength, htasksDirectRows⟩
  rcases CompactNumericChildResultListRowsGraph.realizeDirectRows
      hvalueLayout hvalueRows with
    ⟨values, hvaluesLength, hvaluesDirectRows⟩
  have htaskBoundarySize : Nat.size coordinates.taskBoundary ≤
      (tasks.length + 1) * tokenCount := by
    rw [← htaskSizeEq]
    simpa [htasksLength] using htaskSize
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
        (((proofTokens, certificateTokens), (tasks, values)), status) := by
    refine ⟨coordinates.proofFinish, coordinates.certificateFinish,
      coordinates.tasksFinish, coordinates.valuesFinish,
      coordinates.taskBoundary, coordinates.valueBoundary,
      ?_, ?_, ?_, htasksDirectRows, htaskBoundarySize,
      ?_, hvaluesDirectRows, hvalueBoundarySize, hstatusLayout⟩
    · simpa [hproofLength] using hproofDirect
    · simpa [hcertificateLength] using hcertificateDirect
    · simpa [htasksLength] using htaskLayout
    · simpa [hvaluesLength] using hvalueLayout
  rcases hstatus with hnone | hsome
  · rcases hnone with ⟨htag, hfinish⟩
    have hstatusLayout : CompactAdditiveOptionBoolDirectLayout
        tokenTable width tokenCount coordinates.valuesFinish
        coordinates.finish none :=
      ⟨coordinates.statusTag, coordinates.statusPayloadStart,
        hoption, Or.inl ⟨rfl, htag, hfinish⟩⟩
    exact ⟨proofTokens, certificateTokens, tasks, values, none,
      hproofLength, hcertificateLength, htasksLength, hvaluesLength,
      hbuild none hstatusLayout, hproofDirect, hcertificateDirect,
      by simpa [htasksLength] using htaskLayout, htasksDirectRows,
      by simpa [hvaluesLength] using hvalueLayout, hvaluesDirectRows,
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
    exact ⟨proofTokens, certificateTokens, tasks, values, some result,
      hproofLength, hcertificateLength, htasksLength, hvaluesLength,
      hbuild (some result) hstatusLayout,
      hproofDirect, hcertificateDirect,
      by simpa [htasksLength] using htaskLayout, htasksDirectRows,
      by simpa [hvaluesLength] using hvalueLayout, hvaluesDirectRows,
      Or.inr ⟨result, rfl, htag, hresultTag.symm⟩⟩

#print axioms CompactNumericVerifierStateCoreGraph.realizeDirectLayout

end FoundationCompactNumericListedDirectVerifierStateRealization
