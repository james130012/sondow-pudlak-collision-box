import integration.FoundationCompactNumericListedDirectVerifierStepEnvironmentSurjectivity
import integration.FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound

/-!
# Numeric list-count controls for every valid verifier step formula

The current and next state cores expose proof, certificate, task, and value list
counts.  Each count is bounded by the common state-table token count on the same
formula environment.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStepStateListCountControlBounds

open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectVerifierStepEnvironmentSurjectivity
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound

private theorem compactAdditiveNatListSlice_count_le_tokenCount
    {tokenTable width tokenCount start count finish : Nat}
    (hlayout : CompactAdditiveNatListSlice
      tokenTable width tokenCount start count finish) :
    count <= tokenCount := by
  rcases hlayout with ⟨bodyStart, _hbodyStart, hheader, _hfinish⟩
  exact (Nat.le_add_left count bodyStart).trans hheader.2

structure CompactNumericVerifierStepStateListCountControlBounds
    (environment : Fin 429 -> Nat) : Prop where
  currentProofCount_le : environment 6 <= environment 2
  currentCertificateCount_le : environment 8 <= environment 2
  currentTaskCount_le : environment 10 <= environment 2
  currentValueCount_le : environment 13 <= environment 2
  nextProofCount_le : environment 27 <= environment 2
  nextCertificateCount_le : environment 29 <= environment 2
  nextTaskCount_le : environment 31 <= environment 2
  nextValueCount_le : environment 34 <= environment 2

structure CompactNumericVerifierStepStateListCountBounds
    (environment : Fin 429 -> Nat) (bound : Nat) : Prop where
  currentProofCount_le : environment 6 <= bound
  currentCertificateCount_le : environment 8 <= bound
  currentTaskCount_le : environment 10 <= bound
  currentValueCount_le : environment 13 <= bound
  nextProofCount_le : environment 27 <= bound
  nextCertificateCount_le : environment 29 <= bound
  nextTaskCount_le : environment 31 <= bound
  nextValueCount_le : environment 34 <= bound

theorem CompactNumericVerifierStepStateListCountControlBounds.to_bound
    {environment : Fin 429 -> Nat} {bound : Nat}
    (hcontrol :
      CompactNumericVerifierStepStateListCountControlBounds environment)
    (htokenCount : environment 2 <= bound) :
    CompactNumericVerifierStepStateListCountBounds environment bound :=
  { currentProofCount_le := hcontrol.currentProofCount_le.trans htokenCount
    currentCertificateCount_le :=
      hcontrol.currentCertificateCount_le.trans htokenCount
    currentTaskCount_le := hcontrol.currentTaskCount_le.trans htokenCount
    currentValueCount_le := hcontrol.currentValueCount_le.trans htokenCount
    nextProofCount_le := hcontrol.nextProofCount_le.trans htokenCount
    nextCertificateCount_le :=
      hcontrol.nextCertificateCount_le.trans htokenCount
    nextTaskCount_le := hcontrol.nextTaskCount_le.trans htokenCount
    nextValueCount_le := hcontrol.nextValueCount_le.trans htokenCount }

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
theorem compactNumericVerifierStepGraphDef_stateListCountControlBounds
    (environment : Fin 429 -> Nat)
    (hformula : compactNumericVerifierStepGraphDef.val.Evalb environment) :
    CompactNumericVerifierStepStateListCountControlBounds environment := by
  have hcurrent := compactNumericVerifierStepGraphDef_evalb_currentCore
    environment hformula
  have hnext := compactNumericVerifierStepGraphDef_evalb_nextCore
    environment hformula
  rcases hcurrent with
    ⟨hcurrentProof, hcurrentCertificate, hcurrentTasks, _hcurrentTaskRows,
      _hcurrentTaskSizeEq, _hcurrentTaskSize, hcurrentValues,
      _hcurrentValueRows, _hcurrentValueSizeEq, _hcurrentValueSize,
      _hcurrentStatusLayout, _hcurrentStatus⟩
  rcases hnext with
    ⟨hnextProof, hnextCertificate, hnextTasks, _hnextTaskRows,
      _hnextTaskSizeEq, _hnextTaskSize, hnextValues,
      _hnextValueRows, _hnextValueSizeEq, _hnextValueSize,
      _hnextStatusLayout, _hnextStatus⟩
  have hcurrentFields :=
    compactNumericVerifierStepCurrentCoordinates_fields environment
  have hnextFields :=
    compactNumericVerifierStepNextCoordinates_fields environment
  dsimp only at hcurrentFields hnextFields
  rcases hcurrentFields with
    ⟨_hcurrentStart, _hcurrentFinish, _hcurrentProofFinish,
      hcurrentProofCount, _hcurrentCertificateFinish,
      hcurrentCertificateCount, _hcurrentTasksFinish, hcurrentTaskCount,
      _hcurrentTaskBoundary, _hcurrentValuesFinish, hcurrentValueCount,
      _hcurrentValueBoundary, _hcurrentStatusTag,
      _hcurrentStatusPayloadStart, _hcurrentStatusBool⟩
  rcases hnextFields with
    ⟨_hnextStart, _hnextFinish, _hnextProofFinish, hnextProofCount,
      _hnextCertificateFinish, hnextCertificateCount, _hnextTasksFinish,
      hnextTaskCount, _hnextTaskBoundary, _hnextValuesFinish,
      hnextValueCount, _hnextValueBoundary, _hnextStatusTag,
      _hnextStatusPayloadStart, _hnextStatusBool⟩
  refine
    { currentProofCount_le := ?_
      currentCertificateCount_le := ?_
      currentTaskCount_le := ?_
      currentValueCount_le := ?_
      nextProofCount_le := ?_
      nextCertificateCount_le := ?_
      nextTaskCount_le := ?_
      nextValueCount_le := ?_ }
  · rw [← hcurrentProofCount]
    exact compactAdditiveNatListSlice_count_le_tokenCount hcurrentProof
  · rw [← hcurrentCertificateCount]
    exact compactAdditiveNatListSlice_count_le_tokenCount hcurrentCertificate
  · rw [← hcurrentTaskCount]
    exact structuredListLayout_count_le_tokenCount hcurrentTasks
  · rw [← hcurrentValueCount]
    exact structuredListLayout_count_le_tokenCount hcurrentValues
  · rw [← hnextProofCount]
    exact compactAdditiveNatListSlice_count_le_tokenCount hnextProof
  · rw [← hnextCertificateCount]
    exact compactAdditiveNatListSlice_count_le_tokenCount hnextCertificate
  · rw [← hnextTaskCount]
    exact structuredListLayout_count_le_tokenCount hnextTasks
  · rw [← hnextValueCount]
    exact structuredListLayout_count_le_tokenCount hnextValues

#print axioms compactNumericVerifierStepGraphDef_stateListCountControlBounds
#print axioms
  CompactNumericVerifierStepStateListCountControlBounds.to_bound

end FoundationCompactNumericListedDirectVerifierStepStateListCountControlBounds
