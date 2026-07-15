import integration.FoundationCompactNumericListedDirectVerifierTaskLayout

/-!
# Complete direct layout of central verifier states

One central verifier row consists, in order, of the remaining proof tokens,
remaining certificate tokens, verifier task stack, child-result stack, and an
optional Boolean status.  Every list has its own exact element-boundary table.
The final theorem lifts the row layout to the complete state tableau.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStateLayout

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericSequentValuePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultPrimcodable

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNumericNodeFieldsAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierStateAdditiveCodec

def CompactAdditiveOptionBoolDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (status : Option Bool) : Prop :=
  ∃ tag payloadStart,
    CompactAdditiveOptionLayout
      tokenTable width tokenCount start tag payloadStart finish ∧
    ((status = none ∧ tag = 0 ∧ finish = payloadStart) ∨
      ∃ result,
        status = some result ∧ tag = 1 ∧
        CompactAdditiveBoolSlice tokenTable width tokenCount payloadStart
          (compactAdditiveBoolTag result) finish)

theorem compactAdditiveOptionBoolDirectLayout_canonical
    (frontTokens : List Nat) (status : Option Bool)
    (backTokens : List Nat) :
    let statusTokens := compactAdditiveEncode status
    let tokens := frontTokens ++ statusTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + statusTokens.length
    CompactAdditiveOptionBoolDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish status := by
  cases status with
  | none =>
      have hoption := compactAdditiveOptionLayout_canonical
        frontTokens (none : Option Bool) backTokens
      dsimp only at hoption ⊢
      refine ⟨0, frontTokens.length + 1, ?_, Or.inl ?_⟩
      · simpa [compactAdditiveOptionTag] using hoption
      · simp
  | some result =>
      let afterTag := frontTokens ++ [1]
      have hoption := compactAdditiveOptionLayout_canonical
        frontTokens (some result) backTokens
      have hboolRaw := compactAdditiveBoolSlice_canonical
        afterTag result backTokens
      dsimp only at hoption hboolRaw ⊢
      have htokens : frontTokens ++ compactAdditiveEncode (some result) ++
          backTokens = afterTag ++ compactAdditiveEncode result ++
            backTokens := by
        simp [afterTag, List.append_assoc]
      rw [← htokens] at hboolRaw
      refine ⟨1, frontTokens.length + 1, ?_, Or.inr ?_⟩
      · simpa [compactAdditiveOptionTag] using hoption
      · exact ⟨result, rfl, rfl, by simpa [afterTag] using hboolRaw⟩

def CompactNumericVerifierStateDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (state : CompactNumericVerifierState) : Prop :=
  ∃ proofFinish certificateFinish tasksFinish valuesFinish
      taskBoundaryTable valueBoundaryTable,
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount start proofFinish state.1.1.1 ∧
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount proofFinish certificateFinish
        state.1.1.2 ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount certificateFinish state.1.2.1.length
        tasksFinish taskBoundaryTable ∧
    CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
      taskBoundaryTable state.1.2.1 ∧
    Nat.size taskBoundaryTable ≤
      (state.1.2.1.length + 1) * tokenCount ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount tasksFinish state.1.2.2.length
        valuesFinish valueBoundaryTable ∧
    CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
      valueBoundaryTable state.1.2.2 ∧
    Nat.size valueBoundaryTable ≤
      (state.1.2.2.length + 1) * tokenCount ∧
    CompactAdditiveOptionBoolDirectLayout
      tokenTable width tokenCount valuesFinish finish state.2

theorem compactNumericVerifierStateDirectLayout_canonical
    (frontTokens : List Nat) (state : CompactNumericVerifierState)
    (backTokens : List Nat) :
    let stateTokens := compactAdditiveEncode state
    let tokens := frontTokens ++ stateTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + stateTokens.length
    CompactNumericVerifierStateDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish state := by
  let proofTokens := state.1.1.1
  let certificateTokens := state.1.1.2
  let tasks := state.1.2.1
  let values := state.1.2.2
  let status := state.2
  let stateTokens := compactAdditiveEncode state
  let tokens := frontTokens ++ stateTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let start := frontTokens.length
  let proofFinish := start + (compactAdditiveEncode proofTokens).length
  let certificateFinish := proofFinish +
    (compactAdditiveEncode certificateTokens).length
  let tasksFinish := certificateFinish +
    (compactAdditiveEncode tasks).length
  let valuesFinish := tasksFinish +
    (compactAdditiveEncode values).length
  let finish := start + stateTokens.length
  let afterProof := frontTokens ++ compactAdditiveEncode proofTokens
  let afterCertificate := afterProof ++
    compactAdditiveEncode certificateTokens
  let afterTasks := afterCertificate ++ compactAdditiveEncode tasks
  let afterValues := afterTasks ++ compactAdditiveEncode values
  have hstateTokens : stateTokens =
      compactAdditiveEncode proofTokens ++
      compactAdditiveEncode certificateTokens ++
      compactAdditiveEncode tasks ++
      compactAdditiveEncode values ++
      compactAdditiveEncode status := by
    change compactAdditiveEncode state = _
    rw [show state =
      (((proofTokens, certificateTokens), (tasks, values)), status) by rfl]
    simp only [compactAdditiveEncode_prod]
    simp [List.append_assoc]
  have hcommonTokens : tokens =
      frontTokens ++ compactAdditiveEncode proofTokens ++
      compactAdditiveEncode certificateTokens ++
      compactAdditiveEncode tasks ++
      compactAdditiveEncode values ++
      compactAdditiveEncode status ++ backTokens := by
    rw [show tokens = frontTokens ++ stateTokens ++ backTokens by rfl]
    rw [hstateTokens]
    simp [List.append_assoc]
  have hproofFull :
      frontTokens ++ compactAdditiveEncode proofTokens ++
        (compactAdditiveEncode certificateTokens ++
          compactAdditiveEncode tasks ++ compactAdditiveEncode values ++
          compactAdditiveEncode status ++ backTokens) = tokens := by
    simpa [List.append_assoc] using hcommonTokens.symm
  have hcertificateFull :
      afterProof ++ compactAdditiveEncode certificateTokens ++
        (compactAdditiveEncode tasks ++ compactAdditiveEncode values ++
          compactAdditiveEncode status ++ backTokens) = tokens := by
    simpa [afterProof, List.append_assoc] using hcommonTokens.symm
  have htasksFull :
      afterCertificate ++ compactAdditiveEncode tasks ++
        (compactAdditiveEncode values ++ compactAdditiveEncode status ++
          backTokens) = tokens := by
    simpa [afterCertificate, afterProof, List.append_assoc] using
      hcommonTokens.symm
  have hvaluesFull :
      afterTasks ++ compactAdditiveEncode values ++
        (compactAdditiveEncode status ++ backTokens) = tokens := by
    simpa [afterTasks, afterCertificate, afterProof,
      List.append_assoc] using hcommonTokens.symm
  have hstatusFull :
      afterValues ++ compactAdditiveEncode status ++ backTokens = tokens := by
    simpa [afterValues, afterTasks, afterCertificate, afterProof,
      List.append_assoc] using hcommonTokens.symm
  have hproofRaw := compactAdditiveNatListDirectLayout_canonical
    frontTokens proofTokens
      (compactAdditiveEncode certificateTokens ++
        compactAdditiveEncode tasks ++ compactAdditiveEncode values ++
        compactAdditiveEncode status ++ backTokens)
  have hcertificateRaw := compactAdditiveNatListDirectLayout_canonical
    afterProof certificateTokens
      (compactAdditiveEncode tasks ++ compactAdditiveEncode values ++
        compactAdditiveEncode status ++ backTokens)
  have htasksRaw := compactAdditiveStructuredListElementLayouts_canonical
    CompactNumericVerifierTaskDirectLayout
    compactNumericVerifierTaskDirectLayout_canonical
    afterCertificate tasks
      (compactAdditiveEncode values ++ compactAdditiveEncode status ++
        backTokens)
  have hvaluesRaw := compactAdditiveStructuredListElementLayouts_canonical
    CompactNumericChildResultDirectLayout
    compactNumericChildResultDirectLayout_canonical
    afterTasks values (compactAdditiveEncode status ++ backTokens)
  have hstatusRaw := compactAdditiveOptionBoolDirectLayout_canonical
    afterValues status backTokens
  dsimp only at hproofRaw hcertificateRaw htasksRaw hvaluesRaw hstatusRaw
  rw [hproofFull] at hproofRaw
  rw [hcertificateFull] at hcertificateRaw
  rw [htasksFull] at htasksRaw
  rw [hvaluesFull] at hvaluesRaw
  rw [hstatusFull] at hstatusRaw
  have hafterProof : afterProof.length = proofFinish := by
    simp [afterProof, proofFinish, start]
  have hafterCertificate : afterCertificate.length = certificateFinish := by
    dsimp only [afterCertificate, afterProof, certificateFinish,
      proofFinish, start]
    simp only [List.length_append]
  have hafterTasks : afterTasks.length = tasksFinish := by
    dsimp only [afterTasks, afterCertificate, afterProof, tasksFinish,
      certificateFinish, proofFinish, start]
    simp only [List.length_append]
  have hafterValues : afterValues.length = valuesFinish := by
    dsimp only [afterValues, afterTasks, afterCertificate, afterProof,
      valuesFinish, tasksFinish, certificateFinish, proofFinish, start]
    simp only [List.length_append]
  have hfinish : finish = valuesFinish +
      (compactAdditiveEncode status).length := by
    dsimp only [finish, valuesFinish, tasksFinish, certificateFinish,
      proofFinish, start]
    rw [hstateTokens]
    simp only [List.length_append]
    omega
  rcases htasksRaw with ⟨htasksLayout, htaskRows, htaskSize⟩
  rcases hvaluesRaw with ⟨hvaluesLayout, hvalueRows, hvalueSize⟩
  let taskBoundaryTable :=
    compactAdditiveStructuredListElementBoundaryTable
      tokens.length (certificateFinish + 1) tasks
  let valueBoundaryTable :=
    compactAdditiveStructuredListElementBoundaryTable
      tokens.length (tasksFinish + 1) values
  have hproof : CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      start proofFinish proofTokens := by
    simpa only [width, proofFinish] using hproofRaw
  have hcertificate : CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      proofFinish certificateFinish certificateTokens := by
    simpa only [width, hafterProof, certificateFinish] using hcertificateRaw
  have htasksLayout' : CompactAdditiveStructuredListLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      certificateFinish tasks.length tasksFinish taskBoundaryTable := by
    simpa only [width, hafterCertificate, taskBoundaryTable] using
      htasksLayout
  have htaskRows' : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      taskBoundaryTable tasks := by
    simpa only [width, hafterCertificate, taskBoundaryTable] using htaskRows
  have htaskSize' : Nat.size taskBoundaryTable ≤
      (tasks.length + 1) * tokens.length := by
    simpa only [hafterCertificate, taskBoundaryTable] using htaskSize
  have hvaluesLayout' : CompactAdditiveStructuredListLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      tasksFinish values.length valuesFinish valueBoundaryTable := by
    simpa only [width, hafterTasks, valueBoundaryTable] using hvaluesLayout
  have hvalueRows' : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      valueBoundaryTable values := by
    simpa only [width, hafterTasks, valueBoundaryTable] using hvalueRows
  have hvalueSize' : Nat.size valueBoundaryTable ≤
      (values.length + 1) * tokens.length := by
    simpa only [hafterTasks, valueBoundaryTable] using hvalueSize
  have hstatus : CompactAdditiveOptionBoolDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      valuesFinish finish status := by
    simpa only [width, hafterValues, hfinish] using hstatusRaw
  exact ⟨proofFinish, certificateFinish, tasksFinish, valuesFinish,
    taskBoundaryTable, valueBoundaryTable, hproof, hcertificate,
    htasksLayout', htaskRows', htaskSize', hvaluesLayout', hvalueRows',
    hvalueSize', hstatus⟩

def CompactNumericVerifierStateListDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (states : List CompactNumericVerifierState) : Prop :=
  ∃ boundaryTable,
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start states.length finish boundaryTable ∧
    CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierStateDirectLayout tokenTable width tokenCount
      boundaryTable states ∧
    Nat.size boundaryTable ≤ (states.length + 1) * tokenCount

theorem compactNumericVerifierStateListDirectLayout_canonical
    (frontTokens : List Nat) (states : List CompactNumericVerifierState)
    (backTokens : List Nat) :
    let stateTokens := compactAdditiveEncode states
    let tokens := frontTokens ++ stateTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + stateTokens.length
    CompactNumericVerifierStateListDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish states := by
  rcases compactAdditiveStructuredListElementLayouts_canonical
      CompactNumericVerifierStateDirectLayout
      compactNumericVerifierStateDirectLayout_canonical
      frontTokens states backTokens with
    ⟨hlayout, hrows, hsize⟩
  exact ⟨_, hlayout, hrows, hsize⟩

#print axioms compactAdditiveOptionBoolDirectLayout_canonical
#print axioms compactNumericVerifierStateDirectLayout_canonical
#print axioms compactNumericVerifierStateListDirectLayout_canonical

end FoundationCompactNumericListedDirectVerifierStateLayout
