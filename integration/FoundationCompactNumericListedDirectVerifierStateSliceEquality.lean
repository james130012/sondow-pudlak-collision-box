import integration.FoundationCompactNumericListedDirectVerifierTaskSliceEquality
import integration.FoundationCompactNumericListedDirectVerifierValueSliceEquality

/-!
# Complete same-table slice equality for verifier states

Two layouts of the same typed structured list have equal count headers and
equal element slices.  Applying this once to the verifier task stack and then
concatenating all five state components proves equality of two complete state
slices in one public token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStateSliceEquality

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectNatListSliceEquality
open FoundationCompactNumericListedDirectNatListListSliceEquality
open FoundationCompactNumericListedDirectVerifierTaskSliceEquality
open FoundationCompactNumericListedDirectVerifierValueSliceEquality

theorem CompactAdditiveStructuredListElementRowLayouts.slicesEq_of_eq
    {alpha : Type*} [Inhabited alpha]
    (ElementLayout : Nat -> Nat -> Nat -> Nat -> Nat -> alpha -> Prop)
    {tokenTable width tokenCount
      sourceStart sourceFinish sourceBoundary
      targetStart targetFinish targetBoundary : Nat}
    {sourceValues targetValues : List alpha}
    (hsourceLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount sourceStart sourceValues.length
        sourceFinish sourceBoundary)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      ElementLayout tokenTable width tokenCount sourceBoundary sourceValues)
    (htargetLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount targetStart targetValues.length
        targetFinish targetBoundary)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      ElementLayout tokenTable width tokenCount targetBoundary targetValues)
    (helement :
      forall {sourceElementStart sourceElementFinish
        targetElementStart targetElementFinish : Nat}
        {sourceValue targetValue : alpha},
        ElementLayout tokenTable width tokenCount
          sourceElementStart sourceElementFinish sourceValue ->
        ElementLayout tokenTable width tokenCount
          targetElementStart targetElementFinish targetValue ->
        sourceValue = targetValue ->
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          sourceElementStart sourceElementFinish
          targetElementStart targetElementFinish)
    (hvalues : sourceValues = targetValues) :
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish := by
  subst targetValues
  rcases hsourceLayout with
    ⟨sourceBodyStart, _hsourceBodyStart,
      sourceHeader, sourceBoundaries⟩
  rcases htargetLayout with
    ⟨targetBodyStart, _htargetBodyStart,
      targetHeader, targetBoundaries⟩
  have hheader : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount
      sourceStart sourceBodyStart targetStart targetBodyStart :=
    CompactAdditiveTokenCell.slicesEq_of_same_value
      sourceHeader.1 targetHeader.1
  let rec bodySlices
      (index : Nat) (hindex : index <= sourceValues.length)
      (sourceCursor targetCursor : Nat)
      (hsourceCursor : CompactFixedWidthEntry
        sourceBoundary tokenCount index sourceCursor)
      (htargetCursor : CompactFixedWidthEntry
        targetBoundary tokenCount index targetCursor) :
      CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
        sourceCursor sourceFinish targetCursor targetFinish := by
    by_cases hend : index = sourceValues.length
    · subst index
      have hsourceCursorFinish : sourceCursor = sourceFinish :=
        (CompactFixedWidthEntry.value_eq_tableValue hsourceCursor).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            sourceBoundaries.2.2.2.1).symm
      have htargetCursorFinish : targetCursor = targetFinish :=
        (CompactFixedWidthEntry.value_eq_tableValue htargetCursor).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            targetBoundaries.2.2.2.1).symm
      subst sourceCursor
      subst targetCursor
      exact ⟨0, by omega, by omega, by omega,
        sourceBoundaries.2.1, targetBoundaries.2.1,
        fun offset hoffset _bitIndex _hbitIndex => by omega⟩
    · have hrow : index < sourceValues.length := by omega
      rcases hsourceRows index hrow with
        ⟨sourceLeft, _hsourceLeft,
          sourceRight, _hsourceRight,
          hsourceLeftEntry, hsourceRightEntry, hsourceRow⟩
      rcases htargetRows index hrow with
        ⟨targetLeft, _htargetLeft,
          targetRight, _htargetRight,
          htargetLeftEntry, htargetRightEntry, htargetRow⟩
      have hsourceLeft : sourceCursor = sourceLeft :=
        (CompactFixedWidthEntry.value_eq_tableValue hsourceCursor).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hsourceLeftEntry).symm
      have htargetLeft : targetCursor = targetLeft :=
        (CompactFixedWidthEntry.value_eq_tableValue htargetCursor).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            htargetLeftEntry).symm
      subst sourceLeft
      subst targetLeft
      have hrowSlices : CompactFixedWidthTokenSlicesEq
          tokenTable width tokenCount
          sourceCursor sourceRight targetCursor targetRight :=
        helement hsourceRow htargetRow rfl
      have htail := bodySlices (index + 1) (by omega)
        sourceRight targetRight hsourceRightEntry htargetRightEntry
      exact CompactFixedWidthTokenSlicesEq.append hrowSlices htail
    termination_by sourceValues.length - index
  have hbody : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount
      sourceBodyStart sourceFinish targetBodyStart targetFinish :=
    bodySlices 0 (by omega) sourceBodyStart targetBodyStart
      sourceBoundaries.2.2.1 targetBoundaries.2.2.1
  exact CompactFixedWidthTokenSlicesEq.append hheader hbody

theorem CompactAdditiveOptionBoolDirectLayout.slicesEq_of_eq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat}
    {sourceStatus targetStatus : Option Bool}
    (hsource : CompactAdditiveOptionBoolDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceStatus)
    (htarget : CompactAdditiveOptionBoolDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetStatus)
    (hstatus : sourceStatus = targetStatus) :
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish := by
  subst targetStatus
  rcases hsource with
    ⟨sourceTag, sourcePayloadStart, hsourceOption, hsourceCase⟩
  rcases htarget with
    ⟨targetTag, targetPayloadStart, htargetOption, htargetCase⟩
  cases sourceStatus with
  | none =>
      rcases hsourceCase with hsourceNone | hsourceSome
      · rcases hsourceNone with
          ⟨_hsourceStatus, hsourceTagZero, hsourceFinish⟩
        rcases htargetCase with htargetNone | htargetSome
        · rcases htargetNone with
            ⟨_htargetStatus, htargetTagZero, htargetFinish⟩
          have htag : CompactFixedWidthTokenSlicesEq
              tokenTable width tokenCount sourceStart sourcePayloadStart
                targetStart targetPayloadStart :=
            CompactAdditiveTokenCell.slicesEq_of_same_value
              (by simpa only [hsourceTagZero] using hsourceOption.1)
              (by simpa only [htargetTagZero] using htargetOption.1)
          simpa only [hsourceFinish, htargetFinish] using htag
        · rcases htargetSome with
            ⟨result, htargetStatus, _htargetTag, _htargetBool⟩
          simp at htargetStatus
      · rcases hsourceSome with
          ⟨result, hsourceStatus, _hsourceTag, _hsourceBool⟩
        simp at hsourceStatus
  | some result =>
      rcases hsourceCase with hsourceNone | hsourceSome
      · rcases hsourceNone with
          ⟨hsourceStatus, _hsourceTag, _hsourceFinish⟩
        simp at hsourceStatus
      · rcases hsourceSome with
          ⟨sourceResult, hsourceStatus, hsourceTagOne, hsourceBool⟩
        have hsourceResult : sourceResult = result := by
          exact Option.some.inj hsourceStatus.symm
        subst sourceResult
        rcases htargetCase with htargetNone | htargetSome
        · rcases htargetNone with
            ⟨htargetStatus, _htargetTag, _htargetFinish⟩
          simp at htargetStatus
        · rcases htargetSome with
            ⟨targetResult, htargetStatus, htargetTagOne, htargetBool⟩
          have htargetResult : targetResult = result := by
            exact Option.some.inj htargetStatus.symm
          subst targetResult
          have htag : CompactFixedWidthTokenSlicesEq
              tokenTable width tokenCount sourceStart sourcePayloadStart
                targetStart targetPayloadStart :=
            CompactAdditiveTokenCell.slicesEq_of_same_value
              (by simpa only [hsourceTagOne] using hsourceOption.1)
              (by simpa only [htargetTagOne] using htargetOption.1)
          have hbool : CompactFixedWidthTokenSlicesEq
              tokenTable width tokenCount sourcePayloadStart sourceFinish
                targetPayloadStart targetFinish :=
            CompactAdditiveTokenCell.slicesEq_of_same_value
              hsourceBool.1 htargetBool.1
          exact CompactFixedWidthTokenSlicesEq.append htag hbool

theorem CompactNumericVerifierStateDirectLayout.slicesEq_of_eq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat}
    {sourceState targetState : CompactNumericVerifierState}
    (hsource : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceState)
    (htarget : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetState)
    (hstate : sourceState = targetState) :
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish := by
  subst targetState
  rcases hsource with
    ⟨sourceProofFinish, sourceCertificateFinish, sourceTasksFinish,
      sourceValuesFinish, sourceTaskBoundary, sourceValueBoundary,
      hsourceProof, hsourceCertificate,
      hsourceTasks, hsourceTaskRows, _hsourceTaskSize,
      hsourceValues, hsourceValueRows, hsourceValueSize,
      hsourceStatus⟩
  rcases htarget with
    ⟨targetProofFinish, targetCertificateFinish, targetTasksFinish,
      targetValuesFinish, targetTaskBoundary, targetValueBoundary,
      htargetProof, htargetCertificate,
      htargetTasks, htargetTaskRows, _htargetTaskSize,
      htargetValues, htargetValueRows, htargetValueSize,
      htargetStatus⟩
  have hproof := CompactAdditiveNatListDirectLayout.slicesEq_of_eq
    hsourceProof htargetProof rfl
  have hcertificate := CompactAdditiveNatListDirectLayout.slicesEq_of_eq
    hsourceCertificate htargetCertificate rfl
  have htasks :=
    CompactAdditiveStructuredListElementRowLayouts.slicesEq_of_eq
      CompactNumericVerifierTaskDirectLayout
      hsourceTasks hsourceTaskRows htargetTasks htargetTaskRows
      (fun hleft hright heq =>
        CompactNumericVerifierTaskDirectLayout.slicesEq_of_eq
          hleft hright heq)
      rfl
  have hsourceValuesDirect : CompactNumericChildResultListDirectLayout
      tokenTable width tokenCount sourceTasksFinish sourceValuesFinish
        sourceState.1.2.2 :=
    ⟨sourceValueBoundary, hsourceValues, hsourceValueRows,
      hsourceValueSize⟩
  have htargetValuesDirect : CompactNumericChildResultListDirectLayout
      tokenTable width tokenCount targetTasksFinish targetValuesFinish
        sourceState.1.2.2 :=
    ⟨targetValueBoundary, htargetValues, htargetValueRows,
      htargetValueSize⟩
  have hvalues := CompactNumericChildResultListDirectLayout.slicesEq_of_eq
    hsourceValuesDirect htargetValuesDirect rfl
  have hstatus := CompactAdditiveOptionBoolDirectLayout.slicesEq_of_eq
    hsourceStatus htargetStatus rfl
  exact CompactFixedWidthTokenSlicesEq.append hproof <|
    CompactFixedWidthTokenSlicesEq.append hcertificate <|
      CompactFixedWidthTokenSlicesEq.append htasks <|
        CompactFixedWidthTokenSlicesEq.append hvalues hstatus

#print axioms
  CompactAdditiveStructuredListElementRowLayouts.slicesEq_of_eq
#print axioms CompactAdditiveOptionBoolDirectLayout.slicesEq_of_eq
#print axioms CompactNumericVerifierStateDirectLayout.slicesEq_of_eq

end FoundationCompactNumericListedDirectVerifierStateSliceEquality
