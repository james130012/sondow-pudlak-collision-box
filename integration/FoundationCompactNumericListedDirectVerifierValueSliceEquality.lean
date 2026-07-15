import integration.FoundationCompactNumericListedDirectNatListListSliceEquality
import integration.FoundationCompactNumericListedDirectVerifierValueLayouts
import integration.FoundationCompactNumericListedDirectVerifierPayloadEquality

/-!
# Complete token-slice equality for verifier child-result values

Equal typed child results have equal nested-formula and Boolean slices.  Equal
lists then concatenate these element equalities behind their common count
header.  These constructors expose no equality witness as an input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierValueSliceEquality

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectNatListListSliceEquality

def CompactNumericChildResultListDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (values : List CompactNumericChildResult) : Prop :=
  ∃ boundaryTable,
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start values.length finish boundaryTable ∧
    CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        boundaryTable values ∧
    Nat.size boundaryTable ≤ (values.length + 1) * tokenCount

theorem CompactAdditiveStructuredListLayout.emptySlicesEq
    {tokenTable width tokenCount
      sourceStart sourceFinish sourceBoundary
      targetStart targetFinish targetBoundary : Nat}
    (hsource : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount sourceStart 0 sourceFinish sourceBoundary)
    (htarget : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount targetStart 0 targetFinish targetBoundary) :
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish := by
  have hsourceFinish :=
    CompactAdditiveStructuredListLayout.finish_eq_start_add_one_of_count_zero
      hsource
  have htargetFinish :=
    CompactAdditiveStructuredListLayout.finish_eq_start_add_one_of_count_zero
      htarget
  rcases hsource with
    ⟨sourceBodyStart, _hsourceBodyStart, sourceHeader, _hsourceBoundaries⟩
  rcases htarget with
    ⟨targetBodyStart, _htargetBodyStart, targetHeader, _htargetBoundaries⟩
  have hheader := CompactAdditiveTokenCell.slicesEq_of_same_value
    sourceHeader.1 targetHeader.1
  have hsourceBody : sourceBodyStart = sourceStart + 1 :=
    sourceHeader.1.2.1
  have htargetBody : targetBodyStart = targetStart + 1 :=
    targetHeader.1.2.1
  simpa only [hsourceFinish, htargetFinish,
    hsourceBody, htargetBody] using hheader

theorem CompactNumericChildResultDirectLayout.slicesEq_of_eq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat}
    {sourceValue targetValue : CompactNumericChildResult}
    (hsource : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceValue)
    (htarget : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetValue)
    (hvalue : sourceValue = targetValue) :
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish := by
  subst targetValue
  rcases hsource with
    ⟨sourceGammaFinish, sourceGammaBoundary, sourceBoolValue,
      _hsourceProduct, hsourceGammaLayout, hsourceGammaRows,
      hsourceBoolValue, hsourceBool, hsourceGammaSize⟩
  rcases htarget with
    ⟨targetGammaFinish, targetGammaBoundary, targetBoolValue,
      _htargetProduct, htargetGammaLayout, htargetGammaRows,
      htargetBoolValue, htargetBool, htargetGammaSize⟩
  have hsourceGamma : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount sourceStart sourceGammaFinish
        sourceValue.1 :=
    ⟨sourceGammaBoundary, hsourceGammaLayout,
      hsourceGammaRows, hsourceGammaSize⟩
  have htargetGamma : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount targetStart targetGammaFinish
        sourceValue.1 :=
    ⟨targetGammaBoundary, htargetGammaLayout,
      htargetGammaRows, htargetGammaSize⟩
  have hgamma : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount
      sourceStart sourceGammaFinish targetStart targetGammaFinish :=
    CompactAdditiveNatListListDirectLayout.slicesEq_of_eq
      hsourceGamma htargetGamma rfl
  have hsourceBool' : CompactAdditiveBoolSlice
      tokenTable width tokenCount sourceGammaFinish
        (compactAdditiveBoolTag sourceValue.2) sourceFinish := by
    simpa only [hsourceBoolValue] using hsourceBool
  have htargetBool' : CompactAdditiveBoolSlice
      tokenTable width tokenCount targetGammaFinish
        (compactAdditiveBoolTag sourceValue.2) targetFinish := by
    simpa only [htargetBoolValue] using htargetBool
  have hbool : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount sourceGammaFinish sourceFinish
        targetGammaFinish targetFinish :=
    CompactAdditiveTokenCell.slicesEq_of_same_value
      hsourceBool'.1 htargetBool'.1
  exact CompactFixedWidthTokenSlicesEq.append hgamma hbool

theorem CompactNumericChildResultListDirectLayout.slicesEq_of_eq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat}
    {sourceValues targetValues : List CompactNumericChildResult}
    (hsource : CompactNumericChildResultListDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceValues)
    (htarget : CompactNumericChildResultListDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetValues)
    (hvalues : sourceValues = targetValues) :
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish := by
  subst targetValues
  rcases hsource with
    ⟨sourceBoundary, sourceLayout, sourceRows, _hsourceSize⟩
  rcases htarget with
    ⟨targetBoundary, targetLayout, targetRows, _htargetSize⟩
  rcases sourceLayout with
    ⟨sourceBodyStart, _hsourceBodyStart,
      sourceHeader, sourceBoundaries⟩
  rcases targetLayout with
    ⟨targetBodyStart, _htargetBodyStart,
      targetHeader, targetBoundaries⟩
  have hheader : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount
      sourceStart sourceBodyStart targetStart targetBodyStart :=
    CompactAdditiveTokenCell.slicesEq_of_same_value
      sourceHeader.1 targetHeader.1
  let rec bodySlices
      (index : Nat) (hindex : index ≤ sourceValues.length)
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
      rcases sourceRows index hrow with
        ⟨sourceLeft, _hsourceLeft,
          sourceRight, _hsourceRight,
          hsourceLeftEntry, hsourceRightEntry, hsourceRow⟩
      rcases targetRows index hrow with
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
        CompactNumericChildResultDirectLayout.slicesEq_of_eq
          hsourceRow htargetRow rfl
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

#print axioms CompactNumericChildResultDirectLayout.slicesEq_of_eq
#print axioms CompactNumericChildResultListDirectLayout.slicesEq_of_eq
#print axioms CompactAdditiveStructuredListLayout.emptySlicesEq

end FoundationCompactNumericListedDirectVerifierValueSliceEquality
