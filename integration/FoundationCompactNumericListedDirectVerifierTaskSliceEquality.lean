import integration.FoundationCompactNumericListedDirectNatListListSliceEquality
import integration.FoundationCompactNumericListedDirectVerifierTaskLayout

/-!
# Equality of complete direct verifier-task slices

A verifier task consists of one tag cell followed by five list fields.  Equal
typed tasks therefore have equal complete token slices in any two valid
layouts over the same public token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTaskSliceEquality

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectNatListSliceEquality
open FoundationCompactNumericListedDirectNatListListSliceEquality

theorem CompactNumericNodeFieldsDirectLayout.slicesEq_of_eq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat}
    {sourceFields targetFields : CompactNumericNodeFields}
    (hsource : CompactNumericNodeFieldsDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceFields)
    (htarget : CompactNumericNodeFieldsDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetFields)
    (hfields : sourceFields = targetFields) :
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish := by
  subst targetFields
  rcases hsource with
    ⟨sourceGammaFinish, sourceFirstFinish,
      sourceSecondFinish, sourceWitnessFinish,
      hsourceGamma, hsourceFirst, hsourceSecond,
      hsourceWitness, hsourceSuffix⟩
  rcases htarget with
    ⟨targetGammaFinish, targetFirstFinish,
      targetSecondFinish, targetWitnessFinish,
      htargetGamma, htargetFirst, htargetSecond,
      htargetWitness, htargetSuffix⟩
  have hgamma :=
    CompactAdditiveNatListListDirectLayout.slicesEq_of_eq
      hsourceGamma htargetGamma rfl
  have hfirst := CompactAdditiveNatListDirectLayout.slicesEq_of_eq
    hsourceFirst htargetFirst rfl
  have hsecond := CompactAdditiveNatListDirectLayout.slicesEq_of_eq
    hsourceSecond htargetSecond rfl
  have hwitness := CompactAdditiveNatListDirectLayout.slicesEq_of_eq
    hsourceWitness htargetWitness rfl
  have hsuffix := CompactAdditiveNatListDirectLayout.slicesEq_of_eq
    hsourceSuffix htargetSuffix rfl
  exact CompactFixedWidthTokenSlicesEq.append hgamma <|
    CompactFixedWidthTokenSlicesEq.append hfirst <|
      CompactFixedWidthTokenSlicesEq.append hsecond <|
        CompactFixedWidthTokenSlicesEq.append hwitness hsuffix

theorem CompactNumericVerifierTaskDirectLayout.slicesEq_of_eq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat}
    {sourceTask targetTask : CompactNumericVerifierTask}
    (hsource : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceTask)
    (htarget : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetTask)
    (htask : sourceTask = targetTask) :
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish := by
  subst targetTask
  rcases hsource with
    ⟨sourceFieldsStart, hsourceTag, hsourceFields⟩
  rcases htarget with
    ⟨targetFieldsStart, htargetTag, htargetFields⟩
  have htag := CompactAdditiveTokenCell.slicesEq_of_same_value
    hsourceTag htargetTag
  have hfields := CompactNumericNodeFieldsDirectLayout.slicesEq_of_eq
    hsourceFields htargetFields rfl
  exact CompactFixedWidthTokenSlicesEq.append htag hfields

#print axioms CompactNumericNodeFieldsDirectLayout.slicesEq_of_eq
#print axioms CompactNumericVerifierTaskDirectLayout.slicesEq_of_eq

end FoundationCompactNumericListedDirectVerifierTaskSliceEquality
