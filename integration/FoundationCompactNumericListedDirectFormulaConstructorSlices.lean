import integration.FoundationCompactNumericListedDirectNatListListConsSlices
import integration.FoundationCompactNumericFormulaConstructors

/-!
# Direct bounded graphs for logical formula constructors

The unary and binary token constructors are exposed as Delta-zero slice
relations.  Their exactness theorems identify those relations with the actual
`tokenFormulaAnd`, `tokenFormulaOr`, `tokenFormulaAll`, and `tokenFormulaExs`
functions used by the public listed checker.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaConstructorSlices

open FoundationCompactNumericFormulaConstructors
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectNatListAppendSlices

def CompactAdditiveUnaryFormulaConstructorSlices
    (tokenTable width tokenCount tag
      bodyStart bodyFinish bodyCount
      targetStart targetFinish targetCount : Nat) : Prop :=
  targetCount = bodyCount + 1 ∧
    CompactFixedWidthEntry tokenTable width (targetStart + 1) tag ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      (bodyStart + 1) bodyFinish (targetStart + 2) targetFinish

def CompactAdditiveBinaryFormulaConstructorSlices
    (tokenTable width tokenCount tag
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat) : Prop :=
  targetCount = leftCount + rightCount + 1 ∧
    CompactFixedWidthEntry tokenTable width (targetStart + 1) tag ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      (leftStart + 1) leftFinish
      (targetStart + 2) (targetStart + 2 + leftCount) ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      (rightStart + 1) rightFinish
      (targetStart + 2 + leftCount) targetFinish

def compactAdditiveUnaryFormulaConstructorSlicesDef :
    𝚺₀.Semisentence 10 := .mkSigma
  “tokenTable width tokenCount tag
      bodyStart bodyFinish bodyCount
      targetStart targetFinish targetCount.
    targetCount = bodyCount + 1 ∧
    !(compactFixedWidthEntryDef)
      tokenTable width (targetStart + 1) tag ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
        (bodyStart + 1) bodyFinish (targetStart + 2) targetFinish”

def compactAdditiveBinaryFormulaConstructorSlicesDef :
    𝚺₀.Semisentence 13 := .mkSigma
  “tokenTable width tokenCount tag
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount.
    targetCount = leftCount + rightCount + 1 ∧
    !(compactFixedWidthEntryDef)
      tokenTable width (targetStart + 1) tag ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
        (leftStart + 1) leftFinish
        (targetStart + 2) (targetStart + 2 + leftCount) ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
        (rightStart + 1) rightFinish
        (targetStart + 2 + leftCount) targetFinish”

@[simp] theorem compactAdditiveUnaryFormulaConstructorSlicesDef_spec
    (tokenTable width tokenCount tag
      bodyStart bodyFinish bodyCount
      targetStart targetFinish targetCount : Nat) :
    compactAdditiveUnaryFormulaConstructorSlicesDef.val.Evalb
        ![tokenTable, width, tokenCount, tag,
          bodyStart, bodyFinish, bodyCount,
          targetStart, targetFinish, targetCount] ↔
      CompactAdditiveUnaryFormulaConstructorSlices
        tokenTable width tokenCount tag
          bodyStart bodyFinish bodyCount
          targetStart targetFinish targetCount := by
  have hhead :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount, tag,
                bodyStart, bodyFinish, bodyCount,
                targetStart, targetFinish, targetCount]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 10), #1, ‘(#7 + 1)’, #3])
          Empty.elim) compactFixedWidthEntryDef.val ↔
        CompactFixedWidthEntry tokenTable width (targetStart + 1) tag := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount, tag,
              bodyStart, bodyFinish, bodyCount,
              targetStart, targetFinish, targetCount]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 10), #1, ‘(#7 + 1)’, #3]) =
          ![tokenTable, width, targetStart + 1, tag] := by
      funext coordinate
      fin_cases coordinate <;> simp
    rw [henv]
    exact compactFixedWidthEntryDef_spec
      tokenTable width (targetStart + 1) tag
  have hbody :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount, tag,
                bodyStart, bodyFinish, bodyCount,
                targetStart, targetFinish, targetCount]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 10), #1, #2,
              ‘(#4 + 1)’, #5, ‘(#7 + 2)’, #8])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          (bodyStart + 1) bodyFinish (targetStart + 2) targetFinish := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount, tag,
              bodyStart, bodyFinish, bodyCount,
              targetStart, targetFinish, targetCount]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 10), #1, #2,
            ‘(#4 + 1)’, #5, ‘(#7 + 2)’, #8]) =
          ![tokenTable, width, tokenCount,
            bodyStart + 1, bodyFinish, targetStart + 2, targetFinish] := by
      funext coordinate
      fin_cases coordinate <;> simp
    rw [henv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount
        (bodyStart + 1) bodyFinish (targetStart + 2) targetFinish
  simp [compactAdditiveUnaryFormulaConstructorSlicesDef,
    CompactAdditiveUnaryFormulaConstructorSlices, hhead, hbody]

@[simp] theorem compactAdditiveBinaryFormulaConstructorSlicesDef_spec
    (tokenTable width tokenCount tag
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat) :
    compactAdditiveBinaryFormulaConstructorSlicesDef.val.Evalb
        ![tokenTable, width, tokenCount, tag,
          leftStart, leftFinish, leftCount,
          rightStart, rightFinish, rightCount,
          targetStart, targetFinish, targetCount] ↔
      CompactAdditiveBinaryFormulaConstructorSlices
        tokenTable width tokenCount tag
          leftStart leftFinish leftCount
          rightStart rightFinish rightCount
          targetStart targetFinish targetCount := by
  have hhead :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount, tag,
                leftStart, leftFinish, leftCount,
                rightStart, rightFinish, rightCount,
                targetStart, targetFinish, targetCount]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, ‘(#10 + 1)’, #3])
          Empty.elim) compactFixedWidthEntryDef.val ↔
        CompactFixedWidthEntry tokenTable width (targetStart + 1) tag := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount, tag,
              leftStart, leftFinish, leftCount,
              rightStart, rightFinish, rightCount,
              targetStart, targetFinish, targetCount]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, ‘(#10 + 1)’, #3]) =
          ![tokenTable, width, targetStart + 1, tag] := by
      funext coordinate
      fin_cases coordinate <;> simp
    rw [henv]
    exact compactFixedWidthEntryDef_spec
      tokenTable width (targetStart + 1) tag
  have hleft :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount, tag,
                leftStart, leftFinish, leftCount,
                rightStart, rightFinish, rightCount,
                targetStart, targetFinish, targetCount]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2,
              ‘(#4 + 1)’, #5, ‘(#10 + 2)’, ‘((#10 + 2) + #6)’])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          (leftStart + 1) leftFinish
          (targetStart + 2) (targetStart + 2 + leftCount) := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount, tag,
              leftStart, leftFinish, leftCount,
              rightStart, rightFinish, rightCount,
              targetStart, targetFinish, targetCount]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2,
            ‘(#4 + 1)’, #5, ‘(#10 + 2)’, ‘((#10 + 2) + #6)’]) =
          ![tokenTable, width, tokenCount,
            leftStart + 1, leftFinish,
            targetStart + 2, targetStart + 2 + leftCount] := by
      funext coordinate
      fin_cases coordinate <;> simp
    rw [henv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount
        (leftStart + 1) leftFinish
        (targetStart + 2) (targetStart + 2 + leftCount)
  have hright :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount, tag,
                leftStart, leftFinish, leftCount,
                rightStart, rightFinish, rightCount,
                targetStart, targetFinish, targetCount]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2,
              ‘(#7 + 1)’, #8, ‘((#10 + 2) + #6)’, #11])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          (rightStart + 1) rightFinish
          (targetStart + 2 + leftCount) targetFinish := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount, tag,
              leftStart, leftFinish, leftCount,
              rightStart, rightFinish, rightCount,
              targetStart, targetFinish, targetCount]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2,
            ‘(#7 + 1)’, #8, ‘((#10 + 2) + #6)’, #11]) =
          ![tokenTable, width, tokenCount,
            rightStart + 1, rightFinish,
            targetStart + 2 + leftCount, targetFinish] := by
      funext coordinate
      fin_cases coordinate <;> simp
    rw [henv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount
        (rightStart + 1) rightFinish
        (targetStart + 2 + leftCount) targetFinish
  simp [compactAdditiveBinaryFormulaConstructorSlicesDef,
    CompactAdditiveBinaryFormulaConstructorSlices, hhead, hleft, hright]

theorem compactAdditiveUnaryFormulaConstructorSlicesDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveUnaryFormulaConstructorSlicesDef.val := by
  simp [compactAdditiveUnaryFormulaConstructorSlicesDef]

theorem compactAdditiveBinaryFormulaConstructorSlicesDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveBinaryFormulaConstructorSlicesDef.val := by
  simp [compactAdditiveBinaryFormulaConstructorSlicesDef]

theorem compactAdditiveUnaryFormulaConstructorSlices_iff_cons
    {tokenTable width tokenCount tag
      bodyStart bodyFinish targetStart targetFinish : Nat}
    {body target : List Nat}
    (hbody : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      bodyStart bodyFinish body)
    (htarget : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      targetStart targetFinish target) :
    CompactAdditiveUnaryFormulaConstructorSlices
        tokenTable width tokenCount tag
          bodyStart bodyFinish body.length
          targetStart targetFinish target.length ↔
      target = tag :: body := by
  constructor
  · rintro ⟨hcount, hhead, hbodySlices⟩
    apply List.ext_getElem
    · simp
      omega
    · intro index htargetIndex hconsIndex
      cases index with
      | zero =>
          have htargetEntry :=
            CompactAdditiveNatListDirectLayout.valueEntry
              htarget 0 htargetIndex
          have hvalue : tag = target.getI 0 :=
            (CompactFixedWidthEntry.value_eq_tableValue hhead).trans
              (CompactFixedWidthEntry.value_eq_tableValue
                (by simpa using htargetEntry)).symm
          rw [List.getI_eq_getElem target htargetIndex] at hvalue
          simpa using hvalue.symm
      | succ index =>
          have hbodyIndex : index < body.length := by omega
          have hbodyEntry :=
            CompactAdditiveNatListDirectLayout.valueEntry
              hbody index hbodyIndex
          have htargetEntry :=
            CompactAdditiveNatListDirectLayout.valueEntry
              htarget (index + 1) htargetIndex
          have hvalue := CompactFixedWidthTokenSlicesEq.bodyValue_eq
            (sourceStart := bodyStart + 1)
            (sourceFinish := bodyFinish)
            (targetStart := targetStart + 2)
            (targetFinish := targetFinish)
            (offset := index)
            hbodySlices (by
              rw [CompactAdditiveNatListDirectLayout.finish_eq hbody]
              omega)
            (by simpa [Nat.add_assoc] using hbodyEntry)
            (by convert htargetEntry using 1 <;> omega)
          rw [List.getI_eq_getElem body hbodyIndex] at hvalue
          rw [List.getI_eq_getElem target htargetIndex] at hvalue
          simpa using hvalue.symm
  · intro htargetEq
    have hcount : target.length = body.length + 1 := by
      simp [htargetEq]
    have htargetZero : 0 < target.length := by omega
    have hheadRaw := CompactAdditiveNatListDirectLayout.valueEntry
      htarget 0 htargetZero
    have hhead : CompactFixedWidthEntry tokenTable width
        (targetStart + 1) tag := by
      simpa [htargetEq] using hheadRaw
    have hbodySlicesRaw :=
      CompactAdditiveNatListDirectLayout.bodySlicesEq
        (targetOffset := 1) hbody htarget
          (by simp [htargetEq]; omega) (by
            intro index hindex
            rw [htargetEq]
            simp [Nat.add_comm])
    have htargetFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq htarget
    have hbodySlices : CompactFixedWidthTokenSlicesEq
        tokenTable width tokenCount
          (bodyStart + 1) bodyFinish
          (targetStart + 2) targetFinish := by
      convert hbodySlicesRaw using 1 <;> omega
    exact ⟨hcount, hhead, hbodySlices⟩

theorem compactAdditiveBinaryFormulaConstructorSlices_iff_cons_append
    {tokenTable width tokenCount tag
      leftStart leftFinish rightStart rightFinish
      targetStart targetFinish : Nat}
    {left right target : List Nat}
    (hleft : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      leftStart leftFinish left)
    (hright : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      rightStart rightFinish right)
    (htarget : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      targetStart targetFinish target) :
    CompactAdditiveBinaryFormulaConstructorSlices
        tokenTable width tokenCount tag
          leftStart leftFinish left.length
          rightStart rightFinish right.length
          targetStart targetFinish target.length ↔
      target = tag :: (left ++ right) := by
  constructor
  · rintro ⟨hcount, hhead, hleftSlices, hrightSlices⟩
    apply List.ext_getElem
    · simp
      omega
    · intro index htargetIndex hconsIndex
      cases index with
      | zero =>
          have htargetEntry :=
            CompactAdditiveNatListDirectLayout.valueEntry
              htarget 0 htargetIndex
          have hvalue : tag = target.getI 0 :=
            (CompactFixedWidthEntry.value_eq_tableValue hhead).trans
              (CompactFixedWidthEntry.value_eq_tableValue
                (by simpa using htargetEntry)).symm
          rw [List.getI_eq_getElem target htargetIndex] at hvalue
          simpa using hvalue.symm
      | succ index =>
          by_cases hindex : index < left.length
          · have hleftEntry :=
              CompactAdditiveNatListDirectLayout.valueEntry
                hleft index hindex
            have htargetEntry :=
              CompactAdditiveNatListDirectLayout.valueEntry
                htarget (index + 1) htargetIndex
            have hvalue := CompactFixedWidthTokenSlicesEq.bodyValue_eq
              (sourceStart := leftStart + 1)
              (sourceFinish := leftFinish)
              (targetStart := targetStart + 2)
              (targetFinish := targetStart + 2 + left.length)
              (offset := index)
              hleftSlices (by
                rw [CompactAdditiveNatListDirectLayout.finish_eq hleft]
                omega)
              (by simpa [Nat.add_assoc] using hleftEntry)
              (by convert htargetEntry using 1 <;> omega)
            rw [List.getI_eq_getElem left hindex] at hvalue
            rw [List.getI_eq_getElem target htargetIndex] at hvalue
            simpa [List.getElem_append, hindex] using hvalue.symm
          · have hrightIndex : index - left.length < right.length := by
              omega
            have hrightEntry :=
              CompactAdditiveNatListDirectLayout.valueEntry
                hright (index - left.length) hrightIndex
            have htargetEntry :=
              CompactAdditiveNatListDirectLayout.valueEntry
                htarget (index + 1) htargetIndex
            have hvalue := CompactFixedWidthTokenSlicesEq.bodyValue_eq
              (sourceStart := rightStart + 1)
              (sourceFinish := rightFinish)
              (targetStart := targetStart + 2 + left.length)
              (targetFinish := targetFinish)
              (offset := index - left.length)
              hrightSlices (by
                rw [CompactAdditiveNatListDirectLayout.finish_eq hright]
                omega)
              (by simpa [Nat.add_assoc] using hrightEntry)
              (by
                have hindexEq :
                    left.length + (index - left.length) = index := by
                  omega
                convert htargetEntry using 1 <;> omega)
            rw [List.getI_eq_getElem right hrightIndex] at hvalue
            rw [List.getI_eq_getElem target htargetIndex] at hvalue
            have hleftLe : left.length <= index := Nat.le_of_not_gt hindex
            simpa [List.getElem_append, hindex, hleftLe] using hvalue.symm
  · intro htargetEq
    have hcount : target.length = left.length + right.length + 1 := by
      simp [htargetEq]
    have htargetZero : 0 < target.length := by omega
    have hheadRaw := CompactAdditiveNatListDirectLayout.valueEntry
      htarget 0 htargetZero
    have hhead : CompactFixedWidthEntry tokenTable width
        (targetStart + 1) tag := by
      simpa [htargetEq] using hheadRaw
    have hleftSlicesRaw :=
      CompactAdditiveNatListDirectLayout.bodySlicesEq
        (targetOffset := 1) hleft htarget
          (by simp [htargetEq]; omega) (by
            intro index hindex
            rw [htargetEq]
            simpa [Nat.add_comm] using
              (List.getI_append left right index hindex).symm)
    have hleftSlices : CompactFixedWidthTokenSlicesEq
        tokenTable width tokenCount
          (leftStart + 1) leftFinish
          (targetStart + 2) (targetStart + 2 + left.length) := by
      convert hleftSlicesRaw using 1 <;> omega
    have hrightSlicesRaw :=
      CompactAdditiveNatListDirectLayout.bodySlicesEq
        (targetOffset := 1 + left.length) hright htarget
          (by simp [htargetEq]; omega) (by
            intro index hindex
            rw [htargetEq]
            rw [show 1 + left.length + index =
              (left.length + index) + 1 by omega]
            change right.getI index =
              (left ++ right).getI (left.length + index)
            have happend := List.getI_append_right left right
              (left.length + index) (by omega)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              happend.symm)
    have htargetFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq htarget
    have hrightSlices : CompactFixedWidthTokenSlicesEq
        tokenTable width tokenCount
          (rightStart + 1) rightFinish
          (targetStart + 2 + left.length) targetFinish := by
      convert hrightSlicesRaw using 1 <;> omega
    exact ⟨hcount, hhead, hleftSlices, hrightSlices⟩

theorem compactAdditiveFormulaAndSlices_iff
    {tokenTable width tokenCount
      leftStart leftFinish rightStart rightFinish
      targetStart targetFinish : Nat}
    {left right target : List Nat}
    (hleft : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      leftStart leftFinish left)
    (hright : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      rightStart rightFinish right)
    (htarget : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      targetStart targetFinish target) :
    CompactAdditiveBinaryFormulaConstructorSlices
        tokenTable width tokenCount 4
          leftStart leftFinish left.length
          rightStart rightFinish right.length
          targetStart targetFinish target.length ↔
      target = tokenFormulaAnd left right := by
  simpa [tokenFormulaAnd] using
    compactAdditiveBinaryFormulaConstructorSlices_iff_cons_append
      hleft hright htarget (tag := 4)

theorem compactAdditiveFormulaOrSlices_iff
    {tokenTable width tokenCount
      leftStart leftFinish rightStart rightFinish
      targetStart targetFinish : Nat}
    {left right target : List Nat}
    (hleft : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      leftStart leftFinish left)
    (hright : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      rightStart rightFinish right)
    (htarget : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      targetStart targetFinish target) :
    CompactAdditiveBinaryFormulaConstructorSlices
        tokenTable width tokenCount 5
          leftStart leftFinish left.length
          rightStart rightFinish right.length
          targetStart targetFinish target.length ↔
      target = tokenFormulaOr left right := by
  simpa [tokenFormulaOr] using
    compactAdditiveBinaryFormulaConstructorSlices_iff_cons_append
      hleft hright htarget (tag := 5)

theorem compactAdditiveFormulaAllSlices_iff
    {tokenTable width tokenCount bodyStart bodyFinish
      targetStart targetFinish : Nat}
    {body target : List Nat}
    (hbody : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      bodyStart bodyFinish body)
    (htarget : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      targetStart targetFinish target) :
    CompactAdditiveUnaryFormulaConstructorSlices
        tokenTable width tokenCount 6
          bodyStart bodyFinish body.length
          targetStart targetFinish target.length ↔
      target = tokenFormulaAll body := by
  simpa [tokenFormulaAll] using
    compactAdditiveUnaryFormulaConstructorSlices_iff_cons
      hbody htarget (tag := 6)

theorem compactAdditiveFormulaExsSlices_iff
    {tokenTable width tokenCount bodyStart bodyFinish
      targetStart targetFinish : Nat}
    {body target : List Nat}
    (hbody : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      bodyStart bodyFinish body)
    (htarget : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      targetStart targetFinish target) :
    CompactAdditiveUnaryFormulaConstructorSlices
        tokenTable width tokenCount 7
          bodyStart bodyFinish body.length
          targetStart targetFinish target.length ↔
      target = tokenFormulaExs body := by
  simpa [tokenFormulaExs] using
    compactAdditiveUnaryFormulaConstructorSlices_iff_cons
      hbody htarget (tag := 7)

#print axioms compactAdditiveUnaryFormulaConstructorSlicesDef_spec
#print axioms compactAdditiveBinaryFormulaConstructorSlicesDef_spec
#print axioms compactAdditiveUnaryFormulaConstructorSlicesDef_sigmaZero
#print axioms compactAdditiveBinaryFormulaConstructorSlicesDef_sigmaZero
#print axioms compactAdditiveUnaryFormulaConstructorSlices_iff_cons
#print axioms compactAdditiveBinaryFormulaConstructorSlices_iff_cons_append
#print axioms compactAdditiveFormulaAndSlices_iff
#print axioms compactAdditiveFormulaOrSlices_iff
#print axioms compactAdditiveFormulaAllSlices_iff
#print axioms compactAdditiveFormulaExsSlices_iff

end FoundationCompactNumericListedDirectFormulaConstructorSlices
