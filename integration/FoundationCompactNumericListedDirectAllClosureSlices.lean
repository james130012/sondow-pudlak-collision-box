import integration.FoundationCompactNumericAllClosure
import integration.FoundationCompactNumericListedDirectFormulaConstructorSlices

/-!
# Direct bounded slices for iterated universal closure

The target consists of exactly `depth` universal-quantifier tags followed by
an unchanged copy of the source formula tokens.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectAllClosureSlices

open FoundationCompactNumericAllClosure
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectNatListAppendSlices

def CompactAdditiveAllClosureSlices
    (tokenTable width tokenCount depth
      bodyStart bodyFinish bodyCount
      targetStart targetFinish targetCount : Nat) : Prop :=
  targetCount = depth + bodyCount /\
    (forall index, index < depth ->
      CompactFixedWidthEntry
        tokenTable width (targetStart + 1 + index) 6) /\
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      (bodyStart + 1) bodyFinish
      (targetStart + 1 + depth) targetFinish

def compactAdditiveAllClosureSlicesDef :
    𝚺₀.Semisentence 10 := .mkSigma
  “tokenTable width tokenCount depth
      bodyStart bodyFinish bodyCount
      targetStart targetFinish targetCount.
    targetCount = depth + bodyCount ∧
    (∀ index < depth,
      !(compactFixedWidthEntryDef)
        tokenTable width (targetStart + 1 + index) 6) ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
        (bodyStart + 1) bodyFinish
        (targetStart + 1 + depth) targetFinish”

@[simp] theorem compactAdditiveAllClosureSlicesDef_spec
    (tokenTable width tokenCount depth
      bodyStart bodyFinish bodyCount
      targetStart targetFinish targetCount : Nat) :
    compactAdditiveAllClosureSlicesDef.val.Evalb
        ![tokenTable, width, tokenCount, depth,
          bodyStart, bodyFinish, bodyCount,
          targetStart, targetFinish, targetCount] ↔
      CompactAdditiveAllClosureSlices
        tokenTable width tokenCount depth
        bodyStart bodyFinish bodyCount
        targetStart targetFinish targetCount := by
  have hprefix (index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![index, tokenTable, width, tokenCount, depth,
                bodyStart, bodyFinish, bodyCount,
                targetStart, targetFinish, targetCount]
              Empty.elim ∘
            ![(#1 : Semiterm ℒₒᵣ Empty 11), #2,
              ‘((#8 + 1) + #0)’, ‘6’])
          Empty.elim) compactFixedWidthEntryDef.val ↔
        CompactFixedWidthEntry
          tokenTable width (targetStart + 1 + index) 6 := by
    have henv :
        (Semiterm.val
            ![index, tokenTable, width, tokenCount, depth,
              bodyStart, bodyFinish, bodyCount,
              targetStart, targetFinish, targetCount]
            Empty.elim ∘
          ![(#1 : Semiterm ℒₒᵣ Empty 11), #2,
            ‘((#8 + 1) + #0)’, ‘6’]) =
          ![tokenTable, width, targetStart + 1 + index, 6] := by
      funext coordinate
      fin_cases coordinate <;> simp
    rw [henv]
    exact compactFixedWidthEntryDef_spec
      tokenTable width (targetStart + 1 + index) 6
  have hbody :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount, depth,
                bodyStart, bodyFinish, bodyCount,
                targetStart, targetFinish, targetCount]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 10), #1, #2,
              ‘(#4 + 1)’, #5, ‘((#7 + 1) + #3)’, #8])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          (bodyStart + 1) bodyFinish
          (targetStart + 1 + depth) targetFinish := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount, depth,
              bodyStart, bodyFinish, bodyCount,
              targetStart, targetFinish, targetCount]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 10), #1, #2,
            ‘(#4 + 1)’, #5, ‘((#7 + 1) + #3)’, #8]) =
          ![tokenTable, width, tokenCount,
            bodyStart + 1, bodyFinish,
            targetStart + 1 + depth, targetFinish] := by
      funext coordinate
      fin_cases coordinate <;> simp
    rw [henv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount
      (bodyStart + 1) bodyFinish
      (targetStart + 1 + depth) targetFinish
  simp [compactAdditiveAllClosureSlicesDef,
    CompactAdditiveAllClosureSlices, hprefix, hbody]

theorem compactAdditiveAllClosureSlicesDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveAllClosureSlicesDef.val := by
  simp [compactAdditiveAllClosureSlicesDef]

theorem compactAllClosureTokens_eq_replicate
    (depth : Nat) (body : List Nat) :
    compactAllClosureTokens depth body =
      List.replicate depth 6 ++ body := by
  induction depth generalizing body with
  | zero => rfl
  | succ depth ih =>
      calc
        compactAllClosureTokens (depth + 1) body =
            compactAllClosureTokens depth
              (compactAllClosureTokenStep body) := by
          simp [compactAllClosureTokens, Function.iterate_succ_apply]
        _ = List.replicate depth 6 ++ (6 :: body) := by
          simpa [compactAllClosureTokenStep] using ih (6 :: body)
        _ = List.replicate (depth + 1) 6 ++ body := by
          simp [List.replicate_succ', List.append_assoc]

theorem compactAdditiveAllClosureSlices_iff
    {tokenTable width tokenCount depth
      bodyStart bodyFinish targetStart targetFinish : Nat}
    {body target : List Nat}
    (hbody : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount bodyStart bodyFinish body)
    (htarget : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount targetStart targetFinish target) :
    CompactAdditiveAllClosureSlices
        tokenTable width tokenCount depth
        bodyStart bodyFinish body.length
        targetStart targetFinish target.length ↔
      target = compactAllClosureTokens depth body := by
  rw [compactAllClosureTokens_eq_replicate]
  constructor
  · rintro ⟨hcount, hprefix, hbodySlices⟩
    apply List.ext_getElem
    · simp
      omega
    · intro index htargetIndex hexpectedIndex
      by_cases hindex : index < depth
      · have htargetEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            htarget index htargetIndex
        have hvalue : 6 = target.getI index :=
          (CompactFixedWidthEntry.value_eq_tableValue
            (hprefix index hindex)).trans
            (CompactFixedWidthEntry.value_eq_tableValue
              (by convert htargetEntry using 1 <;> omega)).symm
        rw [List.getI_eq_getElem target htargetIndex] at hvalue
        simpa [List.getElem_append, hindex] using hvalue.symm
      · have hbodyIndex : index - depth < body.length := by omega
        have hbodyEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            hbody (index - depth) hbodyIndex
        have htargetEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            htarget index htargetIndex
        have hvalue := CompactFixedWidthTokenSlicesEq.bodyValue_eq
          (sourceStart := bodyStart + 1)
          (sourceFinish := bodyFinish)
          (targetStart := targetStart + 1 + depth)
          (targetFinish := targetFinish)
          (offset := index - depth)
          hbodySlices (by
            rw [CompactAdditiveNatListDirectLayout.finish_eq hbody]
            omega)
          (by simpa [Nat.add_assoc] using hbodyEntry)
          (by convert htargetEntry using 1 <;> omega)
        rw [List.getI_eq_getElem body hbodyIndex] at hvalue
        rw [List.getI_eq_getElem target htargetIndex] at hvalue
        have hdepthLe : depth <= index := Nat.le_of_not_gt hindex
        simpa [List.getElem_append, hindex, hdepthLe] using hvalue.symm
  · intro htargetEq
    have hcount : target.length = depth + body.length := by
      simp [htargetEq]
    have hprefix : forall index, index < depth ->
        CompactFixedWidthEntry
          tokenTable width (targetStart + 1 + index) 6 := by
      intro index hindex
      have htargetIndex : index < target.length := by omega
      have htargetEntry :=
        CompactAdditiveNatListDirectLayout.valueEntry
          htarget index htargetIndex
      have htargetValue : target.getI index = 6 := by
        rw [htargetEq]
        rw [List.getI_append (List.replicate depth 6) body index
          (by simpa using hindex)]
        rw [List.getI_eq_getElem (List.replicate depth 6)
          (by simpa using hindex)]
        simp
      rw [htargetValue] at htargetEntry
      exact htargetEntry
    have hbodySlicesRaw :=
      CompactAdditiveNatListDirectLayout.bodySlicesEq
        (targetOffset := depth) hbody htarget
          (by simp [htargetEq]) (by
            intro index hindex
            rw [htargetEq]
            have hdepthIndex : depth <= depth + index := Nat.le_add_right _ _
            rw [List.getI_append_right (List.replicate depth 6) body
              (depth + index) (by simp)]
            simp [Nat.add_sub_cancel_left])
    have hbodySlices : CompactFixedWidthTokenSlicesEq
        tokenTable width tokenCount
          (bodyStart + 1) bodyFinish
          (targetStart + 1 + depth) targetFinish := by
      have htargetFinish :=
        CompactAdditiveNatListDirectLayout.finish_eq htarget
      convert hbodySlicesRaw using 1 <;> omega
    exact ⟨hcount, hprefix, hbodySlices⟩

#print axioms compactAdditiveAllClosureSlicesDef_spec
#print axioms compactAdditiveAllClosureSlicesDef_sigmaZero
#print axioms compactAllClosureTokens_eq_replicate
#print axioms compactAdditiveAllClosureSlices_iff

end FoundationCompactNumericListedDirectAllClosureSlices
