import integration.FoundationCompactNumericListedDirectNatListAppendTwoValues

/-!
# Bounded append of one explicit natural value

The target preserves every source row and adds one explicitly checked final
row.  Under exact direct layouts this is precisely
`target = source ++ [value]`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListAppendOneValue

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAtRows

def CompactAdditiveNatListAppendOneValue
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value : Nat) : Prop :=
  targetFinish = targetStart + 1 + targetCount ∧
    targetCount = sourceCount + 1 ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      (sourceStart + 1) sourceFinish
      (targetStart + 1) (targetStart + 1 + sourceCount) ∧
    CompactAdditiveNatListAtRows tokenTable width tokenCount
      targetBoundary targetCount sourceCount value

def compactAdditiveNatListAppendOneValueDef :
    𝚺₀.Semisentence 11 := .mkSigma
  “tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value.
    targetFinish = targetStart + 1 + targetCount ∧
    targetCount = sourceCount + 1 ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
        (sourceStart + 1) sourceFinish
        (targetStart + 1) (targetStart + 1 + sourceCount) ∧
    !(compactAdditiveNatListAtRowsDef)
      tokenTable width tokenCount targetBoundary targetCount
        sourceCount value”

@[simp] theorem compactAdditiveNatListAppendOneValueDef_spec
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount value : Nat) :
    compactAdditiveNatListAppendOneValueDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceStart, sourceFinish, sourceCount,
          targetStart, targetFinish, targetBoundary, targetCount, value] ↔
      CompactAdditiveNatListAppendOneValue tokenTable width tokenCount
        sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount value := by
  let env : Fin 11 → Nat :=
    ![tokenTable, width, tokenCount,
      sourceStart, sourceFinish, sourceCount,
      targetStart, targetFinish, targetBoundary, targetCount, value]
  change compactAdditiveNatListAppendOneValueDef.val.Evalb env ↔ _
  have hslicesEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 11), #1, #2,
          ‘(#3 + 1)’, #4, ‘(#6 + 1)’, ‘((#6 + 1) + #5)’]) =
        ![tokenTable, width, tokenCount,
          sourceStart + 1, sourceFinish,
          targetStart + 1, targetStart + 1 + sourceCount] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  have hvalueEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 11), #1, #2,
          #8, #9, #5, #10]) =
        ![tokenTable, width, tokenCount,
          targetBoundary, targetCount, sourceCount, value] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hvalueSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 11), #1, #2,
              #8, #9, #5, #10])
          Empty.elim) compactAdditiveNatListAtRowsDef.val ↔
        CompactAdditiveNatListAtRows tokenTable width tokenCount
          targetBoundary targetCount sourceCount value := by
    rw [hvalueEnv]
    exact compactAdditiveNatListAtRowsDef_spec
      tokenTable width tokenCount targetBoundary targetCount sourceCount value
  simp [compactAdditiveNatListAppendOneValueDef,
    CompactAdditiveNatListAppendOneValue,
    hslicesEnv, hvalueSpec, env]

theorem compactAdditiveNatListAppendOneValueDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveNatListAppendOneValueDef.val := by
  simp [compactAdditiveNatListAppendOneValueDef]

theorem compactAdditiveNatListAppendOneValue_iff
    {tokenTable width tokenCount sourceStart sourceFinish
      targetStart targetFinish targetBoundary value : Nat}
    {source target : List Nat}
    (hsource : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      sourceStart sourceFinish source)
    (htarget : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      targetStart targetFinish target)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    CompactAdditiveNatListAppendOneValue tokenTable width tokenCount
        sourceStart sourceFinish source.length
        targetStart targetFinish targetBoundary target.length value ↔
      target = source ++ [value] := by
  constructor
  · rintro ⟨_htargetFinish, hcount, hslices, hvalueRows⟩
    have hsourceFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq hsource
    have hvalue :=
      (compactAdditiveNatListAtRows_iff_getI
        htargetRows source.length value).mp hvalueRows
    apply List.ext_getElem
    · simpa using hcount
    · intro index htargetIndex happendIndex
      by_cases hindex : index < source.length
      · have hsourceEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry hsource index hindex
        have htargetEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            htarget index htargetIndex
        have hsame := CompactFixedWidthTokenSlicesEq.bodyValue_eq
          (sourceStart := sourceStart + 1)
          (sourceFinish := sourceFinish)
          (targetStart := targetStart + 1)
          (targetFinish := targetStart + 1 + source.length)
          (offset := index) hslices (by omega)
          (by simpa [Nat.add_assoc] using hsourceEntry)
          (by simpa [Nat.add_assoc] using htargetEntry)
        rw [List.getI_eq_getElem source hindex] at hsame
        rw [List.getI_eq_getElem target htargetIndex] at hsame
        simpa [List.getElem_append, hindex] using hsame.symm
      · have hindexEq : index = source.length := by omega
        subst index
        have hvalueEq := hvalue.2
        rw [List.getI_eq_getElem target htargetIndex] at hvalueEq
        simpa using hvalueEq
  · intro htargetEq
    have hslices :=
      CompactAdditiveNatListDirectLayout.bodySlicesEq
        (targetOffset := 0) hsource htarget
        (by simp [htargetEq]) (by
          intro index hindex
          rw [htargetEq]
          rw [List.getI_eq_getElem source hindex]
          rw [List.getI_eq_getElem (source ++ [value]) (by simp; omega)]
          simp [List.getElem_append, hindex])
    have hvalueRows : CompactAdditiveNatListAtRows
        tokenTable width tokenCount targetBoundary target.length
          source.length value :=
      (compactAdditiveNatListAtRows_iff_getI
        htargetRows source.length value).mpr (by
          rw [htargetEq]
          refine ⟨by simp, ?_⟩
          simpa using
            (List.getI_append_right source [value]
              source.length (by omega)))
    have htargetFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq htarget
    exact ⟨htargetFinish, by simp [htargetEq], hslices, hvalueRows⟩

#print axioms compactAdditiveNatListAppendOneValueDef_spec
#print axioms compactAdditiveNatListAppendOneValueDef_sigmaZero
#print axioms compactAdditiveNatListAppendOneValue_iff

end FoundationCompactNumericListedDirectNatListAppendOneValue
