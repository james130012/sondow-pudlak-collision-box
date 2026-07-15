import integration.FoundationCompactNumericListedDirectVerumRuleCheck

/-!
# Direct equality of two lists of natural-number lists

Equal outer counts and exact equality of each nested token slice are
equivalent to equality of the represented nested lists.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListListSameRows

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectNatListSliceEquality

def CompactAdditiveNatListListSameRows
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount : Nat) : Prop :=
  targetCount = sourceCount ∧
    forall index, index < sourceCount ->
      exists sourceStart, sourceStart <= tokenCount ∧
      exists sourceFinish, sourceFinish <= tokenCount ∧
      exists targetStart, targetStart <= tokenCount ∧
      exists targetFinish, targetFinish <= tokenCount ∧
        CompactFixedWidthEntry sourceBoundary tokenCount index sourceStart ∧
        CompactFixedWidthEntry sourceBoundary tokenCount
          (index + 1) sourceFinish ∧
        CompactFixedWidthEntry targetBoundary tokenCount index targetStart ∧
        CompactFixedWidthEntry targetBoundary tokenCount
          (index + 1) targetFinish ∧
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          sourceStart sourceFinish targetStart targetFinish

def compactAdditiveNatListListSameRowsDef :
    𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount.
    targetCount = sourceCount ∧
    ∀ index < sourceCount,
      ∃ sourceStart <⁺ tokenCount,
        ∃ sourceFinish <⁺ tokenCount,
          ∃ targetStart <⁺ tokenCount,
            ∃ targetFinish <⁺ tokenCount,
              !(compactFixedWidthEntryDef)
                sourceBoundary tokenCount index sourceStart ∧
              !(compactFixedWidthEntryDef)
                sourceBoundary tokenCount (index + 1) sourceFinish ∧
              !(compactFixedWidthEntryDef)
                targetBoundary tokenCount index targetStart ∧
              !(compactFixedWidthEntryDef)
                targetBoundary tokenCount (index + 1) targetFinish ∧
              !(compactFixedWidthTokenSlicesEqDef)
                tokenTable width tokenCount
                  sourceStart sourceFinish targetStart targetFinish”

@[simp] theorem compactAdditiveNatListListSameRowsDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount : Nat) :
    compactAdditiveNatListListSameRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount] ↔
      CompactAdditiveNatListListSameRows tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount := by
  have hslices
      (targetFinish targetStart sourceFinish sourceStart index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![targetFinish, targetStart, sourceFinish, sourceStart, index,
                tokenTable, width, tokenCount,
                sourceBoundary, sourceCount, targetBoundary, targetCount]
              Empty.elim ∘
            ![(#5 : Semiterm ℒₒᵣ Empty 12), #6, #7,
              #3, #2, #1, #0])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          sourceStart sourceFinish targetStart targetFinish := by
    have henv :
        (Semiterm.val
            ![targetFinish, targetStart, sourceFinish, sourceStart, index,
              tokenTable, width, tokenCount,
              sourceBoundary, sourceCount, targetBoundary, targetCount]
            Empty.elim ∘
          ![(#5 : Semiterm ℒₒᵣ Empty 12), #6, #7,
            #3, #2, #1, #0]) =
          ![tokenTable, width, tokenCount,
            sourceStart, sourceFinish, targetStart, targetFinish] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount
        sourceStart sourceFinish targetStart targetFinish
  simp [compactAdditiveNatListListSameRowsDef,
    CompactAdditiveNatListListSameRows, hslices]

theorem compactAdditiveNatListListSameRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveNatListListSameRowsDef.val := by
  simp [compactAdditiveNatListListSameRowsDef]

theorem compactAdditiveNatListListSameRows_iff_eq
    {tokenTable width tokenCount sourceBoundary targetBoundary : Nat}
    {source target : List (List Nat)}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    CompactAdditiveNatListListSameRows tokenTable width tokenCount
        sourceBoundary source.length targetBoundary target.length ↔
      target = source := by
  constructor
  · rintro ⟨hcount, hrows⟩
    apply List.ext_getElem
    · omega
    · intro index htargetIndex hsourceIndex
      rcases hrows index hsourceIndex with
        ⟨sourceStart, _hsourceStart,
          sourceFinish, _hsourceFinish,
          targetStart, _htargetStart,
          targetFinish, _htargetFinish,
          hsourceStartEntry, hsourceFinishEntry,
          htargetStartEntry, htargetFinishEntry, hslices⟩
      rcases hsource index hsourceIndex with
        ⟨rowSourceStart, _hrowSourceStart,
          rowSourceFinish, _hrowSourceFinish,
          hrowSourceStartEntry, hrowSourceFinishEntry, hsourceLayout⟩
      rcases htarget index htargetIndex with
        ⟨rowTargetStart, _hrowTargetStart,
          rowTargetFinish, _hrowTargetFinish,
          hrowTargetStartEntry, hrowTargetFinishEntry, htargetLayout⟩
      have hsourceStartEq : sourceStart = rowSourceStart :=
        (CompactFixedWidthEntry.value_eq_tableValue hsourceStartEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hrowSourceStartEntry).symm
      have hsourceFinishEq : sourceFinish = rowSourceFinish :=
        (CompactFixedWidthEntry.value_eq_tableValue hsourceFinishEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hrowSourceFinishEntry).symm
      have htargetStartEq : targetStart = rowTargetStart :=
        (CompactFixedWidthEntry.value_eq_tableValue htargetStartEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hrowTargetStartEntry).symm
      have htargetFinishEq : targetFinish = rowTargetFinish :=
        (CompactFixedWidthEntry.value_eq_tableValue htargetFinishEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hrowTargetFinishEntry).symm
      subst sourceStart
      subst sourceFinish
      subst targetStart
      subst targetFinish
      have hvalue := CompactFixedWidthTokenSlicesEq.natListValues_eq
        hslices hsourceLayout htargetLayout
      rw [List.getI_eq_getElem source hsourceIndex] at hvalue
      rw [List.getI_eq_getElem target htargetIndex] at hvalue
      exact hvalue
  · intro hsame
    subst target
    refine ⟨rfl, ?_⟩
    intro index hindex
    rcases hsource index hindex with
      ⟨sourceStart, hsourceStart,
        sourceFinish, hsourceFinish,
        hsourceStartEntry, hsourceFinishEntry, hsourceLayout⟩
    rcases htarget index hindex with
      ⟨targetStart, htargetStart,
        targetFinish, htargetFinish,
        htargetStartEntry, htargetFinishEntry, htargetLayout⟩
    have hslices := CompactAdditiveNatListDirectLayout.slicesEq_of_eq
      hsourceLayout htargetLayout rfl
    exact ⟨sourceStart, hsourceStart,
      sourceFinish, hsourceFinish,
      targetStart, htargetStart,
      targetFinish, htargetFinish,
      hsourceStartEntry, hsourceFinishEntry,
      htargetStartEntry, htargetFinishEntry, hslices⟩

#print axioms compactAdditiveNatListListSameRowsDef_spec
#print axioms compactAdditiveNatListListSameRowsDef_sigmaZero
#print axioms compactAdditiveNatListListSameRows_iff_eq

end FoundationCompactNumericListedDirectNatListListSameRows
