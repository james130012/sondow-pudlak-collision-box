import integration.FoundationCompactNumericListedDirectNatListAppendSlices

/-!
# Bounded cons graph for lists of natural-number lists

The head formula is matched against target row zero.  Every source context
row is matched against the following target row.  Exact slice equality makes
the relation independent of element length while remaining Delta-zero.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListListConsSlices

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectNatListSliceEquality

def CompactAdditiveNatListListConsSlices
    (tokenTable width tokenCount
      sourceBoundary sourceCount headStart headFinish
      targetBoundary targetCount : Nat) : Prop :=
  targetCount = sourceCount + 1 ∧
    (exists targetHeadStart, targetHeadStart <= tokenCount ∧
      exists targetHeadFinish, targetHeadFinish <= tokenCount ∧
        CompactFixedWidthEntry targetBoundary tokenCount 0 targetHeadStart ∧
        CompactFixedWidthEntry targetBoundary tokenCount 1 targetHeadFinish ∧
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          headStart headFinish targetHeadStart targetHeadFinish) ∧
    forall index, index < sourceCount ->
      exists sourceStart, sourceStart <= tokenCount ∧
      exists sourceFinish, sourceFinish <= tokenCount ∧
      exists targetStart, targetStart <= tokenCount ∧
      exists targetFinish, targetFinish <= tokenCount ∧
        CompactFixedWidthEntry sourceBoundary tokenCount index sourceStart ∧
        CompactFixedWidthEntry sourceBoundary tokenCount
          (index + 1) sourceFinish ∧
        CompactFixedWidthEntry targetBoundary tokenCount
          (index + 1) targetStart ∧
        CompactFixedWidthEntry targetBoundary tokenCount
          (index + 2) targetFinish ∧
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          sourceStart sourceFinish targetStart targetFinish

def compactAdditiveNatListListConsSlicesDef :
    𝚺₀.Semisentence 9 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary sourceCount headStart headFinish
      targetBoundary targetCount.
    targetCount = sourceCount + 1 ∧
    (∃ targetHeadStart <⁺ tokenCount,
      ∃ targetHeadFinish <⁺ tokenCount,
        !(compactFixedWidthEntryDef)
          targetBoundary tokenCount 0 targetHeadStart ∧
        !(compactFixedWidthEntryDef)
          targetBoundary tokenCount 1 targetHeadFinish ∧
        !(compactFixedWidthTokenSlicesEqDef)
          tokenTable width tokenCount
            headStart headFinish targetHeadStart targetHeadFinish) ∧
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
                targetBoundary tokenCount (index + 1) targetStart ∧
              !(compactFixedWidthEntryDef)
                targetBoundary tokenCount (index + 2) targetFinish ∧
              !(compactFixedWidthTokenSlicesEqDef)
                tokenTable width tokenCount
                  sourceStart sourceFinish targetStart targetFinish”

@[simp] theorem compactAdditiveNatListListConsSlicesDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount headStart headFinish
      targetBoundary targetCount : Nat) :
    compactAdditiveNatListListConsSlicesDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, headStart, headFinish,
          targetBoundary, targetCount] ↔
      CompactAdditiveNatListListConsSlices tokenTable width tokenCount
        sourceBoundary sourceCount headStart headFinish
        targetBoundary targetCount := by
  have hhead (targetHeadFinish targetHeadStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![targetHeadFinish, targetHeadStart,
                tokenTable, width, tokenCount,
                sourceBoundary, sourceCount, headStart, headFinish,
                targetBoundary, targetCount]
              Empty.elim ∘
            ![(#2 : Semiterm ℒₒᵣ Empty 11), #3, #4,
              #7, #8, #1, #0])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          headStart headFinish targetHeadStart targetHeadFinish := by
    have henv :
        (Semiterm.val
            ![targetHeadFinish, targetHeadStart,
              tokenTable, width, tokenCount,
              sourceBoundary, sourceCount, headStart, headFinish,
              targetBoundary, targetCount]
            Empty.elim ∘
          ![(#2 : Semiterm ℒₒᵣ Empty 11), #3, #4,
            #7, #8, #1, #0]) =
          ![tokenTable, width, tokenCount,
            headStart, headFinish, targetHeadStart, targetHeadFinish] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount headStart headFinish
        targetHeadStart targetHeadFinish
  have htail
      (targetFinish targetStart sourceFinish sourceStart index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![targetFinish, targetStart, sourceFinish, sourceStart, index,
                tokenTable, width, tokenCount,
                sourceBoundary, sourceCount, headStart, headFinish,
                targetBoundary, targetCount]
              Empty.elim ∘
            ![(#5 : Semiterm ℒₒᵣ Empty 14), #6, #7,
              #3, #2, #1, #0])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          sourceStart sourceFinish targetStart targetFinish := by
    have henv :
        (Semiterm.val
            ![targetFinish, targetStart, sourceFinish, sourceStart, index,
              tokenTable, width, tokenCount,
              sourceBoundary, sourceCount, headStart, headFinish,
              targetBoundary, targetCount]
            Empty.elim ∘
          ![(#5 : Semiterm ℒₒᵣ Empty 14), #6, #7,
            #3, #2, #1, #0]) =
          ![tokenTable, width, tokenCount,
            sourceStart, sourceFinish, targetStart, targetFinish] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount sourceStart sourceFinish
        targetStart targetFinish
  simp [compactAdditiveNatListListConsSlicesDef,
    CompactAdditiveNatListListConsSlices, hhead, htail]
  intro _hcount _targetHeadStart _htargetHeadStart
    _targetHeadFinish _htargetHeadFinish
    _hstartEntry _hfinishEntry _hheadSlices
  constructor
  · intro hrows index hindex
    exact hrows index hindex
  · intro hrows index hindex
    exact hrows index hindex

theorem compactAdditiveNatListListConsSlicesDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveNatListListConsSlicesDef.val := by
  simp [compactAdditiveNatListListConsSlicesDef]

theorem compactAdditiveNatListListConsSlices_iff_cons
    {tokenTable width tokenCount sourceBoundary
      headStart headFinish targetBoundary : Nat}
    {source target : List (List Nat)} {head : List Nat}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (hhead : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      headStart headFinish head)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    CompactAdditiveNatListListConsSlices tokenTable width tokenCount
        sourceBoundary source.length headStart headFinish
        targetBoundary target.length ↔
      target = head :: source := by
  constructor
  · rintro ⟨hcount,
      ⟨targetHeadStart, _htargetHeadStart,
        targetHeadFinish, _htargetHeadFinish,
        htargetHeadStartEntry, htargetHeadFinishEntry, hheadSlices⟩,
      htail⟩
    apply List.ext_getElem
    · simp
      omega
    · intro index htargetIndex hconsIndex
      cases index with
      | zero =>
          rcases htarget 0 htargetIndex with
            ⟨rowStart, _hrowStart, rowFinish, _hrowFinish,
              hrowStartEntry, hrowFinishEntry, hrowLayout⟩
          have hstart : targetHeadStart = rowStart :=
            (CompactFixedWidthEntry.value_eq_tableValue
              htargetHeadStartEntry).trans
                (CompactFixedWidthEntry.value_eq_tableValue
                  hrowStartEntry).symm
          have hfinish : targetHeadFinish = rowFinish :=
            (CompactFixedWidthEntry.value_eq_tableValue
              htargetHeadFinishEntry).trans
                (CompactFixedWidthEntry.value_eq_tableValue
                  hrowFinishEntry).symm
          subst targetHeadStart
          subst targetHeadFinish
          have hvalue := CompactFixedWidthTokenSlicesEq.natListValues_eq
            hheadSlices hhead hrowLayout
          rw [List.getI_eq_getElem target htargetIndex] at hvalue
          simpa using hvalue
      | succ index =>
          have hsourceIndex : index < source.length := by omega
          rcases htail index hsourceIndex with
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
          rcases htarget (index + 1) htargetIndex with
            ⟨rowTargetStart, _hrowTargetStart,
              rowTargetFinish, _hrowTargetFinish,
              hrowTargetStartEntry, hrowTargetFinishEntry, htargetLayout⟩
          have hsourceStartEq : sourceStart = rowSourceStart :=
            (CompactFixedWidthEntry.value_eq_tableValue
              hsourceStartEntry).trans
                (CompactFixedWidthEntry.value_eq_tableValue
                  hrowSourceStartEntry).symm
          have hsourceFinishEq : sourceFinish = rowSourceFinish :=
            (CompactFixedWidthEntry.value_eq_tableValue
              hsourceFinishEntry).trans
                (CompactFixedWidthEntry.value_eq_tableValue
                  hrowSourceFinishEntry).symm
          have htargetStartEq : targetStart = rowTargetStart :=
            (CompactFixedWidthEntry.value_eq_tableValue
              htargetStartEntry).trans
                (CompactFixedWidthEntry.value_eq_tableValue
                  hrowTargetStartEntry).symm
          have htargetFinishEq : targetFinish = rowTargetFinish :=
            (CompactFixedWidthEntry.value_eq_tableValue
              htargetFinishEntry).trans
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
          simpa using hvalue
  · intro htargetEq
    have hcount : target.length = source.length + 1 := by
      simp [htargetEq]
    have htargetZero : 0 < target.length := by omega
    rcases htarget 0 htargetZero with
      ⟨targetHeadStart, htargetHeadStart,
        targetHeadFinish, htargetHeadFinish,
        htargetHeadStartEntry, htargetHeadFinishEntry,
        htargetHeadLayout⟩
    have hheadEq : head = target.getI 0 := by
      rw [htargetEq]
      rfl
    have hheadSlices :=
      CompactAdditiveNatListDirectLayout.slicesEq_of_eq
        hhead htargetHeadLayout hheadEq
    refine ⟨hcount,
      ⟨targetHeadStart, htargetHeadStart,
        targetHeadFinish, htargetHeadFinish,
        htargetHeadStartEntry, htargetHeadFinishEntry, hheadSlices⟩,
      ?_⟩
    intro index hindex
    have htargetIndex : index + 1 < target.length := by omega
    rcases hsource index hindex with
      ⟨sourceStart, hsourceStart,
        sourceFinish, hsourceFinish,
        hsourceStartEntry, hsourceFinishEntry, hsourceLayout⟩
    rcases htarget (index + 1) htargetIndex with
      ⟨targetStart, htargetStart,
        targetFinish, htargetFinish,
        htargetStartEntry, htargetFinishEntry, htargetLayout⟩
    have hvalue : source.getI index = target.getI (index + 1) := by
      rw [htargetEq]
      simp
    have hslices :=
      CompactAdditiveNatListDirectLayout.slicesEq_of_eq
        hsourceLayout htargetLayout hvalue
    exact ⟨sourceStart, hsourceStart,
      sourceFinish, hsourceFinish,
      targetStart, htargetStart,
      targetFinish, htargetFinish,
      hsourceStartEntry, hsourceFinishEntry,
      htargetStartEntry, htargetFinishEntry, hslices⟩

#print axioms compactAdditiveNatListListConsSlicesDef_spec
#print axioms compactAdditiveNatListListConsSlicesDef_sigmaZero
#print axioms compactAdditiveNatListListConsSlices_iff_cons

end FoundationCompactNumericListedDirectNatListListConsSlices
