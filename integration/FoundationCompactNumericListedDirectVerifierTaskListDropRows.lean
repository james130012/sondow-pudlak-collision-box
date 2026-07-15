import integration.FoundationCompactNumericListedDirectVerifierPayloadEquality
import integration.FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
import integration.FoundationCompactNumericListedDirectVerifierTaskSliceEquality

/-!
# Direct row graph for dropping verifier-task prefixes

Task rows are compared by complete fixed-width token slices.  Under the typed
task layouts this implies equality of every task field, and the list relation
therefore realizes exactly `target = source.drop consumed`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTaskListDropRows

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierTaskSliceEquality

def CompactNumericVerifierTaskBoundedRowsEq
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat) : Prop :=
  ∃ sourceStart, sourceStart ≤ valueBound ∧
  ∃ sourceFinish, sourceFinish ≤ valueBound ∧
  ∃ targetStart, targetStart ≤ valueBound ∧
  ∃ targetFinish, targetFinish ≤ valueBound ∧
    CompactFixedWidthEntry sourceBoundary tokenCount
      sourceIndex sourceStart ∧
    CompactFixedWidthEntry sourceBoundary tokenCount
      (sourceIndex + 1) sourceFinish ∧
    CompactFixedWidthEntry targetBoundary tokenCount
      targetIndex targetStart ∧
    CompactFixedWidthEntry targetBoundary tokenCount
      (targetIndex + 1) targetFinish ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish

def compactNumericVerifierTaskBoundedRowsEqDef :
    𝚺₀.Semisentence 8 := .mkSigma
  “tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex.
    ∃ sourceStart <⁺ valueBound,
    ∃ sourceFinish <⁺ valueBound,
    ∃ targetStart <⁺ valueBound,
    ∃ targetFinish <⁺ valueBound,
      !(compactFixedWidthEntryDef)
        sourceBoundary tokenCount sourceIndex sourceStart ∧
      !(compactFixedWidthEntryDef)
        sourceBoundary tokenCount (sourceIndex + 1) sourceFinish ∧
      !(compactFixedWidthEntryDef)
        targetBoundary tokenCount targetIndex targetStart ∧
      !(compactFixedWidthEntryDef)
        targetBoundary tokenCount (targetIndex + 1) targetFinish ∧
      !(compactFixedWidthTokenSlicesEqDef)
        tokenTable width tokenCount
          sourceStart sourceFinish targetStart targetFinish”

@[simp] theorem compactNumericVerifierTaskBoundedRowsEqDef_spec
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat) :
    compactNumericVerifierTaskBoundedRowsEqDef.val.Evalb
        ![tokenTable, width, tokenCount, sourceBoundary, targetBoundary,
          valueBound, sourceIndex, targetIndex] ↔
      CompactNumericVerifierTaskBoundedRowsEq
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound sourceIndex targetIndex := by
  let env : Fin 8 → Nat :=
    ![tokenTable, width, tokenCount, sourceBoundary, targetBoundary,
      valueBound, sourceIndex, targetIndex]
  change compactNumericVerifierTaskBoundedRowsEqDef.val.Evalb env ↔ _
  have hsourceStartEnv
      (targetFinish targetStart sourceFinish sourceStart : Nat) :
      (Semiterm.val
          ![targetFinish, targetStart, sourceFinish, sourceStart,
            tokenTable, width, tokenCount, sourceBoundary, targetBoundary,
            valueBound, sourceIndex, targetIndex]
          Empty.elim ∘
        ![(#7 : Semiterm ℒₒᵣ Empty 12), #6, #10, #3]) =
        ![sourceBoundary, tokenCount, sourceIndex, sourceStart] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsourceFinishEnv
      (targetFinish targetStart sourceFinish sourceStart : Nat) :
      (Semiterm.val
          ![targetFinish, targetStart, sourceFinish, sourceStart,
            tokenTable, width, tokenCount, sourceBoundary, targetBoundary,
            valueBound, sourceIndex, targetIndex]
          Empty.elim ∘
        ![(#7 : Semiterm ℒₒᵣ Empty 12), #6,
          ‘(#10 + 1)’, #2]) =
        ![sourceBoundary, tokenCount, sourceIndex + 1, sourceFinish] := by
    funext coordinate
    fin_cases coordinate <;> simp
  have htargetStartEnv
      (targetFinish targetStart sourceFinish sourceStart : Nat) :
      (Semiterm.val
          ![targetFinish, targetStart, sourceFinish, sourceStart,
            tokenTable, width, tokenCount, sourceBoundary, targetBoundary,
            valueBound, sourceIndex, targetIndex]
          Empty.elim ∘
        ![(#8 : Semiterm ℒₒᵣ Empty 12), #6, #11, #1]) =
        ![targetBoundary, tokenCount, targetIndex, targetStart] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htargetFinishEnv
      (targetFinish targetStart sourceFinish sourceStart : Nat) :
      (Semiterm.val
          ![targetFinish, targetStart, sourceFinish, sourceStart,
            tokenTable, width, tokenCount, sourceBoundary, targetBoundary,
            valueBound, sourceIndex, targetIndex]
          Empty.elim ∘
        ![(#8 : Semiterm ℒₒᵣ Empty 12), #6,
          ‘(#11 + 1)’, #0]) =
        ![targetBoundary, tokenCount, targetIndex + 1, targetFinish] := by
    funext coordinate
    fin_cases coordinate <;> simp
  have hslicesEnv
      (targetFinish targetStart sourceFinish sourceStart : Nat) :
      (Semiterm.val
          ![targetFinish, targetStart, sourceFinish, sourceStart,
            tokenTable, width, tokenCount, sourceBoundary, targetBoundary,
            valueBound, sourceIndex, targetIndex]
          Empty.elim ∘
        ![(#4 : Semiterm ℒₒᵣ Empty 12), #5, #6,
          #3, #2, #1, #0]) =
        ![tokenTable, width, tokenCount,
          sourceStart, sourceFinish, targetStart, targetFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierTaskBoundedRowsEqDef,
    CompactNumericVerifierTaskBoundedRowsEq,
    hsourceStartEnv, hsourceFinishEnv,
    htargetStartEnv, htargetFinishEnv, hslicesEnv, env]

theorem compactNumericVerifierTaskBoundedRowsEqDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierTaskBoundedRowsEqDef.val := by
  simp [compactNumericVerifierTaskBoundedRowsEqDef]

theorem CompactNumericVerifierTaskBoundedRowsEq.value_eq
    {tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat}
    {source target : List CompactNumericVerifierTask}
    (heq : CompactNumericVerifierTaskBoundedRowsEq
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex)
    (hsourceIndex : sourceIndex < source.length)
    (htargetIndex : targetIndex < target.length)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    target.getI targetIndex = source.getI sourceIndex := by
  rcases heq with
    ⟨sourceStart, _hsourceStartBound,
      sourceFinish, _hsourceFinishBound,
      targetStart, _htargetStartBound,
      targetFinish, _htargetFinishBound,
      hsourceStartEntry, hsourceFinishEntry,
      htargetStartEntry, htargetFinishEntry, hslices⟩
  rcases hsourceRows sourceIndex hsourceIndex with
    ⟨actualSourceStart, _hactualSourceStart,
      actualSourceFinish, _hactualSourceFinish,
      hactualSourceStartEntry, hactualSourceFinishEntry, hsourceLayout⟩
  rcases htargetRows targetIndex htargetIndex with
    ⟨actualTargetStart, _hactualTargetStart,
      actualTargetFinish, _hactualTargetFinish,
      hactualTargetStartEntry, hactualTargetFinishEntry, htargetLayout⟩
  have hsourceStart : sourceStart = actualSourceStart :=
    (CompactFixedWidthEntry.value_eq_tableValue hsourceStartEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualSourceStartEntry).symm
  have hsourceFinish : sourceFinish = actualSourceFinish :=
    (CompactFixedWidthEntry.value_eq_tableValue hsourceFinishEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualSourceFinishEntry).symm
  have htargetStart : targetStart = actualTargetStart :=
    (CompactFixedWidthEntry.value_eq_tableValue htargetStartEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualTargetStartEntry).symm
  have htargetFinish : targetFinish = actualTargetFinish :=
    (CompactFixedWidthEntry.value_eq_tableValue htargetFinishEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualTargetFinishEntry).symm
  subst actualSourceStart
  subst actualSourceFinish
  subst actualTargetStart
  subst actualTargetFinish
  have hsourceStartFinish : sourceStart < sourceFinish := by
    rcases hsourceLayout with
      ⟨sourceFieldsStart, hsourceTag, hsourceFields⟩
    rcases hsourceFields with
      ⟨gammaFinish, firstFinish, secondFinish, witnessFinish,
        hgamma, hfirst, hsecond, hwitness, hsuffix⟩
    rcases hgamma with
      ⟨_gammaBoundary, hgammaLayout, _hgammaRows, _hgammaSize⟩
    have hfieldsStart : sourceFieldsStart = sourceStart + 1 :=
      hsourceTag.2.1
    have hgammaStartFinish :=
      CompactAdditiveStructuredListLayout.start_lt_finish hgammaLayout
    have hfirstFinish := CompactAdditiveNatListDirectLayout.finish_eq hfirst
    have hsecondFinish := CompactAdditiveNatListDirectLayout.finish_eq hsecond
    have hwitnessFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq hwitness
    have hsuffixFinish := CompactAdditiveNatListDirectLayout.finish_eq hsuffix
    omega
  rcases CompactFixedWidthTokenSlicesEq.verifierTaskPrefix_eq
      (offset := 0) hslices rfl rfl (by omega) (le_refl sourceFinish)
        (le_refl targetFinish) hsourceLayout htargetLayout with
    ⟨_finishOffset, _hsourceFinish, _htargetFinish, hvalue⟩
  exact hvalue

theorem CompactNumericVerifierTaskBoundedRowsEq.of_value_eq
    {tokenTable width tokenCount sourceBoundary targetBoundary
      tableWidth valueBound sourceIndex targetIndex : Nat}
    {source target : List CompactNumericVerifierTask}
    (hsourceGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound)
    (hsourceIndex : sourceIndex < source.length)
    (htargetIndex : targetIndex < target.length)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hvalue : target.getI targetIndex = source.getI sourceIndex) :
    CompactNumericVerifierTaskBoundedRowsEq
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex := by
  rcases hsourceGraph.2 sourceIndex hsourceIndex with
    ⟨sourceStart, hsourceStartBound,
      sourceFinish, hsourceFinishBound,
      _sourceTag, _hsourceTagBound,
      _sourceGammaFinish, _hsourceGammaFinishBound,
      _sourceGammaCount, _hsourceGammaCountBound,
      _sourceGammaBoundary, _hsourceGammaBoundaryBound,
      _sourceFirstFinish, _hsourceFirstFinishBound,
      _sourceFirstCount, _hsourceFirstCountBound,
      _sourceSecondFinish, _hsourceSecondFinishBound,
      _sourceSecondCount, _hsourceSecondCountBound,
      _sourceWitnessFinish, _hsourceWitnessFinishBound,
      _sourceWitnessCount, _hsourceWitnessCountBound,
      _sourceSuffixCount, _hsourceSuffixCountBound,
      _sourceGammaBoundarySize, _hsourceGammaBoundarySizeBound,
      hsourceStartEntry, hsourceFinishEntry, _hsourceCore⟩
  rcases htargetGraph.2 targetIndex htargetIndex with
    ⟨targetStart, htargetStartBound,
      targetFinish, htargetFinishBound,
      _targetTag, _htargetTagBound,
      _targetGammaFinish, _htargetGammaFinishBound,
      _targetGammaCount, _htargetGammaCountBound,
      _targetGammaBoundary, _htargetGammaBoundaryBound,
      _targetFirstFinish, _htargetFirstFinishBound,
      _targetFirstCount, _htargetFirstCountBound,
      _targetSecondFinish, _htargetSecondFinishBound,
      _targetSecondCount, _htargetSecondCountBound,
      _targetWitnessFinish, _htargetWitnessFinishBound,
      _targetWitnessCount, _htargetWitnessCountBound,
      _targetSuffixCount, _htargetSuffixCountBound,
      _targetGammaBoundarySize, _htargetGammaBoundarySizeBound,
      htargetStartEntry, htargetFinishEntry, _htargetCore⟩
  rcases hsourceRows sourceIndex hsourceIndex with
    ⟨actualSourceStart, _hactualSourceStartBound,
      actualSourceFinish, _hactualSourceFinishBound,
      hactualSourceStartEntry, hactualSourceFinishEntry, hsourceLayout⟩
  rcases htargetRows targetIndex htargetIndex with
    ⟨actualTargetStart, _hactualTargetStartBound,
      actualTargetFinish, _hactualTargetFinishBound,
      hactualTargetStartEntry, hactualTargetFinishEntry, htargetLayout⟩
  have hsourceStart : sourceStart = actualSourceStart :=
    (CompactFixedWidthEntry.value_eq_tableValue hsourceStartEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualSourceStartEntry).symm
  have hsourceFinish : sourceFinish = actualSourceFinish :=
    (CompactFixedWidthEntry.value_eq_tableValue hsourceFinishEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualSourceFinishEntry).symm
  have htargetStart : targetStart = actualTargetStart :=
    (CompactFixedWidthEntry.value_eq_tableValue htargetStartEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualTargetStartEntry).symm
  have htargetFinish : targetFinish = actualTargetFinish :=
    (CompactFixedWidthEntry.value_eq_tableValue htargetFinishEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualTargetFinishEntry).symm
  subst actualSourceStart
  subst actualSourceFinish
  subst actualTargetStart
  subst actualTargetFinish
  have hslices := CompactNumericVerifierTaskDirectLayout.slicesEq_of_eq
    hsourceLayout htargetLayout hvalue.symm
  exact ⟨sourceStart, hsourceStartBound,
    sourceFinish, hsourceFinishBound,
    targetStart, htargetStartBound,
    targetFinish, htargetFinishBound,
    hsourceStartEntry, hsourceFinishEntry,
    htargetStartEntry, htargetFinishEntry, hslices⟩

def CompactNumericVerifierTaskListDropRows
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      _tableWidth valueBound consumed : Nat) : Prop :=
  consumed ≤ sourceCount ∧
    sourceCount = consumed + targetCount ∧
    ∀ index < targetCount,
      CompactNumericVerifierTaskBoundedRowsEq
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound (consumed + index) index

def compactNumericVerifierTaskListDropRowsDef :
    𝚺₀.Semisentence 10 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound consumed.
    consumed ≤ sourceCount ∧
    sourceCount = consumed + targetCount ∧
    ∀ index < targetCount,
      !(compactNumericVerifierTaskBoundedRowsEqDef)
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound (consumed + index) index”

@[simp] theorem compactNumericVerifierTaskListDropRowsDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound consumed : Nat) :
    compactNumericVerifierTaskListDropRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          tableWidth, valueBound, consumed] ↔
      CompactNumericVerifierTaskListDropRows
        tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount
        tableWidth valueBound consumed := by
  have hrow (index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![index, tokenTable, width, tokenCount,
                sourceBoundary, sourceCount, targetBoundary, targetCount,
                tableWidth, valueBound, consumed]
              Empty.elim ∘
            ![(#1 : Semiterm ℒₒᵣ Empty 11), #2, #3, #4, #6,
              #9, ‘(#10 + #0)’, #0])
          Empty.elim) compactNumericVerifierTaskBoundedRowsEqDef.val ↔
        CompactNumericVerifierTaskBoundedRowsEq
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound (consumed + index) index := by
    have henv :
        (Semiterm.val
            ![index, tokenTable, width, tokenCount,
              sourceBoundary, sourceCount, targetBoundary, targetCount,
              tableWidth, valueBound, consumed]
            Empty.elim ∘
          ![(#1 : Semiterm ℒₒᵣ Empty 11), #2, #3, #4, #6,
            #9, ‘(#10 + #0)’, #0]) =
          ![tokenTable, width, tokenCount,
            sourceBoundary, targetBoundary, valueBound,
            consumed + index, index] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactNumericVerifierTaskBoundedRowsEqDef_spec
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound (consumed + index) index
  simp [compactNumericVerifierTaskListDropRowsDef,
    CompactNumericVerifierTaskListDropRows, hrow]

theorem compactNumericVerifierTaskListDropRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierTaskListDropRowsDef.val := by
  simp [compactNumericVerifierTaskListDropRowsDef]

theorem CompactAdditiveStructuredListElementRowLayouts.verifierTaskDropRows
    {tokenTable width tokenCount sourceBoundary targetBoundary
      tableWidth valueBound consumed : Nat}
    {source target : List CompactNumericVerifierTask}
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hsourceGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound)
    (hconsumed : consumed ≤ source.length)
    (hdrop : target = source.drop consumed) :
    CompactNumericVerifierTaskListDropRows
      tokenTable width tokenCount
      sourceBoundary source.length targetBoundary target.length
      tableWidth valueBound consumed := by
  have hcount : source.length = consumed + target.length := by
    rw [hdrop, List.length_drop]
    omega
  refine ⟨hconsumed, hcount, ?_⟩
  intro index hindex
  have hsourceIndex : consumed + index < source.length := by omega
  have hdropIndex : index < (source.drop consumed).length := by
    simpa [hdrop] using hindex
  have hvalue : target.getI index = source.getI (consumed + index) := by
    rw [hdrop]
    rw [List.getI_eq_getElem _ hdropIndex]
    rw [List.getI_eq_getElem _ hsourceIndex]
    simp
  exact CompactNumericVerifierTaskBoundedRowsEq.of_value_eq
    hsourceGraph htargetGraph hsourceIndex hindex
      hsourceRows htargetRows hvalue

theorem CompactNumericVerifierTaskListDropRows.eq_drop_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary
      tableWidth valueBound consumed : Nat}
    {source target : List CompactNumericVerifierTask}
    (hdropRows : CompactNumericVerifierTaskListDropRows
      tokenTable width tokenCount
        sourceBoundary source.length targetBoundary target.length
        tableWidth valueBound consumed)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    target = source.drop consumed := by
  have hcount := hdropRows.2.1
  have hrowPairs := hdropRows.2.2
  apply List.ext_getElem
  · rw [List.length_drop]
    omega
  · intro index htargetIndex hdropIndex
    have hsourceIndex : consumed + index < source.length := by omega
    have hvalue := (hrowPairs index htargetIndex).value_eq
      hsourceIndex htargetIndex hsourceRows htargetRows
    rw [List.getI_eq_getElem _ htargetIndex] at hvalue
    rw [List.getI_eq_getElem _ hsourceIndex] at hvalue
    simpa using hvalue

theorem compactNumericVerifierTaskListDropRows_iff_drop_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary
      tableWidth valueBound consumed : Nat}
    {source target : List CompactNumericVerifierTask}
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hsourceGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound) :
    CompactNumericVerifierTaskListDropRows
        tokenTable width tokenCount
        sourceBoundary source.length targetBoundary target.length
        tableWidth valueBound consumed ↔
      consumed ≤ source.length ∧ target = source.drop consumed := by
  constructor
  · intro hdropRows
    exact ⟨hdropRows.1,
      hdropRows.eq_drop_of_rows hsourceRows htargetRows⟩
  · rintro ⟨hconsumed, hdrop⟩
    exact CompactAdditiveStructuredListElementRowLayouts.verifierTaskDropRows
      hsourceRows htargetRows hsourceGraph htargetGraph hconsumed hdrop

#print axioms compactNumericVerifierTaskBoundedRowsEqDef_spec
#print axioms compactNumericVerifierTaskBoundedRowsEqDef_sigmaZero
#print axioms CompactNumericVerifierTaskBoundedRowsEq.value_eq
#print axioms CompactNumericVerifierTaskBoundedRowsEq.of_value_eq
#print axioms compactNumericVerifierTaskListDropRowsDef_spec
#print axioms compactNumericVerifierTaskListDropRowsDef_sigmaZero
#print axioms CompactAdditiveStructuredListElementRowLayouts.verifierTaskDropRows
#print axioms CompactNumericVerifierTaskListDropRows.eq_drop_of_rows
#print axioms compactNumericVerifierTaskListDropRows_iff_drop_of_rows

end FoundationCompactNumericListedDirectVerifierTaskListDropRows
