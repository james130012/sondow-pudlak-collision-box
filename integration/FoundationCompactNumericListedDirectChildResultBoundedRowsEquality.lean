import integration.FoundationCompactNumericListedDirectChildResultRowEquality

/-!
# Bounded equality of two verifier child-result list rows

The relation reads one row from each structured child-result list, bounds all
fourteen parsing coordinates by the common value bound, and invokes the direct
child-result row equality graph.  Under the checked list-row graphs it is
equivalent to equality of the selected typed values.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectChildResultBoundedRowsEquality

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierChildResultFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectChildResultRowEquality

def CompactNumericChildResultBoundedRowsEq
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat) : Prop :=
  ∃ sourceStart, sourceStart ≤ valueBound ∧
  ∃ sourceFinish, sourceFinish ≤ valueBound ∧
  ∃ sourceGammaFinish, sourceGammaFinish ≤ valueBound ∧
  ∃ sourceGammaCount, sourceGammaCount ≤ valueBound ∧
  ∃ sourceGammaBoundary, sourceGammaBoundary ≤ valueBound ∧
  ∃ sourceBoolValue, sourceBoolValue ≤ valueBound ∧
  ∃ sourceGammaBoundarySize, sourceGammaBoundarySize ≤ valueBound ∧
  ∃ targetStart, targetStart ≤ valueBound ∧
  ∃ targetFinish, targetFinish ≤ valueBound ∧
  ∃ targetGammaFinish, targetGammaFinish ≤ valueBound ∧
  ∃ targetGammaCount, targetGammaCount ≤ valueBound ∧
  ∃ targetGammaBoundary, targetGammaBoundary ≤ valueBound ∧
  ∃ targetBoolValue, targetBoolValue ≤ valueBound ∧
  ∃ targetGammaBoundarySize, targetGammaBoundarySize ≤ valueBound ∧
    CompactFixedWidthEntry sourceBoundary tokenCount
        sourceIndex sourceStart ∧
    CompactFixedWidthEntry sourceBoundary tokenCount
        (sourceIndex + 1) sourceFinish ∧
    CompactFixedWidthEntry targetBoundary tokenCount
        targetIndex targetStart ∧
    CompactFixedWidthEntry targetBoundary tokenCount
        (targetIndex + 1) targetFinish ∧
    CompactNumericChildResultRowEqGraph tokenTable width tokenCount
      (compactNumericChildResultRowCoordinatesOf
        sourceStart sourceFinish sourceGammaFinish sourceGammaCount
        sourceGammaBoundary sourceBoolValue)
      (compactNumericChildResultRowCoordinatesOf
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBoolValue)
      { gammaBoundarySize := sourceGammaBoundarySize }
      { gammaBoundarySize := targetGammaBoundarySize }

def compactNumericChildResultBoundedRowsEqDef :
    𝚺₀.Semisentence 8 := .mkSigma
  “tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex.
    ∃ sourceStart <⁺ valueBound,
    ∃ sourceFinish <⁺ valueBound,
    ∃ sourceGammaFinish <⁺ valueBound,
    ∃ sourceGammaCount <⁺ valueBound,
    ∃ sourceGammaBoundary <⁺ valueBound,
    ∃ sourceBoolValue <⁺ valueBound,
    ∃ sourceGammaBoundarySize <⁺ valueBound,
    ∃ targetStart <⁺ valueBound,
    ∃ targetFinish <⁺ valueBound,
    ∃ targetGammaFinish <⁺ valueBound,
    ∃ targetGammaCount <⁺ valueBound,
    ∃ targetGammaBoundary <⁺ valueBound,
    ∃ targetBoolValue <⁺ valueBound,
    ∃ targetGammaBoundarySize <⁺ valueBound,
      !(compactFixedWidthEntryDef)
        sourceBoundary tokenCount sourceIndex sourceStart ∧
      !(compactFixedWidthEntryDef)
        sourceBoundary tokenCount (sourceIndex + 1) sourceFinish ∧
      !(compactFixedWidthEntryDef)
        targetBoundary tokenCount targetIndex targetStart ∧
      !(compactFixedWidthEntryDef)
        targetBoundary tokenCount (targetIndex + 1) targetFinish ∧
      !(compactNumericChildResultRowEqGraphDef)
        tokenTable width tokenCount
          sourceStart sourceFinish sourceGammaFinish sourceGammaCount
          sourceGammaBoundary sourceBoolValue sourceGammaBoundarySize
          targetStart targetFinish targetGammaFinish targetGammaCount
          targetGammaBoundary targetBoolValue targetGammaBoundarySize”

@[simp] theorem compactNumericChildResultBoundedRowsEqDef_spec
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat) :
    compactNumericChildResultBoundedRowsEqDef.val.Evalb
        ![tokenTable, width, tokenCount, sourceBoundary, targetBoundary,
          valueBound, sourceIndex, targetIndex] ↔
      CompactNumericChildResultBoundedRowsEq
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound sourceIndex targetIndex := by
  have hrow
      (targetGammaBoundarySize targetBoolValue targetGammaBoundary
        targetGammaCount targetGammaFinish targetFinish targetStart
        sourceGammaBoundarySize sourceBoolValue sourceGammaBoundary
        sourceGammaCount sourceGammaFinish sourceFinish sourceStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![targetGammaBoundarySize, targetBoolValue,
                targetGammaBoundary, targetGammaCount, targetGammaFinish,
                targetFinish, targetStart,
                sourceGammaBoundarySize, sourceBoolValue,
                sourceGammaBoundary, sourceGammaCount, sourceGammaFinish,
                sourceFinish, sourceStart,
                tokenTable, width, tokenCount,
                sourceBoundary, targetBoundary, valueBound,
                sourceIndex, targetIndex]
              Empty.elim ∘
            ![(#14 : Semiterm ℒₒᵣ Empty 22), #15, #16,
              #13, #12, #11, #10, #9, #8, #7,
              #6, #5, #4, #3, #2, #1, #0])
          Empty.elim) compactNumericChildResultRowEqGraphDef.val ↔
        CompactNumericChildResultRowEqGraph tokenTable width tokenCount
          (compactNumericChildResultRowCoordinatesOf
            sourceStart sourceFinish sourceGammaFinish sourceGammaCount
            sourceGammaBoundary sourceBoolValue)
          (compactNumericChildResultRowCoordinatesOf
            targetStart targetFinish targetGammaFinish targetGammaCount
            targetGammaBoundary targetBoolValue)
          { gammaBoundarySize := sourceGammaBoundarySize }
          { gammaBoundarySize := targetGammaBoundarySize } := by
    have henv :
        (Semiterm.val
            ![targetGammaBoundarySize, targetBoolValue,
              targetGammaBoundary, targetGammaCount, targetGammaFinish,
              targetFinish, targetStart,
              sourceGammaBoundarySize, sourceBoolValue,
              sourceGammaBoundary, sourceGammaCount, sourceGammaFinish,
              sourceFinish, sourceStart,
              tokenTable, width, tokenCount,
              sourceBoundary, targetBoundary, valueBound,
              sourceIndex, targetIndex]
            Empty.elim ∘
          ![(#14 : Semiterm ℒₒᵣ Empty 22), #15, #16,
            #13, #12, #11, #10, #9, #8, #7,
            #6, #5, #4, #3, #2, #1, #0]) =
          compactNumericChildResultRowEqGraphEnvironment
            tokenTable width tokenCount
            sourceStart sourceFinish sourceGammaFinish sourceGammaCount
            sourceGammaBoundary sourceBoolValue sourceGammaBoundarySize
            targetStart targetFinish targetGammaFinish targetGammaCount
            targetGammaBoundary targetBoolValue targetGammaBoundarySize := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactNumericChildResultRowEqGraphDef_spec
      tokenTable width tokenCount
      sourceStart sourceFinish sourceGammaFinish sourceGammaCount
      sourceGammaBoundary sourceBoolValue sourceGammaBoundarySize
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBoolValue targetGammaBoundarySize
  simp [compactNumericChildResultBoundedRowsEqDef,
    CompactNumericChildResultBoundedRowsEq, hrow]

theorem compactNumericChildResultBoundedRowsEqDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericChildResultBoundedRowsEqDef.val := by
  simp [compactNumericChildResultBoundedRowsEqDef]

theorem CompactNumericChildResultBoundedRowsEq.value_eq
    {tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat}
    {source target : List CompactNumericChildResult}
    (heq : CompactNumericChildResultBoundedRowsEq
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex)
    (hsourceIndex : sourceIndex < source.length)
    (htargetIndex : targetIndex < target.length)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    target.getI targetIndex = source.getI sourceIndex := by
  rcases heq with
    ⟨sourceStart, _hsourceStartBound,
      sourceFinish, _hsourceFinishBound,
      sourceGammaFinish, _hsourceGammaFinishBound,
      sourceGammaCount, _hsourceGammaCountBound,
      sourceGammaBoundary, _hsourceGammaBoundaryBound,
      sourceBoolValue, _hsourceBoolValueBound,
      sourceGammaBoundarySize, _hsourceGammaBoundarySizeBound,
      targetStart, _htargetStartBound,
      targetFinish, _htargetFinishBound,
      targetGammaFinish, _htargetGammaFinishBound,
      targetGammaCount, _htargetGammaCountBound,
      targetGammaBoundary, _htargetGammaBoundaryBound,
      targetBoolValue, _htargetBoolValueBound,
      targetGammaBoundarySize, _htargetGammaBoundarySizeBound,
      hsourceStartEntry, hsourceFinishEntry,
      htargetStartEntry, htargetFinishEntry, hrowEq⟩
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
  subst sourceStart
  subst sourceFinish
  subst targetStart
  subst targetFinish
  exact hrowEq.value_eq hsourceLayout htargetLayout

theorem CompactNumericChildResultBoundedRowsEq.of_value_eq
    {tokenTable width tokenCount sourceBoundary targetBoundary
      valueCountSource valueCountTarget tableWidth valueBound
      sourceIndex targetIndex : Nat}
    {source target : List CompactNumericChildResult}
    (hsourceGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount sourceBoundary valueCountSource
        tableWidth valueBound)
    (htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetBoundary valueCountTarget
        tableWidth valueBound)
    (hsourceCount : source.length = valueCountSource)
    (htargetCount : target.length = valueCountTarget)
    (hsourceIndex : sourceIndex < source.length)
    (htargetIndex : targetIndex < target.length)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hvalue : target.getI targetIndex = source.getI sourceIndex) :
    CompactNumericChildResultBoundedRowsEq
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex := by
  have hsourceIndexGraph : sourceIndex < valueCountSource := by omega
  have htargetIndexGraph : targetIndex < valueCountTarget := by omega
  rcases hsourceGraph.2 sourceIndex hsourceIndexGraph with
    ⟨sourceStart, hsourceStartBound,
      sourceFinish, hsourceFinishBound,
      sourceGammaFinish, hsourceGammaFinishBound,
      sourceGammaCount, hsourceGammaCountBound,
      sourceGammaBoundary, hsourceGammaBoundaryBound,
      sourceBoolValue, hsourceBoolValueBound,
      sourceGammaBoundarySize, hsourceGammaBoundarySizeBound,
      hsourceStartEntry, hsourceFinishEntry, hsourceCore⟩
  rcases htargetGraph.2 targetIndex htargetIndexGraph with
    ⟨targetStart, htargetStartBound,
      targetFinish, htargetFinishBound,
      targetGammaFinish, htargetGammaFinishBound,
      targetGammaCount, htargetGammaCountBound,
      targetGammaBoundary, htargetGammaBoundaryBound,
      targetBoolValue, htargetBoolValueBound,
      targetGammaBoundarySize, htargetGammaBoundarySizeBound,
      htargetStartEntry, htargetFinishEntry, htargetCore⟩
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
  have hrowEq := CompactNumericChildResultRowEqGraph.of_value_eq
    hsourceCore htargetCore hsourceLayout htargetLayout hvalue
  exact ⟨sourceStart, hsourceStartBound,
    sourceFinish, hsourceFinishBound,
    sourceGammaFinish, hsourceGammaFinishBound,
    sourceGammaCount, hsourceGammaCountBound,
    sourceGammaBoundary, hsourceGammaBoundaryBound,
    sourceBoolValue, hsourceBoolValueBound,
    sourceGammaBoundarySize, hsourceGammaBoundarySizeBound,
    targetStart, htargetStartBound,
    targetFinish, htargetFinishBound,
    targetGammaFinish, htargetGammaFinishBound,
    targetGammaCount, htargetGammaCountBound,
    targetGammaBoundary, htargetGammaBoundaryBound,
    targetBoolValue, htargetBoolValueBound,
    targetGammaBoundarySize, htargetGammaBoundarySizeBound,
    hsourceStartEntry, hsourceFinishEntry,
    htargetStartEntry, htargetFinishEntry, hrowEq⟩

theorem compactNumericChildResultBoundedRowsEq_iff_eq
    {tokenTable width tokenCount sourceBoundary targetBoundary
      valueCountSource valueCountTarget tableWidth valueBound
      sourceIndex targetIndex : Nat}
    {source target : List CompactNumericChildResult}
    (hsourceGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount sourceBoundary valueCountSource
        tableWidth valueBound)
    (htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetBoundary valueCountTarget
        tableWidth valueBound)
    (hsourceCount : source.length = valueCountSource)
    (htargetCount : target.length = valueCountTarget)
    (hsourceIndex : sourceIndex < source.length)
    (htargetIndex : targetIndex < target.length)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    CompactNumericChildResultBoundedRowsEq
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound sourceIndex targetIndex ↔
      target.getI targetIndex = source.getI sourceIndex := by
  constructor
  · exact fun heq => heq.value_eq
      hsourceIndex htargetIndex hsourceRows htargetRows
  · exact CompactNumericChildResultBoundedRowsEq.of_value_eq
      hsourceGraph htargetGraph hsourceCount htargetCount
      hsourceIndex htargetIndex hsourceRows htargetRows

#print axioms compactNumericChildResultBoundedRowsEqDef_spec
#print axioms compactNumericChildResultBoundedRowsEqDef_sigmaZero
#print axioms CompactNumericChildResultBoundedRowsEq.value_eq
#print axioms CompactNumericChildResultBoundedRowsEq.of_value_eq
#print axioms compactNumericChildResultBoundedRowsEq_iff_eq

end FoundationCompactNumericListedDirectChildResultBoundedRowsEquality
