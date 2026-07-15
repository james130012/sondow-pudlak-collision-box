import integration.FoundationCompactNumericListedDirectChildResultListDropRows

/-!
# A bounded child-result row with a prescribed context and Boolean

The relation parses one row from a child-result list, compares its nested
context with a supplied checked context row table, and fixes its Boolean tag.
It is the direct arithmetic head condition needed when a combine rule pushes
its newly computed result onto the verifier stack.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectChildResultBoundedHeadEquality

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierChildResultFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierValueRealization
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectChildResultRowEquality
open FoundationCompactNumericListedDirectNatListListSameRows

def CompactNumericChildResultBoundedHeadEq
    (tokenTable width tokenCount targetBoundary
      expectedGammaBoundary expectedGammaCount valueBound
      targetIndex expectedBool : Nat) : Prop :=
  ∃ targetStart, targetStart ≤ valueBound ∧
  ∃ targetFinish, targetFinish ≤ valueBound ∧
  ∃ targetGammaFinish, targetGammaFinish ≤ valueBound ∧
  ∃ targetGammaCount, targetGammaCount ≤ valueBound ∧
  ∃ targetGammaBoundary, targetGammaBoundary ≤ valueBound ∧
  ∃ targetBoolValue, targetBoolValue ≤ valueBound ∧
  ∃ targetGammaBoundarySize, targetGammaBoundarySize ≤ valueBound ∧
    CompactFixedWidthEntry targetBoundary tokenCount
        targetIndex targetStart ∧
    CompactFixedWidthEntry targetBoundary tokenCount
        (targetIndex + 1) targetFinish ∧
    CompactNumericChildResultCoreGraph tokenTable width tokenCount
      (compactNumericChildResultRowCoordinatesOf
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBoolValue)
      { gammaBoundarySize := targetGammaBoundarySize } ∧
    CompactAdditiveNatListListSameRows tokenTable width tokenCount
      expectedGammaBoundary expectedGammaCount
      targetGammaBoundary targetGammaCount ∧
    targetBoolValue = expectedBool

def compactNumericChildResultBoundedHeadEqDef :
    𝚺₀.Semisentence 9 := .mkSigma
  “tokenTable width tokenCount targetBoundary
      expectedGammaBoundary expectedGammaCount valueBound
      targetIndex expectedBool.
    ∃ targetStart <⁺ valueBound,
    ∃ targetFinish <⁺ valueBound,
    ∃ targetGammaFinish <⁺ valueBound,
    ∃ targetGammaCount <⁺ valueBound,
    ∃ targetGammaBoundary <⁺ valueBound,
    ∃ targetBoolValue <⁺ valueBound,
    ∃ targetGammaBoundarySize <⁺ valueBound,
      !(compactFixedWidthEntryDef)
        targetBoundary tokenCount targetIndex targetStart ∧
      !(compactFixedWidthEntryDef)
        targetBoundary tokenCount (targetIndex + 1) targetFinish ∧
      !(compactNumericChildResultCoreGraphDef)
        tokenTable width tokenCount
          targetStart targetFinish targetGammaFinish targetGammaCount
          targetGammaBoundary targetBoolValue targetGammaBoundarySize ∧
      !(compactAdditiveNatListListSameRowsDef)
        tokenTable width tokenCount
          expectedGammaBoundary expectedGammaCount
          targetGammaBoundary targetGammaCount ∧
      targetBoolValue = expectedBool”

@[simp] theorem compactNumericChildResultBoundedHeadEqDef_spec
    (tokenTable width tokenCount targetBoundary
      expectedGammaBoundary expectedGammaCount valueBound
      targetIndex expectedBool : Nat) :
    compactNumericChildResultBoundedHeadEqDef.val.Evalb
        ![tokenTable, width, tokenCount, targetBoundary,
          expectedGammaBoundary, expectedGammaCount, valueBound,
          targetIndex, expectedBool] ↔
      CompactNumericChildResultBoundedHeadEq
        tokenTable width tokenCount targetBoundary
          expectedGammaBoundary expectedGammaCount valueBound
          targetIndex expectedBool := by
  have hcore
      (targetGammaBoundarySize targetBoolValue targetGammaBoundary
        targetGammaCount targetGammaFinish targetFinish targetStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![targetGammaBoundarySize, targetBoolValue,
                targetGammaBoundary, targetGammaCount, targetGammaFinish,
                targetFinish, targetStart,
                tokenTable, width, tokenCount, targetBoundary,
                expectedGammaBoundary, expectedGammaCount, valueBound,
                targetIndex, expectedBool]
              Empty.elim ∘
            ![(#7 : Semiterm ℒₒᵣ Empty 16), #8, #9,
              #6, #5, #4, #3, #2, #1, #0])
          Empty.elim) compactNumericChildResultCoreGraphDef.val ↔
        CompactNumericChildResultCoreGraph tokenTable width tokenCount
          (compactNumericChildResultRowCoordinatesOf
            targetStart targetFinish targetGammaFinish targetGammaCount
            targetGammaBoundary targetBoolValue)
          { gammaBoundarySize := targetGammaBoundarySize } := by
    have henv :
        (Semiterm.val
            ![targetGammaBoundarySize, targetBoolValue,
              targetGammaBoundary, targetGammaCount, targetGammaFinish,
              targetFinish, targetStart,
              tokenTable, width, tokenCount, targetBoundary,
              expectedGammaBoundary, expectedGammaCount, valueBound,
              targetIndex, expectedBool]
            Empty.elim ∘
          ![(#7 : Semiterm ℒₒᵣ Empty 16), #8, #9,
            #6, #5, #4, #3, #2, #1, #0]) =
          compactNumericChildResultCoreFormulaEnvironment
            tokenTable width tokenCount
            targetStart targetFinish targetGammaFinish targetGammaCount
            targetGammaBoundary targetBoolValue
            targetGammaBoundarySize := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactNumericChildResultCoreGraphDef_spec
      tokenTable width tokenCount
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBoolValue targetGammaBoundarySize
  have hrows
      (targetGammaBoundarySize targetBoolValue targetGammaBoundary
        targetGammaCount targetGammaFinish targetFinish targetStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![targetGammaBoundarySize, targetBoolValue,
                targetGammaBoundary, targetGammaCount, targetGammaFinish,
                targetFinish, targetStart,
                tokenTable, width, tokenCount, targetBoundary,
                expectedGammaBoundary, expectedGammaCount, valueBound,
                targetIndex, expectedBool]
              Empty.elim ∘
            ![(#7 : Semiterm ℒₒᵣ Empty 16), #8, #9,
              #11, #12, #2, #3])
          Empty.elim) compactAdditiveNatListListSameRowsDef.val ↔
        CompactAdditiveNatListListSameRows tokenTable width tokenCount
          expectedGammaBoundary expectedGammaCount
          targetGammaBoundary targetGammaCount := by
    have henv :
        (Semiterm.val
            ![targetGammaBoundarySize, targetBoolValue,
              targetGammaBoundary, targetGammaCount, targetGammaFinish,
              targetFinish, targetStart,
              tokenTable, width, tokenCount, targetBoundary,
              expectedGammaBoundary, expectedGammaCount, valueBound,
              targetIndex, expectedBool]
            Empty.elim ∘
          ![(#7 : Semiterm ℒₒᵣ Empty 16), #8, #9,
            #11, #12, #2, #3]) =
          ![tokenTable, width, tokenCount,
            expectedGammaBoundary, expectedGammaCount,
            targetGammaBoundary, targetGammaCount] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactAdditiveNatListListSameRowsDef_spec
      tokenTable width tokenCount
      expectedGammaBoundary expectedGammaCount
      targetGammaBoundary targetGammaCount
  simp [compactNumericChildResultBoundedHeadEqDef,
    CompactNumericChildResultBoundedHeadEq, hcore, hrows]

theorem compactNumericChildResultBoundedHeadEqDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericChildResultBoundedHeadEqDef.val := by
  simp [compactNumericChildResultBoundedHeadEqDef]

theorem CompactNumericChildResultBoundedHeadEq.value_eq
    {tokenTable width tokenCount targetBoundary expectedGammaBoundary
      valueBound targetIndex : Nat}
    {expectedGamma : List (List Nat)} {expectedResult : Bool}
    {target : List CompactNumericChildResult}
    (hhead : CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount targetBoundary
        expectedGammaBoundary expectedGamma.length valueBound
        targetIndex (compactAdditiveBoolTag expectedResult))
    (htargetIndex : targetIndex < target.length)
    (hexpectedRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        expectedGammaBoundary expectedGamma)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    target.getI targetIndex = (expectedGamma, expectedResult) := by
  rcases hhead with
    ⟨targetStart, _htargetStartBound,
      targetFinish, _htargetFinishBound,
      targetGammaFinish, _htargetGammaFinishBound,
      targetGammaCount, _htargetGammaCountBound,
      targetGammaBoundary, _htargetGammaBoundaryBound,
      targetBoolValue, _htargetBoolValueBound,
      targetGammaBoundarySize, _htargetGammaBoundarySizeBound,
      htargetStartEntry, htargetFinishEntry,
      htargetCore, hgammaRows, hbool⟩
  rcases htargetRows targetIndex htargetIndex with
    ⟨actualTargetStart, _hactualTargetStart,
      actualTargetFinish, _hactualTargetFinish,
      hactualTargetStartEntry, hactualTargetFinishEntry, htargetLayout⟩
  have htargetStart : targetStart = actualTargetStart :=
    (CompactFixedWidthEntry.value_eq_tableValue htargetStartEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualTargetStartEntry).symm
  have htargetFinish : targetFinish = actualTargetFinish :=
    (CompactFixedWidthEntry.value_eq_tableValue htargetFinishEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualTargetFinishEntry).symm
  subst targetStart
  subst targetFinish
  rcases CompactNumericChildResultCoreGraph.realizeDirectLayoutWithRows
      htargetCore with
    ⟨graphValue, hgraphLayout, hgraphRows,
      hgraphLength, hgraphBool⟩
  have hgraphRows' :
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        targetGammaBoundary graphValue.1 := by
    simpa [compactNumericChildResultRowCoordinatesOf] using hgraphRows
  have hgraphLength' : graphValue.1.length = targetGammaCount := by
    simpa [compactNumericChildResultRowCoordinatesOf] using hgraphLength
  have hgraphBool' :
      compactAdditiveBoolTag graphValue.2 = targetBoolValue := by
    simpa [compactNumericChildResultRowCoordinatesOf] using hgraphBool
  have hgraphActual : graphValue = target.getI targetIndex :=
    CompactNumericChildResultCoreGraph.realizedValue_eq
      htargetCore htargetLayout hgraphLayout
  have hgamma : graphValue.1 = expectedGamma := by
    rw [← hgraphLength'] at hgammaRows
    exact (compactAdditiveNatListListSameRows_iff_eq
      hexpectedRows hgraphRows').mp hgammaRows
  have hboolTag : compactAdditiveBoolTag graphValue.2 =
      compactAdditiveBoolTag expectedResult := by
    rw [hgraphBool', hbool]
  have hresult : graphValue.2 = expectedResult :=
    compactAdditiveBoolTag_injective hboolTag
  have hgraphExpected : graphValue = (expectedGamma, expectedResult) :=
    Prod.ext hgamma hresult
  exact hgraphActual.symm.trans hgraphExpected

theorem CompactNumericChildResultBoundedHeadEq.of_value_eq
    {tokenTable width tokenCount targetBoundary expectedGammaBoundary
      tableWidth valueBound targetIndex : Nat}
    {expectedGamma : List (List Nat)} {expectedResult : Bool}
    {target : List CompactNumericChildResult}
    (htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound)
    (htargetIndex : targetIndex < target.length)
    (hexpectedRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        expectedGammaBoundary expectedGamma)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hvalue : target.getI targetIndex = (expectedGamma, expectedResult)) :
    CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount targetBoundary
        expectedGammaBoundary expectedGamma.length valueBound
        targetIndex (compactAdditiveBoolTag expectedResult) := by
  rcases htargetGraph.2 targetIndex htargetIndex with
    ⟨targetStart, htargetStartBound,
      targetFinish, htargetFinishBound,
      targetGammaFinish, htargetGammaFinishBound,
      targetGammaCount, htargetGammaCountBound,
      targetGammaBoundary, htargetGammaBoundaryBound,
      targetBoolValue, htargetBoolValueBound,
      targetGammaBoundarySize, htargetGammaBoundarySizeBound,
      htargetStartEntry, htargetFinishEntry, htargetCore⟩
  rcases htargetRows targetIndex htargetIndex with
    ⟨actualTargetStart, _hactualTargetStart,
      actualTargetFinish, _hactualTargetFinish,
      hactualTargetStartEntry, hactualTargetFinishEntry, htargetLayout⟩
  have htargetStart : targetStart = actualTargetStart :=
    (CompactFixedWidthEntry.value_eq_tableValue htargetStartEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualTargetStartEntry).symm
  have htargetFinish : targetFinish = actualTargetFinish :=
    (CompactFixedWidthEntry.value_eq_tableValue htargetFinishEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue
        hactualTargetFinishEntry).symm
  subst actualTargetStart
  subst actualTargetFinish
  rcases CompactNumericChildResultCoreGraph.realizeDirectLayoutWithRows
      htargetCore with
    ⟨graphValue, hgraphLayout, hgraphRows,
      hgraphLength, hgraphBool⟩
  have hgraphRows' :
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        targetGammaBoundary graphValue.1 := by
    simpa [compactNumericChildResultRowCoordinatesOf] using hgraphRows
  have hgraphLength' : graphValue.1.length = targetGammaCount := by
    simpa [compactNumericChildResultRowCoordinatesOf] using hgraphLength
  have hgraphBool' :
      compactAdditiveBoolTag graphValue.2 = targetBoolValue := by
    simpa [compactNumericChildResultRowCoordinatesOf] using hgraphBool
  have hgraphActual : graphValue = target.getI targetIndex :=
    CompactNumericChildResultCoreGraph.realizedValue_eq
      htargetCore htargetLayout hgraphLayout
  have hgraphExpected : graphValue = (expectedGamma, expectedResult) :=
    hgraphActual.trans hvalue
  have hgammaRows : CompactAdditiveNatListListSameRows
      tokenTable width tokenCount
        expectedGammaBoundary expectedGamma.length
        targetGammaBoundary targetGammaCount := by
    rw [← hgraphLength']
    exact (compactAdditiveNatListListSameRows_iff_eq
      hexpectedRows hgraphRows').mpr (congrArg Prod.fst hgraphExpected)
  have hbool : targetBoolValue = compactAdditiveBoolTag expectedResult := by
    rw [← hgraphBool']
    exact congrArg compactAdditiveBoolTag
      (congrArg Prod.snd hgraphExpected)
  exact ⟨targetStart, htargetStartBound,
    targetFinish, htargetFinishBound,
    targetGammaFinish, htargetGammaFinishBound,
    targetGammaCount, htargetGammaCountBound,
    targetGammaBoundary, htargetGammaBoundaryBound,
    targetBoolValue, htargetBoolValueBound,
    targetGammaBoundarySize, htargetGammaBoundarySizeBound,
    htargetStartEntry, htargetFinishEntry,
    htargetCore, hgammaRows, hbool⟩

theorem compactNumericChildResultBoundedHeadEq_iff_eq
    {tokenTable width tokenCount targetBoundary expectedGammaBoundary
      tableWidth valueBound targetIndex : Nat}
    {expectedGamma : List (List Nat)} {expectedResult : Bool}
    {target : List CompactNumericChildResult}
    (htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound)
    (htargetIndex : targetIndex < target.length)
    (hexpectedRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        expectedGammaBoundary expectedGamma)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    CompactNumericChildResultBoundedHeadEq
        tokenTable width tokenCount targetBoundary
          expectedGammaBoundary expectedGamma.length valueBound
          targetIndex (compactAdditiveBoolTag expectedResult) ↔
      target.getI targetIndex = (expectedGamma, expectedResult) := by
  constructor
  · exact fun hhead => hhead.value_eq
      htargetIndex hexpectedRows htargetRows
  · exact CompactNumericChildResultBoundedHeadEq.of_value_eq
      htargetGraph htargetIndex hexpectedRows htargetRows

theorem CompactNumericChildResultBoundedHeadEq.exists_boolTag
    {tokenTable width tokenCount targetBoundary
      expectedGammaBoundary expectedGammaCount valueBound
      targetIndex expectedBool : Nat}
    (hhead : CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount targetBoundary
        expectedGammaBoundary expectedGammaCount valueBound
        targetIndex expectedBool) :
    ∃ result : Bool, expectedBool = compactAdditiveBoolTag result := by
  rcases hhead with
    ⟨_targetStart, _htargetStart,
      _targetFinish, _htargetFinish,
      _targetGammaFinish, _htargetGammaFinish,
      _targetGammaCount, _htargetGammaCount,
      _targetGammaBoundary, _htargetGammaBoundary,
      targetBoolValue, _htargetBoolValue,
      _targetGammaBoundarySize, _htargetGammaBoundarySize,
      _hstartEntry, _hfinishEntry, hcore, _hgammaRows, hbool⟩
  rcases hcore.2.2.2.2.exists_bool with ⟨result, hresult⟩
  refine ⟨result, hbool.symm.trans ?_⟩
  simpa [compactNumericChildResultRowCoordinatesOf,
    compactAdditiveBoolTag] using hresult

#print axioms compactNumericChildResultBoundedHeadEqDef_spec
#print axioms compactNumericChildResultBoundedHeadEqDef_sigmaZero
#print axioms CompactNumericChildResultBoundedHeadEq.value_eq
#print axioms CompactNumericChildResultBoundedHeadEq.of_value_eq
#print axioms compactNumericChildResultBoundedHeadEq_iff_eq
#print axioms CompactNumericChildResultBoundedHeadEq.exists_boolTag

end FoundationCompactNumericListedDirectChildResultBoundedHeadEquality
