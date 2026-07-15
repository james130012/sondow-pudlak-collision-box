import integration.FoundationCompactNumericListedDirectNatListListSameRows
import integration.FoundationCompactNumericListedDirectVerifierValueRealization

/-!
# Direct equality of two verifier child-result rows

A child result consists of a nested formula context followed by one Boolean.
The bounded graph below parses both rows, compares every context row directly,
and compares the Boolean tags.  Under the real direct layouts it is equivalent
to equality of the represented child results.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectChildResultRowEquality

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierChildResultFormula
open FoundationCompactNumericListedDirectVerifierValueRealization
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectNatListListSameRows

def CompactNumericChildResultRowEqGraph
    (tokenTable width tokenCount : Nat)
    (sourceCoordinates targetCoordinates :
      CompactNumericChildResultRowCoordinates)
    (sourceSizeWitness targetSizeWitness :
      CompactNumericChildResultSizeWitness) : Prop :=
  CompactNumericChildResultCoreGraph tokenTable width tokenCount
      sourceCoordinates sourceSizeWitness ∧
    CompactNumericChildResultCoreGraph tokenTable width tokenCount
      targetCoordinates targetSizeWitness ∧
    CompactAdditiveNatListListSameRows tokenTable width tokenCount
      sourceCoordinates.gammaBoundary sourceCoordinates.gammaCount
      targetCoordinates.gammaBoundary targetCoordinates.gammaCount ∧
    sourceCoordinates.boolValue = targetCoordinates.boolValue

def compactNumericChildResultRowEqGraphDef :
    𝚺₀.Semisentence 17 := .mkSigma
  “tokenTable width tokenCount
      sourceStart sourceFinish sourceGammaFinish sourceGammaCount
      sourceGammaBoundary sourceBoolValue sourceGammaBoundarySize
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBoolValue targetGammaBoundarySize.
    !(compactNumericChildResultCoreGraphDef)
      tokenTable width tokenCount
        sourceStart sourceFinish sourceGammaFinish sourceGammaCount
        sourceGammaBoundary sourceBoolValue sourceGammaBoundarySize ∧
    !(compactNumericChildResultCoreGraphDef)
      tokenTable width tokenCount
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBoolValue targetGammaBoundarySize ∧
    !(compactAdditiveNatListListSameRowsDef)
      tokenTable width tokenCount
        sourceGammaBoundary sourceGammaCount
        targetGammaBoundary targetGammaCount ∧
    sourceBoolValue = targetBoolValue”

def compactNumericChildResultRowEqGraphEnvironment
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceGammaFinish sourceGammaCount
      sourceGammaBoundary sourceBoolValue sourceGammaBoundarySize
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBoolValue targetGammaBoundarySize : Nat) :
    Fin 17 → Nat :=
  ![tokenTable, width, tokenCount,
    sourceStart, sourceFinish, sourceGammaFinish, sourceGammaCount,
    sourceGammaBoundary, sourceBoolValue, sourceGammaBoundarySize,
    targetStart, targetFinish, targetGammaFinish, targetGammaCount,
    targetGammaBoundary, targetBoolValue, targetGammaBoundarySize]

@[simp] theorem compactNumericChildResultRowEqGraphDef_spec
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceGammaFinish sourceGammaCount
      sourceGammaBoundary sourceBoolValue sourceGammaBoundarySize
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBoolValue targetGammaBoundarySize : Nat) :
    compactNumericChildResultRowEqGraphDef.val.Evalb
        (compactNumericChildResultRowEqGraphEnvironment
          tokenTable width tokenCount
          sourceStart sourceFinish sourceGammaFinish sourceGammaCount
          sourceGammaBoundary sourceBoolValue sourceGammaBoundarySize
          targetStart targetFinish targetGammaFinish targetGammaCount
          targetGammaBoundary targetBoolValue targetGammaBoundarySize) ↔
      CompactNumericChildResultRowEqGraph tokenTable width tokenCount
        (compactNumericChildResultRowCoordinatesOf
          sourceStart sourceFinish sourceGammaFinish sourceGammaCount
          sourceGammaBoundary sourceBoolValue)
        (compactNumericChildResultRowCoordinatesOf
          targetStart targetFinish targetGammaFinish targetGammaCount
          targetGammaBoundary targetBoolValue)
        { gammaBoundarySize := sourceGammaBoundarySize }
        { gammaBoundarySize := targetGammaBoundarySize } := by
  let env := compactNumericChildResultRowEqGraphEnvironment
    tokenTable width tokenCount
    sourceStart sourceFinish sourceGammaFinish sourceGammaCount
    sourceGammaBoundary sourceBoolValue sourceGammaBoundarySize
    targetStart targetFinish targetGammaFinish targetGammaCount
    targetGammaBoundary targetBoolValue targetGammaBoundarySize
  change compactNumericChildResultRowEqGraphDef.val.Evalb env ↔ _
  have hsourceEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #3, #4,
          #5, #6, #7, #8, #9]) =
        ![tokenTable, width, tokenCount,
          sourceStart, sourceFinish, sourceGammaFinish, sourceGammaCount,
          sourceGammaBoundary, sourceBoolValue, sourceGammaBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have htargetEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #10, #11,
          #12, #13, #14, #15, #16]) =
        ![tokenTable, width, tokenCount,
          targetStart, targetFinish, targetGammaFinish, targetGammaCount,
          targetGammaBoundary, targetBoolValue, targetGammaBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hrowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2,
          #7, #6, #14, #13]) =
        ![tokenTable, width, tokenCount,
          sourceGammaBoundary, sourceGammaCount,
          targetGammaBoundary, targetGammaCount] := by
    funext index
    fin_cases index <;> rfl
  have hsourceBool : env 8 = sourceBoolValue := rfl
  have htargetBool : env 15 = targetBoolValue := rfl
  have hsourceCore :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #3, #4,
              #5, #6, #7, #8, #9])
          Empty.elim) compactNumericChildResultCoreGraphDef.val ↔
        CompactNumericChildResultCoreGraph tokenTable width tokenCount
          (compactNumericChildResultRowCoordinatesOf
            sourceStart sourceFinish sourceGammaFinish sourceGammaCount
            sourceGammaBoundary sourceBoolValue)
          { gammaBoundarySize := sourceGammaBoundarySize } := by
    rw [hsourceEnv]
    exact compactNumericChildResultCoreGraphDef_spec
      tokenTable width tokenCount
      sourceStart sourceFinish sourceGammaFinish sourceGammaCount
      sourceGammaBoundary sourceBoolValue sourceGammaBoundarySize
  have htargetCore :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #10, #11,
              #12, #13, #14, #15, #16])
          Empty.elim) compactNumericChildResultCoreGraphDef.val ↔
        CompactNumericChildResultCoreGraph tokenTable width tokenCount
          (compactNumericChildResultRowCoordinatesOf
            targetStart targetFinish targetGammaFinish targetGammaCount
            targetGammaBoundary targetBoolValue)
          { gammaBoundarySize := targetGammaBoundarySize } := by
    rw [htargetEnv]
    exact compactNumericChildResultCoreGraphDef_spec
      tokenTable width tokenCount
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBoolValue targetGammaBoundarySize
  have hrows :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2,
              #7, #6, #14, #13])
          Empty.elim) compactAdditiveNatListListSameRowsDef.val ↔
        CompactAdditiveNatListListSameRows tokenTable width tokenCount
          sourceGammaBoundary sourceGammaCount
          targetGammaBoundary targetGammaCount := by
    rw [hrowsEnv]
    exact compactAdditiveNatListListSameRowsDef_spec
      tokenTable width tokenCount
      sourceGammaBoundary sourceGammaCount
      targetGammaBoundary targetGammaCount
  simp [compactNumericChildResultRowEqGraphDef,
    CompactNumericChildResultRowEqGraph,
    compactNumericChildResultRowCoordinatesOf,
    hsourceCore, htargetCore, hrows, hsourceBool, htargetBool]

theorem compactNumericChildResultRowEqGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericChildResultRowEqGraphDef.val := by
  simp [compactNumericChildResultRowEqGraphDef]

theorem CompactNumericChildResultCoreGraph.realizeDirectLayoutWithRows
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactNumericChildResultRowCoordinates}
    {sizeWitness : CompactNumericChildResultSizeWitness}
    (hgraph : CompactNumericChildResultCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    ∃ value : CompactNumericChildResult,
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        coordinates.start coordinates.finish value ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        coordinates.gammaBoundary value.1 ∧
      value.1.length = coordinates.gammaCount ∧
      compactAdditiveBoolTag value.2 = coordinates.boolValue := by
  rcases hgraph with
    ⟨hgammaLayout, hgammaRows, hgammaSizeEq,
      hgammaSize, hbool⟩
  have hgammaBoundarySize :
      Nat.size coordinates.gammaBoundary ≤
        (coordinates.gammaCount + 1) * tokenCount := by
    rw [← hgammaSizeEq]
    exact hgammaSize
  rcases CompactAdditiveNatListListRowsWellFormed.realizeDirectLayout
      hgammaLayout hgammaRows hgammaBoundarySize with
    ⟨gamma, hgammaLength, _hgamma, hgammaValueRows⟩
  rcases hbool.exists_bool with ⟨result, hresult⟩
  have hresultTag :
      coordinates.boolValue = compactAdditiveBoolTag result := by
    simpa [compactAdditiveBoolTag] using hresult
  have hstartGamma : coordinates.start < coordinates.gammaFinish := by
    rcases hgammaLayout with
      ⟨bodyStart, _hbodyStart, hheader, hboundary⟩
    have hbodyStart : bodyStart = coordinates.start + 1 :=
      hheader.1.2.1
    have hbodyFinish : bodyStart ≤ coordinates.gammaFinish :=
      CompactAdditiveBoundaryTable.start_le_finish hboundary
    omega
  have hproduct : CompactAdditiveProductSplit tokenCount
      coordinates.start coordinates.gammaFinish coordinates.finish := by
    have hfinishEq :
        coordinates.finish = coordinates.gammaFinish + 1 :=
      hbool.1.2.1
    have hmiddleBound : coordinates.gammaFinish < tokenCount :=
      hbool.1.1
    exact ⟨hstartGamma, by omega, by omega⟩
  let value : CompactNumericChildResult := (gamma, result)
  refine ⟨value, ?_, ?_, ?_, hresultTag.symm⟩
  · refine ⟨coordinates.gammaFinish, coordinates.gammaBoundary,
      coordinates.boolValue, hproduct, ?_, ?_, hresultTag,
      hbool, ?_⟩
    · simpa [value, hgammaLength] using hgammaLayout
    · simpa [value] using hgammaValueRows
    · simpa [value, hgammaLength, hgammaSizeEq] using hgammaSize
  · simpa [value] using hgammaValueRows
  · simpa [value] using hgammaLength

theorem CompactNumericChildResultCoreGraph.realizedValue_eq
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactNumericChildResultRowCoordinates}
    {sizeWitness : CompactNumericChildResultSizeWitness}
    {actualValue realizedValue : CompactNumericChildResult}
    (hcore : CompactNumericChildResultCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (hactual : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount coordinates.start coordinates.finish
        actualValue)
    (hrealized : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount coordinates.start coordinates.finish
        realizedValue) :
    realizedValue = actualValue := by
  have hbounds := hcore.bounds
  have hstartFinish : coordinates.start ≤ coordinates.finish := by
    have hlayout := hrealized
    rcases hlayout with
      ⟨gammaFinish, _gammaBoundary, _boolValue,
        hproduct, _hgammaLayout, _hgammaRows,
        _hboolValue, _hbool, _hgammaSize⟩
    rcases hproduct with
      ⟨hstartGamma, hgammaFinish, _hfinishBound⟩
    omega
  have hslices := CompactFixedWidthTokenSlicesEq.refl
    (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
    hstartFinish hbounds.finish_le
  exact CompactFixedWidthTokenSlicesEq.childResultValue_eq
    hslices hactual hrealized

theorem CompactNumericChildResultRowEqGraph.value_eq
    {tokenTable width tokenCount : Nat}
    {sourceCoordinates targetCoordinates :
      CompactNumericChildResultRowCoordinates}
    {sourceSizeWitness targetSizeWitness :
      CompactNumericChildResultSizeWitness}
    {sourceValue targetValue : CompactNumericChildResult}
    (heq : CompactNumericChildResultRowEqGraph
      tokenTable width tokenCount sourceCoordinates targetCoordinates
        sourceSizeWitness targetSizeWitness)
    (hsource : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount sourceCoordinates.start
        sourceCoordinates.finish sourceValue)
    (htarget : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount targetCoordinates.start
        targetCoordinates.finish targetValue) :
    targetValue = sourceValue := by
  rcases heq with
    ⟨hsourceCore, htargetCore, hgammaRowsEq, hboolEq⟩
  rcases CompactNumericChildResultCoreGraph.realizeDirectLayoutWithRows
      hsourceCore with
    ⟨sourceGraphValue, hsourceGraphLayout,
      hsourceGraphRows, hsourceGraphLength, hsourceGraphBool⟩
  rcases CompactNumericChildResultCoreGraph.realizeDirectLayoutWithRows
      htargetCore with
    ⟨targetGraphValue, htargetGraphLayout,
      htargetGraphRows, htargetGraphLength, htargetGraphBool⟩
  rw [← hsourceGraphLength, ← htargetGraphLength] at hgammaRowsEq
  have hgammaEq : targetGraphValue.1 = sourceGraphValue.1 :=
    (compactAdditiveNatListListSameRows_iff_eq
      hsourceGraphRows htargetGraphRows).mp hgammaRowsEq
  have hboolTagEq :
      compactAdditiveBoolTag targetGraphValue.2 =
        compactAdditiveBoolTag sourceGraphValue.2 := by
    rw [htargetGraphBool, hsourceGraphBool]
    exact hboolEq.symm
  have hboolValueEq : targetGraphValue.2 = sourceGraphValue.2 :=
    compactAdditiveBoolTag_injective hboolTagEq
  have hgraphValueEq : targetGraphValue = sourceGraphValue :=
    Prod.ext hgammaEq hboolValueEq
  have hsourceValueEq : sourceGraphValue = sourceValue :=
    CompactNumericChildResultCoreGraph.realizedValue_eq
      hsourceCore hsource hsourceGraphLayout
  have htargetValueEq : targetGraphValue = targetValue :=
    CompactNumericChildResultCoreGraph.realizedValue_eq
      htargetCore htarget htargetGraphLayout
  calc
    targetValue = targetGraphValue := htargetValueEq.symm
    _ = sourceGraphValue := hgraphValueEq
    _ = sourceValue := hsourceValueEq

theorem CompactNumericChildResultRowEqGraph.of_value_eq
    {tokenTable width tokenCount : Nat}
    {sourceCoordinates targetCoordinates :
      CompactNumericChildResultRowCoordinates}
    {sourceSizeWitness targetSizeWitness :
      CompactNumericChildResultSizeWitness}
    {sourceValue targetValue : CompactNumericChildResult}
    (hsourceCore : CompactNumericChildResultCoreGraph
      tokenTable width tokenCount sourceCoordinates sourceSizeWitness)
    (htargetCore : CompactNumericChildResultCoreGraph
      tokenTable width tokenCount targetCoordinates targetSizeWitness)
    (hsource : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount sourceCoordinates.start
        sourceCoordinates.finish sourceValue)
    (htarget : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount targetCoordinates.start
        targetCoordinates.finish targetValue)
    (hvalue : targetValue = sourceValue) :
    CompactNumericChildResultRowEqGraph tokenTable width tokenCount
      sourceCoordinates targetCoordinates
        sourceSizeWitness targetSizeWitness := by
  rcases CompactNumericChildResultCoreGraph.realizeDirectLayoutWithRows
      hsourceCore with
    ⟨sourceGraphValue, hsourceGraphLayout,
      hsourceGraphRows, hsourceGraphLength, hsourceGraphBool⟩
  rcases CompactNumericChildResultCoreGraph.realizeDirectLayoutWithRows
      htargetCore with
    ⟨targetGraphValue, htargetGraphLayout,
      htargetGraphRows, htargetGraphLength, htargetGraphBool⟩
  have hsourceValueEq : sourceGraphValue = sourceValue :=
    CompactNumericChildResultCoreGraph.realizedValue_eq
      hsourceCore hsource hsourceGraphLayout
  have htargetValueEq : targetGraphValue = targetValue :=
    CompactNumericChildResultCoreGraph.realizedValue_eq
      htargetCore htarget htargetGraphLayout
  have hgraphValueEq : targetGraphValue = sourceGraphValue := by
    calc
      targetGraphValue = targetValue := htargetValueEq
      _ = sourceValue := hvalue
      _ = sourceGraphValue := hsourceValueEq.symm
  have hgammaRows : CompactAdditiveNatListListSameRows
      tokenTable width tokenCount
        sourceCoordinates.gammaBoundary sourceCoordinates.gammaCount
        targetCoordinates.gammaBoundary targetCoordinates.gammaCount := by
    rw [← hsourceGraphLength, ← htargetGraphLength]
    exact (compactAdditiveNatListListSameRows_iff_eq
      hsourceGraphRows htargetGraphRows).mpr
        (congrArg Prod.fst hgraphValueEq)
  have hbool :
      sourceCoordinates.boolValue = targetCoordinates.boolValue := by
    calc
      sourceCoordinates.boolValue =
          compactAdditiveBoolTag sourceGraphValue.2 := hsourceGraphBool.symm
      _ = compactAdditiveBoolTag targetGraphValue.2 := by
        exact congrArg compactAdditiveBoolTag
          (congrArg Prod.snd hgraphValueEq).symm
      _ = targetCoordinates.boolValue := htargetGraphBool
  exact ⟨hsourceCore, htargetCore, hgammaRows, hbool⟩

theorem compactNumericChildResultRowEqGraph_iff_eq
    {tokenTable width tokenCount : Nat}
    {sourceCoordinates targetCoordinates :
      CompactNumericChildResultRowCoordinates}
    {sourceSizeWitness targetSizeWitness :
      CompactNumericChildResultSizeWitness}
    {sourceValue targetValue : CompactNumericChildResult}
    (hsourceCore : CompactNumericChildResultCoreGraph
      tokenTable width tokenCount sourceCoordinates sourceSizeWitness)
    (htargetCore : CompactNumericChildResultCoreGraph
      tokenTable width tokenCount targetCoordinates targetSizeWitness)
    (hsource : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount sourceCoordinates.start
        sourceCoordinates.finish sourceValue)
    (htarget : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount targetCoordinates.start
        targetCoordinates.finish targetValue) :
    CompactNumericChildResultRowEqGraph tokenTable width tokenCount
        sourceCoordinates targetCoordinates
          sourceSizeWitness targetSizeWitness ↔
      targetValue = sourceValue := by
  constructor
  · exact fun heq => heq.value_eq hsource htarget
  · exact CompactNumericChildResultRowEqGraph.of_value_eq
      hsourceCore htargetCore hsource htarget

theorem CompactNumericChildResultDirectLayout.exists_rowEqGraph_of_eq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat}
    {sourceValue targetValue : CompactNumericChildResult}
    (hsource : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceValue)
    (htarget : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetValue)
    (hvalue : targetValue = sourceValue) :
    ∃ sourceCoordinates sourceSizeWitness
        targetCoordinates targetSizeWitness,
      sourceCoordinates.start = sourceStart ∧
      sourceCoordinates.finish = sourceFinish ∧
      targetCoordinates.start = targetStart ∧
      targetCoordinates.finish = targetFinish ∧
      CompactNumericChildResultRowEqGraph tokenTable width tokenCount
        sourceCoordinates targetCoordinates
          sourceSizeWitness targetSizeWitness := by
  subst targetValue
  rcases hsource with
    ⟨sourceGammaFinish, sourceGammaBoundary, sourceBoolValue,
      _hsourceProduct, hsourceGammaLayout, hsourceGammaRows,
      hsourceBoolValue, hsourceBool, hsourceGammaSize⟩
  rcases htarget with
    ⟨targetGammaFinish, targetGammaBoundary, targetBoolValue,
      _htargetProduct, htargetGammaLayout, htargetGammaRows,
      htargetBoolValue, htargetBool, htargetGammaSize⟩
  let sourceCoordinates : CompactNumericChildResultRowCoordinates :=
    { start := sourceStart
      finish := sourceFinish
      gammaFinish := sourceGammaFinish
      gammaCount := sourceValue.1.length
      gammaBoundary := sourceGammaBoundary
      boolValue := sourceBoolValue }
  let targetCoordinates : CompactNumericChildResultRowCoordinates :=
    { start := targetStart
      finish := targetFinish
      gammaFinish := targetGammaFinish
      gammaCount := sourceValue.1.length
      gammaBoundary := targetGammaBoundary
      boolValue := targetBoolValue }
  let sourceSizeWitness : CompactNumericChildResultSizeWitness :=
    { gammaBoundarySize := Nat.size sourceGammaBoundary }
  let targetSizeWitness : CompactNumericChildResultSizeWitness :=
    { gammaBoundarySize := Nat.size targetGammaBoundary }
  have hsourceCore : CompactNumericChildResultCoreGraph
      tokenTable width tokenCount sourceCoordinates sourceSizeWitness := by
    exact ⟨hsourceGammaLayout,
      CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
        hsourceGammaRows,
      rfl, hsourceGammaSize, hsourceBool⟩
  have htargetCore : CompactNumericChildResultCoreGraph
      tokenTable width tokenCount targetCoordinates targetSizeWitness := by
    exact ⟨htargetGammaLayout,
      CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
        htargetGammaRows,
      rfl, htargetGammaSize, htargetBool⟩
  have hrowsEq : CompactAdditiveNatListListSameRows
      tokenTable width tokenCount
        sourceGammaBoundary sourceValue.1.length
        targetGammaBoundary sourceValue.1.length :=
    (compactAdditiveNatListListSameRows_iff_eq
      hsourceGammaRows htargetGammaRows).mpr rfl
  have hboolEq : sourceBoolValue = targetBoolValue := by
    rw [hsourceBoolValue, htargetBoolValue]
  exact ⟨sourceCoordinates, sourceSizeWitness,
    targetCoordinates, targetSizeWitness,
    rfl, rfl, rfl, rfl,
    hsourceCore, htargetCore, hrowsEq, hboolEq⟩

theorem compactNumericChildResultExistsRowEqGraph_iff_eq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat}
    {sourceValue targetValue : CompactNumericChildResult}
    (hsource : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceValue)
    (htarget : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetValue) :
    (∃ sourceCoordinates sourceSizeWitness
        targetCoordinates targetSizeWitness,
      sourceCoordinates.start = sourceStart ∧
      sourceCoordinates.finish = sourceFinish ∧
      targetCoordinates.start = targetStart ∧
      targetCoordinates.finish = targetFinish ∧
      CompactNumericChildResultRowEqGraph tokenTable width tokenCount
        sourceCoordinates targetCoordinates
          sourceSizeWitness targetSizeWitness) ↔
      targetValue = sourceValue := by
  constructor
  · rintro ⟨sourceCoordinates, sourceSizeWitness,
      targetCoordinates, targetSizeWitness,
      hsourceStart, hsourceFinish, htargetStart, htargetFinish, heq⟩
    subst sourceStart
    subst sourceFinish
    subst targetStart
    subst targetFinish
    exact heq.value_eq hsource htarget
  · exact fun hvalue =>
      CompactNumericChildResultDirectLayout.exists_rowEqGraph_of_eq
        hsource htarget hvalue

#print axioms compactNumericChildResultRowEqGraphDef_spec
#print axioms compactNumericChildResultRowEqGraphDef_sigmaZero
#print axioms CompactNumericChildResultCoreGraph.realizeDirectLayoutWithRows
#print axioms CompactNumericChildResultCoreGraph.realizedValue_eq
#print axioms CompactNumericChildResultRowEqGraph.value_eq
#print axioms CompactNumericChildResultRowEqGraph.of_value_eq
#print axioms compactNumericChildResultRowEqGraph_iff_eq
#print axioms CompactNumericChildResultDirectLayout.exists_rowEqGraph_of_eq
#print axioms compactNumericChildResultExistsRowEqGraph_iff_eq

end FoundationCompactNumericListedDirectChildResultRowEquality
