import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
import integration.FoundationCompactNumericListedDirectFormulaSetEqCons

/-!
# Direct bounded graph for cut

The negation trace is unconditional and uses the empty list as the ignored
mode-three control witness.  Consequently the arithmetic result bit agrees
with the public cut checker even on malformed numeric formula fields.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCutRuleCheck

open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaSetEqCons
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula

def CompactAdditiveCutRuleCheck
    (tokenTable width tokenCount
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
      leftBoundary leftCount leftBoolValue
      rightBoundary rightCount rightBoolValue
      negatedStart negatedFinish negatedBoundary negatedCount
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBoolValue : Nat) : Prop :=
  CompactFormulaTransformTotalExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount 3
      emptyStart emptyFinish 0
      formulaBoundary formulaCount negatedBoundary negatedCount
      emptyBoundary 0 tableWidth valueBound ∧
    resultBoolValue ≤ 1 ∧
    (resultBoolValue = 1 ↔
      CompactAdditiveFormulaSetEqConsRows
        tokenTable width tokenCount
          leftBoundary leftCount formulaStart formulaFinish
          gammaBoundary gammaCount ∧
      CompactAdditiveFormulaSetEqConsRows
        tokenTable width tokenCount
          rightBoundary rightCount negatedStart negatedFinish
          gammaBoundary gammaCount ∧
      leftBoolValue = 1 ∧ rightBoolValue = 1)

def compactAdditiveCutRuleCheckDef : 𝚺₀.Semisentence 27 := .mkSigma
  “tokenTable width tokenCount
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
      leftBoundary leftCount leftBoolValue
      rightBoundary rightCount rightBoolValue
      negatedStart negatedFinish negatedBoundary negatedCount
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBoolValue.
    !(compactFormulaTransformTotalExactBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount 3
      emptyStart emptyFinish 0
      formulaBoundary formulaCount negatedBoundary negatedCount
      emptyBoundary 0 tableWidth valueBound ∧
    resultBoolValue ≤ 1 ∧
    (resultBoolValue = 1 ↔
      !(compactAdditiveFormulaSetEqConsRowsDef)
        tokenTable width tokenCount
          leftBoundary leftCount formulaStart formulaFinish
          gammaBoundary gammaCount ∧
      !(compactAdditiveFormulaSetEqConsRowsDef)
        tokenTable width tokenCount
          rightBoundary rightCount negatedStart negatedFinish
          gammaBoundary gammaCount ∧
      leftBoolValue = 1 ∧ rightBoolValue = 1)”

@[simp] theorem compactAdditiveCutRuleCheckDef_spec
    (tokenTable width tokenCount
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
      leftBoundary leftCount leftBoolValue
      rightBoundary rightCount rightBoolValue
      negatedStart negatedFinish negatedBoundary negatedCount
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBoolValue : Nat) :
    compactAdditiveCutRuleCheckDef.val.Evalb
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount,
          formulaStart, formulaFinish, formulaBoundary, formulaCount,
          leftBoundary, leftCount, leftBoolValue,
          rightBoundary, rightCount, rightBoolValue,
          negatedStart, negatedFinish, negatedBoundary, negatedCount,
          stateBoundary, stateCount,
          emptyStart, emptyFinish, emptyBoundary,
          tableWidth, valueBound, resultBoolValue] ↔
      CompactAdditiveCutRuleCheck
        tokenTable width tokenCount
        gammaBoundary gammaCount
        formulaStart formulaFinish formulaBoundary formulaCount
        leftBoundary leftCount leftBoolValue
        rightBoundary rightCount rightBoolValue
        negatedStart negatedFinish negatedBoundary negatedCount
        stateBoundary stateCount
        emptyStart emptyFinish emptyBoundary
        tableWidth valueBound resultBoolValue := by
  let env : Fin 27 → Nat :=
    ![tokenTable, width, tokenCount,
      gammaBoundary, gammaCount,
      formulaStart, formulaFinish, formulaBoundary, formulaCount,
      leftBoundary, leftCount, leftBoolValue,
      rightBoundary, rightCount, rightBoolValue,
      negatedStart, negatedFinish, negatedBoundary, negatedCount,
      stateBoundary, stateCount,
      emptyStart, emptyFinish, emptyBoundary,
      tableWidth, valueBound, resultBoolValue]
  change compactAdditiveCutRuleCheckDef.val.Evalb env ↔ _
  have htransformEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2, #19, #20,
          (↑(3 : Nat) : Semiterm ℒₒᵣ Empty 27),
          #21, #22, (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 27),
          #7, #8, #17, #18, #23,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 27), #24, #25]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, 3,
          emptyStart, emptyFinish, 0,
          formulaBoundary, formulaCount, negatedBoundary, negatedCount,
          emptyBoundary, 0, tableWidth, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hleftEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2,
          #9, #10, #5, #6, #3, #4]) =
        ![tokenTable, width, tokenCount,
          leftBoundary, leftCount, formulaStart, formulaFinish,
          gammaBoundary, gammaCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hrightEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2,
          #12, #13, #15, #16, #3, #4]) =
        ![tokenTable, width, tokenCount,
          rightBoundary, rightCount, negatedStart, negatedFinish,
          gammaBoundary, gammaCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hleftBoolValue : env 11 = leftBoolValue := rfl
  have hrightBoolValue : env 14 = rightBoolValue := rfl
  have hresultBoolValue : env 26 = resultBoolValue := rfl
  simp [compactAdditiveCutRuleCheckDef, CompactAdditiveCutRuleCheck,
    htransformEnv, hleftEnv, hrightEnv,
    hleftBoolValue, hrightBoolValue, hresultBoolValue]

theorem compactAdditiveCutRuleCheckDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveCutRuleCheckDef.val := by
  simp [compactAdditiveCutRuleCheckDef]

theorem compactAdditiveCutRuleCheck_iff
    {tokenTable width tokenCount gammaBoundary
      formulaStart formulaFinish formulaBoundary
      leftBoundary leftBoolValue rightBoundary rightBoolValue
      negatedStart negatedFinish negatedBoundary
      stateBoundary stateCount emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBoolValue : Nat}
    {Gamma left right : List (List Nat)}
    {formula negated : List Nat}
    {leftValid rightValid : Bool}
    (htransform : CompactFormulaTransformTotalExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount 3
      emptyStart emptyFinish 0
      formulaBoundary formula.length negatedBoundary negated.length
      emptyBoundary 0 tableWidth valueBound)
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hformula : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount formulaStart formulaFinish formula)
    (hformulaRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        formulaBoundary formula)
    (hleft : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        leftBoundary left)
    (hright : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        rightBoundary right)
    (hnegated : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount negatedStart negatedFinish negated)
    (hnegatedRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        negatedBoundary negated)
    (hempty : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount emptyStart emptyFinish [])
    (hemptyRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary [])
    (hleftBool : leftBoolValue = compactAdditiveBoolTag leftValid)
    (hrightBool : rightBoolValue = compactAdditiveBoolTag rightValid) :
    CompactAdditiveCutRuleCheck
        tokenTable width tokenCount
        gammaBoundary Gamma.length
        formulaStart formulaFinish formulaBoundary formula.length
        leftBoundary left.length leftBoolValue
        rightBoundary right.length rightBoolValue
        negatedStart negatedFinish negatedBoundary negated.length
        stateBoundary stateCount
        emptyStart emptyFinish emptyBoundary
        tableWidth valueBound resultBoolValue ↔
      resultBoolValue = compactAdditiveBoolTag
        (compactCutRuleCheck
          (Gamma, (formula,
            ((left, leftValid), (right, rightValid))))) := by
  have hnegatedResult :=
    CompactFormulaTransformTotalExactBoundedGraph.sound_selfContained
      htransform hempty rfl
      hformulaRows hnegatedRows hemptyRows
  have hnegatedExact : negated =
      (compactFormulaNegationExact 0 formula).getD [] := by
    simpa [compactFormulaNegationExact] using hnegatedResult
  simp only [CompactAdditiveCutRuleCheck]
  rw [compactAdditiveFormulaSetEqConsRows_iff_tokenCheck
      hleft hformula hGamma,
    compactAdditiveFormulaSetEqConsRows_iff_tokenCheck
      hright hnegated hGamma,
    hleftBool, hrightBool]
  rw [and_iff_right htransform]
  rw [hnegatedExact]
  cases hleftEq : tokenFormulaSetEq left (formula :: Gamma) <;>
    cases hrightEq : tokenFormulaSetEq right
      ((compactFormulaNegationExact 0 formula).getD [] :: Gamma) <;>
    cases leftValid <;> cases rightValid <;>
    simp [compactCutRuleCheck, compactAdditiveBoolTag,
      hleftEq, hrightEq] <;> omega

#print axioms compactAdditiveCutRuleCheckDef_spec
#print axioms compactAdditiveCutRuleCheckDef_sigmaZero
#print axioms compactAdditiveCutRuleCheck_iff

end FoundationCompactNumericListedDirectCutRuleCheck
