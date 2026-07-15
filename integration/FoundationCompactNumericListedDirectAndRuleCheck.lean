import integration.FoundationCompactNumericListedDirectFormulaConstructorMembership

/-!
# Direct bounded graph for the listed conjunction rule check

The graph uses only stored task and child coordinates.  Its exactness theorem
identifies the arithmetic result bit with the public `compactAndRuleCheck`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectAndRuleCheck

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericFormulaConstructors
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaSetEqCons
open FoundationCompactNumericListedDirectFormulaConstructorMembership

def CompactAdditiveAndRuleCheck
    (tokenTable width tokenCount
      gammaBoundary gammaCount
      leftFormulaStart leftFormulaFinish leftFormulaCount
      rightFormulaStart rightFormulaFinish rightFormulaCount
      leftConclusionBoundary leftConclusionCount leftBoolValue
      rightConclusionBoundary rightConclusionCount rightBoolValue
      resultBoolValue : Nat) : Prop :=
  resultBoolValue <= 1 ∧
    (resultBoolValue = 1 ↔
      CompactAdditiveBinaryFormulaConstructorMemberRows
        tokenTable width tokenCount 4
          gammaBoundary gammaCount
          leftFormulaStart leftFormulaFinish leftFormulaCount
          rightFormulaStart rightFormulaFinish rightFormulaCount ∧
      CompactAdditiveFormulaSetEqConsRows
        tokenTable width tokenCount
          leftConclusionBoundary leftConclusionCount
          leftFormulaStart leftFormulaFinish
          gammaBoundary gammaCount ∧
      CompactAdditiveFormulaSetEqConsRows
        tokenTable width tokenCount
          rightConclusionBoundary rightConclusionCount
          rightFormulaStart rightFormulaFinish
          gammaBoundary gammaCount ∧
      leftBoolValue = 1 ∧ rightBoolValue = 1)

def compactAdditiveAndRuleCheckDef :
    𝚺₀.Semisentence 18 := .mkSigma
  “tokenTable width tokenCount
      gammaBoundary gammaCount
      leftFormulaStart leftFormulaFinish leftFormulaCount
      rightFormulaStart rightFormulaFinish rightFormulaCount
      leftConclusionBoundary leftConclusionCount leftBoolValue
      rightConclusionBoundary rightConclusionCount rightBoolValue
      resultBoolValue.
    resultBoolValue ≤ 1 ∧
    (resultBoolValue = 1 ↔
      !(compactAdditiveBinaryFormulaConstructorMemberRowsDef)
        tokenTable width tokenCount 4
          gammaBoundary gammaCount
          leftFormulaStart leftFormulaFinish leftFormulaCount
          rightFormulaStart rightFormulaFinish rightFormulaCount ∧
      !(compactAdditiveFormulaSetEqConsRowsDef)
        tokenTable width tokenCount
          leftConclusionBoundary leftConclusionCount
          leftFormulaStart leftFormulaFinish
          gammaBoundary gammaCount ∧
      !(compactAdditiveFormulaSetEqConsRowsDef)
        tokenTable width tokenCount
          rightConclusionBoundary rightConclusionCount
          rightFormulaStart rightFormulaFinish
          gammaBoundary gammaCount ∧
      leftBoolValue = 1 ∧ rightBoolValue = 1)”

@[simp] theorem compactAdditiveAndRuleCheckDef_spec
    (tokenTable width tokenCount
      gammaBoundary gammaCount
      leftFormulaStart leftFormulaFinish leftFormulaCount
      rightFormulaStart rightFormulaFinish rightFormulaCount
      leftConclusionBoundary leftConclusionCount leftBoolValue
      rightConclusionBoundary rightConclusionCount rightBoolValue
      resultBoolValue : Nat) :
    compactAdditiveAndRuleCheckDef.val.Evalb
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount,
          leftFormulaStart, leftFormulaFinish, leftFormulaCount,
          rightFormulaStart, rightFormulaFinish, rightFormulaCount,
          leftConclusionBoundary, leftConclusionCount, leftBoolValue,
          rightConclusionBoundary, rightConclusionCount, rightBoolValue,
          resultBoolValue] ↔
      CompactAdditiveAndRuleCheck tokenTable width tokenCount
        gammaBoundary gammaCount
        leftFormulaStart leftFormulaFinish leftFormulaCount
        rightFormulaStart rightFormulaFinish rightFormulaCount
        leftConclusionBoundary leftConclusionCount leftBoolValue
        rightConclusionBoundary rightConclusionCount rightBoolValue
        resultBoolValue := by
  let env : Fin 18 → Nat :=
    ![tokenTable, width, tokenCount,
      gammaBoundary, gammaCount,
      leftFormulaStart, leftFormulaFinish, leftFormulaCount,
      rightFormulaStart, rightFormulaFinish, rightFormulaCount,
      leftConclusionBoundary, leftConclusionCount, leftBoolValue,
      rightConclusionBoundary, rightConclusionCount, rightBoolValue,
      resultBoolValue]
  change compactAdditiveAndRuleCheckDef.val.Evalb env ↔ _
  have hmemberEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 18), #1, #2,
          (↑(4 : Nat) : Semiterm ℒₒᵣ Empty 18),
          #3, #4, #5, #6, #7, #8, #9, #10]) =
        ![tokenTable, width, tokenCount, 4,
          gammaBoundary, gammaCount,
          leftFormulaStart, leftFormulaFinish, leftFormulaCount,
          rightFormulaStart, rightFormulaFinish, rightFormulaCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hleftEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 18), #1, #2,
          #11, #12, #5, #6, #3, #4]) =
        ![tokenTable, width, tokenCount,
          leftConclusionBoundary, leftConclusionCount,
          leftFormulaStart, leftFormulaFinish,
          gammaBoundary, gammaCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hrightEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 18), #1, #2,
          #14, #15, #8, #9, #3, #4]) =
        ![tokenTable, width, tokenCount,
          rightConclusionBoundary, rightConclusionCount,
          rightFormulaStart, rightFormulaFinish,
          gammaBoundary, gammaCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hresultValue : env 17 = resultBoolValue := rfl
  have hleftBoolValue : env 13 = leftBoolValue := rfl
  have hrightBoolValue : env 16 = rightBoolValue := rfl
  simp [compactAdditiveAndRuleCheckDef, CompactAdditiveAndRuleCheck,
    hmemberEnv, hleftEnv, hrightEnv,
    hresultValue, hleftBoolValue, hrightBoolValue]

theorem compactAdditiveAndRuleCheckDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveAndRuleCheckDef.val := by
  simp [compactAdditiveAndRuleCheckDef]

theorem compactAdditiveAndRuleCheck_iff
    {tokenTable width tokenCount
      gammaBoundary leftFormulaStart leftFormulaFinish
      rightFormulaStart rightFormulaFinish
      leftConclusionBoundary rightConclusionBoundary
      leftBoolValue rightBoolValue resultBoolValue : Nat}
    {Gamma leftConclusion rightConclusion : List (List Nat)}
    {leftFormula rightFormula : List Nat}
    {leftValid rightValid : Bool}
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hleftFormula : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount
        leftFormulaStart leftFormulaFinish leftFormula)
    (hrightFormula : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount
        rightFormulaStart rightFormulaFinish rightFormula)
    (hleftConclusion : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        leftConclusionBoundary leftConclusion)
    (hrightConclusion : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        rightConclusionBoundary rightConclusion)
    (hleftBool : leftBoolValue = compactAdditiveBoolTag leftValid)
    (hrightBool : rightBoolValue = compactAdditiveBoolTag rightValid) :
    CompactAdditiveAndRuleCheck tokenTable width tokenCount
        gammaBoundary Gamma.length
        leftFormulaStart leftFormulaFinish leftFormula.length
        rightFormulaStart rightFormulaFinish rightFormula.length
        leftConclusionBoundary leftConclusion.length leftBoolValue
        rightConclusionBoundary rightConclusion.length rightBoolValue
        resultBoolValue ↔
      resultBoolValue = compactAdditiveBoolTag
        (compactAndRuleCheck
          (Gamma, (leftFormula, (rightFormula,
            ((leftConclusion, leftValid),
              (rightConclusion, rightValid)))))) := by
  simp only [CompactAdditiveAndRuleCheck]
  rw [compactAdditiveFormulaAndMemberRows_iff
      hGamma hleftFormula hrightFormula,
    compactAdditiveFormulaSetEqConsRows_iff_tokenCheck
      hleftConclusion hleftFormula hGamma,
    compactAdditiveFormulaSetEqConsRows_iff_tokenCheck
      hrightConclusion hrightFormula hGamma,
    hleftBool, hrightBool]
  cases hmember : tokenFormulaMem
      (tokenFormulaAnd leftFormula rightFormula) Gamma <;>
    cases hleftEq : tokenFormulaSetEq
      leftConclusion (leftFormula :: Gamma) <;>
    cases hrightEq : tokenFormulaSetEq
      rightConclusion (rightFormula :: Gamma) <;>
    cases leftValid <;> cases rightValid <;>
    simp [compactAndRuleCheck, compactAdditiveBoolTag,
      hmember, hleftEq, hrightEq] <;> omega

#print axioms compactAdditiveAndRuleCheckDef_spec
#print axioms compactAdditiveAndRuleCheckDef_sigmaZero
#print axioms compactAdditiveAndRuleCheck_iff

end FoundationCompactNumericListedDirectAndRuleCheck
