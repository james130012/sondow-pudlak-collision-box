import integration.FoundationCompactNumericListedDirectFormulaSetEqTwoCons

/-!
# Direct bounded graph for the listed disjunction rule check
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectOrRuleCheck

open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericFormulaConstructors
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaConstructorMembership
open FoundationCompactNumericListedDirectFormulaSetEqTwoCons

def CompactAdditiveOrRuleCheck
    (tokenTable width tokenCount
      gammaBoundary gammaCount
      leftFormulaStart leftFormulaFinish leftFormulaCount
      rightFormulaStart rightFormulaFinish rightFormulaCount
      premiseBoundary premiseCount premiseBoolValue
      resultBoolValue : Nat) : Prop :=
  resultBoolValue <= 1 ∧
    (resultBoolValue = 1 ↔
      CompactAdditiveBinaryFormulaConstructorMemberRows
        tokenTable width tokenCount 5
          gammaBoundary gammaCount
          leftFormulaStart leftFormulaFinish leftFormulaCount
          rightFormulaStart rightFormulaFinish rightFormulaCount ∧
      CompactAdditiveFormulaSetEqTwoConsRows
        tokenTable width tokenCount
          premiseBoundary premiseCount
          leftFormulaStart leftFormulaFinish
          rightFormulaStart rightFormulaFinish
          gammaBoundary gammaCount ∧
      premiseBoolValue = 1)

def compactAdditiveOrRuleCheckDef :
    𝚺₀.Semisentence 15 := .mkSigma
  “tokenTable width tokenCount
      gammaBoundary gammaCount
      leftFormulaStart leftFormulaFinish leftFormulaCount
      rightFormulaStart rightFormulaFinish rightFormulaCount
      premiseBoundary premiseCount premiseBoolValue
      resultBoolValue.
    resultBoolValue ≤ 1 ∧
    (resultBoolValue = 1 ↔
      !(compactAdditiveBinaryFormulaConstructorMemberRowsDef)
        tokenTable width tokenCount 5
          gammaBoundary gammaCount
          leftFormulaStart leftFormulaFinish leftFormulaCount
          rightFormulaStart rightFormulaFinish rightFormulaCount ∧
      !(compactAdditiveFormulaSetEqTwoConsRowsDef)
        tokenTable width tokenCount
          premiseBoundary premiseCount
          leftFormulaStart leftFormulaFinish
          rightFormulaStart rightFormulaFinish
          gammaBoundary gammaCount ∧
      premiseBoolValue = 1)”

@[simp] theorem compactAdditiveOrRuleCheckDef_spec
    (tokenTable width tokenCount
      gammaBoundary gammaCount
      leftFormulaStart leftFormulaFinish leftFormulaCount
      rightFormulaStart rightFormulaFinish rightFormulaCount
      premiseBoundary premiseCount premiseBoolValue
      resultBoolValue : Nat) :
    compactAdditiveOrRuleCheckDef.val.Evalb
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount,
          leftFormulaStart, leftFormulaFinish, leftFormulaCount,
          rightFormulaStart, rightFormulaFinish, rightFormulaCount,
          premiseBoundary, premiseCount, premiseBoolValue,
          resultBoolValue] ↔
      CompactAdditiveOrRuleCheck tokenTable width tokenCount
        gammaBoundary gammaCount
        leftFormulaStart leftFormulaFinish leftFormulaCount
        rightFormulaStart rightFormulaFinish rightFormulaCount
        premiseBoundary premiseCount premiseBoolValue resultBoolValue := by
  let env : Fin 15 → Nat :=
    ![tokenTable, width, tokenCount,
      gammaBoundary, gammaCount,
      leftFormulaStart, leftFormulaFinish, leftFormulaCount,
      rightFormulaStart, rightFormulaFinish, rightFormulaCount,
      premiseBoundary, premiseCount, premiseBoolValue,
      resultBoolValue]
  change compactAdditiveOrRuleCheckDef.val.Evalb env ↔ _
  have hmemberEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 15), #1, #2,
          (↑(5 : Nat) : Semiterm ℒₒᵣ Empty 15),
          #3, #4, #5, #6, #7, #8, #9, #10]) =
        ![tokenTable, width, tokenCount, 5,
          gammaBoundary, gammaCount,
          leftFormulaStart, leftFormulaFinish, leftFormulaCount,
          rightFormulaStart, rightFormulaFinish, rightFormulaCount] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  have hsetEqEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 15), #1, #2,
          #11, #12, #5, #6, #8, #9, #3, #4]) =
        ![tokenTable, width, tokenCount,
          premiseBoundary, premiseCount,
          leftFormulaStart, leftFormulaFinish,
          rightFormulaStart, rightFormulaFinish,
          gammaBoundary, gammaCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hpremiseValue : env 13 = premiseBoolValue := rfl
  have hresultValue : env 14 = resultBoolValue := rfl
  simp [compactAdditiveOrRuleCheckDef, CompactAdditiveOrRuleCheck,
    hmemberEnv, hsetEqEnv, hpremiseValue, hresultValue]

theorem compactAdditiveOrRuleCheckDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveOrRuleCheckDef.val := by
  simp [compactAdditiveOrRuleCheckDef]

theorem compactAdditiveOrRuleCheck_iff
    {tokenTable width tokenCount gammaBoundary
      leftFormulaStart leftFormulaFinish
      rightFormulaStart rightFormulaFinish
      premiseBoundary premiseBoolValue resultBoolValue : Nat}
    {Gamma premise : List (List Nat)}
    {leftFormula rightFormula : List Nat} {premiseValid : Bool}
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hleftFormula : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount
        leftFormulaStart leftFormulaFinish leftFormula)
    (hrightFormula : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount
        rightFormulaStart rightFormulaFinish rightFormula)
    (hpremise : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        premiseBoundary premise)
    (hpremiseBool :
      premiseBoolValue = compactAdditiveBoolTag premiseValid) :
    CompactAdditiveOrRuleCheck tokenTable width tokenCount
        gammaBoundary Gamma.length
        leftFormulaStart leftFormulaFinish leftFormula.length
        rightFormulaStart rightFormulaFinish rightFormula.length
        premiseBoundary premise.length premiseBoolValue resultBoolValue ↔
      resultBoolValue = compactAdditiveBoolTag
        (compactOrRuleCheck
          (Gamma, (leftFormula, (rightFormula,
            (premise, premiseValid))))) := by
  simp only [CompactAdditiveOrRuleCheck]
  rw [compactAdditiveFormulaOrMemberRows_iff
      hGamma hleftFormula hrightFormula,
    compactAdditiveFormulaSetEqTwoConsRows_iff_tokenCheck
      hpremise hleftFormula hrightFormula hGamma,
    hpremiseBool]
  cases hmember : tokenFormulaMem
      (tokenFormulaOr leftFormula rightFormula) Gamma <;>
    cases hsetEq : tokenFormulaSetEq premise
      (leftFormula :: rightFormula :: Gamma) <;>
    cases premiseValid <;>
    simp [compactOrRuleCheck, compactAdditiveBoolTag,
      hmember, hsetEq] <;> omega

#print axioms compactAdditiveOrRuleCheckDef_spec
#print axioms compactAdditiveOrRuleCheckDef_sigmaZero
#print axioms compactAdditiveOrRuleCheck_iff

end FoundationCompactNumericListedDirectOrRuleCheck
