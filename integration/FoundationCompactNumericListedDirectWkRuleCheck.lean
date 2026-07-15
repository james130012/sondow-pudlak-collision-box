import integration.FoundationCompactNumericListedDirectAndRuleCheck

/-!
# Direct bounded graph for weakening
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectWkRuleCheck

open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaSetChecks

def CompactAdditiveWkRuleCheck
    (tokenTable width tokenCount
      gammaBoundary gammaCount premiseBoundary premiseCount
      premiseBoolValue resultBoolValue : Nat) : Prop :=
  resultBoolValue <= 1 ∧
    (resultBoolValue = 1 ↔
      CompactAdditiveFormulaSubsetRows tokenTable width tokenCount
        premiseBoundary premiseCount gammaBoundary gammaCount ∧
      premiseBoolValue = 1)

def compactAdditiveWkRuleCheckDef : 𝚺₀.Semisentence 9 := .mkSigma
  “tokenTable width tokenCount
      gammaBoundary gammaCount premiseBoundary premiseCount
      premiseBoolValue resultBoolValue.
    resultBoolValue ≤ 1 ∧
    (resultBoolValue = 1 ↔
      !(compactAdditiveFormulaSubsetRowsDef)
        tokenTable width tokenCount
          premiseBoundary premiseCount gammaBoundary gammaCount ∧
      premiseBoolValue = 1)”

@[simp] theorem compactAdditiveWkRuleCheckDef_spec
    (tokenTable width tokenCount
      gammaBoundary gammaCount premiseBoundary premiseCount
      premiseBoolValue resultBoolValue : Nat) :
    compactAdditiveWkRuleCheckDef.val.Evalb
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount, premiseBoundary, premiseCount,
          premiseBoolValue, resultBoolValue] ↔
      CompactAdditiveWkRuleCheck tokenTable width tokenCount
        gammaBoundary gammaCount premiseBoundary premiseCount
        premiseBoolValue resultBoolValue := by
  let env : Fin 9 → Nat :=
    ![tokenTable, width, tokenCount,
      gammaBoundary, gammaCount, premiseBoundary, premiseCount,
      premiseBoolValue, resultBoolValue]
  change compactAdditiveWkRuleCheckDef.val.Evalb env ↔ _
  have hsubsetEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 9), #1, #2,
          #5, #6, #3, #4]) =
        ![tokenTable, width, tokenCount,
          premiseBoundary, premiseCount, gammaBoundary, gammaCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hpremiseValue : env 7 = premiseBoolValue := rfl
  have hresultValue : env 8 = resultBoolValue := rfl
  simp [compactAdditiveWkRuleCheckDef, CompactAdditiveWkRuleCheck,
    hsubsetEnv, hpremiseValue, hresultValue]

theorem compactAdditiveWkRuleCheckDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveWkRuleCheckDef.val := by
  simp [compactAdditiveWkRuleCheckDef]

theorem compactAdditiveWkRuleCheck_iff
    {tokenTable width tokenCount gammaBoundary premiseBoundary
      premiseBoolValue resultBoolValue : Nat}
    {Gamma premise : List (List Nat)} {premiseValid : Bool}
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hpremise : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        premiseBoundary premise)
    (hpremiseBool :
      premiseBoolValue = compactAdditiveBoolTag premiseValid) :
    CompactAdditiveWkRuleCheck tokenTable width tokenCount
        gammaBoundary Gamma.length premiseBoundary premise.length
        premiseBoolValue resultBoolValue ↔
      resultBoolValue = compactAdditiveBoolTag
        (compactWkRuleCheck (Gamma, (premise, premiseValid))) := by
  simp only [CompactAdditiveWkRuleCheck]
  rw [compactAdditiveFormulaSubsetRows_iff_tokenCheck hpremise hGamma,
    hpremiseBool]
  cases hsubset : tokenFormulaSubset premise Gamma <;>
    cases premiseValid <;>
    simp [compactWkRuleCheck, compactAdditiveBoolTag, hsubset] <;> omega

#print axioms compactAdditiveWkRuleCheckDef_spec
#print axioms compactAdditiveWkRuleCheckDef_sigmaZero
#print axioms compactAdditiveWkRuleCheck_iff

end FoundationCompactNumericListedDirectWkRuleCheck
