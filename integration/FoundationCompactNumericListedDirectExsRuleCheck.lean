import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
import integration.FoundationCompactNumericListedDirectFormulaConstructorMembership

/-!
# Direct bounded graph for existential introduction

The substitution trace is an unconditional part of the certificate.  Thus a
false rule result cannot be manufactured by omitting a transform witness; the
trace always computes the same `getD []` value used by the public checker.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectExsRuleCheck

open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericFormulaConstructors
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaSetEqCons
open FoundationCompactNumericListedDirectFormulaConstructorMembership
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula

def CompactAdditiveExsRuleCheck
    (tokenTable width tokenCount
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
      witnessStart witnessFinish witnessCount
      premiseBoundary premiseCount premiseBoolValue
      substitutedStart substitutedFinish substitutedBoundary substitutedCount
      stateBoundary stateCount emptyBoundary tableWidth valueBound
      resultBoolValue : Nat) : Prop :=
  CompactFormulaTransformTotalExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount 2
      witnessStart witnessFinish witnessCount
      formulaBoundary formulaCount substitutedBoundary substitutedCount
      emptyBoundary 1 tableWidth valueBound ∧
    resultBoolValue ≤ 1 ∧
    (resultBoolValue = 1 ↔
      CompactAdditiveUnaryFormulaConstructorMemberRows
        tokenTable width tokenCount 7
          gammaBoundary gammaCount
          formulaStart formulaFinish formulaCount ∧
      CompactAdditiveFormulaSetEqConsRows
        tokenTable width tokenCount
          premiseBoundary premiseCount
          substitutedStart substitutedFinish
          gammaBoundary gammaCount ∧
      premiseBoolValue = 1)

def compactAdditiveExsRuleCheckDef : 𝚺₀.Semisentence 25 := .mkSigma
  “tokenTable width tokenCount
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
      witnessStart witnessFinish witnessCount
      premiseBoundary premiseCount premiseBoolValue
      substitutedStart substitutedFinish substitutedBoundary substitutedCount
      stateBoundary stateCount emptyBoundary tableWidth valueBound
      resultBoolValue.
    !(compactFormulaTransformTotalExactBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount 2
      witnessStart witnessFinish witnessCount
      formulaBoundary formulaCount substitutedBoundary substitutedCount
      emptyBoundary 1 tableWidth valueBound ∧
    resultBoolValue ≤ 1 ∧
    (resultBoolValue = 1 ↔
      !(compactAdditiveUnaryFormulaConstructorMemberRowsDef)
        tokenTable width tokenCount 7
          gammaBoundary gammaCount
          formulaStart formulaFinish formulaCount ∧
      !(compactAdditiveFormulaSetEqConsRowsDef)
        tokenTable width tokenCount
          premiseBoundary premiseCount
          substitutedStart substitutedFinish
          gammaBoundary gammaCount ∧
      premiseBoolValue = 1)”

@[simp] theorem compactAdditiveExsRuleCheckDef_spec
    (tokenTable width tokenCount
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
      witnessStart witnessFinish witnessCount
      premiseBoundary premiseCount premiseBoolValue
      substitutedStart substitutedFinish substitutedBoundary substitutedCount
      stateBoundary stateCount emptyBoundary tableWidth valueBound
      resultBoolValue : Nat) :
    compactAdditiveExsRuleCheckDef.val.Evalb
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount,
          formulaStart, formulaFinish, formulaBoundary, formulaCount,
          witnessStart, witnessFinish, witnessCount,
          premiseBoundary, premiseCount, premiseBoolValue,
          substitutedStart, substitutedFinish,
          substitutedBoundary, substitutedCount,
          stateBoundary, stateCount, emptyBoundary, tableWidth, valueBound,
          resultBoolValue] ↔
      CompactAdditiveExsRuleCheck
        tokenTable width tokenCount
        gammaBoundary gammaCount
        formulaStart formulaFinish formulaBoundary formulaCount
        witnessStart witnessFinish witnessCount
        premiseBoundary premiseCount premiseBoolValue
        substitutedStart substitutedFinish substitutedBoundary substitutedCount
        stateBoundary stateCount emptyBoundary tableWidth valueBound
        resultBoolValue := by
  let env : Fin 25 → Nat :=
    ![tokenTable, width, tokenCount,
      gammaBoundary, gammaCount,
      formulaStart, formulaFinish, formulaBoundary, formulaCount,
      witnessStart, witnessFinish, witnessCount,
      premiseBoundary, premiseCount, premiseBoolValue,
      substitutedStart, substitutedFinish,
      substitutedBoundary, substitutedCount,
      stateBoundary, stateCount, emptyBoundary, tableWidth, valueBound,
      resultBoolValue]
  change compactAdditiveExsRuleCheckDef.val.Evalb env ↔ _
  have htransformEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #19, #20,
          (↑(2 : Nat) : Semiterm ℒₒᵣ Empty 25),
          #9, #10, #11, #7, #8, #17, #18, #21,
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 25), #22, #23]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, 2,
          witnessStart, witnessFinish, witnessCount,
          formulaBoundary, formulaCount, substitutedBoundary,
          substitutedCount, emptyBoundary, 1, tableWidth, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hmemberEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2,
          (↑(7 : Nat) : Semiterm ℒₒᵣ Empty 25),
          #3, #4, #5, #6, #8]) =
        ![tokenTable, width, tokenCount, 7,
          gammaBoundary, gammaCount,
          formulaStart, formulaFinish, formulaCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hpremiseEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2,
          #12, #13, #15, #16, #3, #4]) =
        ![tokenTable, width, tokenCount,
          premiseBoundary, premiseCount,
          substitutedStart, substitutedFinish,
          gammaBoundary, gammaCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hpremiseBoolValue : env 14 = premiseBoolValue := rfl
  have hresultBoolValue : env 24 = resultBoolValue := rfl
  simp [compactAdditiveExsRuleCheckDef, CompactAdditiveExsRuleCheck,
    htransformEnv, hmemberEnv, hpremiseEnv,
    hpremiseBoolValue, hresultBoolValue]

theorem compactAdditiveExsRuleCheckDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveExsRuleCheckDef.val := by
  simp [compactAdditiveExsRuleCheckDef]

theorem compactAdditiveExsRuleCheck_iff
    {tokenTable width tokenCount gammaBoundary
      formulaStart formulaFinish formulaBoundary
      witnessStart witnessFinish premiseBoundary premiseBoolValue
      substitutedStart substitutedFinish substitutedBoundary
      stateBoundary stateCount emptyBoundary tableWidth valueBound
      resultBoolValue : Nat}
    {Gamma premise : List (List Nat)}
    {formula witness substituted : List Nat}
    {premiseValid : Bool}
    (htransform : CompactFormulaTransformTotalExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount 2
      witnessStart witnessFinish witness.length
      formulaBoundary formula.length substitutedBoundary substituted.length
      emptyBoundary 1 tableWidth valueBound)
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hformula : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount formulaStart formulaFinish formula)
    (hformulaRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        formulaBoundary formula)
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hpremise : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        premiseBoundary premise)
    (hsubstituted : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount
        substitutedStart substitutedFinish substituted)
    (hsubstitutedRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        substitutedBoundary substituted)
    (hemptyRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary [])
    (hpremiseBool : premiseBoolValue =
      compactAdditiveBoolTag premiseValid) :
    CompactAdditiveExsRuleCheck
        tokenTable width tokenCount
        gammaBoundary Gamma.length
        formulaStart formulaFinish formulaBoundary formula.length
        witnessStart witnessFinish witness.length
        premiseBoundary premise.length premiseBoolValue
        substitutedStart substitutedFinish substitutedBoundary
          substituted.length
        stateBoundary stateCount emptyBoundary tableWidth valueBound
        resultBoolValue ↔
      resultBoolValue = compactAdditiveBoolTag
        (compactExsRuleCheck
          (Gamma, (formula, (witness, (premise, premiseValid))))) := by
  have hsubstitutedResult :=
    CompactFormulaTransformTotalExactBoundedGraph.sound_selfContained
      htransform hwitness rfl
      hformulaRows hsubstitutedRows hemptyRows
  have hsubstitutedExact : substituted =
      (compactFormulaSubstitutionExact 1 (witness, formula)).getD [] := by
    simpa [compactFormulaSubstitutionExact] using hsubstitutedResult
  simp only [CompactAdditiveExsRuleCheck]
  rw [compactAdditiveFormulaExsMemberRows_iff hGamma hformula,
    compactAdditiveFormulaSetEqConsRows_iff_tokenCheck
      hpremise hsubstituted hGamma,
    hpremiseBool]
  rw [and_iff_right htransform]
  rw [hsubstitutedExact]
  cases hmember : tokenFormulaMem (tokenFormulaExs formula) Gamma <;>
    cases hsetEq : tokenFormulaSetEq premise
      ((compactFormulaSubstitutionExact 1 (witness, formula)).getD [] ::
        Gamma) <;>
    cases premiseValid <;>
    simp [compactExsRuleCheck, compactAdditiveBoolTag,
      hmember, hsetEq] <;> omega

#print axioms compactAdditiveExsRuleCheckDef_spec
#print axioms compactAdditiveExsRuleCheckDef_sigmaZero
#print axioms compactAdditiveExsRuleCheck_iff

end FoundationCompactNumericListedDirectExsRuleCheck
