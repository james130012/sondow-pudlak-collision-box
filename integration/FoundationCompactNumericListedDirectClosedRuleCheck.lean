import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
import integration.FoundationCompactNumericListedDirectFormulaMembership

/-!
# Direct bounded graph for the listed closed rule check

The graph executes numeric negation and checks membership of both the source
formula and its negation in the same context.  The semantic equivalence is
stated for a successfully parsed formula, which rules out the transform's
totalized empty-list fallback.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectClosedRuleCheck

open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericSuccIndSentence
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaMembership
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula

def CompactAdditiveClosedRuleCheck
    (tokenTable width tokenCount
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
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
      CompactAdditiveFormulaMemberRows
        tokenTable width tokenCount gammaBoundary gammaCount
          formulaStart formulaFinish ∧
      CompactAdditiveFormulaMemberRows
        tokenTable width tokenCount gammaBoundary gammaCount
          negatedStart negatedFinish)

def compactAdditiveClosedRuleCheckDef :
    𝚺₀.Semisentence 21 := .mkSigma
  “tokenTable width tokenCount
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
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
      !(compactAdditiveFormulaMemberRowsDef)
        tokenTable width tokenCount gammaBoundary gammaCount
          formulaStart formulaFinish ∧
      !(compactAdditiveFormulaMemberRowsDef)
        tokenTable width tokenCount gammaBoundary gammaCount
          negatedStart negatedFinish)”

@[simp] theorem compactAdditiveClosedRuleCheckDef_spec
    (tokenTable width tokenCount
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
      negatedStart negatedFinish negatedBoundary negatedCount
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBoolValue : Nat) :
    compactAdditiveClosedRuleCheckDef.val.Evalb
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount,
          formulaStart, formulaFinish, formulaBoundary, formulaCount,
          negatedStart, negatedFinish, negatedBoundary, negatedCount,
          stateBoundary, stateCount,
          emptyStart, emptyFinish, emptyBoundary,
          tableWidth, valueBound, resultBoolValue] ↔
      CompactAdditiveClosedRuleCheck
        tokenTable width tokenCount
        gammaBoundary gammaCount
        formulaStart formulaFinish formulaBoundary formulaCount
        negatedStart negatedFinish negatedBoundary negatedCount
        stateBoundary stateCount
        emptyStart emptyFinish emptyBoundary
        tableWidth valueBound resultBoolValue := by
  let env : Fin 21 → Nat :=
    ![tokenTable, width, tokenCount,
      gammaBoundary, gammaCount,
      formulaStart, formulaFinish, formulaBoundary, formulaCount,
      negatedStart, negatedFinish, negatedBoundary, negatedCount,
      stateBoundary, stateCount,
      emptyStart, emptyFinish, emptyBoundary,
      tableWidth, valueBound, resultBoolValue]
  change compactAdditiveClosedRuleCheckDef.val.Evalb env ↔ _
  have htransformEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 21), #1, #2, #13, #14,
          (↑(3 : Nat) : Semiterm ℒₒᵣ Empty 21),
          #15, #16, (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 21),
          #7, #8, #11, #12, #17,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 21), #18, #19]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, 3,
          emptyStart, emptyFinish, 0,
          formulaBoundary, formulaCount, negatedBoundary, negatedCount,
          emptyBoundary, 0, tableWidth, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hformulaEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 21), #1, #2,
          #3, #4, #5, #6]) =
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount, formulaStart, formulaFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hnegatedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 21), #1, #2,
          #3, #4, #9, #10]) =
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount, negatedStart, negatedFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hresultBoolValue : env 20 = resultBoolValue := rfl
  simp [compactAdditiveClosedRuleCheckDef,
    CompactAdditiveClosedRuleCheck,
    htransformEnv, hformulaEnv, hnegatedEnv, hresultBoolValue]

theorem compactAdditiveClosedRuleCheckDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveClosedRuleCheckDef.val := by
  simp [compactAdditiveClosedRuleCheckDef]

theorem compactAdditiveClosedRuleCheck_iff
    {tokenTable width tokenCount gammaBoundary
      formulaStart formulaFinish formulaBoundary
      negatedStart negatedFinish negatedBoundary
      stateBoundary stateCount emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBoolValue : Nat}
    {Gamma : List (List Nat)} {formula negated : List Nat}
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
    (hparsed : ∃ parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0,
      formula = compactArithmeticFormulaTokens parsed) :
    CompactAdditiveClosedRuleCheck
        tokenTable width tokenCount
        gammaBoundary Gamma.length
        formulaStart formulaFinish formulaBoundary formula.length
        negatedStart negatedFinish negatedBoundary negated.length
        stateBoundary stateCount
        emptyStart emptyFinish emptyBoundary
        tableWidth valueBound resultBoolValue ↔
      resultBoolValue = compactAdditiveBoolTag
        (compactClosedRuleCheck (Gamma, formula)) := by
  have hnegatedResult :=
    CompactFormulaTransformTotalExactBoundedGraph.sound_selfContained
      htransform hempty rfl hformulaRows hnegatedRows hemptyRows
  have hnegatedExact : negated =
      (compactFormulaNegationExact 0 formula).getD [] := by
    simpa [compactFormulaNegationExact] using hnegatedResult
  rcases hparsed with ⟨parsed, hformulaCanonical⟩
  have hrawExact : compactFormulaNegationExact 0 formula =
      some (compactArithmeticFormulaTokens (∼parsed)) := by
    simpa [hformulaCanonical] using compactFormulaNegationExact_canonical parsed
  have hnegatedCanonical : negated =
      compactArithmeticFormulaTokens (∼parsed) := by
    simpa [hrawExact] using hnegatedExact
  have hexact : compactFormulaNegationExact 0 formula = some negated := by
    rw [hrawExact, hnegatedCanonical]
  simp only [CompactAdditiveClosedRuleCheck]
  rw [compactAdditiveFormulaMemberRows_iff_mem hGamma hformula,
    compactAdditiveFormulaMemberRows_iff_mem hGamma hnegated]
  rw [and_iff_right htransform]
  have htokenOriginal :
      (formula ∈ Gamma) = (tokenFormulaMem formula Gamma = true) := by
    exact propext (tokenFormulaMem_eq_true_iff formula Gamma).symm
  have htokenNegated :
      (negated ∈ Gamma) = (tokenFormulaMem negated Gamma = true) := by
    exact propext (tokenFormulaMem_eq_true_iff negated Gamma).symm
  rw [htokenOriginal, htokenNegated]
  cases horiginal : tokenFormulaMem formula Gamma <;>
    cases hnegatedMem : tokenFormulaMem negated Gamma <;>
    simp [compactClosedRuleCheck, compactAdditiveBoolTag,
      hexact, horiginal, hnegatedMem] <;> omega

#print axioms compactAdditiveClosedRuleCheckDef_spec
#print axioms compactAdditiveClosedRuleCheckDef_sigmaZero
#print axioms compactAdditiveClosedRuleCheck_iff

end FoundationCompactNumericListedDirectClosedRuleCheck
