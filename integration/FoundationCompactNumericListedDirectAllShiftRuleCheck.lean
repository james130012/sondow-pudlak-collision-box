import integration.FoundationCompactNumericListedDirectFormulaShiftExactListRows
import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
import integration.FoundationCompactNumericListedDirectFormulaConstructorMembership
import integration.FoundationCompactNumericListedDirectFormulaSetEqCons
import integration.FoundationCompactNumericListedDirectFormulaSetChecks

/-!
# Direct bounded checks for universal introduction and shift

Both rules use the same exact list-shift graph.  Universal introduction also
executes the single-formula free transform unconditionally.  All transformed
lists are reconstructed from bounded rows before comparison with the public
checker.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectAllShiftRuleCheck

open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericFormulaConstructors
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectNatListListRowsRealization
open FoundationCompactNumericListedDirectFormulaShiftExactListRows
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
open FoundationCompactNumericListedDirectFormulaConstructorMembership
open FoundationCompactNumericListedDirectFormulaSetEqCons
open FoundationCompactNumericListedDirectFormulaSetChecks

def CompactAdditiveAllRuleCheck
    (tokenTable width tokenCount
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
      premiseBoundary premiseCount premiseBoolValue
      freedStart freedFinish freedBoundary freedCount
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      resultBoolValue : Nat) : Prop :=
  CompactFormulaTransformTotalExactBoundedGraph
      tokenTable width tokenCount freeStateBoundary freeStateCount 0
      emptyStart emptyFinish 0
      formulaBoundary formulaCount freedBoundary freedCount
      emptyBoundary 1 freeTableWidth freeValueBound ∧
    CompactFormulaShiftExactListRows
      tokenTable width tokenCount
      gammaBoundary gammaCount shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound ∧
    CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount shiftedBoundary shiftedCount ∧
    resultBoolValue ≤ 1 ∧
    (resultBoolValue = 1 ↔
      CompactAdditiveUnaryFormulaConstructorMemberRows
        tokenTable width tokenCount 6
          gammaBoundary gammaCount
          formulaStart formulaFinish formulaCount ∧
      CompactAdditiveFormulaSetEqConsRows
        tokenTable width tokenCount
          premiseBoundary premiseCount
          freedStart freedFinish shiftedBoundary shiftedCount ∧
      premiseBoolValue = 1)

def compactAdditiveAllRuleCheckDef : 𝚺₀.Semisentence 30 := .mkSigma
  “tokenTable width tokenCount
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
      premiseBoundary premiseCount premiseBoolValue
      freedStart freedFinish freedBoundary freedCount
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound resultBoolValue.
    !(compactFormulaTransformTotalExactBoundedGraphDef)
      tokenTable width tokenCount freeStateBoundary freeStateCount 0
      emptyStart emptyFinish 0
      formulaBoundary formulaCount freedBoundary freedCount
      emptyBoundary 1 freeTableWidth freeValueBound ∧
    !(compactFormulaShiftExactListRowsDef)
      tokenTable width tokenCount
      gammaBoundary gammaCount shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound ∧
    !(compactAdditiveNatListListRowsWellFormedDef)
      tokenTable width tokenCount shiftedBoundary shiftedCount ∧
    resultBoolValue ≤ 1 ∧
    (resultBoolValue = 1 ↔
      !(compactAdditiveUnaryFormulaConstructorMemberRowsDef)
        tokenTable width tokenCount 6
          gammaBoundary gammaCount
          formulaStart formulaFinish formulaCount ∧
      !(compactAdditiveFormulaSetEqConsRowsDef)
        tokenTable width tokenCount
          premiseBoundary premiseCount
          freedStart freedFinish shiftedBoundary shiftedCount ∧
      premiseBoolValue = 1)”

@[simp] theorem compactAdditiveAllRuleCheckDef_spec
    (tokenTable width tokenCount
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
      premiseBoundary premiseCount premiseBoolValue
      freedStart freedFinish freedBoundary freedCount
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      resultBoolValue : Nat) :
    compactAdditiveAllRuleCheckDef.val.Evalb
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount,
          formulaStart, formulaFinish, formulaBoundary, formulaCount,
          premiseBoundary, premiseCount, premiseBoolValue,
          freedStart, freedFinish, freedBoundary, freedCount,
          freeStateBoundary, freeStateCount,
          shiftCandidateBoundary, shiftSuccessTable,
          shiftedBoundary, shiftedCount,
          emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
          shiftWitnessBound, freeTableWidth, freeValueBound,
          resultBoolValue] ↔
      CompactAdditiveAllRuleCheck
        tokenTable width tokenCount
        gammaBoundary gammaCount
        formulaStart formulaFinish formulaBoundary formulaCount
        premiseBoundary premiseCount premiseBoolValue
        freedStart freedFinish freedBoundary freedCount
        freeStateBoundary freeStateCount
        shiftCandidateBoundary shiftSuccessTable
        shiftedBoundary shiftedCount
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        shiftWitnessBound freeTableWidth freeValueBound
        resultBoolValue := by
  let env : Fin 30 → Nat :=
    ![tokenTable, width, tokenCount,
      gammaBoundary, gammaCount,
      formulaStart, formulaFinish, formulaBoundary, formulaCount,
      premiseBoundary, premiseCount, premiseBoolValue,
      freedStart, freedFinish, freedBoundary, freedCount,
      freeStateBoundary, freeStateCount,
      shiftCandidateBoundary, shiftSuccessTable,
      shiftedBoundary, shiftedCount,
      emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
      shiftWitnessBound, freeTableWidth, freeValueBound,
      resultBoolValue]
  change compactAdditiveAllRuleCheckDef.val.Evalb env ↔ _
  have hfreeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 30), #1, #2, #16, #17,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 30),
          #22, #23, (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 30),
          #7, #8, #14, #15, #24,
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 30), #27, #28]) =
        ![tokenTable, width, tokenCount,
          freeStateBoundary, freeStateCount, 0,
          emptyStart, emptyFinish, 0,
          formulaBoundary, formulaCount, freedBoundary, freedCount,
          emptyBoundary, 1, freeTableWidth, freeValueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hshiftEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 30), #1, #2,
          #3, #4, #18, #19, #20, #21,
          #22, #23, #24, #25, #26]) =
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount,
          shiftCandidateBoundary, shiftSuccessTable,
          shiftedBoundary, shiftedCount,
          emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
          shiftWitnessBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hshiftedRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 30), #1, #2, #20, #21]) =
        ![tokenTable, width, tokenCount, shiftedBoundary, shiftedCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hmemberEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 30), #1, #2,
          (↑(6 : Nat) : Semiterm ℒₒᵣ Empty 30),
          #3, #4, #5, #6, #8]) =
        ![tokenTable, width, tokenCount, 6,
          gammaBoundary, gammaCount,
          formulaStart, formulaFinish, formulaCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hpremiseEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 30), #1, #2,
          #9, #10, #12, #13, #20, #21]) =
        ![tokenTable, width, tokenCount,
          premiseBoundary, premiseCount,
          freedStart, freedFinish, shiftedBoundary, shiftedCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hresultValue : env 29 = resultBoolValue := rfl
  have hpremiseBoolValue : env 11 = premiseBoolValue := rfl
  simp [compactAdditiveAllRuleCheckDef, CompactAdditiveAllRuleCheck,
    hfreeEnv, hshiftEnv, hshiftedRowsEnv, hmemberEnv, hpremiseEnv,
    hresultValue, hpremiseBoolValue]

theorem compactAdditiveAllRuleCheckDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveAllRuleCheckDef.val := by
  simp [compactAdditiveAllRuleCheckDef]

theorem compactAdditiveAllRuleCheck_iff
    {tokenTable width tokenCount gammaBoundary
      formulaStart formulaFinish formulaBoundary
      premiseBoundary premiseBoolValue
      freedStart freedFinish freedBoundary
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      resultBoolValue : Nat}
    {Gamma premise : List (List Nat)}
    {formula freed : List Nat}
    {premiseValid : Bool}
    (hcheck : CompactAdditiveAllRuleCheck
      tokenTable width tokenCount
      gammaBoundary Gamma.length
      formulaStart formulaFinish formulaBoundary formula.length
      premiseBoundary premise.length premiseBoolValue
      freedStart freedFinish freedBoundary freed.length
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound resultBoolValue)
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hformula : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount formulaStart formulaFinish formula)
    (hformulaRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        formulaBoundary formula)
    (hpremise : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        premiseBoundary premise)
    (hfreed : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount freedStart freedFinish freed)
    (hfreedRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        freedBoundary freed)
    (hpremiseBool : premiseBoolValue =
      compactAdditiveBoolTag premiseValid) :
    resultBoolValue = compactAdditiveBoolTag
      (compactAllRuleCheck (Gamma, (formula, (premise, premiseValid)))) := by
  rcases hcheck with
    ⟨hfreeTransform, hshiftTransform, hshiftedRows,
      hresultBound, hresult⟩
  rcases
      FoundationCompactNumericListedDirectNatListListRowsRealization.CompactAdditiveNatListListRowsWellFormed.realizeRows
        hshiftedRows with
    ⟨shiftedGamma, hshiftedLength, hshiftedGammaRows⟩
  rw [← hshiftedLength] at hshiftTransform
  rw [← hshiftedLength] at hresult
  have hshiftedResult := hshiftTransform.sound
    rfl hGamma hshiftedGammaRows
  have hshiftedExact : shiftedGamma =
      (compactFormulaShiftExactList Gamma).getD [] := hshiftedResult
  rcases hshiftTransform.1.realize with
    ⟨emptyValue, hemptyLength, hemptyLayout, hemptyRows⟩
  have hemptyValue : emptyValue = [] :=
    List.eq_nil_of_length_eq_zero hemptyLength
  subst emptyValue
  have hfreedResult :=
    hfreeTransform.sound_selfContained
      hemptyLayout rfl hformulaRows hfreedRows hemptyRows
  have hfreedExact : freed =
      (compactFormulaFreeExact formula).getD [] := by
    simpa [compactFormulaFreeExact] using hfreedResult
  have hmember :=
    compactAdditiveFormulaAllMemberRows_iff hGamma hformula
  have hsetEq :=
    compactAdditiveFormulaSetEqConsRows_iff_tokenCheck
      hpremise hfreed hshiftedGammaRows
  rw [hmember, hsetEq, hpremiseBool] at hresult
  rw [hfreedExact, hshiftedExact] at hresult
  cases hmemberValue : tokenFormulaMem
      (tokenFormulaAll formula) Gamma <;>
    cases hsetEqValue : tokenFormulaSetEq premise
      ((compactFormulaFreeExact formula).getD [] ::
        (compactFormulaShiftExactList Gamma).getD []) <;>
    cases premiseValid <;>
    simp [compactAllRuleCheck, compactAdditiveBoolTag,
      hmemberValue, hsetEqValue] at hresult ⊢ <;>
    omega

def CompactAdditiveShiftRuleCheck
    (tokenTable width tokenCount
      gammaBoundary gammaCount
      premiseBoundary premiseCount premiseBoolValue
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound resultBoolValue : Nat) : Prop :=
  CompactFormulaShiftExactListRows
      tokenTable width tokenCount
      premiseBoundary premiseCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound ∧
    CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount shiftedBoundary shiftedCount ∧
    resultBoolValue ≤ 1 ∧
    (resultBoolValue = 1 ↔
      CompactAdditiveFormulaSetEqRows
        tokenTable width tokenCount
          gammaBoundary gammaCount shiftedBoundary shiftedCount ∧
      premiseBoolValue = 1)

def compactAdditiveShiftRuleCheckDef : 𝚺₀.Semisentence 18 := .mkSigma
  “tokenTable width tokenCount
      gammaBoundary gammaCount
      premiseBoundary premiseCount premiseBoolValue
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound resultBoolValue.
    !(compactFormulaShiftExactListRowsDef)
      tokenTable width tokenCount
      premiseBoundary premiseCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound ∧
    !(compactAdditiveNatListListRowsWellFormedDef)
      tokenTable width tokenCount shiftedBoundary shiftedCount ∧
    resultBoolValue ≤ 1 ∧
    (resultBoolValue = 1 ↔
      !(compactAdditiveFormulaSetEqRowsDef)
        tokenTable width tokenCount
          gammaBoundary gammaCount shiftedBoundary shiftedCount ∧
      premiseBoolValue = 1)”

@[simp] theorem compactAdditiveShiftRuleCheckDef_spec
    (tokenTable width tokenCount
      gammaBoundary gammaCount
      premiseBoundary premiseCount premiseBoolValue
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound resultBoolValue : Nat) :
    compactAdditiveShiftRuleCheckDef.val.Evalb
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount,
          premiseBoundary, premiseCount, premiseBoolValue,
          shiftCandidateBoundary, shiftSuccessTable,
          shiftedBoundary, shiftedCount,
          emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
          shiftWitnessBound, resultBoolValue] ↔
      CompactAdditiveShiftRuleCheck
        tokenTable width tokenCount
        gammaBoundary gammaCount
        premiseBoundary premiseCount premiseBoolValue
        shiftCandidateBoundary shiftSuccessTable
        shiftedBoundary shiftedCount
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        shiftWitnessBound resultBoolValue := by
  let env : Fin 18 → Nat :=
    ![tokenTable, width, tokenCount,
      gammaBoundary, gammaCount,
      premiseBoundary, premiseCount, premiseBoolValue,
      shiftCandidateBoundary, shiftSuccessTable,
      shiftedBoundary, shiftedCount,
      emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
      shiftWitnessBound, resultBoolValue]
  change compactAdditiveShiftRuleCheckDef.val.Evalb env ↔ _
  have hshiftEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 18), #1, #2,
          #5, #6, #8, #9, #10, #11,
          #12, #13, #14, #15, #16]) =
        ![tokenTable, width, tokenCount,
          premiseBoundary, premiseCount,
          shiftCandidateBoundary, shiftSuccessTable,
          shiftedBoundary, shiftedCount,
          emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
          shiftWitnessBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hshiftedRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 18), #1, #2, #10, #11]) =
        ![tokenTable, width, tokenCount, shiftedBoundary, shiftedCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsetEqEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 18), #1, #2,
          #3, #4, #10, #11]) =
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount, shiftedBoundary, shiftedCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hresultValue : env 17 = resultBoolValue := rfl
  have hpremiseBoolValue : env 7 = premiseBoolValue := rfl
  simp [compactAdditiveShiftRuleCheckDef, CompactAdditiveShiftRuleCheck,
    hshiftEnv, hshiftedRowsEnv, hsetEqEnv,
    hresultValue, hpremiseBoolValue]

theorem compactAdditiveShiftRuleCheckDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveShiftRuleCheckDef.val := by
  simp [compactAdditiveShiftRuleCheckDef]

theorem compactAdditiveShiftRuleCheck_iff
    {tokenTable width tokenCount gammaBoundary
      premiseBoundary premiseBoolValue
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound resultBoolValue : Nat}
    {Gamma premise : List (List Nat)}
    {premiseValid : Bool}
    (hcheck : CompactAdditiveShiftRuleCheck
      tokenTable width tokenCount
      gammaBoundary Gamma.length
      premiseBoundary premise.length premiseBoolValue
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound resultBoolValue)
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hpremise : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        premiseBoundary premise)
    (hpremiseBool : premiseBoolValue =
      compactAdditiveBoolTag premiseValid) :
    resultBoolValue = compactAdditiveBoolTag
      (compactShiftRuleCheck (Gamma, (premise, premiseValid))) := by
  rcases hcheck with
    ⟨hshiftTransform, hshiftedRows, hresultBound, hresult⟩
  rcases
      FoundationCompactNumericListedDirectNatListListRowsRealization.CompactAdditiveNatListListRowsWellFormed.realizeRows
        hshiftedRows with
    ⟨shiftedPremise, hshiftedLength, hshiftedPremiseRows⟩
  rw [← hshiftedLength] at hshiftTransform
  rw [← hshiftedLength] at hresult
  have hshiftedResult := hshiftTransform.sound
    rfl hpremise hshiftedPremiseRows
  have hshiftedExact : shiftedPremise =
      (compactFormulaShiftExactList premise).getD [] := hshiftedResult
  have hsetEq := compactAdditiveFormulaSetEqRows_iff_tokenCheck
    hGamma hshiftedPremiseRows
  rw [hsetEq, hpremiseBool, hshiftedExact] at hresult
  cases hsetEqValue : tokenFormulaSetEq Gamma
      ((compactFormulaShiftExactList premise).getD []) <;>
    cases premiseValid <;>
    simp [compactShiftRuleCheck, compactAdditiveBoolTag,
      hsetEqValue] at hresult ⊢ <;>
    omega

#print axioms compactAdditiveAllRuleCheckDef_spec
#print axioms compactAdditiveAllRuleCheckDef_sigmaZero
#print axioms compactAdditiveAllRuleCheck_iff
#print axioms compactAdditiveShiftRuleCheckDef_spec
#print axioms compactAdditiveShiftRuleCheckDef_sigmaZero
#print axioms compactAdditiveShiftRuleCheck_iff

end FoundationCompactNumericListedDirectAllShiftRuleCheck
