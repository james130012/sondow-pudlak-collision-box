import integration.FoundationCompactNumericListedDirectOrRuleCheck

/-!
# Direct bounded graph for the listed verum rule check
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerumRuleCheck

open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericFormulaConstructors
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierPayloadEquality

def CompactAdditiveConstantFormulaMemberRows
    (tokenTable width tokenCount tag gammaBoundary gammaCount : Nat) : Prop :=
  exists index, index < gammaCount ∧
    exists targetStart, targetStart <= tokenCount ∧
    exists targetFinish, targetFinish <= tokenCount ∧
      CompactFixedWidthEntry gammaBoundary tokenCount index targetStart ∧
      CompactFixedWidthEntry gammaBoundary tokenCount
        (index + 1) targetFinish ∧
      targetFinish = targetStart + 2 ∧
      CompactFixedWidthEntry tokenTable width targetStart 1 ∧
      CompactFixedWidthEntry tokenTable width (targetStart + 1) tag

def compactAdditiveConstantFormulaMemberRowsDef :
    𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount tag gammaBoundary gammaCount.
    ∃ index < gammaCount,
      ∃ targetStart <⁺ tokenCount,
        ∃ targetFinish <⁺ tokenCount,
          !(compactFixedWidthEntryDef)
            gammaBoundary tokenCount index targetStart ∧
          !(compactFixedWidthEntryDef)
            gammaBoundary tokenCount (index + 1) targetFinish ∧
          targetFinish = targetStart + 2 ∧
          !(compactFixedWidthEntryDef)
            tokenTable width targetStart 1 ∧
          !(compactFixedWidthEntryDef)
            tokenTable width (targetStart + 1) tag”

@[simp] theorem compactAdditiveConstantFormulaMemberRowsDef_spec
    (tokenTable width tokenCount tag gammaBoundary gammaCount : Nat) :
    compactAdditiveConstantFormulaMemberRowsDef.val.Evalb
        ![tokenTable, width, tokenCount, tag, gammaBoundary, gammaCount] ↔
      CompactAdditiveConstantFormulaMemberRows
        tokenTable width tokenCount tag gammaBoundary gammaCount := by
  simp [compactAdditiveConstantFormulaMemberRowsDef,
    CompactAdditiveConstantFormulaMemberRows]
  constructor
  · intro h
    exact h
  · intro h
    exact h

theorem compactAdditiveConstantFormulaMemberRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveConstantFormulaMemberRowsDef.val := by
  simp [compactAdditiveConstantFormulaMemberRowsDef]

theorem compactAdditiveConstantFormulaMemberRows_iff
    {tokenTable width tokenCount tag gammaBoundary : Nat}
    {gamma : List (List Nat)}
    (hgamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary gamma) :
    CompactAdditiveConstantFormulaMemberRows
        tokenTable width tokenCount tag gammaBoundary gamma.length ↔
      tokenFormulaMem [tag] gamma = true := by
  rw [tokenFormulaMem_eq_true_iff]
  constructor
  · rintro ⟨index, hindex,
      targetStart, _htargetStart, targetFinish, _htargetFinish,
      htargetStartEntry, htargetFinishEntry, _hfinish,
      hcountEntry, htagEntry⟩
    rcases hgamma index hindex with
      ⟨rowStart, _hrowStart, rowFinish, _hrowFinish,
        hrowStartEntry, hrowFinishEntry, hrowLayout⟩
    have hstart : targetStart = rowStart :=
      (CompactFixedWidthEntry.value_eq_tableValue htargetStartEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hrowStartEntry).symm
    have hfinish : targetFinish = rowFinish :=
      (CompactFixedWidthEntry.value_eq_tableValue htargetFinishEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hrowFinishEntry).symm
    subst targetStart
    subst targetFinish
    have hlength : (gamma.getI index).length = 1 :=
      ((CompactFixedWidthEntry.value_eq_tableValue
        (CompactAdditiveNatListDirectLayout.headerEntry hrowLayout)).trans
        (CompactFixedWidthEntry.value_eq_tableValue hcountEntry).symm)
    have hzero : 0 < (gamma.getI index).length := by omega
    have hrowValueEntry :=
      CompactAdditiveNatListDirectLayout.valueEntry hrowLayout 0 hzero
    have hvalue : gamma.getI index = [tag] := by
      apply List.ext_getElem
      · simpa using hlength
      · intro position hrowPosition hsingletonPosition
        have hposition : position = 0 := by omega
        subst position
        have htag : tag = (gamma.getI index).getI 0 :=
          (CompactFixedWidthEntry.value_eq_tableValue htagEntry).trans
            (CompactFixedWidthEntry.value_eq_tableValue
              (by simpa using hrowValueEntry)).symm
        rw [List.getI_eq_getElem _ hrowPosition] at htag
        simpa using htag.symm
    rw [List.getI_eq_getElem gamma hindex] at hvalue
    exact hvalue ▸ List.getElem_mem hindex
  · intro hmember
    obtain ⟨index, hindex, hvalue⟩ :=
      List.mem_iff_getElem.mp hmember
    rcases hgamma index hindex with
      ⟨rowStart, hrowStart, rowFinish, hrowFinish,
        hrowStartEntry, hrowFinishEntry, hrowLayout⟩
    have hrowEq : gamma.getI index = [tag] := by
      rw [List.getI_eq_getElem gamma hindex, hvalue]
    have hrowLayout' : CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount rowStart rowFinish [tag] := by
      simpa [hrowEq] using hrowLayout
    have hfinish := CompactAdditiveNatListDirectLayout.finish_eq hrowLayout'
    have hcountEntry :=
      CompactAdditiveNatListDirectLayout.headerEntry hrowLayout'
    have htagEntry :=
      CompactAdditiveNatListDirectLayout.valueEntry hrowLayout' 0 (by simp)
    exact ⟨index, hindex,
      rowStart, hrowStart, rowFinish, hrowFinish,
      hrowStartEntry, hrowFinishEntry,
      (by simpa using hfinish),
      (by simpa using hcountEntry),
      (by simpa using htagEntry)⟩

def CompactAdditiveVerumRuleCheck
    (tokenTable width tokenCount gammaBoundary gammaCount
      resultBoolValue : Nat) : Prop :=
  resultBoolValue <= 1 ∧
    (resultBoolValue = 1 ↔
      CompactAdditiveConstantFormulaMemberRows
        tokenTable width tokenCount 2 gammaBoundary gammaCount)

def compactAdditiveVerumRuleCheckDef : 𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue.
    resultBoolValue ≤ 1 ∧
    (resultBoolValue = 1 ↔
      !(compactAdditiveConstantFormulaMemberRowsDef)
        tokenTable width tokenCount 2 gammaBoundary gammaCount)”

@[simp] theorem compactAdditiveVerumRuleCheckDef_spec
    (tokenTable width tokenCount gammaBoundary gammaCount
      resultBoolValue : Nat) :
    compactAdditiveVerumRuleCheckDef.val.Evalb
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount, resultBoolValue] ↔
      CompactAdditiveVerumRuleCheck tokenTable width tokenCount
        gammaBoundary gammaCount resultBoolValue := by
  let env : Fin 6 → Nat :=
    ![tokenTable, width, tokenCount,
      gammaBoundary, gammaCount, resultBoolValue]
  change compactAdditiveVerumRuleCheckDef.val.Evalb env ↔ _
  have hmemberEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 6), #1, #2,
          (↑(2 : Nat) : Semiterm ℒₒᵣ Empty 6), #3, #4]) =
        ![tokenTable, width, tokenCount, 2, gammaBoundary, gammaCount] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  have hresultValue : env 5 = resultBoolValue := rfl
  simp [compactAdditiveVerumRuleCheckDef,
    CompactAdditiveVerumRuleCheck, hmemberEnv, hresultValue]

theorem compactAdditiveVerumRuleCheckDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveVerumRuleCheckDef.val := by
  simp [compactAdditiveVerumRuleCheckDef]

theorem compactAdditiveVerumRuleCheck_iff
    {tokenTable width tokenCount gammaBoundary resultBoolValue : Nat}
    {Gamma : List (List Nat)}
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma) :
    CompactAdditiveVerumRuleCheck tokenTable width tokenCount
        gammaBoundary Gamma.length resultBoolValue ↔
      resultBoolValue = compactAdditiveBoolTag
        (compactVerumRuleCheck Gamma) := by
  simp only [CompactAdditiveVerumRuleCheck]
  rw [compactAdditiveConstantFormulaMemberRows_iff hGamma]
  change (resultBoolValue ≤ 1 ∧
      (resultBoolValue = 1 ↔ tokenFormulaMem [2] Gamma = true)) ↔
    resultBoolValue = compactAdditiveBoolTag (tokenFormulaMem [2] Gamma)
  cases tokenFormulaMem [2] Gamma <;>
    simp [compactAdditiveBoolTag] <;> omega

#print axioms compactAdditiveConstantFormulaMemberRowsDef_spec
#print axioms compactAdditiveConstantFormulaMemberRowsDef_sigmaZero
#print axioms compactAdditiveConstantFormulaMemberRows_iff
#print axioms compactAdditiveVerumRuleCheckDef_spec
#print axioms compactAdditiveVerumRuleCheckDef_sigmaZero
#print axioms compactAdditiveVerumRuleCheck_iff

end FoundationCompactNumericListedDirectVerumRuleCheck
