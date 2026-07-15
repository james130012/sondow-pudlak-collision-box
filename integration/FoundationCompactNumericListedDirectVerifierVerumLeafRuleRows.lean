import integration.FoundationCompactNumericListedDirectVerifierLeafParseStackRows
import integration.FoundationCompactNumericListedDirectVerumRuleCheck

/-!
# Exact verifier leaf row for the verum rule

The proof/certificate tags are fixed to `2/0`, and the stored result bit is
the direct bounded verum check on the same decoded `Gamma` row.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierVerumLeafRuleRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectVerumRuleCheck

def CompactNumericVerifierVerumLeafRuleRows
    (tokenTable width tokenCount proofTag certificateTag
      gammaBoundary gammaCount resultBool : Nat) : Prop :=
  proofTag = 2 ∧
    certificateTag = 0 ∧
    CompactAdditiveVerumRuleCheck
      tokenTable width tokenCount gammaBoundary gammaCount resultBool

def compactNumericVerifierVerumLeafRuleRowsDef :
    𝚺₀.Semisentence 8 := .mkSigma
  “tokenTable width tokenCount proofTag certificateTag
      gammaBoundary gammaCount resultBool.
    proofTag = 2 ∧
    certificateTag = 0 ∧
    !(compactAdditiveVerumRuleCheckDef)
      tokenTable width tokenCount gammaBoundary gammaCount resultBool”

@[simp] theorem compactNumericVerifierVerumLeafRuleRowsDef_spec
    (tokenTable width tokenCount proofTag certificateTag
      gammaBoundary gammaCount resultBool : Nat) :
    compactNumericVerifierVerumLeafRuleRowsDef.val.Evalb
        ![tokenTable, width, tokenCount, proofTag, certificateTag,
          gammaBoundary, gammaCount, resultBool] ↔
      CompactNumericVerifierVerumLeafRuleRows
        tokenTable width tokenCount proofTag certificateTag
        gammaBoundary gammaCount resultBool := by
  have hcheckEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount, proofTag, certificateTag,
            gammaBoundary, gammaCount, resultBool]
          Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 8), #1, #2, #5, #6, #7]) =
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount, resultBool] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierVerumLeafRuleRowsDef,
    CompactNumericVerifierVerumLeafRuleRows, hcheckEnv]
  intros
  rfl

theorem compactNumericVerifierVerumLeafRuleRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierVerumLeafRuleRowsDef.val := by
  simp [compactNumericVerifierVerumLeafRuleRowsDef]

theorem CompactNumericVerifierVerumLeafRuleRows.sound
    {tokenTable width tokenCount certificateTag resultBool : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hcore : CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (hrows : CompactNumericVerifierVerumLeafRuleRows
      tokenTable width tokenCount coordinates.tag certificateTag
      coordinates.gammaBoundary coordinates.gammaCount resultBool) :
    ∃ root : CompactNumericVerifierTask,
      CompactNumericVerifierTaskDirectLayout
        tokenTable width tokenCount coordinates.start coordinates.finish root ∧
      root.1 = 2 ∧
      certificateTag = 0 ∧
      resultBool = compactAdditiveBoolTag
        (compactVerumRuleCheck root.2.1) := by
  rcases hrows with ⟨hproofTag, hcertificateTag, hcheck⟩
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hcore with
    ⟨root, hrootLayout, hrootTag,
      hgammaRows, hgammaLength,
      _hfirstLayout, _hfirstLength,
      _hsecondLayout, _hsecondLength,
      _hwitnessLayout, _hwitnessLength,
      _hsuffixLayout, _hsuffixLength⟩
  have hcheck' : CompactAdditiveVerumRuleCheck
      tokenTable width tokenCount coordinates.gammaBoundary
      root.2.1.length resultBool := by
    simpa [hgammaLength] using hcheck
  have hresult :=
    (compactAdditiveVerumRuleCheck_iff hgammaRows).mp hcheck'
  exact ⟨root, hrootLayout, hrootTag.trans hproofTag,
    hcertificateTag, hresult⟩

#print axioms compactNumericVerifierVerumLeafRuleRowsDef_spec
#print axioms compactNumericVerifierVerumLeafRuleRowsDef_sigmaZero
#print axioms CompactNumericVerifierVerumLeafRuleRows.sound

end FoundationCompactNumericListedDirectVerifierVerumLeafRuleRows
