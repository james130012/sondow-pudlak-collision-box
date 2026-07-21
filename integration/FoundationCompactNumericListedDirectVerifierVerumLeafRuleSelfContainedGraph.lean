import integration.FoundationCompactNumericListedDirectNatListListWitnessRows
import integration.FoundationCompactNumericListedDirectVerifierVerumLeafRuleRowsCompleteness

/-!
# Self-contained numeric graph for a verum leaf

The public row carries a typed `Gamma` witness and the verum-leaf check over
that same boundary table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierVerumLeafRuleSelfContainedGraph

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerumRuleCheck
open FoundationCompactNumericListedDirectNatListListWitnessRows
open FoundationCompactNumericListedDirectVerifierVerumLeafRuleRows
open FoundationCompactNumericListedDirectVerifierVerumLeafRuleRowsCompleteness

def CompactNumericVerifierVerumLeafRuleSelfContainedGraph
    (tokenTable width tokenCount proofTag certificateTag
      gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize
      resultBool : Nat) : Prop :=
  CompactAdditiveNatListListWitnessRows
      tokenTable width tokenCount gammaStart gammaCount gammaFinish
      gammaBoundary gammaBoundarySize ∧
    CompactNumericVerifierVerumLeafRuleRows
      tokenTable width tokenCount proofTag certificateTag
      gammaBoundary gammaCount resultBool

def compactNumericVerifierVerumLeafRuleSelfContainedGraphDef :
    𝚺₀.Semisentence 11 := .mkSigma
  “tokenTable width tokenCount proofTag certificateTag
      gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize
      resultBool.
    !(compactAdditiveNatListListWitnessRowsDef)
      tokenTable width tokenCount gammaStart gammaCount gammaFinish
      gammaBoundary gammaBoundarySize ∧
    !(compactNumericVerifierVerumLeafRuleRowsDef)
      tokenTable width tokenCount proofTag certificateTag
      gammaBoundary gammaCount resultBool”

def compactNumericVerifierVerumLeafRuleSelfContainedGraphEnvironment
    (tokenTable width tokenCount proofTag certificateTag
      gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize
      resultBool : Nat) : Fin 11 → Nat :=
  ![tokenTable, width, tokenCount, proofTag, certificateTag,
    gammaStart, gammaFinish, gammaBoundary, gammaCount, gammaBoundarySize,
    resultBool]

@[simp] theorem compactNumericVerifierVerumLeafRuleSelfContainedGraphDef_spec
    (tokenTable width tokenCount proofTag certificateTag
      gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize
      resultBool : Nat) :
    compactNumericVerifierVerumLeafRuleSelfContainedGraphDef.val.Evalb
        (compactNumericVerifierVerumLeafRuleSelfContainedGraphEnvironment
          tokenTable width tokenCount proofTag certificateTag
          gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize
          resultBool) ↔
      CompactNumericVerifierVerumLeafRuleSelfContainedGraph
        tokenTable width tokenCount proofTag certificateTag
        gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize
        resultBool := by
  let env := compactNumericVerifierVerumLeafRuleSelfContainedGraphEnvironment
    tokenTable width tokenCount proofTag certificateTag
    gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize resultBool
  have hwitnessEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 11), #1, #2, #5, #8, #6, #7, #9]) =
      ![tokenTable, width, tokenCount, gammaStart, gammaCount, gammaFinish,
        gammaBoundary, gammaBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hleafEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 11), #1, #2, #3, #4, #7, #8, #10]) =
      ![tokenTable, width, tokenCount, proofTag, certificateTag,
        gammaBoundary, gammaCount, resultBool] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierVerumLeafRuleSelfContainedGraphDef,
    CompactNumericVerifierVerumLeafRuleSelfContainedGraph,
    hwitnessEnv, hleafEnv, env]

theorem compactNumericVerifierVerumLeafRuleSelfContainedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierVerumLeafRuleSelfContainedGraphDef.val := by
  simp [compactNumericVerifierVerumLeafRuleSelfContainedGraphDef]

theorem CompactNumericVerifierVerumLeafRuleSelfContainedGraph.sound
    {tokenTable width tokenCount proofTag certificateTag
      gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize
      resultBool : Nat}
    (hgraph : CompactNumericVerifierVerumLeafRuleSelfContainedGraph
      tokenTable width tokenCount proofTag certificateTag
      gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize
      resultBool) :
    ∃ Gamma : List (List Nat),
      CompactAdditiveNatListListDirectLayout
        tokenTable width tokenCount gammaStart gammaFinish Gamma ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma ∧
      proofTag = 2 ∧
      certificateTag = 0 ∧
      resultBool = compactAdditiveBoolTag (compactVerumRuleCheck Gamma) := by
  rcases hgraph with ⟨hwitness, hleaf⟩
  rcases hwitness.realize with ⟨Gamma, hlength, hGamma, hGammaRows⟩
  rcases hleaf with ⟨hproofTag, hcertificateTag, hcheck⟩
  have hcheck' : CompactAdditiveVerumRuleCheck
      tokenTable width tokenCount gammaBoundary Gamma.length resultBool := by
    simpa [hlength] using hcheck
  exact ⟨Gamma, hGamma, hGammaRows, hproofTag, hcertificateTag,
    (compactAdditiveVerumRuleCheck_iff hGammaRows).mp hcheck'⟩

theorem CompactNumericVerifierVerumLeafRuleSelfContainedGraph.exists_canonical
    (Gamma : List (List Nat)) :
    ∃ tokenTable width tokenCount gammaStart gammaFinish gammaBoundary
      gammaBoundarySize,
      CompactNumericVerifierVerumLeafRuleSelfContainedGraph
        tokenTable width tokenCount 2 0
        gammaStart gammaFinish gammaBoundary Gamma.length gammaBoundarySize
        (compactAdditiveBoolTag (compactVerumRuleCheck Gamma)) := by
  rcases CompactNumericVerifierVerumLeafRuleRows.exists_canonical Gamma with
    ⟨tokenTable, width, tokenCount, gammaStart, gammaFinish, _,
      htyped, _, _⟩
  rcases htyped with ⟨gammaBoundary, hGammaLayout, hGammaRows, hGammaSize⟩
  have hwitness : CompactAdditiveNatListListWitnessRows
      tokenTable width tokenCount gammaStart Gamma.length gammaFinish gammaBoundary
        (Nat.size gammaBoundary) :=
    ⟨hGammaLayout,
      CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
        hGammaRows,
      rfl,
      hGammaSize⟩
  exact ⟨tokenTable, width, tokenCount, gammaStart, gammaFinish, gammaBoundary,
    Nat.size gammaBoundary, hwitness,
    CompactNumericVerifierVerumLeafRuleRows.of_gammaRows hGammaRows⟩

#print axioms compactNumericVerifierVerumLeafRuleSelfContainedGraphDef_spec
#print axioms compactNumericVerifierVerumLeafRuleSelfContainedGraphDef_sigmaZero
#print axioms CompactNumericVerifierVerumLeafRuleSelfContainedGraph.sound
#print axioms CompactNumericVerifierVerumLeafRuleSelfContainedGraph.exists_canonical

end FoundationCompactNumericListedDirectVerifierVerumLeafRuleSelfContainedGraph
