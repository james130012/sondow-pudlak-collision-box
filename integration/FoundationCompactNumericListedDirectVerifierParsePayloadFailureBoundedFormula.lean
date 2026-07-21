import integration.FoundationCompactNumericListedDirectProofRootFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectProofRootTaggedSuccessBoundedFormula
import integration.FoundationCompactNumericListedDirectCertificateNodeFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectCertificateNodeSuccessBoundedFormula
import integration.FoundationCompactNumericListedDirectNodeTransitionCases
import integration.FoundationCompactNumericListedDirectVerifierStepCases
import integration.FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy

/-!
# Total bounded failure graph for one parse payload

The graph covers exactly the three public failure modes: proof parser failure,
certificate parser failure after a successful proof parse, and transition-tag
mismatch after both parsers succeed.  In the third branch the tags are read
from the exact decoded proof and certificate slices, so no independent tag
witness can satisfy the formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParsePayloadFailureBoundedFormula

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectProofRootFailureBoundedFormula
open FoundationCompactNumericListedDirectProofRootTaggedSuccessBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeFailureBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeSuccessBoundedFormula
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectVerifierStepCases

def CompactNumericParsePayloadFailureBoundedGraph
    (tokenTable width tokenCount
      proofStart proofFinish certificateStart certificateFinish
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound : Nat) : Prop :=
  CompactProofRootFailureEndpointBoundedGraph
      tokenTable width tokenCount proofStart proofFinish proofEndpointBound ∨
    (CompactProofRootTaggedSuccessBoundedGraph
        tokenTable width tokenCount proofStart proofFinish
          rootStart rootFinish proofTag proofEndpointBound ∧
      CompactCertificateNodeFailureBoundedGraph
        tokenTable width tokenCount certificateStart certificateFinish
          certificateEndpointBound) ∨
    (CompactProofRootTaggedSuccessBoundedGraph
        tokenTable width tokenCount proofStart proofFinish
          rootStart rootFinish proofTag proofEndpointBound ∧
      CompactCertificateNodeSuccessBoundedGraph
        tokenTable width tokenCount certificateStart certificateFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound ∧
      ¬ CompactNumericNodeTransitionTagMatch proofTag certificateTag)

def compactNumericParsePayloadFailureBoundedGraphDef :
    𝚺₀.Semisentence 19 := .mkSigma
  “tokenTable width tokenCount
      proofStart proofFinish certificateStart certificateFinish
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound.
    !(compactProofRootFailureEndpointBoundedGraphDef)
      tokenTable width tokenCount proofStart proofFinish proofEndpointBound ∨
    (!(compactProofRootTaggedSuccessBoundedGraphDef)
        tokenTable width tokenCount proofStart proofFinish
          rootStart rootFinish proofTag proofEndpointBound ∧
      !(compactCertificateNodeFailureBoundedGraphDef)
        tokenTable width tokenCount certificateStart certificateFinish
          certificateEndpointBound) ∨
    (!(compactProofRootTaggedSuccessBoundedGraphDef)
        tokenTable width tokenCount proofStart proofFinish
          rootStart rootFinish proofTag proofEndpointBound ∧
      !(compactCertificateNodeSuccessBoundedGraphDef)
        tokenTable width tokenCount certificateStart certificateFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound ∧
      ¬ !(compactNumericNodeTransitionTagMatchDef)
        proofTag certificateTag)”

def compactNumericParsePayloadFailureBoundedGraphEnvironment
    (tokenTable width tokenCount
      proofStart proofFinish certificateStart certificateFinish
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound : Nat) : Fin 19 → Nat :=
  ![tokenTable, width, tokenCount,
    proofStart, proofFinish, certificateStart, certificateFinish,
    rootStart, rootFinish, proofTag,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag,
    proofEndpointBound, certificateEndpointBound]

@[simp] theorem compactNumericParsePayloadFailureBoundedGraphDef_spec
    (tokenTable width tokenCount
      proofStart proofFinish certificateStart certificateFinish
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound : Nat) :
    compactNumericParsePayloadFailureBoundedGraphDef.val.Evalb
        (compactNumericParsePayloadFailureBoundedGraphEnvironment
          tokenTable width tokenCount
          proofStart proofFinish certificateStart certificateFinish
          rootStart rootFinish proofTag
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag
          proofEndpointBound certificateEndpointBound) ↔
      CompactNumericParsePayloadFailureBoundedGraph
        tokenTable width tokenCount
        proofStart proofFinish certificateStart certificateFinish
        rootStart rootFinish proofTag
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag
        proofEndpointBound certificateEndpointBound := by
  let env := compactNumericParsePayloadFailureBoundedGraphEnvironment
    tokenTable width tokenCount
    proofStart proofFinish certificateStart certificateFinish
    rootStart rootFinish proofTag
    axiomStart axiomFinish formulaStart formulaFinish
    suffixStart suffixFinish certificateTag
    proofEndpointBound certificateEndpointBound
  change compactNumericParsePayloadFailureBoundedGraphDef.val.Evalb env ↔ _
  have hproofFailureEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2, #3, #4, #17]) =
        ![tokenTable, width, tokenCount,
          proofStart, proofFinish, proofEndpointBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hproofSuccessEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2, #3, #4,
          #7, #8, #9, #17]) =
        ![tokenTable, width, tokenCount, proofStart, proofFinish,
          rootStart, rootFinish, proofTag, proofEndpointBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcertificateFailureEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2, #5, #6, #18]) =
        ![tokenTable, width, tokenCount,
          certificateStart, certificateFinish, certificateEndpointBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcertificateSuccessEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2, #5, #6,
          #10, #11, #12, #13, #14, #15, #16, #18]) =
        ![tokenTable, width, tokenCount,
          certificateStart, certificateFinish,
          axiomStart, axiomFinish, formulaStart, formulaFinish,
          suffixStart, suffixFinish, certificateTag,
          certificateEndpointBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htagMatchEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#9 : Semiterm ℒₒᵣ Empty 19), #16]) =
        ![proofTag, certificateTag] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericParsePayloadFailureBoundedGraphDef,
    CompactNumericParsePayloadFailureBoundedGraph,
    hproofFailureEnv, hproofSuccessEnv,
    hcertificateFailureEnv, hcertificateSuccessEnv, htagMatchEnv]

theorem compactNumericParsePayloadFailureBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericParsePayloadFailureBoundedGraphDef.val := by
  simp [compactNumericParsePayloadFailureBoundedGraphDef]

private theorem natList_eq_of_same_slice
    {tokenTable width tokenCount start finish : Nat}
    {left right : List Nat}
    (hleft : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount start finish left)
    (hright : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount start finish right) :
    right = left :=
  (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
    hleft hright).1

private theorem certificateSuccessNode
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointBound : Nat}
    (hgraph : CompactCertificateNodeSuccessBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag endpointBound) :
    ∃ input : List Nat, ∃ certificateNode : Nat × (List Nat × List Nat),
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactStructuralCertificateNodeParser input = some certificateNode ∧
      certificateNode.1 = certificateTag := by
  rcases hgraph.sound with
    ⟨input, suffix, hinput, _hsuffix, hparser⟩ |
      ⟨input, axiomTokens, suffix, hinput, _haxiom, _hsuffix, hparser⟩
  · exact ⟨input, (certificateTag, ([], suffix)), hinput, hparser, rfl⟩
  · exact ⟨input, (certificateTag, (axiomTokens, suffix)),
      hinput, hparser, rfl⟩

theorem CompactNumericParsePayloadFailureBoundedGraph.sound
    {tokenTable width tokenCount
      proofStart proofFinish certificateStart certificateFinish
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound : Nat}
    {proofTokens certificateTokens : List Nat}
    {restTasks : List CompactNumericVerifierTask}
    {values : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    (hgraph : CompactNumericParsePayloadFailureBoundedGraph
      tokenTable width tokenCount
      proofStart proofFinish certificateStart certificateFinish
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound)
    (hproofLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount proofStart proofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount certificateStart certificateFinish
        certificateTokens) :
    compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) = none := by
  apply (compactNumericParsePayload_eq_none_iff
    ((proofTokens, certificateTokens), (restTasks, values))).2
  rcases hgraph with hproofFailure |
      ⟨hproofSuccess, hcertificateFailure⟩ |
      ⟨hproofSuccess, hcertificateSuccess, htagMismatch⟩
  · rcases hproofFailure.sound with ⟨input, hinput, hparser⟩
    have hinputEq : input = proofTokens :=
      natList_eq_of_same_slice hproofLayout hinput
    subst input
    exact Or.inl hparser
  · rcases hproofSuccess.sound with
      ⟨input, proofNode, hinput, _hroot, hproofParser, _hproofTag⟩
    rcases hcertificateFailure.sound with
      ⟨certificateInput, hcertificateInput, hcertificateParser⟩
    have hinputEq : input = proofTokens :=
      natList_eq_of_same_slice hproofLayout hinput
    have hcertificateInputEq : certificateInput = certificateTokens :=
      natList_eq_of_same_slice hcertificateLayout hcertificateInput
    subst input
    subst certificateInput
    exact Or.inr (Or.inl
      ⟨proofNode, hproofParser, hcertificateParser⟩)
  · rcases hproofSuccess.sound with
      ⟨input, proofNode, hinput, _hroot, hproofParser, hproofTag⟩
    rcases certificateSuccessNode hcertificateSuccess with
      ⟨certificateInput, certificateNode,
        hcertificateInput, hcertificateParser, hcertificateTag⟩
    have hinputEq : input = proofTokens :=
      natList_eq_of_same_slice hproofLayout hinput
    have hcertificateInputEq : certificateInput = certificateTokens :=
      natList_eq_of_same_slice hcertificateLayout hcertificateInput
    subst input
    subst certificateInput
    have hactualMismatch :
        ¬ CompactNumericNodeTransitionTagMatch
          proofNode.1 certificateNode.1 := by
      simpa only [hproofTag, hcertificateTag] using htagMismatch
    have htransition :
        compactNumericNodeTransition proofNode certificateNode
          restTasks values = none :=
      (compactNumericNodeTransition_eq_none_iff_not_tagMatch
        proofNode certificateNode restTasks values).2 hactualMismatch
    exact Or.inr (Or.inr
      ⟨proofNode, certificateNode,
        hproofParser, hcertificateParser, htransition⟩)

#print axioms compactNumericParsePayloadFailureBoundedGraphDef_spec
#print axioms compactNumericParsePayloadFailureBoundedGraphDef_sigmaZero
#print axioms CompactNumericParsePayloadFailureBoundedGraph.sound

end FoundationCompactNumericListedDirectVerifierParsePayloadFailureBoundedFormula
