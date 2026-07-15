import integration.FoundationCompactNumericListedDirectCrossTableSliceEquality
import integration.FoundationCompactNumericListedDirectProofRootSuccessBoundedFormula
import integration.FoundationCompactNumericListedDirectProofRootTaggedSuccessBoundedFormula
import integration.FoundationCompactNumericListedDirectCertificateNodeSuccessBoundedFormula
import integration.FoundationCompactNumericListedDirectNodeTransitionCases
import integration.FoundationCompactNumericListedDirectVerifierStepCases

/-!
# Parse-payload success with independently canonical parser tables

The verifier-state streams and parser endpoint graphs may occupy separate
fixed-width tables. Exact cross-table equality ties each graph to its state
stream, while the two exposed parser tags certify a real node transition.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesFormula

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectProofRootSuccessBoundedFormula
open FoundationCompactNumericListedDirectProofRootTaggedSuccessBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeSuccessBoundedFormula
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectVerifierStepCases

def CompactNumericParsePayloadSuccessSeparatedTablesGraph
    (stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound : Nat) :
    Prop :=
  CompactFixedWidthCrossTableSlicesEq
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish ∧
    CompactFixedWidthCrossTableSlicesEq
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish
      certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish ∧
    CompactProofRootTaggedSuccessBoundedGraph
      proofTable proofWidth proofTokenCount
        proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound ∧
    CompactCertificateNodeSuccessBoundedGraph
      certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound ∧
    CompactNumericNodeTransitionTagMatch proofTag certificateTag

def compactNumericParsePayloadSuccessSeparatedTablesGraphDef :
    𝚺₀.Semisentence 29 := .mkSigma
  “stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound.
    !(compactFixedWidthCrossTableSlicesEqDef)
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish ∧
    !(compactFixedWidthCrossTableSlicesEqDef)
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish
      certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish ∧
    !(compactProofRootTaggedSuccessBoundedGraphDef)
      proofTable proofWidth proofTokenCount
        proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound ∧
    !(compactCertificateNodeSuccessBoundedGraphDef)
      certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound ∧
    !(compactNumericNodeTransitionTagMatchDef) proofTag certificateTag”

def compactNumericParsePayloadSuccessSeparatedTablesGraphEnvironment
    (stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound : Nat) :
    Fin 29 → Nat :=
  ![stateTable, stateWidth, stateTokenCount,
    stateProofStart, stateProofFinish,
    stateCertificateStart, stateCertificateFinish,
    proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
    rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound]

@[simp] theorem compactNumericParsePayloadSuccessSeparatedTablesGraphDef_spec
    (stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound : Nat) :
    compactNumericParsePayloadSuccessSeparatedTablesGraphDef.val.Evalb
        (compactNumericParsePayloadSuccessSeparatedTablesGraphEnvironment
          stateTable stateWidth stateTokenCount
          stateProofStart stateProofFinish
          stateCertificateStart stateCertificateFinish
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound) ↔
      CompactNumericParsePayloadSuccessSeparatedTablesGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound := by
  let env := compactNumericParsePayloadSuccessSeparatedTablesGraphEnvironment
    stateTable stateWidth stateTokenCount
    stateProofStart stateProofFinish
    stateCertificateStart stateCertificateFinish
    proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
    rootStart rootFinish proofTag proofEndpointBound
    certificateTable certificateWidth certificateTokenCount
    certificateInputStart certificateInputFinish
    axiomStart axiomFinish formulaStart formulaFinish
    suffixStart suffixFinish certificateTag certificateEndpointBound
  change compactNumericParsePayloadSuccessSeparatedTablesGraphDef.val.Evalb env ↔ _
  have hproofCrossEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 29), #1, #2, #3, #4,
          #7, #8, #9, #10, #11]) =
        ![stateTable, stateWidth, stateTokenCount,
          stateProofStart, stateProofFinish,
          proofTable, proofWidth, proofTokenCount,
          proofInputStart, proofInputFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcertificateCrossEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 29), #1, #2, #5, #6,
          #16, #17, #18, #19, #20]) =
        ![stateTable, stateWidth, stateTokenCount,
          stateCertificateStart, stateCertificateFinish,
          certificateTable, certificateWidth, certificateTokenCount,
          certificateInputStart, certificateInputFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hproofSuccessEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#7 : Semiterm ℒₒᵣ Empty 29), #8, #9, #10, #11,
          #12, #13, #14, #15]) =
        ![proofTable, proofWidth, proofTokenCount,
          proofInputStart, proofInputFinish,
          rootStart, rootFinish, proofTag, proofEndpointBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcertificateSuccessEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#16 : Semiterm ℒₒᵣ Empty 29), #17, #18, #19, #20,
          #21, #22, #23, #24, #25, #26, #27, #28]) =
        ![certificateTable, certificateWidth, certificateTokenCount,
          certificateInputStart, certificateInputFinish,
          axiomStart, axiomFinish, formulaStart, formulaFinish,
          suffixStart, suffixFinish, certificateTag,
          certificateEndpointBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htagEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#14 : Semiterm ℒₒᵣ Empty 29), #27]) =
        ![proofTag, certificateTag] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericParsePayloadSuccessSeparatedTablesGraphDef,
    CompactNumericParsePayloadSuccessSeparatedTablesGraph,
    hproofCrossEnv, hcertificateCrossEnv, hproofSuccessEnv,
    hcertificateSuccessEnv, htagEnv]

theorem compactNumericParsePayloadSuccessSeparatedTablesGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericParsePayloadSuccessSeparatedTablesGraphDef.val := by
  simp [compactNumericParsePayloadSuccessSeparatedTablesGraphDef]

private theorem compactListedProofNodeFieldsParser_deterministic
    {input : List Nat} {left right : CompactNumericProofRoot}
    (hleft : compactListedProofNodeFieldsParser input = some left)
    (hright : compactListedProofNodeFieldsParser input = some right) :
    left = right :=
  Option.some.inj (hleft.symm.trans hright)

private theorem certificateSuccessNode
    {certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound : Nat}
    (hgraph : CompactCertificateNodeSuccessBoundedGraph
      certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound) :
    ∃ input : List Nat, ∃ certificateNode : Nat × (List Nat × List Nat),
      CompactAdditiveNatListDirectLayout
        certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish input ∧
      compactStructuralCertificateNodeParser input = some certificateNode ∧
      certificateNode.1 = certificateTag := by
  rcases hgraph.sound with
    ⟨input, suffix, hinput, _hsuffix, hparser⟩ |
      ⟨input, axiomTokens, suffix, hinput, _haxiom, _hsuffix, hparser⟩
  · exact ⟨input, (certificateTag, ([], suffix)), hinput, hparser, rfl⟩
  · exact ⟨input, (certificateTag, (axiomTokens, suffix)),
      hinput, hparser, rfl⟩

theorem CompactNumericParsePayloadSuccessSeparatedTablesGraph.sound
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound : Nat}
    {proofTokens certificateTokens : List Nat}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    (hgraph : CompactNumericParsePayloadSuccessSeparatedTablesGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound)
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens) :
    ∃ parsed, compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) = some parsed := by
  rcases hgraph with
    ⟨hproofCross, hcertificateCross, hproofSuccess,
      hcertificateSuccess, htagMatch⟩
  rcases hproofSuccess.sound with
    ⟨proofInput, proofNode, hproofInputLayout, _hroot,
      hproofParser, hproofTag⟩
  rcases certificateSuccessNode hcertificateSuccess with
    ⟨certificateInput, certificateNode, hcertificateInputLayout,
      hcertificateParser, hcertificateTag⟩
  have hproofInputEq : proofInput = proofTokens :=
    hproofCross.natListValues_eq hproofLayout hproofInputLayout
  have hcertificateInputEq : certificateInput = certificateTokens :=
    hcertificateCross.natListValues_eq
      hcertificateLayout hcertificateInputLayout
  subst proofInput
  subst certificateInput
  have hactualTagMatch :
      CompactNumericNodeTransitionTagMatch proofNode.1 certificateNode.1 := by
    simpa only [hproofTag, hcertificateTag] using htagMatch
  rcases (compactNumericNodeTransition_exists_iff_tagMatch
      proofNode certificateNode restTasks values).2 hactualTagMatch with
    ⟨parsed, htransition⟩
  exact ⟨parsed, (compactNumericParsePayload_eq_some_iff
    ((proofTokens, certificateTokens), (restTasks, values)) parsed).2
      ⟨proofNode, certificateNode, hproofParser, hcertificateParser,
        htransition⟩⟩

theorem exists_compactNumericParsePayloadSuccessSeparatedTablesGraph_of_exists_some
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hparse : ∃ parsed, compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) = some parsed) :
    ∃ proofTable proofWidth proofTokenCount proofInputStart proofInputFinish,
    ∃ rootStart rootFinish proofTag proofEndpointBound,
    ∃ certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish certificateTag certificateEndpointBound,
      CompactNumericParsePayloadSuccessSeparatedTablesGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound := by
  rcases hparse with ⟨parsed, hparse⟩
  rcases (compactNumericParsePayload_eq_some_iff
      ((proofTokens, certificateTokens), (restTasks, values)) parsed).mp hparse with
    ⟨proofNode, certificateNode, hproofParser, hcertificateParser,
      htransition⟩
  rcases
      exists_compactProofRootSuccessBoundedGraph_of_parser_success_with_inputLayout
        hproofParser with
    ⟨proofTable, proofWidth, proofTokenCount,
      proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofEndpointBound,
      hproofInputLayout, hproofSuccessGraph⟩
  rcases
      FoundationCompactNumericListedDirectProofRootTaggedSuccessBoundedFormula.CompactProofRootSuccessBoundedGraph.exists_tagged
        hproofSuccessGraph with
    ⟨proofTag, hproofTaggedGraph⟩
  rcases certificateNode with ⟨certificateTag, axiomTokens, suffix⟩
  rcases
      exists_compactCertificateNodeSuccessBoundedGraph_of_parser_success_with_inputLayout
        hcertificateParser with
    ⟨certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateEndpointBound,
      hcertificateInputLayout, hcertificateSuccessGraph⟩
  have hproofCross :=
    CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
      hproofLayout hproofInputLayout
  have hcertificateCross :=
    CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
      hcertificateLayout hcertificateInputLayout
  have hactualTagMatch :
      CompactNumericNodeTransitionTagMatch proofNode.1 certificateTag :=
    (compactNumericNodeTransition_exists_iff_tagMatch
      proofNode (certificateTag, (axiomTokens, suffix))
        restTasks values).mp ⟨parsed, htransition⟩
  rcases hproofTaggedGraph.sound with
    ⟨decodedInput, decodedRoot, hdecodedInputLayout, _hdecodedRootLayout,
      hdecodedParser, hdecodedTag⟩
  have hdecodedInputEq : decodedInput = proofTokens :=
    hproofCross.natListValues_eq hproofLayout hdecodedInputLayout
  subst decodedInput
  have hdecodedRootEq : decodedRoot = proofNode :=
    compactListedProofNodeFieldsParser_deterministic
      hdecodedParser hproofParser
  subst decodedRoot
  have htagMatch :
      CompactNumericNodeTransitionTagMatch proofTag certificateTag := by
    simpa only [hdecodedTag] using hactualTagMatch
  exact ⟨proofTable, proofWidth, proofTokenCount,
    proofInputStart, proofInputFinish,
    rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
    hproofCross, hcertificateCross, hproofTaggedGraph,
    hcertificateSuccessGraph, htagMatch⟩

theorem compactNumericParsePayload_exists_some_iff_exists_successSeparatedTablesGraph
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens) :
    (∃ parsed, compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) = some parsed) ↔
      ∃ proofTable proofWidth proofTokenCount proofInputStart proofInputFinish,
      ∃ rootStart rootFinish proofTag proofEndpointBound,
      ∃ certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish,
      ∃ axiomStart axiomFinish formulaStart formulaFinish,
      ∃ suffixStart suffixFinish certificateTag certificateEndpointBound,
        CompactNumericParsePayloadSuccessSeparatedTablesGraph
          stateTable stateWidth stateTokenCount
          stateProofStart stateProofFinish
          stateCertificateStart stateCertificateFinish
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound := by
  constructor
  · exact exists_compactNumericParsePayloadSuccessSeparatedTablesGraph_of_exists_some
      hproofLayout hcertificateLayout
  · rintro ⟨proofTable, proofWidth, proofTokenCount,
      proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      hgraph⟩
    exact hgraph.sound hproofLayout hcertificateLayout

#print axioms compactNumericParsePayloadSuccessSeparatedTablesGraphDef_spec
#print axioms
  compactNumericParsePayloadSuccessSeparatedTablesGraphDef_sigmaZero
#print axioms CompactNumericParsePayloadSuccessSeparatedTablesGraph.sound
#print axioms
  exists_compactNumericParsePayloadSuccessSeparatedTablesGraph_of_exists_some
#print axioms
  compactNumericParsePayload_exists_some_iff_exists_successSeparatedTablesGraph

end FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesFormula
