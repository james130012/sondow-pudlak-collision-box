import integration.FoundationCompactNumericListedDirectCrossTableSliceEquality
import integration.FoundationCompactNumericListedDirectProofRootFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectProofRootSuccessBoundedFormula
import integration.FoundationCompactNumericListedDirectProofRootTaggedSuccessBoundedFormula
import integration.FoundationCompactNumericListedDirectCertificateNodeFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectCertificateNodeSuccessBoundedFormula
import integration.FoundationCompactNumericListedDirectNodeTransitionCases
import integration.FoundationCompactNumericListedDirectVerifierStepCases

/-!
# Parse-payload failure with independently canonical parser tables

The verifier-state streams and the two parser endpoint graphs may live in
different fixed-width tables.  Exact cross-table slice equality binds each
parser input to the corresponding state stream before any failure branch is
accepted.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParsePayloadFailureSeparatedTablesFormula

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectProofRootFailureBoundedFormula
open FoundationCompactNumericListedDirectProofRootSuccessBoundedFormula
open FoundationCompactNumericListedDirectProofRootTaggedSuccessBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeFailureBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeSuccessBoundedFormula
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectVerifierStepCases

def CompactNumericParsePayloadFailureSeparatedTablesGraph
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
    (CompactProofRootFailureEndpointBoundedGraph
        proofTable proofWidth proofTokenCount
          proofInputStart proofInputFinish proofEndpointBound ∨
      (CompactProofRootTaggedSuccessBoundedGraph
          proofTable proofWidth proofTokenCount
            proofInputStart proofInputFinish
            rootStart rootFinish proofTag proofEndpointBound ∧
        CompactCertificateNodeFailureBoundedGraph
          certificateTable certificateWidth certificateTokenCount
            certificateInputStart certificateInputFinish
            certificateEndpointBound) ∨
      (CompactProofRootTaggedSuccessBoundedGraph
          proofTable proofWidth proofTokenCount
            proofInputStart proofInputFinish
            rootStart rootFinish proofTag proofEndpointBound ∧
        CompactCertificateNodeSuccessBoundedGraph
          certificateTable certificateWidth certificateTokenCount
            certificateInputStart certificateInputFinish
            axiomStart axiomFinish formulaStart formulaFinish
            suffixStart suffixFinish certificateTag certificateEndpointBound ∧
        ¬ CompactNumericNodeTransitionTagMatch proofTag certificateTag))

def compactNumericParsePayloadFailureSeparatedTablesGraphDef :
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
    (!(compactProofRootFailureEndpointBoundedGraphDef)
        proofTable proofWidth proofTokenCount
          proofInputStart proofInputFinish proofEndpointBound ∨
      (!(compactProofRootTaggedSuccessBoundedGraphDef)
          proofTable proofWidth proofTokenCount
            proofInputStart proofInputFinish
            rootStart rootFinish proofTag proofEndpointBound ∧
        !(compactCertificateNodeFailureBoundedGraphDef)
          certificateTable certificateWidth certificateTokenCount
            certificateInputStart certificateInputFinish
            certificateEndpointBound) ∨
      (!(compactProofRootTaggedSuccessBoundedGraphDef)
          proofTable proofWidth proofTokenCount
            proofInputStart proofInputFinish
            rootStart rootFinish proofTag proofEndpointBound ∧
        !(compactCertificateNodeSuccessBoundedGraphDef)
          certificateTable certificateWidth certificateTokenCount
            certificateInputStart certificateInputFinish
            axiomStart axiomFinish formulaStart formulaFinish
            suffixStart suffixFinish certificateTag certificateEndpointBound ∧
        ¬ !(compactNumericNodeTransitionTagMatchDef)
          proofTag certificateTag))”

def compactNumericParsePayloadFailureSeparatedTablesGraphEnvironment
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

@[simp] theorem compactNumericParsePayloadFailureSeparatedTablesGraphDef_spec
    (stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound : Nat) :
    compactNumericParsePayloadFailureSeparatedTablesGraphDef.val.Evalb
        (compactNumericParsePayloadFailureSeparatedTablesGraphEnvironment
          stateTable stateWidth stateTokenCount
          stateProofStart stateProofFinish
          stateCertificateStart stateCertificateFinish
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound) ↔
      CompactNumericParsePayloadFailureSeparatedTablesGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound := by
  let env := compactNumericParsePayloadFailureSeparatedTablesGraphEnvironment
    stateTable stateWidth stateTokenCount
    stateProofStart stateProofFinish
    stateCertificateStart stateCertificateFinish
    proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
    rootStart rootFinish proofTag proofEndpointBound
    certificateTable certificateWidth certificateTokenCount
    certificateInputStart certificateInputFinish
    axiomStart axiomFinish formulaStart formulaFinish
    suffixStart suffixFinish certificateTag certificateEndpointBound
  change compactNumericParsePayloadFailureSeparatedTablesGraphDef.val.Evalb env ↔ _
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
  have hproofFailureEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#7 : Semiterm ℒₒᵣ Empty 29), #8, #9, #10, #11, #15]) =
        ![proofTable, proofWidth, proofTokenCount,
          proofInputStart, proofInputFinish, proofEndpointBound] := by
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
  have hcertificateFailureEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#16 : Semiterm ℒₒᵣ Empty 29), #17, #18, #19, #20, #28]) =
        ![certificateTable, certificateWidth, certificateTokenCount,
          certificateInputStart, certificateInputFinish,
          certificateEndpointBound] := by
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
  simp [compactNumericParsePayloadFailureSeparatedTablesGraphDef,
    CompactNumericParsePayloadFailureSeparatedTablesGraph,
    hproofCrossEnv, hcertificateCrossEnv,
    hproofFailureEnv, hproofSuccessEnv,
    hcertificateFailureEnv, hcertificateSuccessEnv, htagEnv]

theorem compactNumericParsePayloadFailureSeparatedTablesGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericParsePayloadFailureSeparatedTablesGraphDef.val := by
  simp [compactNumericParsePayloadFailureSeparatedTablesGraphDef]

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

theorem CompactNumericParsePayloadFailureSeparatedTablesGraph.sound
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
    (hgraph : CompactNumericParsePayloadFailureSeparatedTablesGraph
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
    compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) = none := by
  apply (compactNumericParsePayload_eq_none_iff
    ((proofTokens, certificateTokens), (restTasks, values))).2
  rcases hgraph with ⟨hproofCross, hcertificateCross, hbranch⟩
  rcases hbranch with hproofFailure |
      ⟨hproofSuccess, hcertificateFailure⟩ |
      ⟨hproofSuccess, hcertificateSuccess, htagMismatch⟩
  · rcases hproofFailure.sound with
      ⟨parserInput, hparserInput, hparser⟩
    have hinputEq : parserInput = proofTokens :=
      hproofCross.natListValues_eq hproofLayout hparserInput
    subst parserInput
    exact Or.inl hparser
  · rcases hproofSuccess.sound with
      ⟨parserInput, proofNode, hparserInput,
        _hroot, hproofParser, _hproofTag⟩
    rcases hcertificateFailure.sound with
      ⟨certificateInput, hcertificateInput, hcertificateParser⟩
    have hproofInputEq : parserInput = proofTokens :=
      hproofCross.natListValues_eq hproofLayout hparserInput
    have hcertificateInputEq : certificateInput = certificateTokens :=
      hcertificateCross.natListValues_eq
        hcertificateLayout hcertificateInput
    subst parserInput
    subst certificateInput
    exact Or.inr (Or.inl
      ⟨proofNode, hproofParser, hcertificateParser⟩)
  · rcases hproofSuccess.sound with
      ⟨parserInput, proofNode, hparserInput,
        _hroot, hproofParser, hproofTag⟩
    rcases certificateSuccessNode hcertificateSuccess with
      ⟨certificateInput, certificateNode,
        hcertificateInput, hcertificateParser, hcertificateTag⟩
    have hproofInputEq : parserInput = proofTokens :=
      hproofCross.natListValues_eq hproofLayout hparserInput
    have hcertificateInputEq : certificateInput = certificateTokens :=
      hcertificateCross.natListValues_eq
        hcertificateLayout hcertificateInput
    subst parserInput
    subst certificateInput
    have hactualMismatch :
        ¬ CompactNumericNodeTransitionTagMatch
          proofNode.1 certificateNode.1 := by
      simpa only [hproofTag, hcertificateTag] using htagMismatch
    have htransition : compactNumericNodeTransition proofNode certificateNode
        restTasks values = none :=
      (compactNumericNodeTransition_eq_none_iff_not_tagMatch
        proofNode certificateNode restTasks values).2 hactualMismatch
    exact Or.inr (Or.inr
      ⟨proofNode, certificateNode,
        hproofParser, hcertificateParser, htransition⟩)

theorem exists_compactNumericParsePayloadFailureSeparatedTablesGraph_of_eq_none
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
    (hparse : compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) = none) :
    ∃ proofTable proofWidth proofTokenCount proofInputStart proofInputFinish,
    ∃ rootStart rootFinish proofTag proofEndpointBound,
    ∃ certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish certificateTag certificateEndpointBound,
      CompactNumericParsePayloadFailureSeparatedTablesGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound := by
  have hcases := (compactNumericParsePayload_eq_none_iff
    ((proofTokens, certificateTokens), (restTasks, values))).mp hparse
  rcases hcases with hproofFailure |
      ⟨proofNode, hproofParser, hcertificateFailure⟩ |
      ⟨proofNode, certificateNode,
        hproofParser, hcertificateParser, htransitionFailure⟩
  · rcases
        exists_compactProofRootFailureEndpointBoundedGraph_of_none_with_inputLayout
          proofTokens hproofFailure with
      ⟨proofTable, proofWidth, proofTokenCount,
        proofInputStart, proofInputFinish, proofEndpointBound,
        hparserInputLayout, hproofFailureGraph⟩
    have hproofCross :=
      CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
        hproofLayout hparserInputLayout
    have hcertificateCross :=
      CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
        hcertificateLayout hcertificateLayout
    exact ⟨proofTable, proofWidth, proofTokenCount,
      proofInputStart, proofInputFinish,
      0, 0, 0, proofEndpointBound,
      stateTable, stateWidth, stateTokenCount,
      stateCertificateStart, stateCertificateFinish,
      0, 0, 0, 0, 0, 0, 0, 0,
      hproofCross, hcertificateCross, Or.inl hproofFailureGraph⟩
  · rcases
        exists_compactProofRootSuccessBoundedGraph_of_parser_success_with_inputLayout
          hproofParser with
      ⟨proofTable, proofWidth, proofTokenCount,
        proofInputStart, proofInputFinish,
        rootStart, rootFinish, proofEndpointBound,
        hparserInputLayout, hproofSuccessGraph⟩
    rcases
        FoundationCompactNumericListedDirectProofRootTaggedSuccessBoundedFormula.CompactProofRootSuccessBoundedGraph.exists_tagged
          hproofSuccessGraph with
      ⟨proofTag, hproofTaggedGraph⟩
    rcases
        exists_compactCertificateNodeFailureBoundedGraph_of_parser_none_with_inputLayout
          certificateTokens hcertificateFailure with
      ⟨certificateTable, certificateWidth, certificateTokenCount,
        certificateInputStart, certificateInputFinish,
        certificateEndpointBound,
        hcertificateInputLayout, hcertificateFailureGraph⟩
    have hproofCross :=
      CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
        hproofLayout hparserInputLayout
    have hcertificateCross :=
      CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
        hcertificateLayout hcertificateInputLayout
    exact ⟨proofTable, proofWidth, proofTokenCount,
      proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      0, 0, 0, 0, 0, 0, 0, certificateEndpointBound,
      hproofCross, hcertificateCross,
      Or.inr (Or.inl ⟨hproofTaggedGraph, hcertificateFailureGraph⟩)⟩
  · rcases certificateNode with ⟨certificateTag, axiomTokens, suffix⟩
    rcases
        exists_compactProofRootSuccessBoundedGraph_of_parser_success_with_inputLayout
          hproofParser with
      ⟨proofTable, proofWidth, proofTokenCount,
        proofInputStart, proofInputFinish,
        rootStart, rootFinish, proofEndpointBound,
        hparserInputLayout, hproofSuccessGraph⟩
    rcases
        FoundationCompactNumericListedDirectProofRootTaggedSuccessBoundedFormula.CompactProofRootSuccessBoundedGraph.exists_tagged
          hproofSuccessGraph with
      ⟨proofTag, hproofTaggedGraph⟩
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
        hproofLayout hparserInputLayout
    have hcertificateCross :=
      CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
        hcertificateLayout hcertificateInputLayout
    have hactualMismatch :
        ¬ CompactNumericNodeTransitionTagMatch proofNode.1 certificateTag :=
      (compactNumericNodeTransition_eq_none_iff_not_tagMatch
        proofNode (certificateTag, (axiomTokens, suffix))
          restTasks values).mp htransitionFailure
    rcases hproofTaggedGraph.sound with
      ⟨decodedInput, decodedRoot, hdecodedInputLayout,
        _hdecodedRootLayout, hdecodedParser, hdecodedTag⟩
    have hdecodedInputEq : decodedInput = proofTokens :=
      hproofCross.natListValues_eq hproofLayout hdecodedInputLayout
    subst decodedInput
    have hdecodedRootEq : decodedRoot = proofNode :=
      Option.some.inj (hdecodedParser.symm.trans hproofParser)
    subst decodedRoot
    have htagMismatch :
        ¬ CompactNumericNodeTransitionTagMatch proofTag certificateTag := by
      simpa only [hdecodedTag] using hactualMismatch
    exact ⟨proofTable, proofWidth, proofTokenCount,
      proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      hproofCross, hcertificateCross,
      Or.inr (Or.inr
        ⟨hproofTaggedGraph, hcertificateSuccessGraph, htagMismatch⟩)⟩

theorem compactNumericParsePayload_eq_none_iff_exists_failureSeparatedTablesGraph
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
    compactNumericParsePayload
        ((proofTokens, certificateTokens), (restTasks, values)) = none ↔
      ∃ proofTable proofWidth proofTokenCount proofInputStart proofInputFinish,
      ∃ rootStart rootFinish proofTag proofEndpointBound,
      ∃ certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish,
      ∃ axiomStart axiomFinish formulaStart formulaFinish,
      ∃ suffixStart suffixFinish certificateTag certificateEndpointBound,
        CompactNumericParsePayloadFailureSeparatedTablesGraph
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
  · exact exists_compactNumericParsePayloadFailureSeparatedTablesGraph_of_eq_none
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

#print axioms compactNumericParsePayloadFailureSeparatedTablesGraphDef_spec
#print axioms
  compactNumericParsePayloadFailureSeparatedTablesGraphDef_sigmaZero
#print axioms CompactNumericParsePayloadFailureSeparatedTablesGraph.sound
#print axioms
  exists_compactNumericParsePayloadFailureSeparatedTablesGraph_of_eq_none
#print axioms
  compactNumericParsePayload_eq_none_iff_exists_failureSeparatedTablesGraph

end FoundationCompactNumericListedDirectVerifierParsePayloadFailureSeparatedTablesFormula
