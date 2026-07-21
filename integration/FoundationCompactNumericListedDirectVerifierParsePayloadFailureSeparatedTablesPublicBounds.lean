import integration.FoundationCompactNumericListedDirectVerifierParsePayloadFailureSeparatedTablesFormula
import integration.FoundationCompactNumericListedDirectProofRootFailurePublicBounds
import integration.FoundationCompactNumericListedDirectProofRootSuccessPublicBounds
import integration.FoundationCompactNumericListedDirectCertificateNodeFailurePublicBounds
import integration.FoundationCompactNumericListedDirectCertificateNodeSuccessPublicBounds

/-!
# Public coordinates for a failed parse payload

The state stream and the two parser tables are kept separate.  The seven state
coordinates are controlled by a caller-supplied canonical-state budget; every
remaining coordinate is constructed with the public proof-root and
certificate-node bounds.  No parser table, endpoint, or tag remains hidden in
an existential environment constant.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParsePayloadFailureSeparatedTablesPublicBounds

open FoundationCompactAdditiveTokenCodec
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
open FoundationCompactNumericListedDirectVerifierParsePayloadFailureSeparatedTablesFormula

def compactNumericParsePayloadFailureSeparatedTablesParserCoordinateSizeBound
    (proofWeight certificateWeight : Nat) : Nat :=
  proofWeight + certificateWeight +
    FoundationCompactNumericListedDirectProofRootFailurePublicBounds.compactProofRootFailurePublicCoordinateSizeBound
      proofWeight +
    FoundationCompactNumericListedDirectProofRootSuccessPublicBounds.compactProofRootSuccessPublicCoordinateSizeBound
      proofWeight +
    FoundationCompactNumericListedDirectCertificateNodeFailurePublicBounds.compactCertificateNodeFailurePublicCoordinateSizeBound
      certificateWeight +
    FoundationCompactNumericListedDirectCertificateNodeSuccessPublicBounds.compactCertificateNodeSuccessPublicCoordinateSizeBound
      certificateWeight +
    10

def compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
    (stateBound proofWeight certificateWeight : Nat) : Nat :=
  stateBound +
    compactNumericParsePayloadFailureSeparatedTablesParserCoordinateSizeBound
      proofWeight certificateWeight

structure CompactNumericParsePayloadFailureSeparatedTablesStateCoordinateBounds
    (stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish bound : Nat) : Prop where
  stateTable : Nat.size stateTable <= bound
  stateWidth : Nat.size stateWidth <= bound
  stateTokenCount : Nat.size stateTokenCount <= bound
  stateProofStart : Nat.size stateProofStart <= bound
  stateProofFinish : Nat.size stateProofFinish <= bound
  stateCertificateStart : Nat.size stateCertificateStart <= bound
  stateCertificateFinish : Nat.size stateCertificateFinish <= bound

structure CompactNumericParsePayloadFailureSeparatedTablesParserCoordinateBounds
    (proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      bound : Nat) : Prop where
  proofTable : Nat.size proofTable <= bound
  proofWidth : Nat.size proofWidth <= bound
  proofTokenCount : Nat.size proofTokenCount <= bound
  proofInputStart : Nat.size proofInputStart <= bound
  proofInputFinish : Nat.size proofInputFinish <= bound
  rootStart : Nat.size rootStart <= bound
  rootFinish : Nat.size rootFinish <= bound
  proofTag : Nat.size proofTag <= bound
  proofEndpointBound : Nat.size proofEndpointBound <= bound
  certificateTable : Nat.size certificateTable <= bound
  certificateWidth : Nat.size certificateWidth <= bound
  certificateTokenCount : Nat.size certificateTokenCount <= bound
  certificateInputStart : Nat.size certificateInputStart <= bound
  certificateInputFinish : Nat.size certificateInputFinish <= bound
  axiomStart : Nat.size axiomStart <= bound
  axiomFinish : Nat.size axiomFinish <= bound
  formulaStart : Nat.size formulaStart <= bound
  formulaFinish : Nat.size formulaFinish <= bound
  suffixStart : Nat.size suffixStart <= bound
  suffixFinish : Nat.size suffixFinish <= bound
  certificateTag : Nat.size certificateTag <= bound
  certificateEndpointBound : Nat.size certificateEndpointBound <= bound

private theorem stateBound_le_publicBound
    (stateBound proofWeight certificateWeight : Nat) :
    stateBound <=
      compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
        stateBound proofWeight certificateWeight := by
  unfold compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
  omega

private theorem proofFailureBound_le_publicBound
    (stateBound proofWeight certificateWeight : Nat) :
    FoundationCompactNumericListedDirectProofRootFailurePublicBounds.compactProofRootFailurePublicCoordinateSizeBound
        proofWeight <=
      compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
        stateBound proofWeight certificateWeight := by
  unfold compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
  unfold compactNumericParsePayloadFailureSeparatedTablesParserCoordinateSizeBound
  omega

private theorem proofSuccessBound_le_publicBound
    (stateBound proofWeight certificateWeight : Nat) :
    FoundationCompactNumericListedDirectProofRootSuccessPublicBounds.compactProofRootSuccessPublicCoordinateSizeBound
        proofWeight <=
      compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
        stateBound proofWeight certificateWeight := by
  unfold compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
  unfold compactNumericParsePayloadFailureSeparatedTablesParserCoordinateSizeBound
  omega

private theorem certificateFailureBound_le_publicBound
    (stateBound proofWeight certificateWeight : Nat) :
    FoundationCompactNumericListedDirectCertificateNodeFailurePublicBounds.compactCertificateNodeFailurePublicCoordinateSizeBound
        certificateWeight <=
      compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
        stateBound proofWeight certificateWeight := by
  unfold compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
  unfold compactNumericParsePayloadFailureSeparatedTablesParserCoordinateSizeBound
  omega

private theorem certificateSuccessBound_le_publicBound
    (stateBound proofWeight certificateWeight : Nat) :
    FoundationCompactNumericListedDirectCertificateNodeSuccessPublicBounds.compactCertificateNodeSuccessPublicCoordinateSizeBound
        certificateWeight <=
      compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
        stateBound proofWeight certificateWeight := by
  unfold compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
  unfold compactNumericParsePayloadFailureSeparatedTablesParserCoordinateSizeBound
  omega

private theorem four_le_publicBound
    (stateBound proofWeight certificateWeight : Nat) :
    4 <=
      compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
        stateBound proofWeight certificateWeight := by
  unfold compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
  unfold compactNumericParsePayloadFailureSeparatedTablesParserCoordinateSizeBound
  omega

private theorem compactProofRootParser_success_tag_cases
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root) :
    root.1 = 0 \/ root.1 = 1 \/ root.1 = 2 \/ root.1 = 3 \/
      root.1 = 4 \/ root.1 = 5 \/ root.1 = 6 \/ root.1 = 7 \/
      root.1 = 8 \/ root.1 = 9 := by
  have hvalid :=
    (compactListedProofNodeFieldsParser_eq_some_iff_branchValid
      input root).mp hparser
  cases input with
  | nil =>
      simp [CompactNumericProofRootBranchValid] at hvalid
  | cons tag body =>
      by_cases h0 : tag = 0
      · have hbranch : root.1 = 0 /\
            compactNodeSequentFormulaFields 0 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid, h0] using hvalid
        exact Or.inl hbranch.1
      by_cases h1 : tag = 1
      · have hbranch : root.1 = 1 /\
            compactNodeSequentClosedFormulaFields body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid, h0, h1] using hvalid
        exact Or.inr (Or.inl hbranch.1)
      by_cases h2 : tag = 2
      · have hbranch : root.1 = 2 /\
            compactNodeSequentOnlyFields body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid, h0, h1, h2] using hvalid
        exact Or.inr (Or.inr (Or.inl hbranch.1))
      by_cases h3 : tag = 3
      · have hbranch : root.1 = 3 /\
            compactNodeSequentTwoFormulaFields 0 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inl hbranch.1)))
      by_cases h4 : tag = 4
      · have hbranch : root.1 = 4 /\
            compactNodeSequentTwoFormulaFields 0 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbranch.1))))
      by_cases h5 : tag = 5
      · have hbranch : root.1 = 5 /\
            compactNodeSequentFormulaFields 1 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4, h5] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl hbranch.1)))))
      by_cases h6 : tag = 6
      · have hbranch : root.1 = 6 /\
            compactNodeSequentFormulaTermFields 1 0 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4, h5, h6] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl hbranch.1))))))
      by_cases h7 : tag = 7
      · have hbranch : root.1 = 7 /\
            compactNodeSequentOnlyFields body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4, h5, h6, h7] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl hbranch.1)))))))
      by_cases h8 : tag = 8
      · have hbranch : root.1 = 8 /\
            compactNodeSequentOnlyFields body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4, h5, h6, h7, h8] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbranch.1))))))))
      by_cases h9 : tag = 9
      · have hbranch : root.1 = 9 /\
            compactNodeSequentFormulaFields 0 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hbranch.1))))))))
      simp [CompactNumericProofRootBranchValid,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] at hvalid

private theorem compactProofRootParser_success_tag_size_le_four
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root) :
    Nat.size root.1 <= 4 := by
  rcases compactProofRootParser_success_tag_cases hparser with
    h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  all_goals simp_all <;> decide

theorem compactNumericParsePayloadFailureSeparatedTablesGraphEnvironment_size_le
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      bound : Nat}
    (hstate :
      CompactNumericParsePayloadFailureSeparatedTablesStateCoordinateBounds
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish bound)
    (hparser :
      CompactNumericParsePayloadFailureSeparatedTablesParserCoordinateBounds
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        bound)
    (coordinate : Fin 29) :
    Nat.size
        (compactNumericParsePayloadFailureSeparatedTablesGraphEnvironment
          stateTable stateWidth stateTokenCount
          stateProofStart stateProofFinish
          stateCertificateStart stateCertificateFinish
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound
          coordinate) <= bound := by
  rcases hstate with
    ⟨hstateTable, hstateWidth, hstateTokenCount,
      hstateProofStart, hstateProofFinish,
      hstateCertificateStart, hstateCertificateFinish⟩
  rcases hparser with
    ⟨hproofTable, hproofWidth, hproofTokenCount,
      hproofInputStart, hproofInputFinish,
      hrootStart, hrootFinish, hproofTag, hproofEndpointBound,
      hcertificateTable, hcertificateWidth, hcertificateTokenCount,
      hcertificateInputStart, hcertificateInputFinish,
      haxiomStart, haxiomFinish, hformulaStart, hformulaFinish,
      hsuffixStart, hsuffixFinish, hcertificateTag,
      hcertificateEndpointBound⟩
  fin_cases coordinate <;>
    simp [compactNumericParsePayloadFailureSeparatedTablesGraphEnvironment] <;>
    assumption

/- Every actual parse-payload failure produces the exact separated-tables
graph, and every one of its 29 exposed coordinates has a public bound. -/
set_option maxHeartbeats 2400000 in
theorem
    exists_compactNumericParsePayloadFailureSeparatedTablesGraph_of_eq_none_with_publicBounds
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish stateBound : Nat}
    {proofTokens certificateTokens : List Nat}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hstateBounds :
      CompactNumericParsePayloadFailureSeparatedTablesStateCoordinateBounds
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish stateBound)
    (hparse : compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) = none) :
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    let publicBound :=
      compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
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
        suffixStart suffixFinish certificateTag certificateEndpointBound ∧
      CompactNumericParsePayloadFailureSeparatedTablesParserCoordinateBounds
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        publicBound ∧
      ∀ coordinate : Fin 29,
        Nat.size
          (compactNumericParsePayloadFailureSeparatedTablesGraphEnvironment
            stateTable stateWidth stateTokenCount
            stateProofStart stateProofFinish
            stateCertificateStart stateCertificateFinish
            proofTable proofWidth proofTokenCount
            proofInputStart proofInputFinish
            rootStart rootFinish proofTag proofEndpointBound
            certificateTable certificateWidth certificateTokenCount
            certificateInputStart certificateInputFinish
            axiomStart axiomFinish formulaStart formulaFinish
            suffixStart suffixFinish certificateTag certificateEndpointBound
            coordinate) <= publicBound := by
  let proofWeight := compactAdditiveValueWeight proofTokens
  let certificateWeight := compactAdditiveValueWeight certificateTokens
  let publicBound :=
    compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  have hstateLift : stateBound <= publicBound := by
    exact stateBound_le_publicBound stateBound proofWeight certificateWeight
  have hproofFailureLift :
      FoundationCompactNumericListedDirectProofRootFailurePublicBounds.compactProofRootFailurePublicCoordinateSizeBound
          proofWeight <= publicBound := by
    exact proofFailureBound_le_publicBound
      stateBound proofWeight certificateWeight
  have hproofSuccessLift :
      FoundationCompactNumericListedDirectProofRootSuccessPublicBounds.compactProofRootSuccessPublicCoordinateSizeBound
          proofWeight <= publicBound := by
    exact proofSuccessBound_le_publicBound
      stateBound proofWeight certificateWeight
  have hcertificateFailureLift :
      FoundationCompactNumericListedDirectCertificateNodeFailurePublicBounds.compactCertificateNodeFailurePublicCoordinateSizeBound
          certificateWeight <= publicBound := by
    exact certificateFailureBound_le_publicBound
      stateBound proofWeight certificateWeight
  have hcertificateSuccessLift :
      FoundationCompactNumericListedDirectCertificateNodeSuccessPublicBounds.compactCertificateNodeSuccessPublicCoordinateSizeBound
          certificateWeight <= publicBound := by
    exact certificateSuccessBound_le_publicBound
      stateBound proofWeight certificateWeight
  have hfour : 4 <= publicBound := by
    exact four_le_publicBound stateBound proofWeight certificateWeight
  have hzero : Nat.size 0 <= publicBound := by simp
  have hcases := (compactNumericParsePayload_eq_none_iff
    ((proofTokens, certificateTokens), (restTasks, values))).mp hparse
  rcases hcases with hproofFailure |
      ⟨proofNode, hproofParser, hcertificateFailure⟩ |
      ⟨proofNode, certificateNode,
        hproofParser, hcertificateParser, htransitionFailure⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootFailurePublicBounds.exists_compactProofRootFailureEndpointBoundedGraph_of_none_with_publicBounds
          proofTokens hproofFailure with
      ⟨proofTable, proofWidth, proofTokenCount,
        proofInputStart, proofInputFinish, proofEndpointBound,
        hparserInputLayout, hproofFailureGraph, hproofBounds⟩
    have hproofCross :=
      CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
        hproofLayout hparserInputLayout
    have hcertificateCross :=
      CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
        hcertificateLayout hcertificateLayout
    have hparserBounds :
        CompactNumericParsePayloadFailureSeparatedTablesParserCoordinateBounds
          proofTable proofWidth proofTokenCount
          proofInputStart proofInputFinish
          0 0 0 proofEndpointBound
          stateTable stateWidth stateTokenCount
          stateCertificateStart stateCertificateFinish
          0 0 0 0 0 0 0 0 publicBound :=
      { proofTable := hproofBounds.tokenTable.trans hproofFailureLift
        proofWidth := hproofBounds.width.trans hproofFailureLift
        proofTokenCount := hproofBounds.tokenCount.trans hproofFailureLift
        proofInputStart := hproofBounds.inputStart.trans hproofFailureLift
        proofInputFinish := hproofBounds.inputFinish.trans hproofFailureLift
        rootStart := hzero
        rootFinish := hzero
        proofTag := hzero
        proofEndpointBound :=
          hproofBounds.endpointBound.trans hproofFailureLift
        certificateTable := hstateBounds.stateTable.trans hstateLift
        certificateWidth := hstateBounds.stateWidth.trans hstateLift
        certificateTokenCount :=
          hstateBounds.stateTokenCount.trans hstateLift
        certificateInputStart :=
          hstateBounds.stateCertificateStart.trans hstateLift
        certificateInputFinish :=
          hstateBounds.stateCertificateFinish.trans hstateLift
        axiomStart := hzero
        axiomFinish := hzero
        formulaStart := hzero
        formulaFinish := hzero
        suffixStart := hzero
        suffixFinish := hzero
        certificateTag := hzero
        certificateEndpointBound := hzero }
    have hstatePublic :
        CompactNumericParsePayloadFailureSeparatedTablesStateCoordinateBounds
          stateTable stateWidth stateTokenCount
          stateProofStart stateProofFinish
          stateCertificateStart stateCertificateFinish publicBound :=
      { stateTable := hstateBounds.stateTable.trans hstateLift
        stateWidth := hstateBounds.stateWidth.trans hstateLift
        stateTokenCount := hstateBounds.stateTokenCount.trans hstateLift
        stateProofStart := hstateBounds.stateProofStart.trans hstateLift
        stateProofFinish := hstateBounds.stateProofFinish.trans hstateLift
        stateCertificateStart :=
          hstateBounds.stateCertificateStart.trans hstateLift
        stateCertificateFinish :=
          hstateBounds.stateCertificateFinish.trans hstateLift }
    refine ⟨proofTable, proofWidth, proofTokenCount,
      proofInputStart, proofInputFinish,
      0, 0, 0, proofEndpointBound,
      stateTable, stateWidth, stateTokenCount,
      stateCertificateStart, stateCertificateFinish,
      0, 0, 0, 0, 0, 0, 0, 0, ?_, hparserBounds, ?_⟩
    · exact ⟨hproofCross, hcertificateCross, Or.inl hproofFailureGraph⟩
    · exact
        compactNumericParsePayloadFailureSeparatedTablesGraphEnvironment_size_le
          hstatePublic hparserBounds
  · rcases
        FoundationCompactNumericListedDirectProofRootSuccessPublicBounds.exists_compactProofRootSuccessBoundedGraph_of_parser_success_with_publicBounds
          hproofParser with
      ⟨proofTable, proofWidth, proofTokenCount,
        proofInputStart, proofInputFinish,
        rootStart, rootFinish, proofEndpointBound,
        hparserInputLayout, hproofSuccessGraph, hproofBounds⟩
    rcases
        CompactProofRootSuccessBoundedGraph.exists_tagged
          hproofSuccessGraph with
      ⟨proofTag, hproofTaggedGraph⟩
    rcases
        FoundationCompactNumericListedDirectCertificateNodeFailurePublicBounds.exists_compactCertificateNodeFailureBoundedGraph_of_parser_none_with_publicBounds
          certificateTokens hcertificateFailure with
      ⟨certificateTable, certificateWidth, certificateTokenCount,
        certificateInputStart, certificateInputFinish,
        certificateEndpointBound,
        hcertificateInputLayout, hcertificateFailureGraph,
        hcertificateBounds⟩
    have hproofCross :=
      CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
        hproofLayout hparserInputLayout
    have hcertificateCross :=
      CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
        hcertificateLayout hcertificateInputLayout
    rcases hproofTaggedGraph.sound with
      ⟨decodedInput, decodedRoot, hdecodedInputLayout,
        _hdecodedRootLayout, hdecodedParser, hdecodedTag⟩
    have hdecodedInputEq : decodedInput = proofTokens :=
      hproofCross.natListValues_eq hproofLayout hdecodedInputLayout
    subst decodedInput
    have hdecodedRootEq : decodedRoot = proofNode :=
      Option.some.inj (hdecodedParser.symm.trans hproofParser)
    subst decodedRoot
    have hproofTagBound : Nat.size proofTag <= publicBound := by
      rw [← hdecodedTag]
      exact
        (compactProofRootParser_success_tag_size_le_four hproofParser).trans
          hfour
    have hparserBounds :
        CompactNumericParsePayloadFailureSeparatedTablesParserCoordinateBounds
          proofTable proofWidth proofTokenCount
          proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          0 0 0 0 0 0 0 certificateEndpointBound publicBound :=
      { proofTable := hproofBounds.tokenTable.trans hproofSuccessLift
        proofWidth := hproofBounds.width.trans hproofSuccessLift
        proofTokenCount := hproofBounds.tokenCount.trans hproofSuccessLift
        proofInputStart := hproofBounds.inputStart.trans hproofSuccessLift
        proofInputFinish := hproofBounds.inputFinish.trans hproofSuccessLift
        rootStart := hproofBounds.rootStart.trans hproofSuccessLift
        rootFinish := hproofBounds.rootFinish.trans hproofSuccessLift
        proofTag := hproofTagBound
        proofEndpointBound :=
          hproofBounds.endpointBound.trans hproofSuccessLift
        certificateTable :=
          hcertificateBounds.tokenTable.trans hcertificateFailureLift
        certificateWidth :=
          hcertificateBounds.width.trans hcertificateFailureLift
        certificateTokenCount :=
          hcertificateBounds.tokenCount.trans hcertificateFailureLift
        certificateInputStart :=
          hcertificateBounds.inputStart.trans hcertificateFailureLift
        certificateInputFinish :=
          hcertificateBounds.inputFinish.trans hcertificateFailureLift
        axiomStart := hzero
        axiomFinish := hzero
        formulaStart := hzero
        formulaFinish := hzero
        suffixStart := hzero
        suffixFinish := hzero
        certificateTag := hzero
        certificateEndpointBound :=
          hcertificateBounds.endpointBound.trans hcertificateFailureLift }
    have hstatePublic :
        CompactNumericParsePayloadFailureSeparatedTablesStateCoordinateBounds
          stateTable stateWidth stateTokenCount
          stateProofStart stateProofFinish
          stateCertificateStart stateCertificateFinish publicBound :=
      { stateTable := hstateBounds.stateTable.trans hstateLift
        stateWidth := hstateBounds.stateWidth.trans hstateLift
        stateTokenCount := hstateBounds.stateTokenCount.trans hstateLift
        stateProofStart := hstateBounds.stateProofStart.trans hstateLift
        stateProofFinish := hstateBounds.stateProofFinish.trans hstateLift
        stateCertificateStart :=
          hstateBounds.stateCertificateStart.trans hstateLift
        stateCertificateFinish :=
          hstateBounds.stateCertificateFinish.trans hstateLift }
    refine ⟨proofTable, proofWidth, proofTokenCount,
      proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      0, 0, 0, 0, 0, 0, 0, certificateEndpointBound,
      ?_, hparserBounds, ?_⟩
    · exact ⟨hproofCross, hcertificateCross,
        Or.inr (Or.inl
          ⟨hproofTaggedGraph, hcertificateFailureGraph⟩)⟩
    · exact
        compactNumericParsePayloadFailureSeparatedTablesGraphEnvironment_size_le
          hstatePublic hparserBounds
  · rcases certificateNode with ⟨certificateTag, axiomTokens, suffix⟩
    rcases
        FoundationCompactNumericListedDirectProofRootSuccessPublicBounds.exists_compactProofRootSuccessBoundedGraph_of_parser_success_with_publicBounds
          hproofParser with
      ⟨proofTable, proofWidth, proofTokenCount,
        proofInputStart, proofInputFinish,
        rootStart, rootFinish, proofEndpointBound,
        hparserInputLayout, hproofSuccessGraph, hproofBounds⟩
    rcases
        CompactProofRootSuccessBoundedGraph.exists_tagged
          hproofSuccessGraph with
      ⟨proofTag, hproofTaggedGraph⟩
    rcases
        FoundationCompactNumericListedDirectCertificateNodeSuccessPublicBounds.exists_compactCertificateNodeSuccessBoundedGraph_of_parser_success_with_publicBounds
          hcertificateParser with
      ⟨certificateTable, certificateWidth, certificateTokenCount,
        certificateInputStart, certificateInputFinish,
        axiomStart, axiomFinish, formulaStart, formulaFinish,
        suffixStart, suffixFinish, certificateEndpointBound,
        hcertificateInputLayout, hcertificateSuccessGraph,
        hcertificateBounds⟩
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
    have hproofTagBound : Nat.size proofTag <= publicBound := by
      rw [← hdecodedTag]
      exact
        (compactProofRootParser_success_tag_size_le_four hproofParser).trans
          hfour
    have hparserBounds :
        CompactNumericParsePayloadFailureSeparatedTablesParserCoordinateBounds
          proofTable proofWidth proofTokenCount
          proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound
          publicBound :=
      { proofTable := hproofBounds.tokenTable.trans hproofSuccessLift
        proofWidth := hproofBounds.width.trans hproofSuccessLift
        proofTokenCount := hproofBounds.tokenCount.trans hproofSuccessLift
        proofInputStart := hproofBounds.inputStart.trans hproofSuccessLift
        proofInputFinish := hproofBounds.inputFinish.trans hproofSuccessLift
        rootStart := hproofBounds.rootStart.trans hproofSuccessLift
        rootFinish := hproofBounds.rootFinish.trans hproofSuccessLift
        proofTag := hproofTagBound
        proofEndpointBound :=
          hproofBounds.endpointBound.trans hproofSuccessLift
        certificateTable :=
          hcertificateBounds.tokenTable.trans hcertificateSuccessLift
        certificateWidth :=
          hcertificateBounds.width.trans hcertificateSuccessLift
        certificateTokenCount :=
          hcertificateBounds.tokenCount.trans hcertificateSuccessLift
        certificateInputStart :=
          hcertificateBounds.inputStart.trans hcertificateSuccessLift
        certificateInputFinish :=
          hcertificateBounds.inputFinish.trans hcertificateSuccessLift
        axiomStart :=
          hcertificateBounds.axiomStart.trans hcertificateSuccessLift
        axiomFinish :=
          hcertificateBounds.axiomFinish.trans hcertificateSuccessLift
        formulaStart :=
          hcertificateBounds.formulaStart.trans hcertificateSuccessLift
        formulaFinish :=
          hcertificateBounds.formulaFinish.trans hcertificateSuccessLift
        suffixStart :=
          hcertificateBounds.suffixStart.trans hcertificateSuccessLift
        suffixFinish :=
          hcertificateBounds.suffixFinish.trans hcertificateSuccessLift
        certificateTag :=
          hcertificateBounds.certificateTag.trans hcertificateSuccessLift
        certificateEndpointBound :=
          hcertificateBounds.endpointBound.trans hcertificateSuccessLift }
    have hstatePublic :
        CompactNumericParsePayloadFailureSeparatedTablesStateCoordinateBounds
          stateTable stateWidth stateTokenCount
          stateProofStart stateProofFinish
          stateCertificateStart stateCertificateFinish publicBound :=
      { stateTable := hstateBounds.stateTable.trans hstateLift
        stateWidth := hstateBounds.stateWidth.trans hstateLift
        stateTokenCount := hstateBounds.stateTokenCount.trans hstateLift
        stateProofStart := hstateBounds.stateProofStart.trans hstateLift
        stateProofFinish := hstateBounds.stateProofFinish.trans hstateLift
        stateCertificateStart :=
          hstateBounds.stateCertificateStart.trans hstateLift
        stateCertificateFinish :=
          hstateBounds.stateCertificateFinish.trans hstateLift }
    refine ⟨proofTable, proofWidth, proofTokenCount,
      proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      ?_, hparserBounds, ?_⟩
    · exact ⟨hproofCross, hcertificateCross,
        Or.inr (Or.inr
          ⟨hproofTaggedGraph, hcertificateSuccessGraph, htagMismatch⟩)⟩
    · exact
        compactNumericParsePayloadFailureSeparatedTablesGraphEnvironment_size_le
          hstatePublic hparserBounds

#print axioms
  exists_compactNumericParsePayloadFailureSeparatedTablesGraph_of_eq_none_with_publicBounds

end FoundationCompactNumericListedDirectVerifierParsePayloadFailureSeparatedTablesPublicBounds
