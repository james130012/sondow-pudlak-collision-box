import integration.FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesFormula
import integration.FoundationCompactNumericListedDirectProofRootSuccessPublicBounds
import integration.FoundationCompactNumericListedDirectCertificateNodeSuccessPublicBounds

/-!
# Public coordinates for a successful parse payload

The verifier-state stream and the two parser tables remain independent.  The
seven state coordinates are controlled by a caller-supplied canonical-state
budget.  The proof-root and certificate parsers are reconstructed with their
public input-weight bounds, so all twenty-nine coordinates of the successful
separated-table graph have one explicit bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectProofRootSuccessBoundedFormula
open FoundationCompactNumericListedDirectProofRootTaggedSuccessBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeSuccessBoundedFormula
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectVerifierStepCases
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesFormula

def compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound
    (stateBound proofWeight certificateWeight : Nat) : Nat :=
  stateBound + proofWeight + certificateWeight +
    FoundationCompactNumericListedDirectProofRootSuccessPublicBounds.compactProofRootSuccessPublicCoordinateSizeBound
      proofWeight +
    FoundationCompactNumericListedDirectCertificateNodeSuccessPublicBounds.compactCertificateNodeSuccessPublicCoordinateSizeBound
      certificateWeight +
    10

structure CompactNumericParsePayloadSuccessSeparatedTablesStateCoordinateBounds
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

structure CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
    (proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      bound : Nat) : Prop where
  proofTable : Nat.size proofTable <= bound
  proofWidth_value : proofWidth <= bound
  proofWidth : Nat.size proofWidth <= bound
  proofTokenCount_value : proofTokenCount <= bound
  proofTokenCount : Nat.size proofTokenCount <= bound
  proofInputStart : Nat.size proofInputStart <= bound
  proofInputFinish : Nat.size proofInputFinish <= bound
  rootStart : Nat.size rootStart <= bound
  rootFinish : Nat.size rootFinish <= bound
  proofTag : Nat.size proofTag <= bound
  proofEndpointBound : Nat.size proofEndpointBound <= bound
  certificateTable : Nat.size certificateTable <= bound
  certificateWidth_value : certificateWidth <= bound
  certificateWidth : Nat.size certificateWidth <= bound
  certificateTokenCount_value : certificateTokenCount <= bound
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

theorem compactNumericNodeTransitionTagMatch_proofTag_size_le_four
    {proofTag certificateTag : Nat}
    (hmatch : CompactNumericNodeTransitionTagMatch
      proofTag certificateTag) :
    Nat.size proofTag <= 4 := by
  rcases hmatch with
    h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  all_goals rcases ‹_ ∧ _› with ⟨rfl, _⟩ <;> decide

theorem compactNumericParsePayloadSuccessSeparatedTablesGraphEnvironment_size_le
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
      CompactNumericParsePayloadSuccessSeparatedTablesStateCoordinateBounds
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish bound)
    (hparser :
      CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        bound)
    (coordinate : Fin 29) :
    Nat.size
        (compactNumericParsePayloadSuccessSeparatedTablesGraphEnvironment
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
    ⟨hproofTable, _hproofWidthValue, hproofWidth,
      _hproofTokenCountValue, hproofTokenCount,
      hproofInputStart, hproofInputFinish,
      hrootStart, hrootFinish, hproofTag, hproofEndpointBound,
      hcertificateTable, _hcertificateWidthValue, hcertificateWidth,
      _hcertificateTokenCountValue, hcertificateTokenCount,
      hcertificateInputStart, hcertificateInputFinish,
      haxiomStart, haxiomFinish, hformulaStart, hformulaFinish,
      hsuffixStart, hsuffixFinish, hcertificateTag,
      hcertificateEndpointBound⟩
  fin_cases coordinate <;>
    simp [compactNumericParsePayloadSuccessSeparatedTablesGraphEnvironment] <;>
    assumption

/- Every successful parser execution is rebuilt from the public proof-root
and certificate constructors.  The returned environment is therefore the
actual formula environment, not an arbitrary extensionally valid table. -/
set_option maxHeartbeats 2400000 in
theorem
    exists_compactNumericParsePayloadSuccessSeparatedTablesGraph_of_exists_some_with_publicBounds
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
      CompactNumericParsePayloadSuccessSeparatedTablesStateCoordinateBounds
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish stateBound)
    (hparse : exists parsed, compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) = some parsed) :
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    let publicBound :=
      compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
    exists proofTable proofWidth proofTokenCount proofInputStart proofInputFinish,
    exists rootStart rootFinish proofTag proofEndpointBound,
    exists certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish,
    exists axiomStart axiomFinish formulaStart formulaFinish,
    exists suffixStart suffixFinish certificateTag certificateEndpointBound,
      CompactNumericParsePayloadSuccessSeparatedTablesGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound /\
      CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        publicBound /\
      forall coordinate : Fin 29,
        Nat.size
          (compactNumericParsePayloadSuccessSeparatedTablesGraphEnvironment
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
    compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  have hstateLift : stateBound <= publicBound := by
    dsimp only [publicBound,
      compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound]
    omega
  have hproofLift :
      FoundationCompactNumericListedDirectProofRootSuccessPublicBounds.compactProofRootSuccessPublicCoordinateSizeBound
          proofWeight <= publicBound := by
    dsimp only [publicBound,
      compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound]
    omega
  have hcertificateLift :
      FoundationCompactNumericListedDirectCertificateNodeSuccessPublicBounds.compactCertificateNodeSuccessPublicCoordinateSizeBound
          certificateWeight <= publicBound := by
    dsimp only [publicBound,
      compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound]
    omega
  have hfour : 4 <= publicBound := by
    dsimp only [publicBound,
      compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound]
    omega
  rcases hparse with ⟨parsed, hparse⟩
  rcases (compactNumericParsePayload_eq_some_iff
      ((proofTokens, certificateTokens), (restTasks, values)) parsed).mp
      hparse with
    ⟨proofNode, certificateNode, hproofParser, hcertificateParser,
      htransition⟩
  rcases certificateNode with ⟨certificateTag, axiomTokens, suffix⟩
  rcases
      FoundationCompactNumericListedDirectProofRootSuccessPublicBounds.exists_compactProofRootSuccessBoundedGraph_of_parser_success_with_publicBounds
        hproofParser with
    ⟨proofTable, proofWidth, proofTokenCount,
      proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofEndpointBound,
      hproofInputLayout, hproofSuccessGraph, hproofBounds⟩
  rcases CompactProofRootSuccessBoundedGraph.exists_tagged
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
    ⟨decodedInput, decodedRoot, hdecodedInputLayout,
      _hdecodedRootLayout, hdecodedParser, hdecodedTag⟩
  have hdecodedInputEq : decodedInput = proofTokens :=
    hproofCross.natListValues_eq hproofLayout hdecodedInputLayout
  subst decodedInput
  have hdecodedRootEq : decodedRoot = proofNode :=
    Option.some.inj (hdecodedParser.symm.trans hproofParser)
  subst decodedRoot
  have htagMatch :
      CompactNumericNodeTransitionTagMatch proofTag certificateTag := by
    simpa only [hdecodedTag] using hactualTagMatch
  have hproofTagBound : Nat.size proofTag <= publicBound :=
    (compactNumericNodeTransitionTagMatch_proofTag_size_le_four
      htagMatch).trans hfour
  have hparserBounds :
      CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        publicBound :=
    { proofTable := hproofBounds.tokenTable.trans hproofLift
      proofWidth_value := hproofBounds.width_value.trans hproofLift
      proofWidth := hproofBounds.width.trans hproofLift
      proofTokenCount_value :=
        hproofBounds.tokenCount_value.trans hproofLift
      proofTokenCount := hproofBounds.tokenCount.trans hproofLift
      proofInputStart := hproofBounds.inputStart.trans hproofLift
      proofInputFinish := hproofBounds.inputFinish.trans hproofLift
      rootStart := hproofBounds.rootStart.trans hproofLift
      rootFinish := hproofBounds.rootFinish.trans hproofLift
      proofTag := hproofTagBound
      proofEndpointBound := hproofBounds.endpointBound.trans hproofLift
      certificateTable := hcertificateBounds.tokenTable.trans hcertificateLift
      certificateWidth_value :=
        hcertificateBounds.width_value.trans hcertificateLift
      certificateWidth := hcertificateBounds.width.trans hcertificateLift
      certificateTokenCount_value :=
        hcertificateBounds.tokenCount_value.trans hcertificateLift
      certificateTokenCount :=
        hcertificateBounds.tokenCount.trans hcertificateLift
      certificateInputStart :=
        hcertificateBounds.inputStart.trans hcertificateLift
      certificateInputFinish :=
        hcertificateBounds.inputFinish.trans hcertificateLift
      axiomStart := hcertificateBounds.axiomStart.trans hcertificateLift
      axiomFinish := hcertificateBounds.axiomFinish.trans hcertificateLift
      formulaStart := hcertificateBounds.formulaStart.trans hcertificateLift
      formulaFinish := hcertificateBounds.formulaFinish.trans hcertificateLift
      suffixStart := hcertificateBounds.suffixStart.trans hcertificateLift
      suffixFinish := hcertificateBounds.suffixFinish.trans hcertificateLift
      certificateTag :=
        hcertificateBounds.certificateTag.trans hcertificateLift
      certificateEndpointBound :=
        hcertificateBounds.endpointBound.trans hcertificateLift }
  have hstatePublic :
      CompactNumericParsePayloadSuccessSeparatedTablesStateCoordinateBounds
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
  · exact ⟨hproofCross, hcertificateCross, hproofTaggedGraph,
      hcertificateSuccessGraph, htagMatch⟩
  · exact
      compactNumericParsePayloadSuccessSeparatedTablesGraphEnvironment_size_le
        hstatePublic hparserBounds

#print axioms compactNumericNodeTransitionTagMatch_proofTag_size_le_four
#print axioms
  compactNumericParsePayloadSuccessSeparatedTablesGraphEnvironment_size_le
#print axioms
  exists_compactNumericParsePayloadSuccessSeparatedTablesGraph_of_exists_some_with_publicBounds

end FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesPublicBounds
