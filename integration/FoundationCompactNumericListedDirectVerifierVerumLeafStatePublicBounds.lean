import integration.FoundationCompactNumericListedDirectVerifierVerumLeafStateGraph
import integration.FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportPublicBounds

/-!
# Public bounds for the verum leaf state graph

The public successful-leaf transport constructor supplies the actual parser,
exposed-root, and leaf-output coordinates used by the verum state graph.  The
verum rule rows add no further witnesses or coordinate bounds.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierVerumLeafStatePublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectVerifierStepCases
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportGraph
open FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportPublicBounds
open FoundationCompactNumericListedDirectVerifierLeafOutputPublicBounds
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierVerumLeafRuleRows
open FoundationCompactNumericListedDirectVerifierVerumLeafRuleRowsCompleteness
open FoundationCompactNumericListedDirectVerifierVerumLeafStateGraph

def compactNumericVerifierVerumLeafStatePublicCoordinateSizeBound
    (stateBound proofWeight certificateWeight : Nat) : Nat :=
  compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound
    stateBound proofWeight certificateWeight

/- Every successful verum transition produces the actual verum state graph,
together with public bounds for exactly the parser, exposed root, and leaf
output coordinates that occur in that graph. -/
set_option maxHeartbeats 2400000 in
theorem
    exists_compactNumericVerifierVerumLeafStateGraph_of_success_and_transition_with_publicBounds
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      sourceTaskBoundary targetTaskBoundary sourceValueBoundary targetValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag stateBound : Nat}
    {proofTokens certificateTokens nextProof nextCertificate : List Nat}
    {sourceTasks targetTasks : List CompactNumericVerifierTask}
    {sourceValues targetValues : List CompactNumericChildResult}
    {proofNode : CompactNumericVerifierTask}
    {certificateNode : Nat × (List Nat × List Nat)}
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hstateBounds :
      CompactNumericParsePayloadSuccessSeparatedTablesStateCoordinateBounds
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish stateBound)
    (hnextValueValueBoundSize : Nat.size nextValueValueBound <= stateBound)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens = some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser certificateTokens =
      some certificateNode)
    (hproofTag : proofNode.1 = 2)
    (htransition : compactNumericNodeTransition proofNode certificateNode
      (sourceTasks.drop 1) sourceValues =
        some ((nextProof, nextCertificate), (targetTasks, targetValues)))
    (hnextProof : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextProofFinish nextProof)
    (hnextCertificate : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount nextProofFinish nextCertificateFinish nextCertificate)
    (hsourceTaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout
        stateTable stateWidth stateTokenCount sourceTaskBoundary sourceTasks)
    (htargetTaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout
        stateTable stateWidth stateTokenCount targetTaskBoundary targetTasks)
    (hsourceValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount sourceValueBoundary sourceValues)
    (htargetValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount targetValueBoundary targetValues)
    (hsourceTaskGraph : CompactNumericVerifierTaskListRowsGraph
      stateTable stateWidth stateTokenCount sourceTaskBoundary
        sourceTasks.length currentTaskTableWidth currentTaskValueBound)
    (htargetTaskGraph : CompactNumericVerifierTaskListRowsGraph
      stateTable stateWidth stateTokenCount targetTaskBoundary
        targetTasks.length currentTaskTableWidth currentTaskValueBound)
    (hsourceValueGraph : CompactNumericChildResultListRowsGraph
      stateTable stateWidth stateTokenCount sourceValueBoundary
        sourceValues.length currentValueTableWidth currentValueValueBound)
    (htargetValueGraph : CompactNumericChildResultListRowsGraph
      stateTable stateWidth stateTokenCount targetValueBoundary
        targetValues.length currentValueTableWidth currentValueValueBound)
    (hsourceTaskNonempty : 1 <= sourceTasks.length)
    (htaskTableWidth : nextTaskTableWidth = currentTaskTableWidth)
    (htaskValueBound : nextTaskValueBound = currentTaskValueBound)
    (hvalueTableWidth : nextValueTableWidth = currentValueTableWidth)
    (hvalueValueBound : nextValueValueBound = currentValueValueBound)
    (hnextStatus : nextStatusTag = 0) :
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    let publicBound :=
      compactNumericVerifierVerumLeafStatePublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
    exists proofTable proofWidth proofTokenCount proofInputStart proofInputFinish,
    exists rootStart rootFinish proofTag proofEndpointBound,
    exists certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish,
    exists axiomStart axiomFinish formulaStart formulaFinish,
    exists suffixStart suffixFinish certificateTag certificateEndpointBound,
    exists rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount rootGammaBoundarySize,
    exists targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize,
      CompactNumericVerifierVerumLeafStateGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount rootGammaBoundarySize
        sourceTaskBoundary sourceTasks.length targetTaskBoundary targetTasks.length
        sourceValueBoundary sourceValues.length targetValueBoundary targetValues.length
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStart nextProofFinish nextCertificateFinish nextStatusTag
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBool targetGammaBoundarySize
        (compactAdditiveBoolTag (compactVerumRuleCheck proofNode.2.1)) /\
      CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        publicBound /\
      CompactNumericParsePayloadSuccessExposedTaskCoordinateBounds
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize publicBound /\
      CompactNumericVerifierLeafOutputCoordinateBounds
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBool targetGammaBoundarySize
        (compactAdditiveBoolTag (compactVerumRuleCheck proofNode.2.1))
        publicBound /\
      (forall coordinate : Fin 40,
        Nat.size
          (compactNumericParsePayloadSuccessExposedSeparatedTablesGraphEnvironment
            stateTable stateWidth stateTokenCount
            stateProofStart stateProofFinish
            stateCertificateStart stateCertificateFinish
            proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
            rootStart rootFinish proofTag proofEndpointBound
            certificateTable certificateWidth certificateTokenCount
            certificateInputStart certificateInputFinish
            axiomStart axiomFinish formulaStart formulaFinish
            suffixStart suffixFinish certificateTag certificateEndpointBound
            rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
            secondFinish secondCount witnessFinish witnessCount suffixCount
            rootGammaBoundarySize coordinate) <= publicBound) /\
      forall coordinate : Fin 8,
        Nat.size
          (compactNumericVerifierParseLeafOutputEnvironment
            targetStart targetFinish targetGammaFinish targetGammaCount
            targetGammaBoundary targetBool targetGammaBoundarySize
            (compactAdditiveBoolTag (compactVerumRuleCheck proofNode.2.1))
            coordinate) <= publicBound := by
  let proofWeight := compactAdditiveValueWeight proofTokens
  let certificateWeight := compactAdditiveValueWeight certificateTokens
  let publicBound :=
    compactNumericVerifierVerumLeafStatePublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  have houtputCase :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode (sourceTasks.drop 1) sourceValues
      ((nextProof, nextCertificate), (targetTasks, targetValues))).1 htransition
  have hverumOutput :
      certificateNode.1 = 0 ∧
      ((proofNode.2.2.2.2.2, certificateNode.2.2),
        (sourceTasks.drop 1,
          (proofNode.2.1, compactVerumRuleCheck proofNode.2.1) ::
            sourceValues)) =
        ((nextProof, nextCertificate), (targetTasks, targetValues)) := by
    simpa [CompactNumericNodeTransitionOutputCase, hproofTag,
      compactNumericNodeFieldsSuffix] using houtputCase
  rcases hverumOutput with ⟨_hcertificateNodeTag, houtput⟩
  have hnextProofValue : nextProof = proofNode.2.2.2.2.2 := by
    have h := congrArg (fun output : CompactNumericRunningPayload => output.1.1)
      houtput
    simpa using h.symm
  have hnextCertificateValue : nextCertificate = certificateNode.2.2 := by
    have h := congrArg (fun output : CompactNumericRunningPayload => output.1.2)
      houtput
    simpa using h.symm
  have htasks : targetTasks = sourceTasks.drop 1 := by
    have h := congrArg (fun output : CompactNumericRunningPayload => output.2.1)
      houtput
    simpa using h.symm
  have hvalues : targetValues =
      (proofNode.2.1, compactVerumRuleCheck proofNode.2.1) :: sourceValues := by
    have h := congrArg (fun output : CompactNumericRunningPayload => output.2.2)
      houtput
    simpa using h.symm
  rcases
      exists_compactNumericVerifierLeafParseSuccessTransportGraph_of_success_and_transition_with_publicBounds
        hproofLayout hcertificateLayout hstateBounds hnextValueValueBoundSize
        hproofParser hcertificateParser htransition
        rfl rfl rfl hnextProof hnextCertificate
        hsourceTaskRows htargetTaskRows hsourceValueRows htargetValueRows
        hsourceTaskGraph htargetTaskGraph hsourceValueGraph htargetValueGraph
        hsourceTaskNonempty htasks hvalues hnextProofValue
        hnextCertificateValue htaskTableWidth htaskValueBound
        hvalueTableWidth hvalueValueBound hnextStatus with
    ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      rootGammaFinish, rootGammaCount, rootGammaBoundary, firstFinish, firstCount,
      secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
      rootGammaBoundarySize,
      targetStart, targetFinish, targetGammaFinish, targetGammaCount,
      targetGammaBoundary, targetBool, targetGammaBoundarySize,
      htransport, hparserBounds, hrootBounds, hleafBounds,
      hparserEnvironmentBounds, hleafEnvironmentBounds⟩
  have hsuccess := htransport.1
  rcases hsuccess.1.2.2.1.sound with
    ⟨decodedProofTokens, decodedRoot, hdecodedProofLayout, hdecodedRootLayout,
      hdecodedProof, hdecodedTag⟩
  have hdecodedProofTokensEq : decodedProofTokens = proofTokens :=
    hsuccess.1.1.natListValues_eq hproofLayout hdecodedProofLayout
  subst decodedProofTokens
  have hdecodedRootEq : decodedRoot = proofNode :=
    Option.some.inj (hdecodedProof.symm.trans hproofParser)
  subst decodedRoot
  have hproofTagCoord : proofTag = 2 := hdecodedTag.symm.trans hproofTag
  have htagMatch := hsuccess.1.2.2.2.2
  have hcertificateTagCoord : certificateTag = 0 := by
    rw [hproofTagCoord] at htagMatch
    simpa [CompactNumericNodeTransitionTagMatch] using htagMatch
  rcases CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
      hsuccess.2 with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag, hgammaRows, hgammaLength,
      _hfirstLayout, _hfirstLength, _hsecondLayout, _hsecondLength,
      _hwitnessLayout, _hwitnessLength, _hsuffixLayout, _hsuffixLength⟩
  have hrealizedRootEq : realizedRoot = proofNode :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hsuccess.2 hdecodedRootLayout hrealizedRoot
  subst realizedRoot
  have hverum : CompactNumericVerifierVerumLeafRuleRows
      proofTable proofWidth proofTokenCount proofTag certificateTag
      rootGammaBoundary rootGammaCount
      (compactAdditiveBoolTag (compactVerumRuleCheck proofNode.2.1)) := by
    have hraw := CompactNumericVerifierVerumLeafRuleRows.of_gammaRows hgammaRows
    simpa only [hproofTagCoord, hcertificateTagCoord, hgammaLength,
      compactNumericVerifierTaskRowCoordinatesOf] using hraw
  exact ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
    rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
    rootGammaFinish, rootGammaCount, rootGammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    rootGammaBoundarySize,
    targetStart, targetFinish, targetGammaFinish, targetGammaCount,
    targetGammaBoundary, targetBool, targetGammaBoundarySize,
    ⟨htransport, hverum⟩, hparserBounds, hrootBounds, hleafBounds,
    hparserEnvironmentBounds, hleafEnvironmentBounds⟩

#print axioms
  exists_compactNumericVerifierVerumLeafStateGraph_of_success_and_transition_with_publicBounds

end FoundationCompactNumericListedDirectVerifierVerumLeafStatePublicBounds
