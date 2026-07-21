import integration.FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportGraph
import integration.FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierLeafOutputPublicBounds

/-!
# Public bounds for successful parsed-leaf transport

The successful parser is rebuilt with its public input-weight constructor.  Its
actual parser and exposed-task coordinates are then reused to construct the
leaf transport, whose output coordinates are controlled by the target state's
existing child-result value bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierStepCases
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportRows
open FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportExactness
open FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportGraph
open FoundationCompactNumericListedDirectVerifierLeafOutputPublicBounds
open FoundationCompactNumericListedDirectVerifierParseStateFormula

def compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound
    (stateBound proofWeight certificateWeight : Nat) : Nat :=
  compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound
    stateBound proofWeight certificateWeight

set_option maxHeartbeats 2400000 in
theorem
    exists_compactNumericVerifierLeafParseSuccessTransportGraph_of_success_and_transition_with_publicBounds
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      sourceTaskBoundary targetTaskBoundary sourceValueBoundary targetValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag stateBound : Nat}
    {proofTokens certificateTokens proofSuffix certificateSuffix nextProof nextCertificate : List Nat}
    {sourceTasks targetTasks : List CompactNumericVerifierTask}
    {sourceValues targetValues : List CompactNumericChildResult}
    {proofNode : CompactNumericVerifierTask}
    {certificateNode : Nat × (List Nat × List Nat)}
    {rootGamma : List (List Nat)} {result : Bool}
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
    (htransition : compactNumericNodeTransition proofNode certificateNode
      (sourceTasks.drop 1) sourceValues =
        some ((nextProof, nextCertificate), (targetTasks, targetValues)))
    (hrootGammaValue : rootGamma = proofNode.2.1)
    (hproofSuffixValue : proofSuffix = proofNode.2.2.2.2.2)
    (hcertificateSuffixValue : certificateSuffix = certificateNode.2.2)
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
    (htasks : targetTasks = sourceTasks.drop 1)
    (hvalues : targetValues = (rootGamma, result) :: sourceValues)
    (hnextProofValue : nextProof = proofSuffix)
    (hnextCertificateValue : nextCertificate = certificateSuffix)
    (htaskTableWidth : nextTaskTableWidth = currentTaskTableWidth)
    (htaskValueBound : nextTaskValueBound = currentTaskValueBound)
    (hvalueTableWidth : nextValueTableWidth = currentValueTableWidth)
    (hvalueValueBound : nextValueValueBound = currentValueValueBound)
    (hnextStatus : nextStatusTag = 0) :
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    let publicBound :=
      compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound
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
      CompactNumericVerifierLeafParseSuccessTransportGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize
        sourceTaskBoundary sourceTasks.length targetTaskBoundary targetTasks.length
        sourceValueBoundary sourceValues.length targetValueBoundary targetValues.length
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStart nextProofFinish nextCertificateFinish nextStatusTag
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBool targetGammaBoundarySize
        (compactAdditiveBoolTag result) /\
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
        (compactAdditiveBoolTag result) publicBound /\
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
            (compactAdditiveBoolTag result) coordinate) <= publicBound := by
  let proofWeight := compactAdditiveValueWeight proofTokens
  let certificateWeight := compactAdditiveValueWeight certificateTokens
  let publicBound :=
    compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  have hstateToBase : stateBound <=
      compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound
        stateBound proofWeight certificateWeight := by
    dsimp only [
      compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound]
    omega
  have hbaseToPublic :
      compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound
          stateBound proofWeight certificateWeight <= publicBound := by
    dsimp only [publicBound,
      compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound,
      compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound]
    omega
  have hstateToPublic : stateBound <= publicBound := by
    exact hstateToBase.trans hbaseToPublic
  have hnextValueValueBoundPublic :
      Nat.size nextValueValueBound <= publicBound :=
    hnextValueValueBoundSize.trans hstateToPublic
  have hparse : exists parsed, compactNumericParsePayload
      ((proofTokens, certificateTokens), (sourceTasks.drop 1, sourceValues)) =
        some parsed := by
    refine ⟨((nextProof, nextCertificate), (targetTasks, targetValues)), ?_⟩
    apply (compactNumericParsePayload_eq_some_iff
      ((proofTokens, certificateTokens), (sourceTasks.drop 1, sourceValues)) _).2
    exact ⟨proofNode, certificateNode, hproofParser, hcertificateParser, htransition⟩
  rcases
      exists_compactNumericParsePayloadSuccessExposedSeparatedTablesGraph_of_exists_some_with_publicBounds
        hproofLayout hcertificateLayout hstateBounds hparse with
    ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      rootGammaFinish, rootGammaCount, rootGammaBoundary, firstFinish, firstCount,
      secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
      rootGammaBoundarySize, hsuccess, hparserBounds, htaskBounds,
      hsuccessEnvironmentBounds⟩
  have hproofCross := hsuccess.1.1
  have hcertificateCross := hsuccess.1.2.1
  have hproofRoot := hsuccess.1.2.2.1
  have hcertificateRoot := hsuccess.1.2.2.2.1
  rcases hproofRoot.sound with
    ⟨parsedProofTokens, parsedProofNode, hparsedProofLayout,
      hparsedProofNodeLayout, hparsedProof, hparsedProofTag⟩
  have hproofTokensEq : parsedProofTokens = proofTokens :=
    hproofCross.natListValues_eq hproofLayout hparsedProofLayout
  subst parsedProofTokens
  have hproofNodeEq : parsedProofNode = proofNode :=
    Option.some.inj (hparsedProof.symm.trans hproofParser)
  subst parsedProofNode
  have hcoreSaved := hsuccess.2
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hcoreSaved with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag, hrootGammaRows,
      _hrootGammaLength, hfirst, _hfirstLength, hsecond, _hsecondLength,
      hwitness, _hwitnessLength, hsuffix, _hsuffixLength⟩
  have hrealizedRootEq : realizedRoot = proofNode :=
    FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hcoreSaved hparsedProofNodeLayout hrealizedRoot
  subst realizedRoot
  rcases hcoreSaved with
    ⟨htag, hrootGammaLayout, hrootGammaRows', hrootGammaSizeEq,
      hrootGammaSize, _hfirstSlice, _hsecondSlice, _hwitnessSlice,
      _hsuffixSlice⟩
  have hrootGammaLength : proofNode.2.1.length = rootGammaCount := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using
      _hrootGammaLength
  have hrootGammaStructure :
      CompactAdditiveStructuredListLayout proofTable proofWidth proofTokenCount
        (rootStart + 1) proofNode.2.1.length rootGammaFinish
        rootGammaBoundary := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf, hrootGammaLength] using
      hrootGammaLayout
  have hrootGammaSizeEq' :
      rootGammaBoundarySize = Nat.size rootGammaBoundary := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using
      hrootGammaSizeEq
  have hrootGammaSize' :
      rootGammaBoundarySize <= (rootGammaCount + 1) * proofTokenCount := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using hrootGammaSize
  have hrootGammaSizeBound : Nat.size rootGammaBoundary <=
      (proofNode.2.1.length + 1) * proofTokenCount := by
    rw [hrootGammaLength, ← hrootGammaSizeEq']
    exact hrootGammaSize'
  have hrootGammaLayoutNode : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount (rootStart + 1) rootGammaFinish
        proofNode.2.1 :=
    ⟨rootGammaBoundary, hrootGammaStructure, hrootGammaRows,
      hrootGammaSizeBound⟩
  have hrootGammaLayoutActual : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount (rootStart + 1) rootGammaFinish rootGamma := by
    simpa [hrootGammaValue] using hrootGammaLayoutNode
  have hproofSuffixLayout : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount witnessFinish rootFinish proofSuffix := by
    simpa [hproofSuffixValue, compactNumericVerifierTaskRowCoordinatesOf] using
      hsuffix
  have hcertificateSuffixLayout : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        suffixStart suffixFinish certificateSuffix := by
    rcases hcertificateRoot.sound with
      ⟨parsedCertificateTokens, parsedSuffix, hparsedCertificateLayout,
        hparsedSuffixLayout, hparsedCertificate⟩ |
      ⟨parsedCertificateTokens, _parsedAxiomTokens, parsedSuffix,
        hparsedCertificateLayout, _hparsedAxiomLayout, hparsedSuffixLayout,
        hparsedCertificate⟩
    · have hcertificateTokensEq : parsedCertificateTokens = certificateTokens :=
        hcertificateCross.natListValues_eq hcertificateLayout hparsedCertificateLayout
      subst parsedCertificateTokens
      have hcertificateNodeEq :
          (certificateTag, ([], parsedSuffix)) = certificateNode :=
        Option.some.inj (hparsedCertificate.symm.trans hcertificateParser)
      have hsuffixEq : parsedSuffix = certificateNode.2.2 := by
        simpa using congrArg (fun node => node.2.2) hcertificateNodeEq
      simpa [hcertificateSuffixValue, hsuffixEq] using hparsedSuffixLayout
    · have hcertificateTokensEq : parsedCertificateTokens = certificateTokens :=
        hcertificateCross.natListValues_eq hcertificateLayout hparsedCertificateLayout
      subst parsedCertificateTokens
      have hcertificateNodeEq :
          (certificateTag, (_parsedAxiomTokens, parsedSuffix)) = certificateNode :=
        Option.some.inj (hparsedCertificate.symm.trans hcertificateParser)
      have hsuffixEq : parsedSuffix = certificateNode.2.2 := by
        simpa using congrArg (fun node => node.2.2) hcertificateNodeEq
      simpa [hcertificateSuffixValue, hsuffixEq] using hparsedSuffixLayout
  rcases exists_compactNumericVerifierLeafParseSeparatedTablesTransportRows_of_rows
      hproofSuffixLayout hcertificateSuffixLayout hrootGammaLayoutActual
      hnextProof hnextCertificate
      hsourceTaskRows htargetTaskRows hsourceValueRows htargetValueRows
      hsourceTaskGraph htargetTaskGraph hsourceValueGraph htargetValueGraph
      hnextProofValue hnextCertificateValue
      htaskTableWidth htaskValueBound hvalueTableWidth hvalueValueBound
      hsourceTaskNonempty htasks hvalues hnextStatus with
    ⟨targetStart, targetFinish, targetGammaFinish, targetGammaCount,
      targetGammaBoundary, targetBool, targetGammaBoundarySize, htransport⟩
  have hgraph : CompactNumericVerifierLeafParseSuccessTransportGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      sourceTaskBoundary sourceTasks.length targetTaskBoundary targetTasks.length
      sourceValueBoundary sourceValues.length targetValueBoundary targetValues.length
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize
      (compactAdditiveBoolTag result) :=
    ⟨hsuccess, htransport⟩
  have hleafBounds :=
    FoundationCompactNumericListedDirectVerifierLeafOutputPublicBounds.CompactNumericVerifierLeafParseSuccessTransportGraph.leafOutputCoordinateBounds
      hgraph hnextValueValueBoundPublic
  have hleafEnvironmentBounds :=
    compactNumericVerifierParseLeafOutputEnvironment_size_le hleafBounds
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
    hgraph, hparserBounds, htaskBounds, hleafBounds,
    hsuccessEnvironmentBounds, hleafEnvironmentBounds⟩

#print axioms
  exists_compactNumericVerifierLeafParseSuccessTransportGraph_of_success_and_transition_with_publicBounds

end FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportPublicBounds
