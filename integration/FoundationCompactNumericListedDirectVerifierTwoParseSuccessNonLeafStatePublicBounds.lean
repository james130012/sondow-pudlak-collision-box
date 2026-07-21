import integration.FoundationCompactNumericListedDirectVerifierTwoParseSuccessNonLeafStateGraph
import integration.FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafPublicBounds

/-!
# Public bounds for the complete two-parse non-leaf state graph

The public parser constructor supplies the same exposed separated-tables graph
used by the two-parse state formula.  Its parser and exposed-root coordinates
are lifted to a common bound with the three actual scheduled task rows.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTwoParseSuccessNonLeafStatePublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierParseScheduleRows
open FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafCommonRows
open FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateCoordinates
open FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafPublicBounds
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierTaskCrossTableBridgeGraph
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierStepCases
open FoundationCompactNumericListedDirectVerifierParseScheduleRowsCompleteness
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality
open FoundationCompactNumericListedDirectVerifierTwoParseSuccessNonLeafStateGraph

private theorem twoParsePublicOutput_of_outputCase
    {proofNode : CompactNumericVerifierTask}
    {certificateNode : CompactNumericCertificateNode}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    {output : CompactNumericRunningPayload}
    (hcase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode restTasks values output)
    (htag : proofNode.1 = 3 ∨ proofNode.1 = 9) :
    certificateNode.1 = 3 ∧
      ((proofNode.2.2.2.2.2, certificateNode.2.2),
        (compactNumericParseTask :: compactNumericParseTask ::
          compactNumericCombineTask proofNode.1 proofNode.2 :: restTasks,
          values)) = output := by
  rcases proofNode with ⟨proofTag, fields⟩
  rcases certificateNode with ⟨certificateTag, certificatePayload⟩
  change proofTag = 3 ∨ proofTag = 9 at htag
  rcases htag with htag | htag <;>
    subst proofTag <;>
    simpa [CompactNumericNodeTransitionOutputCase,
      compactNumericNodeFieldsSuffix] using hcase

def compactNumericVerifierTwoParseSuccessNonLeafStatePublicCoordinateSizeBound
    (stateBound proofWeight certificateWeight : Nat) : Nat :=
  Nat.max
    (compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight)
    stateBound

/- Every concrete two-parse transition constructs the actual state graph and
returns public bounds for all parser, exposed-root, and schedule coordinates. -/
set_option maxHeartbeats 4000000 in
theorem
    exists_compactNumericVerifierTwoParseSuccessNonLeafStateGraph_of_transition_with_publicBounds
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish
      sourceTaskBoundary targetTaskBoundary
      sourceValueBoundary targetValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      stateBound : Nat}
    {proofTokens certificateTokens nextProof nextCertificate : List Nat}
    {sourceTasks targetTasks : List CompactNumericVerifierTask}
    {sourceValues targetValues : List CompactNumericChildResult}
    {proofNode : CompactNumericVerifierTask}
    {certificateNode : CompactNumericCertificateNode}
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
    (hcurrentTaskValueBound :
      Nat.size currentTaskValueBound <= stateBound)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens = some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser certificateTokens =
      some certificateNode)
    (hproofTag : proofNode.1 = 3 \/ proofNode.1 = 9)
    (htransition : compactNumericNodeTransition proofNode certificateNode
      (sourceTasks.drop 1) sourceValues =
        some ((nextProof, nextCertificate), (targetTasks, targetValues)))
    (hnextProof : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextProofFinish nextProof)
    (hnextCertificate : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        nextProofFinish nextCertificateFinish nextCertificate)
    (hsourceTaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout
        stateTable stateWidth stateTokenCount sourceTaskBoundary sourceTasks)
    (htargetTaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout
        stateTable stateWidth stateTokenCount targetTaskBoundary targetTasks)
    (hsourceTaskGraph : CompactNumericVerifierTaskListRowsGraph
      stateTable stateWidth stateTokenCount sourceTaskBoundary
        sourceTasks.length currentTaskTableWidth currentTaskValueBound)
    (htargetTaskGraph : CompactNumericVerifierTaskListRowsGraph
      stateTable stateWidth stateTokenCount targetTaskBoundary
        targetTasks.length currentTaskTableWidth currentTaskValueBound)
    (hsourceValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount sourceValueBoundary sourceValues)
    (htargetValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount targetValueBoundary targetValues)
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
      compactNumericVerifierTwoParseSuccessNonLeafStatePublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
    exists proofTable proofWidth proofTokenCount proofInputStart proofInputFinish,
    exists rootStart rootFinish proofTag proofEndpointBound,
    exists certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish,
    exists axiomStart axiomFinish formulaStart formulaFinish,
    exists suffixStart suffixFinish certificateTag certificateEndpointBound,
    exists gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize,
    exists firstParseCoordinates secondParseCoordinates combineCoordinates,
    exists firstParseSize secondParseSize combineSize,
      CompactNumericVerifierTwoParseSuccessNonLeafStateGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        gammaFinish gammaCount gammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        gammaBoundarySize
        sourceTaskBoundary sourceTasks.length targetTaskBoundary targetTasks.length
        sourceValueBoundary sourceValues.length targetValueBoundary targetValues.length
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStart nextProofFinish nextCertificateFinish nextStatusTag
        firstParseCoordinates secondParseCoordinates combineCoordinates
        firstParseSize secondParseSize combineSize /\
      CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        publicBound /\
      CompactNumericParsePayloadSuccessExposedTaskCoordinateBounds
        gammaFinish gammaCount gammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        gammaBoundarySize publicBound /\
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
            gammaFinish gammaCount gammaBoundary firstFinish firstCount
            secondFinish secondCount witnessFinish witnessCount suffixCount
            gammaBoundarySize coordinate) <= publicBound) /\
      forall coordinate : Fin 42,
        Nat.size
          (compactNumericVerifierParseNonLeafEnvironment
            firstParseCoordinates secondParseCoordinates combineCoordinates
            firstParseSize secondParseSize combineSize coordinate) <=
          publicBound := by
  let proofWeight := compactAdditiveValueWeight proofTokens
  let certificateWeight := compactAdditiveValueWeight certificateTokens
  let parserBound :=
    compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  let publicBound :=
    compactNumericVerifierTwoParseSuccessNonLeafStatePublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  have hparserBoundLe : parserBound <= publicBound := by
    dsimp only [parserBound, publicBound,
      compactNumericVerifierTwoParseSuccessNonLeafStatePublicCoordinateSizeBound]
    exact Nat.le_max_left _ _
  have htaskValueBoundPublic :
      Nat.size currentTaskValueBound <= publicBound := by
    exact hcurrentTaskValueBound.trans (by
      dsimp only [publicBound,
        compactNumericVerifierTwoParseSuccessNonLeafStatePublicCoordinateSizeBound]
      exact Nat.le_max_right _ _)
  have houtputCase :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode (sourceTasks.drop 1) sourceValues
      ((nextProof, nextCertificate), (targetTasks, targetValues))).1 htransition
  rcases twoParsePublicOutput_of_outputCase houtputCase hproofTag with
    ⟨_hcertificateNodeTag, houtput⟩
  have hnextProofValue : nextProof = proofNode.2.2.2.2.2 := by
    have h := congrArg (fun output : CompactNumericRunningPayload => output.1.1)
      houtput
    simpa using h.symm
  have hnextCertificateValue : nextCertificate = certificateNode.2.2 := by
    have h := congrArg (fun output : CompactNumericRunningPayload => output.1.2)
      houtput
    simpa using h.symm
  have htargetTasks : targetTasks = compactNumericParseTask ::
      compactNumericParseTask :: compactNumericCombineTask proofNode.1
        proofNode.2 :: sourceTasks.drop 1 := by
    have h := congrArg (fun output : CompactNumericRunningPayload => output.2.1)
      houtput
    simpa using h.symm
  have htargetValues : targetValues = sourceValues := by
    have h := congrArg (fun output : CompactNumericRunningPayload => output.2.2)
      houtput
    simpa using h.symm
  have hparsePayload : compactNumericParsePayload
      ((proofTokens, certificateTokens), (sourceTasks.drop 1, sourceValues)) =
        some ((nextProof, nextCertificate), (targetTasks, targetValues)) :=
    (compactNumericParsePayload_eq_some_iff
      ((proofTokens, certificateTokens), (sourceTasks.drop 1, sourceValues))
      ((nextProof, nextCertificate), (targetTasks, targetValues))).2
      ⟨proofNode, certificateNode, hproofParser, hcertificateParser, htransition⟩
  rcases
      exists_compactNumericParsePayloadSuccessExposedSeparatedTablesGraph_of_exists_some_with_publicBounds
        hproofLayout hcertificateLayout hstateBounds
        ⟨((nextProof, nextCertificate), (targetTasks, targetValues)),
          hparsePayload⟩ with
    ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
      secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
      gammaBoundarySize, hparseGraph, hparserBounds, htaskBounds,
      hparseEnvironmentBounds⟩
  rcases hparseGraph.realize_nonleaf_fields with
    ⟨parsedProofInput, parsedProofNode, parsedCertificateInput,
      parsedCertificateNode, proofSuffix, certificateSuffix,
      hparsedProofInput, hparsedProofNode, hparsedProofParser,
      hparsedProofNodeTag, hproofSuffix, hproofSuffixValue,
      hparsedCertificateInput, hcertificateSuffix,
      hparsedCertificateParser, hparsedCertificateNodeTag,
      hcertificateSuffixValue⟩
  have hparsedProofInputValue : parsedProofInput = proofTokens :=
    hparseGraph.1.1.natListValues_eq hproofLayout hparsedProofInput
  have hparsedCertificateInputValue : parsedCertificateInput = certificateTokens :=
    hparseGraph.1.2.1.natListValues_eq
      hcertificateLayout hparsedCertificateInput
  have hparsedProofParserState :
      compactListedProofNodeFieldsParser proofTokens = some parsedProofNode := by
    simpa only [hparsedProofInputValue] using hparsedProofParser
  have hparsedCertificateParserState :
      compactStructuralCertificateNodeParser certificateTokens =
        some parsedCertificateNode := by
    simpa only [hparsedCertificateInputValue] using hparsedCertificateParser
  have hparsedProofNodeValue : parsedProofNode = proofNode := by
    have hsome : some parsedProofNode = some proofNode :=
      hparsedProofParserState.symm.trans hproofParser
    exact Option.some.inj hsome
  have hparsedCertificateNodeValue : parsedCertificateNode = certificateNode := by
    have hsome : some parsedCertificateNode = some certificateNode :=
      hparsedCertificateParserState.symm.trans hcertificateParser
    exact Option.some.inj hsome
  subst parsedProofNode
  subst parsedCertificateNode
  have hsourceNonempty : sourceTasks ≠ [] := by
    intro hnil
    simp [hnil] at hsourceTaskNonempty
  rcases
      CompactNumericVerifierTwoParseScheduleRows.of_components_self_root
        hsourceTaskRows htargetTaskRows hsourceTaskGraph htargetTaskGraph
        hproofTag hsourceNonempty htargetTasks with
    ⟨firstParseCoordinates, secondParseCoordinates, combineCoordinates,
      firstParseSize, secondParseSize, combineSize, hscheduleRowsActualTag⟩
  have hscheduleRows : CompactNumericVerifierTwoParseScheduleRows
      stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTasks.length targetTaskBoundary targetTasks.length
      currentTaskValueBound
      combineCoordinates.start combineCoordinates.finish proofTag
      firstParseCoordinates secondParseCoordinates combineCoordinates
      firstParseSize secondParseSize combineSize := by
    simpa only [hparsedProofNodeTag] using hscheduleRowsActualTag
  have hcommonRows :=
    CompactNumericVerifierParseSuccessNonLeafCommonRows.of_components
      hproofSuffix hcertificateSuffix hnextProof hnextCertificate
      hsourceValueRows htargetValueRows hsourceValueGraph htargetValueGraph
      (hnextProofValue.trans hproofSuffixValue.symm)
      (hnextCertificateValue.trans hcertificateSuffixValue.symm)
      htargetValues htaskTableWidth htaskValueBound
      hvalueTableWidth hvalueValueBound hnextStatus
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithAllFields
        hparseGraph.2 with
    ⟨sourceRoot, hsourceRoot, hsourceRootTag,
      hsourceGamma, hsourceFirst, hsourceSecond,
      hsourceWitness, hsourceSuffix⟩
  have hsourceRootValue : sourceRoot = proofNode :=
    FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hparseGraph.2 hparsedProofNode hsourceRoot
  rcases hscheduleRows with
    ⟨_htagCases, _hreplace, _hfirstAt, _hfirstShape, _hsecondAt,
      _hsecondShape, hcombineAt, _hcombineSlices⟩
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithAllFields
        hcombineAt.core with
    ⟨targetRoot, htargetRoot, htargetRootTag,
      htargetGamma, htargetFirst, htargetSecond,
      htargetWitness, htargetSuffix⟩
  have htargetIndex : 2 < targetTasks.length := by
    rw [htargetTasks]
    simp
  rcases hcombineAt.realize_actualAtWithFields htargetIndex htargetTaskRows with
    ⟨actualTargetRoot, hactualTargetRoot, _hactualTargetRootTag,
      hactualTargetRootLayout, _hactualGammaRows, _hactualGammaLength,
      _hactualFirst, _hactualFirstLength, _hactualSecond,
      _hactualSecondLength, _hactualWitness, _hactualWitnessLength,
      _hactualSuffix, _hactualSuffixLength⟩
  have htargetRootActual : targetRoot = actualTargetRoot :=
    FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hcombineAt.core hactualTargetRootLayout htargetRoot
  have htargetAt : targetTasks.getI 2 = proofNode := by
    rw [htargetTasks]
    rfl
  have htargetRootValue : targetRoot = proofNode :=
    htargetRootActual.trans (hactualTargetRoot.trans htargetAt)
  have hsourceRootTag' : proofNode.1 = proofTag := by
    rw [← hsourceRootValue]
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using hsourceRootTag
  have htargetRootTag' : proofNode.1 = combineCoordinates.tag := by
    rw [← htargetRootValue]
    exact htargetRootTag
  have hsourceGamma' := hsourceGamma
  have hsourceFirst' := hsourceFirst
  have hsourceSecond' := hsourceSecond
  have hsourceWitness' := hsourceWitness
  have hsourceSuffix' := hsourceSuffix
  have htargetGamma' := htargetGamma
  have htargetFirst' := htargetFirst
  have htargetSecond' := htargetSecond
  have htargetWitness' := htargetWitness
  have htargetSuffix' := htargetSuffix
  rw [hsourceRootValue] at hsourceGamma' hsourceFirst' hsourceSecond'
  rw [hsourceRootValue] at hsourceWitness' hsourceSuffix'
  rw [htargetRootValue] at htargetGamma' htargetFirst' htargetSecond'
  rw [htargetRootValue] at htargetWitness' htargetSuffix'
  have hbridgeRows : CompactNumericVerifierTaskCrossTableBridgeGraph
      proofTable proofWidth proofTokenCount rootStart rootFinish proofTag
      gammaFinish firstFinish secondFinish witnessFinish
      stateTable stateWidth stateTokenCount
      combineCoordinates.start combineCoordinates.finish combineCoordinates.tag
      combineCoordinates.gammaFinish combineCoordinates.firstFinish
      combineCoordinates.secondFinish combineCoordinates.witnessFinish := by
    refine ⟨hsourceRootTag'.symm.trans htargetRootTag',
      CompactFixedWidthCrossTableSlicesEq.of_natListListLayouts
        hsourceGamma' htargetGamma',
      CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
        hsourceFirst' htargetFirst',
      CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
        hsourceSecond' htargetSecond',
      CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
        hsourceWitness' htargetWitness',
      CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
        hsourceSuffix' htargetSuffix'⟩
  have hgraph : CompactNumericVerifierTwoParseSuccessNonLeafStateGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize
      sourceTaskBoundary sourceTasks.length targetTaskBoundary targetTasks.length
      sourceValueBoundary sourceValues.length targetValueBoundary targetValues.length
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      firstParseCoordinates secondParseCoordinates combineCoordinates
      firstParseSize secondParseSize combineSize :=
    ⟨hparseGraph, hcommonRows,
      ⟨_htagCases, _hreplace, _hfirstAt, _hfirstShape, _hsecondAt,
        _hsecondShape, hcombineAt, _hcombineSlices⟩,
      hbridgeRows⟩
  have hparserBoundsPublic :
      CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        publicBound :=
    FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds.CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds.mono
      hparserBounds hparserBoundLe
  have htaskBoundsPublic :
      CompactNumericParsePayloadSuccessExposedTaskCoordinateBounds
        gammaFinish gammaCount gammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        gammaBoundarySize publicBound :=
    { gammaFinish := htaskBounds.gammaFinish.trans hparserBoundLe
      gammaCount := htaskBounds.gammaCount.trans hparserBoundLe
      gammaBoundary := htaskBounds.gammaBoundary.trans hparserBoundLe
      firstFinish := htaskBounds.firstFinish.trans hparserBoundLe
      firstCount := htaskBounds.firstCount.trans hparserBoundLe
      secondFinish := htaskBounds.secondFinish.trans hparserBoundLe
      secondCount := htaskBounds.secondCount.trans hparserBoundLe
      witnessFinish := htaskBounds.witnessFinish.trans hparserBoundLe
      witnessCount := htaskBounds.witnessCount.trans hparserBoundLe
      suffixCount := htaskBounds.suffixCount.trans hparserBoundLe
      gammaBoundarySize := htaskBounds.gammaBoundarySize.trans hparserBoundLe }
  exact ⟨proofTable, proofWidth, proofTokenCount, proofInputStart,
    proofInputFinish, rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
    gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    gammaBoundarySize, firstParseCoordinates, secondParseCoordinates,
    combineCoordinates, firstParseSize, secondParseSize, combineSize,
    hgraph, hparserBoundsPublic, htaskBoundsPublic,
    (fun coordinate =>
      (hparseEnvironmentBounds coordinate).trans hparserBoundLe),
    (fun coordinate =>
      compactNumericVerifierParseNonLeafEnvironment_size_le_of_two
        hgraph htaskValueBoundPublic coordinate)⟩

#print axioms
  exists_compactNumericVerifierTwoParseSuccessNonLeafStateGraph_of_transition_with_publicBounds

end FoundationCompactNumericListedDirectVerifierTwoParseSuccessNonLeafStatePublicBounds
