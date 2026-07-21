import integration.FoundationCompactNumericListedDirectVerifierOneParseSuccessNonLeafStatePublicBounds
import integration.FoundationCompactNumericListedDirectVerifierTwoParseSuccessNonLeafStatePublicBounds
import integration.FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierParseSuccessCanonicalFrameCompleteness
import integration.FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
import integration.FoundationCompactNumericListedDirectVerifierCheckedStepRow
import integration.FoundationCompactNumericListedDirectVerifierPAAxiomLeafStatePublicBounds

/-!
# Public 429-column rows for successful non-leaf parse steps

The public state construction is split by the real node-transition output:
tags 3 and 9 use two parse rows, while tags 4 through 8 use one parse row and
the canonical zero second slot.  The resulting parser, exposed-root, and
non-leaf bounds feed the complete 429-column step formula.  The final source
theorems build the canonical two-state table and a checked-row wrapper.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTypedNonLeafStepPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierParseStateFrameRows
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierParseStateCompleteness
open FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateGraph
open FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateCoordinates
open FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafPublicBounds
open FoundationCompactNumericListedDirectVerifierOneParseSuccessNonLeafStateGraph
open FoundationCompactNumericListedDirectVerifierOneParseSuccessNonLeafStatePublicBounds
open FoundationCompactNumericListedDirectVerifierTwoParseSuccessNonLeafStateGraph
open FoundationCompactNumericListedDirectVerifierTwoParseSuccessNonLeafStatePublicBounds
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessStepPublicBounds
open FoundationCompactNumericListedDirectVerifierParseSuccessCanonicalFrameCompleteness
open FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafStatePublicBounds

def compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound
    (stateBound proofWeight certificateWeight : Nat) : Nat :=
  compactNumericVerifierTwoParseSuccessNonLeafStatePublicCoordinateSizeBound
    stateBound proofWeight certificateWeight

set_option maxHeartbeats 6000000 in
theorem
    exists_compactNumericVerifierParseSuccessNonLeafStateGraph_of_transition_with_publicBounds
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
    (hcurrentTaskValueBound : Nat.size currentTaskValueBound <= stateBound)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens = some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser certificateTokens =
      some certificateNode)
    (hproofTag : proofNode.1 = 3 \/ proofNode.1 = 4 \/ proofNode.1 = 5 \/
      proofNode.1 = 6 \/ proofNode.1 = 7 \/ proofNode.1 = 8 \/
      proofNode.1 = 9)
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
      compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound
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
      CompactNumericVerifierParseSuccessNonLeafStateGraph
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
    compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  have hparserToPublic : parserBound <= publicBound := by
    dsimp only [parserBound, publicBound,
      compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound,
      compactNumericVerifierTwoParseSuccessNonLeafStatePublicCoordinateSizeBound]
    exact Nat.le_max_left _ _
  have hstateToPublic : stateBound <= publicBound := by
    dsimp only [publicBound,
      compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound,
      compactNumericVerifierTwoParseSuccessNonLeafStatePublicCoordinateSizeBound]
    exact Nat.le_max_right _ _
  have htaskValuePublic : Nat.size currentTaskValueBound <= publicBound :=
    hcurrentTaskValueBound.trans hstateToPublic
  by_cases htwo : proofNode.1 = 3 \/ proofNode.1 = 9
  · rcases
        exists_compactNumericVerifierTwoParseSuccessNonLeafStateGraph_of_transition_with_publicBounds
          hproofLayout hcertificateLayout hstateBounds hcurrentTaskValueBound
          hproofParser hcertificateParser htwo htransition
          hnextProof hnextCertificate hsourceTaskRows htargetTaskRows
          hsourceTaskGraph htargetTaskGraph hsourceValueRows htargetValueRows
          hsourceValueGraph htargetValueGraph hsourceTaskNonempty
          htaskTableWidth htaskValueBound hvalueTableWidth hvalueValueBound
          hnextStatus with
      ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
        rootStart, rootFinish, proofTag, proofEndpointBound,
        certificateTable, certificateWidth, certificateTokenCount,
        certificateInputStart, certificateInputFinish,
        axiomStart, axiomFinish, formulaStart, formulaFinish,
        suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
        gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
        secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
        gammaBoundarySize,
        firstParseCoordinates, secondParseCoordinates, combineCoordinates,
        firstParseSize, secondParseSize, combineSize,
        hgraph, hparserBounds, hrootBounds,
        _hparserEnvironmentBounds, _hnonLeafBounds⟩
    have hnonLeafBounds : forall coordinate : Fin 42,
        Nat.size
          (compactNumericVerifierParseNonLeafEnvironment
            firstParseCoordinates secondParseCoordinates combineCoordinates
            firstParseSize secondParseSize combineSize coordinate) <=
          publicBound := by
      exact compactNumericVerifierParseNonLeafEnvironment_size_le_of_two
        hgraph htaskValuePublic
    exact ⟨proofTable, proofWidth, proofTokenCount, proofInputStart,
      proofInputFinish, rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
      secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
      gammaBoundarySize,
      firstParseCoordinates, secondParseCoordinates, combineCoordinates,
      firstParseSize, secondParseSize, combineSize,
      Or.inr hgraph, hparserBounds, hrootBounds, hnonLeafBounds⟩
  · have hone : proofNode.1 = 4 \/ proofNode.1 = 5 \/ proofNode.1 = 6 \/
        proofNode.1 = 7 \/ proofNode.1 = 8 := by
      rcases hproofTag with hthree | hfour | hfive | hsix | hseven | height | hnine
      · exact False.elim (htwo (Or.inl hthree))
      · exact Or.inl hfour
      · exact Or.inr (Or.inl hfive)
      · exact Or.inr (Or.inr (Or.inl hsix))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hseven)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr height)))
      · exact False.elim (htwo (Or.inr hnine))
    rcases
        exists_compactNumericVerifierOneParseSuccessNonLeafStateGraph_of_transition_with_publicBounds
          hproofLayout hcertificateLayout hstateBounds hcurrentTaskValueBound
          hproofParser hcertificateParser hone htransition
          hnextProof hnextCertificate hsourceTaskRows htargetTaskRows
          hsourceTaskGraph htargetTaskGraph hsourceValueRows htargetValueRows
          hsourceValueGraph htargetValueGraph hsourceTaskNonempty
          htaskTableWidth htaskValueBound hvalueTableWidth hvalueValueBound
          hnextStatus with
      ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
        rootStart, rootFinish, proofTag, proofEndpointBound,
        certificateTable, certificateWidth, certificateTokenCount,
        certificateInputStart, certificateInputFinish,
        axiomStart, axiomFinish, formulaStart, formulaFinish,
        suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
        gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
        secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
        gammaBoundarySize, parseCoordinates, combineCoordinates,
        parseSize, combineSize, hgraph, hparserBounds, hrootBounds,
        _hparserEnvironmentBounds, _hparseBounds, _hcombineBounds⟩
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
        hparserBounds hparserToPublic
    have hrootBoundsPublic :
        CompactNumericParsePayloadSuccessExposedTaskCoordinateBounds
          gammaFinish gammaCount gammaBoundary firstFinish firstCount
          secondFinish secondCount witnessFinish witnessCount suffixCount
          gammaBoundarySize publicBound :=
      { gammaFinish := hrootBounds.gammaFinish.trans hparserToPublic
        gammaCount := hrootBounds.gammaCount.trans hparserToPublic
        gammaBoundary := hrootBounds.gammaBoundary.trans hparserToPublic
        firstFinish := hrootBounds.firstFinish.trans hparserToPublic
        firstCount := hrootBounds.firstCount.trans hparserToPublic
        secondFinish := hrootBounds.secondFinish.trans hparserToPublic
        secondCount := hrootBounds.secondCount.trans hparserToPublic
        witnessFinish := hrootBounds.witnessFinish.trans hparserToPublic
        witnessCount := hrootBounds.witnessCount.trans hparserToPublic
        suffixCount := hrootBounds.suffixCount.trans hparserToPublic
        gammaBoundarySize := hrootBounds.gammaBoundarySize.trans hparserToPublic }
    have hsecondBounds : forall coordinate : Fin 14,
        Nat.size
          (compactNumericVerifierTaskScheduleEnvironment
            compactNumericVerifierParseUnusedTaskCoordinates
            compactNumericVerifierParseUnusedTaskSize coordinate) <=
          publicBound :=
      compactNumericVerifierUnusedTaskScheduleEnvironment_size_le publicBound
    have hnonLeafBounds : forall coordinate : Fin 42,
        Nat.size
          (compactNumericVerifierParseNonLeafEnvironment
            parseCoordinates compactNumericVerifierParseUnusedTaskCoordinates
            combineCoordinates parseSize compactNumericVerifierParseUnusedTaskSize
            combineSize coordinate) <= publicBound := by
      exact compactNumericVerifierParseNonLeafEnvironment_size_le_of_one
        hgraph htaskValuePublic hsecondBounds
    exact ⟨proofTable, proofWidth, proofTokenCount, proofInputStart,
      proofInputFinish, rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
      secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
      gammaBoundarySize,
      parseCoordinates, compactNumericVerifierParseUnusedTaskCoordinates,
      combineCoordinates, parseSize, compactNumericVerifierParseUnusedTaskSize,
      combineSize, Or.inl hgraph, hparserBoundsPublic, hrootBoundsPublic,
      hnonLeafBounds⟩

#print axioms
  exists_compactNumericVerifierParseSuccessNonLeafStateGraph_of_transition_with_publicBounds

set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierNonLeafStepFormulaWitness_with_publicBounds
    {stateTable stateWidth stateTokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {currentTask : CompactNumericVerifierTask}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    {nextProofTokens nextCertificateTokens : List Nat}
    {nextTasks : List CompactNumericVerifierTask}
    {nextValues : List CompactNumericChildResult}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {proofNode : CompactNumericVerifierTask}
    {certificateNode : CompactNumericCertificateNode}
    (hframePackage : CompactNumericVerifierParseSuccessCanonicalFramePackage
      stateTable stateWidth stateTokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens currentTask restTasks
      values nextProofTokens nextCertificateTokens nextTasks nextValues
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness)
    (hstateTable : Nat.size stateTable <=
      compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser
      certificateTokens = some certificateNode)
    (hproofTag : proofNode.1 = 3 \/ proofNode.1 = 4 \/ proofNode.1 = 5 \/
      proofNode.1 = 6 \/ proofNode.1 = 7 \/ proofNode.1 = 8 \/
      proofNode.1 = 9)
    (htransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, nextValues))) :
    let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
      stateWidth stateTokenCount
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    let blockBound :=
      compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
    exists witness : CompactNumericVerifierStepFormulaWitness
        stateTable stateWidth stateTokenCount
        currentStart currentFinish nextStart nextFinish,
      (forall coordinate : Fin 429,
          Nat.size (witness.environment coordinate) <=
            compactNumericVerifierParseSuccessStepCoordinateSizeBound
              stateWidth stateTokenCount blockBound) /\
        CompactNumericVerifierParseSuccessParserControlBounds
          witness.environment blockBound := by
  let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
    stateWidth stateTokenCount
  let proofWeight := compactAdditiveValueWeight proofTokens
  let certificateWeight := compactAdditiveValueWeight certificateTokens
  let blockBound :=
    compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  rcases hframePackage with
    ⟨hcurrentPackage, hnextPackage, hhead, hframe⟩
  have hcurrentPackageSaved := hcurrentPackage
  have hnextPackageSaved := hnextPackage
  have hcurrentBounds :=
    CompactNumericVerifierStateCanonicalCorePackage.coordinateSizeBounds
      hcurrentPackageSaved
  rcases hcurrentPackage with
    ⟨_hcurrentStart, _hcurrentFinish,
      hcurrentProof, hcurrentCertificate,
      _hcurrentTaskLayout, hcurrentTaskRows,
      _hcurrentValueLayout, hcurrentValueRows,
      hcurrentTaskCount, hcurrentValueCount,
      hcurrentTaskTableWidth, hcurrentTaskValueBound,
      hcurrentValueTableWidth, hcurrentValueValueBound,
      _hcurrentStatus, hcurrentCore⟩
  rcases hnextPackage with
    ⟨_hnextStart, _hnextFinish,
      hnextProof, hnextCertificate,
      _hnextTaskLayout, hnextTaskRows,
      _hnextValueLayout, hnextValueRows,
      hnextTaskCount, hnextValueCount,
      hnextTaskTableWidth, hnextTaskValueBound,
      hnextValueTableWidth, hnextValueValueBound,
      _hnextStatus, hnextCore⟩
  have hcurrentCoreSaved := hcurrentCore
  have hnextCoreSaved := hnextCore
  rcases hcurrentCore with
    ⟨_hcurrentProofSlice, _hcurrentCertificateSlice,
      _hcurrentTaskStructure, hcurrentTaskGraph,
      _hcurrentTaskBoundarySizeEq, _hcurrentTaskBoundarySize,
      _hcurrentValueStructure, hcurrentValueGraph,
      _hcurrentValueBoundarySizeEq, _hcurrentValueBoundarySize,
      _hcurrentOption, _hcurrentCoreStatus⟩
  rcases hnextCore with
    ⟨_hnextProofSlice, _hnextCertificateSlice,
      _hnextTaskStructure, hnextTaskGraph,
      _hnextTaskBoundarySizeEq, _hnextTaskBoundarySize,
      _hnextValueStructure, hnextValueGraph,
      _hnextValueBoundarySizeEq, _hnextValueBoundarySize,
      _hnextOption, _hnextCoreStatus⟩
  have hstateWidth : Nat.size stateWidth <= stateBound := by
    exact natSize_le_of_le
      (width_le_stateCoreCoordinateSizeBound stateWidth stateTokenCount)
  have hstateTokenCount : Nat.size stateTokenCount <= stateBound := by
    exact natSize_le_of_le
      (tokenCount_le_stateCoreCoordinateSizeBound stateWidth stateTokenCount)
  have hstateBounds :
      CompactNumericParsePayloadSuccessSeparatedTablesStateCoordinateBounds
        stateTable stateWidth stateTokenCount
        currentCoordinates.start currentCoordinates.proofFinish
        currentCoordinates.proofFinish currentCoordinates.certificateFinish
        stateBound :=
    ⟨hstateTable, hstateWidth, hstateTokenCount,
      hcurrentBounds.start, hcurrentBounds.proofFinish,
      hcurrentBounds.proofFinish, hcurrentBounds.certificateFinish⟩
  have hsourceTaskGraph : CompactNumericVerifierTaskListRowsGraph
      stateTable stateWidth stateTokenCount currentCoordinates.taskBoundary
      (currentTask :: restTasks).length
      currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound := by
    simpa only [hcurrentTaskCount] using hcurrentTaskGraph
  have htargetTaskGraphNext : CompactNumericVerifierTaskListRowsGraph
      stateTable stateWidth stateTokenCount nextCoordinates.taskBoundary
      nextTasks.length nextSizeWitness.taskTableWidth
      nextSizeWitness.taskValueBound := by
    simpa only [hnextTaskCount] using hnextTaskGraph
  have hsourceValueGraph : CompactNumericChildResultListRowsGraph
      stateTable stateWidth stateTokenCount currentCoordinates.valueBoundary
      values.length currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hcurrentValueCount] using hcurrentValueGraph
  have htargetValueGraphNext : CompactNumericChildResultListRowsGraph
      stateTable stateWidth stateTokenCount nextCoordinates.valueBoundary
      nextValues.length nextSizeWitness.valueTableWidth
      nextSizeWitness.valueValueBound := by
    simpa only [hnextValueCount] using hnextValueGraph
  have htaskTableWidth : nextSizeWitness.taskTableWidth =
      currentSizeWitness.taskTableWidth :=
    hnextTaskTableWidth.trans hcurrentTaskTableWidth.symm
  have htaskValueBound : nextSizeWitness.taskValueBound =
      currentSizeWitness.taskValueBound :=
    hnextTaskValueBound.trans hcurrentTaskValueBound.symm
  have hvalueTableWidth : nextSizeWitness.valueTableWidth =
      currentSizeWitness.valueTableWidth :=
    hnextValueTableWidth.trans hcurrentValueTableWidth.symm
  have hvalueValueBound : nextSizeWitness.valueValueBound =
      currentSizeWitness.valueValueBound :=
    hnextValueValueBound.trans hcurrentValueValueBound.symm
  have htargetTaskGraph : CompactNumericVerifierTaskListRowsGraph
      stateTable stateWidth stateTokenCount nextCoordinates.taskBoundary
      nextTasks.length currentSizeWitness.taskTableWidth
      currentSizeWitness.taskValueBound := by
    simpa only [htaskTableWidth, htaskValueBound] using htargetTaskGraphNext
  have htargetValueGraph : CompactNumericChildResultListRowsGraph
      stateTable stateWidth stateTokenCount nextCoordinates.valueBoundary
      nextValues.length currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hvalueTableWidth, hvalueValueBound] using htargetValueGraphNext
  have hsourceTaskNonempty : 1 <= (currentTask :: restTasks).length := by
    simp
  have hnextStatus : nextCoordinates.statusTag = 0 :=
    hnextPackageSaved.statusTag_eq_zero rfl
  have htransitionFull : compactNumericNodeTransition proofNode certificateNode
      ((currentTask :: restTasks).drop 1) values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, nextValues)) := by
    simpa using htransition
  rcases
      exists_compactNumericVerifierParseSuccessNonLeafStateGraph_of_transition_with_publicBounds
        hcurrentProof hcurrentCertificate hstateBounds
        hcurrentBounds.taskValueBound hproofParser hcertificateParser
        hproofTag htransitionFull hnextProof hnextCertificate
        hcurrentTaskRows hnextTaskRows hsourceTaskGraph htargetTaskGraph
        hcurrentValueRows hnextValueRows hsourceValueGraph htargetValueGraph
        hsourceTaskNonempty htaskTableWidth htaskValueBound
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
      firstParseCoordinates, secondParseCoordinates, combineCoordinates,
      firstParseSize, secondParseSize, combineSize,
      hnonLeafGraph, hparserBounds, hrootBounds, hnonLeafBounds⟩
  let arguments : CompactNumericVerifierStepArguments :=
    { compactNumericVerifierStepUnusedArguments with
      taskCoordinates := taskCoordinates
      taskSizeWitness := taskSizeWitness
      proofTable := proofTable
      proofWidth := proofWidth
      proofTokenCount := proofTokenCount
      proofInputStart := proofInputStart
      proofInputFinish := proofInputFinish
      rootStart := rootStart
      rootFinish := rootFinish
      proofTag := proofTag
      proofEndpointBound := proofEndpointBound
      certificateTable := certificateTable
      certificateWidth := certificateWidth
      certificateTokenCount := certificateTokenCount
      certificateInputStart := certificateInputStart
      certificateInputFinish := certificateInputFinish
      axiomStart := axiomStart
      axiomFinish := axiomFinish
      formulaStart := formulaStart
      formulaFinish := formulaFinish
      suffixStart := suffixStart
      suffixFinish := suffixFinish
      certificateTag := certificateTag
      certificateEndpointBound := certificateEndpointBound
      rootGammaFinish := rootGammaFinish
      rootGammaCount := rootGammaCount
      rootGammaBoundary := rootGammaBoundary
      firstFinish := firstFinish
      firstCount := firstCount
      secondFinish := secondFinish
      secondCount := secondCount
      witnessFinish := witnessFinish
      witnessCount := witnessCount
      suffixCount := suffixCount
      rootGammaBoundarySize := rootGammaBoundarySize
      firstParseCoordinates := firstParseCoordinates
      secondParseCoordinates := secondParseCoordinates
      combineCoordinates := combineCoordinates
      firstParseSize := firstParseSize
      secondParseSize := secondParseSize
      combineSize := combineSize }
  have hnonLeafGraphCoordinateCounts := hnonLeafGraph
  rw [← hcurrentTaskCount, ← hnextTaskCount,
    ← hcurrentValueCount, ← hnextValueCount] at hnonLeafGraphCoordinateCounts
  have hparseSuccess : CompactNumericVerifierParseSuccessStateGraph
      stateTable stateWidth stateTokenCount currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0
      compactNumericVerifierParseUnusedPACoordinates
      firstParseCoordinates secondParseCoordinates combineCoordinates
      firstParseSize secondParseSize combineSize :=
    ⟨hcurrentCoreSaved, hnextCoreSaved, hhead, hframe,
      Or.inr (Or.inr (Or.inr hnonLeafGraphCoordinateCounts))⟩
  have hparseGraph : CompactNumericVerifierParseStateGraph
      stateTable stateWidth stateTokenCount currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0
      compactNumericVerifierParseUnusedPACoordinates
      firstParseCoordinates secondParseCoordinates combineCoordinates
      firstParseSize secondParseSize combineSize :=
    Or.inr hparseSuccess
  have hargumentsGraph : arguments.Graph
      stateTable stateWidth stateTokenCount currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness := by
    dsimp only [CompactNumericVerifierStepArguments.Graph, arguments]
    exact Or.inr (Or.inr (Or.inl hparseGraph))
  have hstateToBlock : stateBound <= blockBound := by
    dsimp only [blockBound,
      compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound,
      compactNumericVerifierTwoParseSuccessNonLeafStatePublicCoordinateSizeBound]
    exact Nat.le_max_right _ _
  have hvalueBound : Nat.size currentSizeWitness.taskValueBound <= blockBound :=
    hcurrentBounds.taskValueBound.trans hstateToBlock
  have hblocks : CompactNumericVerifierParseSuccessArgumentBlockBounds
      arguments blockBound := by
    refine
      { parser := ?_
        parsedRoot := ?_
        leafOutput := ?_
        closedExtra := ?_
        pa := ?_
        nonLeaf := ?_ }
    · simpa only [arguments] using hparserBounds
    · simpa only [arguments] using hrootBounds
    · intro coordinate
      simpa [arguments, compactNumericVerifierStepUnusedArguments] using
        compactNumericVerifierUnusedLeafOutputEnvironment_size_le
          blockBound coordinate
    · intro coordinate
      simpa [arguments, compactNumericVerifierStepUnusedArguments] using
        compactNumericVerifierUnusedClosedExtraEnvironment_size_le
          blockBound coordinate
    · intro coordinate
      simpa [arguments, compactNumericVerifierStepUnusedArguments,
        compactNumericVerifierParseUnusedPACoordinates] using
        compactNumericVerifierParseUnusedPACoordinates_size_le
          blockBound coordinate
    · simpa only [arguments] using hnonLeafBounds
  exact
    exists_compactNumericVerifierParseSuccessStepFormulaWitness_with_publicSizeBound
      arguments hstateTable hcurrentPackageSaved hnextPackageSaved
      hargumentsGraph hhead hvalueBound hblocks

#print axioms
  exists_compactNumericVerifierNonLeafStepFormulaWitness_with_publicBounds

set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierNonLeafStepFormulaWitness_of_outputCase_with_sourcePublicBounds
    (proofTokens certificateTokens nextProofTokens nextCertificateTokens : List Nat)
    (restTasks nextTasks : List CompactNumericVerifierTask)
    (values nextValues : List CompactNumericChildResult)
    (proofNode : CompactNumericVerifierTask)
    (certificateNode : CompactNumericCertificateNode)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser
      certificateTokens = some certificateNode)
    (hproofTag : proofNode.1 = 3 \/ proofNode.1 = 4 \/ proofNode.1 = 5 \/
      proofNode.1 = 6 \/ proofNode.1 = 7 \/ proofNode.1 = 8 \/
      proofNode.1 = 9)
    (houtputCase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens), (nextTasks, nextValues))) :
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((nextProofTokens, nextCertificateTokens),
        (nextTasks, nextValues)), none)
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let tokens := currentTokens ++ nextTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let stateTable := compactFixedWidthTableCode width tokens
    let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
      width tokens.length
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    let blockBound :=
      compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
    exists witness : CompactNumericVerifierStepFormulaWitness
        stateTable width tokens.length
        0 currentTokens.length currentTokens.length
        (currentTokens.length + nextTokens.length),
      (forall coordinate : Fin 429,
          Nat.size (witness.environment coordinate) <=
            compactNumericVerifierParseSuccessStepCoordinateSizeBound
              width tokens.length blockBound) /\
        CompactNumericVerifierParseSuccessParserControlBounds
          witness.environment blockBound := by
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens),
      (compactNumericParseTask :: restTasks, values)), none)
  let nextState : CompactNumericVerifierState :=
    (((nextProofTokens, nextCertificateTokens),
      (nextTasks, nextValues)), none)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let stateTable := compactFixedWidthTableCode width tokens
  let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
    width tokens.length
  let proofWeight := compactAdditiveValueWeight proofTokens
  let certificateWeight := compactAdditiveValueWeight certificateTokens
  let blockBound :=
    compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  have hpairRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState []
  have hpair :
      CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length 0 currentTokens.length currentState /\
        CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length currentTokens.length
            (currentTokens.length + nextTokens.length) nextState := by
    simpa only [stateTable, width, tokens, currentTokens, nextTokens,
      List.append_nil] using hpairRaw
  rcases hpair with ⟨hcurrentLayout, hnextLayout⟩
  rcases
      CompactNumericVerifierParseSuccessCanonicalFramePackage.exists_of_layouts
        hcurrentLayout hnextLayout (by rfl) with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, hframePackage⟩
  have hstateTable : Nat.size stateTable <= stateBound := by
    exact (compactFixedWidthTableCode_size_le width tokens).trans
      (tokenTableArea_le_stateCoreCoordinateSizeBound width tokens.length)
  have htransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, nextValues)) :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens),
          (nextTasks, nextValues))).2 houtputCase
  exact
    exists_compactNumericVerifierNonLeafStepFormulaWitness_with_publicBounds
      hframePackage hstateTable hproofParser hcertificateParser
      hproofTag htransition

#print axioms
  exists_compactNumericVerifierNonLeafStepFormulaWitness_of_outputCase_with_sourcePublicBounds

set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_sourcePublicBounds
    (proofTokens certificateTokens nextProofTokens nextCertificateTokens : List Nat)
    (restTasks nextTasks : List CompactNumericVerifierTask)
    (values nextValues : List CompactNumericChildResult)
    (proofNode : CompactNumericVerifierTask)
    (certificateNode : CompactNumericCertificateNode)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser
      certificateTokens = some certificateNode)
    (hproofTag : proofNode.1 = 3 \/ proofNode.1 = 4 \/ proofNode.1 = 5 \/
      proofNode.1 = 6 \/ proofNode.1 = 7 \/ proofNode.1 = 8 \/
      proofNode.1 = 9)
    (houtputCase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens), (nextTasks, nextValues))) :
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((nextProofTokens, nextCertificateTokens),
        (nextTasks, nextValues)), none)
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let tokens := currentTokens ++ nextTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let stateTable := compactFixedWidthTableCode width tokens
    let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
      width tokens.length
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    let blockBound :=
      compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
    let coordinateBound :=
      compactNumericVerifierParseSuccessStepCoordinateSizeBound
        width tokens.length blockBound
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = currentState /\
        row.nextState = nextState /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <= coordinateBound := by
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens),
      (compactNumericParseTask :: restTasks, values)), none)
  let nextState : CompactNumericVerifierState :=
    (((nextProofTokens, nextCertificateTokens),
      (nextTasks, nextValues)), none)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let stateTable := compactFixedWidthTableCode width tokens
  let stateBound := compactNumericVerifierStateCoreCoordinateSizeBound
    width tokens.length
  let proofWeight := compactAdditiveValueWeight proofTokens
  let certificateWeight := compactAdditiveValueWeight certificateTokens
  let blockBound :=
    compactNumericVerifierParseSuccessNonLeafStatePublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  let coordinateBound :=
    compactNumericVerifierParseSuccessStepCoordinateSizeBound
      width tokens.length blockBound
  rcases
      exists_compactNumericVerifierNonLeafStepFormulaWitness_of_outputCase_with_sourcePublicBounds
        proofTokens certificateTokens nextProofTokens nextCertificateTokens
        restTasks nextTasks values nextValues proofNode certificateNode
        hproofParser hcertificateParser hproofTag houtputCase with
    ⟨witness, hwitness, _hparserControls⟩
  have hpairRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState []
  have hpair :
      CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length 0 currentTokens.length currentState /\
        CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length currentTokens.length
            (currentTokens.length + nextTokens.length) nextState := by
    simpa only [stateTable, width, tokens, currentTokens, nextTokens,
      List.append_nil] using hpairRaw
  rcases hpair with ⟨hcurrentLayout, hnextLayout⟩
  let row :=
    FoundationCompactNumericListedDirectVerifierCheckedStepRow.CompactNumericVerifierStepFormulaWitness.toCheckedStepRow
      witness currentState nextState hcurrentLayout hnextLayout
  exact ⟨row, rfl, rfl, fun coordinate => hwitness coordinate⟩

#print axioms
  exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_sourcePublicBounds

end FoundationCompactNumericListedDirectVerifierTypedNonLeafStepPublicBounds
