import integration.FoundationCompactNumericListedDirectVerifierVerumLeafStateGraph
import integration.FoundationCompactNumericListedDirectVerifierClosedLeafStateGraph
import integration.FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraph
import integration.FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafParsedSemantics
import integration.FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization

/-!
# Exact parser and transition semantics for successful leaf states
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierVerumLeafStateGraph

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula

theorem CompactNumericVerifierVerumLeafStateGraph.sound_exact
    {stateTable stateWidth stateTokenCount
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
      sourceTaskBoundary targetTaskBoundary sourceValueBoundary targetValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool : Nat}
    {proofTokens certificateTokens proofSuffix certificateSuffix
      nextProof nextCertificate : List Nat}
    {sourceTasks targetTasks : List CompactNumericVerifierTask}
    {sourceValues targetValues : List CompactNumericChildResult}
    {rootGamma : List (List Nat)}
    (hgraph : CompactNumericVerifierVerumLeafStateGraph
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
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool)
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hproofSuffix : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount witnessFinish rootFinish proofSuffix)
    (hcertificateSuffix : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        suffixStart suffixFinish certificateSuffix)
    (hrootGamma : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) rootGammaFinish rootGamma)
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
    (hsourceValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount sourceValueBoundary sourceValues)
    (htargetValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount targetValueBoundary targetValues) :
    exists proofNode : CompactNumericVerifierTask,
    exists certificateNode : CompactNumericCertificateNode,
      proofNode.1 = 2 ∧
      compactListedProofNodeFieldsParser proofTokens = some proofNode ∧
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode ∧
      compactNumericNodeTransition proofNode certificateNode
        (sourceTasks.drop 1) sourceValues =
          some ((nextProof, nextCertificate), (targetTasks, targetValues)) ∧
      nextTaskTableWidth = currentTaskTableWidth ∧
      nextTaskValueBound = currentTaskValueBound ∧
      nextValueTableWidth = currentValueTableWidth ∧
      nextValueValueBound = currentValueValueBound ∧
      nextStatusTag = 0 := by
  rcases CompactNumericVerifierVerumLeafStateGraph.sound hgraph
      hproofLayout hcertificateLayout hproofSuffix hcertificateSuffix
      hrootGamma hnextProof hnextCertificate hsourceTaskRows htargetTaskRows
      hsourceValueRows htargetValueRows with
    ⟨_hresult, hproofTagTwo, hcertificateTagZero, _hparse,
      hnextProofValue, hnextCertificateValue, htargetTasksValue,
      htargetValuesValue, htaskWidth, htaskBound, hvalueWidth, hvalueBound,
      hstatus⟩
  have hparseGraph := hgraph.1.1
  rcases hparseGraph.realize_nonleaf_fields with
    ⟨proofInput, proofNode, certificateInput, certificateNode,
      parsedProofSuffix, parsedCertificateSuffix,
      hproofInput, hproofNode, hproofParser, hproofNodeTag,
      _hparsedProofSuffix, _hparsedProofSuffixValue,
      hcertificateInput, hparsedCertificateSuffix, hcertificateParser,
      hcertificateNodeTag, hcertificateSuffixNode⟩
  have hproofInputValue : proofInput = proofTokens :=
    hparseGraph.1.1.natListValues_eq hproofLayout hproofInput
  have hcertificateInputValue : certificateInput = certificateTokens :=
    hparseGraph.1.2.1.natListValues_eq
      hcertificateLayout hcertificateInput
  have hproofParserState :
      compactListedProofNodeFieldsParser proofTokens = some proofNode := by
    simpa only [hproofInputValue] using hproofParser
  have hcertificateParserState :
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode := by
    simpa only [hcertificateInputValue] using hcertificateParser
  have hproofNodeTagTwo : proofNode.1 = 2 :=
    hproofNodeTag.trans hproofTagTwo
  have hcertificateNodeTagZero : certificateNode.1 = 0 :=
    hcertificateNodeTag.trans hcertificateTagZero
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithAllFields
        hparseGraph.2 with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag, _hrealizedGamma,
      hrealizedFirst, hrealizedSecond, hrealizedWitness, _hrealizedSuffix⟩
  have hrealizedRootValue : realizedRoot = proofNode :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hparseGraph.2 hproofNode hrealizedRoot
  subst realizedRoot
  let actualRoot : CompactNumericVerifierTask :=
    (proofTag, (rootGamma,
      (proofNode.2.2.1,
        (proofNode.2.2.2.1, (proofNode.2.2.2.2.1, proofSuffix)))))
  have hactualFields : CompactNumericNodeFieldsDirectLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) rootFinish actualRoot.2 := by
    refine ⟨rootGammaFinish, firstFinish, secondFinish, witnessFinish,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [actualRoot] using hrootGamma
    · simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using
        hrealizedFirst
    · simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using
        hrealizedSecond
    · simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using
        hrealizedWitness
    · simpa [actualRoot] using hproofSuffix
  have hactualRoot : CompactNumericVerifierTaskDirectLayout
      proofTable proofWidth proofTokenCount rootStart rootFinish actualRoot :=
    ⟨rootStart + 1, by
      simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using
        hparseGraph.2.1,
      hactualFields⟩
  have hproofNodeValue : proofNode = actualRoot :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hparseGraph.2 hactualRoot hproofNode
  have hproofNodeGamma : proofNode.2.1 = rootGamma := by
    rw [hproofNodeValue]
  have hproofNodeSuffix :
      compactNumericNodeFieldsSuffix proofNode.2 = proofSuffix := by
    rw [hproofNodeValue]
    rfl
  have hparsedCertificateSuffixEq :
      parsedCertificateSuffix = certificateSuffix :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hcertificateSuffix hparsedCertificateSuffix).1
  have hcertificateNodeSuffix : certificateNode.2.2 = certificateSuffix :=
    hcertificateSuffixNode.symm.trans hparsedCertificateSuffixEq
  have houtput :
      ((compactNumericNodeFieldsSuffix proofNode.2, certificateNode.2.2),
        (sourceTasks.drop 1,
          (proofNode.2.1, compactVerumRuleCheck proofNode.2.1) ::
            sourceValues)) =
        ((nextProof, nextCertificate), (targetTasks, targetValues)) := by
    rw [hproofNodeSuffix, hcertificateNodeSuffix, hproofNodeGamma,
      hnextProofValue, hnextCertificateValue, htargetTasksValue,
      htargetValuesValue]
  have houtputCase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode (sourceTasks.drop 1) sourceValues
        ((nextProof, nextCertificate), (targetTasks, targetValues)) := by
    unfold CompactNumericNodeTransitionOutputCase
    exact Or.inr (Or.inr (Or.inl
      ⟨hproofNodeTagTwo, hcertificateNodeTagZero, houtput⟩))
  have htransition :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode (sourceTasks.drop 1) sourceValues
        ((nextProof, nextCertificate), (targetTasks, targetValues))).2
      houtputCase
  exact ⟨proofNode, certificateNode, hproofNodeTagTwo,
    hproofParserState, hcertificateParserState, htransition,
    htaskWidth, htaskBound, hvalueWidth, hvalueBound, hstatus⟩

end FoundationCompactNumericListedDirectVerifierVerumLeafStateGraph

namespace FoundationCompactNumericListedDirectVerifierClosedLeafStateGraph

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula

theorem CompactNumericVerifierClosedLeafStateGraph.sound_exact
    {stateTable stateWidth stateTokenCount
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
      sourceTaskBoundary targetTaskBoundary sourceValueBoundary targetValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound : Nat}
    {proofTokens certificateTokens proofSuffix certificateSuffix
      nextProof nextCertificate rootFormula : List Nat}
    {sourceTasks targetTasks : List CompactNumericVerifierTask}
    {sourceValues targetValues : List CompactNumericChildResult}
    {rootGamma : List (List Nat)}
    (hgraph : CompactNumericVerifierClosedLeafStateGraph
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
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound)
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hproofSuffix : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount witnessFinish rootFinish proofSuffix)
    (hcertificateSuffix : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        suffixStart suffixFinish certificateSuffix)
    (hrootGamma : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) rootGammaFinish rootGamma)
    (hrootFormula : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount
        rootGammaFinish firstFinish rootFormula)
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
    (hsourceValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount sourceValueBoundary sourceValues)
    (htargetValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount targetValueBoundary targetValues) :
    exists proofNode : CompactNumericVerifierTask,
    exists certificateNode : CompactNumericCertificateNode,
      proofNode.1 = 0 ∧
      compactListedProofNodeFieldsParser proofTokens = some proofNode ∧
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode ∧
      compactNumericNodeTransition proofNode certificateNode
        (sourceTasks.drop 1) sourceValues =
          some ((nextProof, nextCertificate), (targetTasks, targetValues)) ∧
      nextTaskTableWidth = currentTaskTableWidth ∧
      nextTaskValueBound = currentTaskValueBound ∧
      nextValueTableWidth = currentValueTableWidth ∧
      nextValueValueBound = currentValueValueBound ∧
      nextStatusTag = 0 := by
  rcases CompactNumericVerifierClosedLeafStateGraph.sound hgraph
      hproofLayout hcertificateLayout hproofSuffix hcertificateSuffix
      hrootGamma hrootFormula hnextProof hnextCertificate hsourceTaskRows
      htargetTaskRows hsourceValueRows htargetValueRows with
    ⟨_hresult, hproofTagZero, hcertificateTagZero, _hparse,
      hnextProofValue, hnextCertificateValue, htargetTasksValue,
      htargetValuesValue, htaskWidth, htaskBound, hvalueWidth, hvalueBound,
      hstatus⟩
  have hparseGraph := hgraph.1.1
  rcases hparseGraph.realize_nonleaf_fields with
    ⟨proofInput, proofNode, certificateInput, certificateNode,
      parsedProofSuffix, parsedCertificateSuffix,
      hproofInput, hproofNode, hproofParser, hproofNodeTag,
      _hparsedProofSuffix, _hparsedProofSuffixValue,
      hcertificateInput, hparsedCertificateSuffix, hcertificateParser,
      hcertificateNodeTag, hcertificateSuffixNode⟩
  have hproofInputValue : proofInput = proofTokens :=
    hparseGraph.1.1.natListValues_eq hproofLayout hproofInput
  have hcertificateInputValue : certificateInput = certificateTokens :=
    hparseGraph.1.2.1.natListValues_eq
      hcertificateLayout hcertificateInput
  have hproofParserState :
      compactListedProofNodeFieldsParser proofTokens = some proofNode := by
    simpa only [hproofInputValue] using hproofParser
  have hcertificateParserState :
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode := by
    simpa only [hcertificateInputValue] using hcertificateParser
  have hproofNodeTagZero : proofNode.1 = 0 :=
    hproofNodeTag.trans hproofTagZero
  have hcertificateNodeTagZero : certificateNode.1 = 0 :=
    hcertificateNodeTag.trans hcertificateTagZero
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithAllFields
        hparseGraph.2 with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag, _hrealizedGamma,
      _hrealizedFirst, hrealizedSecond, hrealizedWitness, _hrealizedSuffix⟩
  have hrealizedRootValue : realizedRoot = proofNode :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hparseGraph.2 hproofNode hrealizedRoot
  subst realizedRoot
  let actualRoot : CompactNumericVerifierTask :=
    (proofTag, (rootGamma,
      (rootFormula,
        (proofNode.2.2.2.1, (proofNode.2.2.2.2.1, proofSuffix)))))
  have hactualFields : CompactNumericNodeFieldsDirectLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) rootFinish actualRoot.2 := by
    refine ⟨rootGammaFinish, firstFinish, secondFinish, witnessFinish,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [actualRoot] using hrootGamma
    · simpa [actualRoot] using hrootFormula
    · simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using
        hrealizedSecond
    · simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using
        hrealizedWitness
    · simpa [actualRoot] using hproofSuffix
  have hactualRoot : CompactNumericVerifierTaskDirectLayout
      proofTable proofWidth proofTokenCount rootStart rootFinish actualRoot :=
    ⟨rootStart + 1, by
      simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using
        hparseGraph.2.1,
      hactualFields⟩
  have hproofNodeValue : proofNode = actualRoot :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hparseGraph.2 hactualRoot hproofNode
  have hproofNodeGamma : proofNode.2.1 = rootGamma := by
    rw [hproofNodeValue]
  have hproofNodeFormula : proofNode.2.2.1 = rootFormula := by
    rw [hproofNodeValue]
  have hproofNodeSuffix :
      compactNumericNodeFieldsSuffix proofNode.2 = proofSuffix := by
    rw [hproofNodeValue]
    rfl
  have hparsedCertificateSuffixEq :
      parsedCertificateSuffix = certificateSuffix :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hcertificateSuffix hparsedCertificateSuffix).1
  have hcertificateNodeSuffix : certificateNode.2.2 = certificateSuffix :=
    hcertificateSuffixNode.symm.trans hparsedCertificateSuffixEq
  have houtput :
      ((compactNumericNodeFieldsSuffix proofNode.2, certificateNode.2.2),
        (sourceTasks.drop 1,
          (proofNode.2.1,
            compactClosedRuleCheck (proofNode.2.1, proofNode.2.2.1)) ::
              sourceValues)) =
        ((nextProof, nextCertificate), (targetTasks, targetValues)) := by
    rw [hproofNodeSuffix, hcertificateNodeSuffix, hproofNodeGamma,
      hproofNodeFormula, hnextProofValue, hnextCertificateValue,
      htargetTasksValue, htargetValuesValue]
  have houtputCase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode (sourceTasks.drop 1) sourceValues
        ((nextProof, nextCertificate), (targetTasks, targetValues)) := by
    unfold CompactNumericNodeTransitionOutputCase
    exact Or.inl ⟨hproofNodeTagZero, hcertificateNodeTagZero, houtput⟩
  have htransition :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode (sourceTasks.drop 1) sourceValues
        ((nextProof, nextCertificate), (targetTasks, targetValues))).2
      houtputCase
  exact ⟨proofNode, certificateNode, hproofNodeTagZero,
    hproofParserState, hcertificateParserState, htransition,
    htaskWidth, htaskBound, hvalueWidth, hvalueBound, hstatus⟩

end FoundationCompactNumericListedDirectVerifierClosedLeafStateGraph

namespace FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraph

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
open FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafParsedSemantics

theorem CompactNumericVerifierPAAxiomLeafStateGraph.sound_exact
    {stateTable stateWidth stateTokenCount
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
      sourceTaskBoundary targetTaskBoundary sourceValueBoundary targetValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool : Nat}
    {c : CompactNumericVerifierPAAxiomJointLeafCoordinates}
    {proofTokens certificateTokens proofSuffix certificateSuffix
      nextProof nextCertificate actualCandidate actualAxiomTokens : List Nat}
    {sourceTasks targetTasks : List CompactNumericVerifierTask}
    {sourceValues targetValues : List CompactNumericChildResult}
    {actualGamma : List (List Nat)}
    (hgraph : CompactNumericVerifierPAAxiomLeafStateGraph
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
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool c)
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hproofSuffix : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount witnessFinish rootFinish proofSuffix)
    (hcertificateSuffix : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        suffixStart suffixFinish certificateSuffix)
    (hactualGamma : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) rootGammaFinish actualGamma)
    (hactualCandidate : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount
        rootGammaFinish firstFinish actualCandidate)
    (hactualAxiom : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        axiomStart axiomFinish actualAxiomTokens)
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
    (hsourceValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount sourceValueBoundary sourceValues)
    (htargetValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount targetValueBoundary targetValues) :
    exists proofNode : CompactNumericVerifierTask,
    exists certificateNode : CompactNumericCertificateNode,
      proofNode.1 = 1 ∧
      compactListedProofNodeFieldsParser proofTokens = some proofNode ∧
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode ∧
      compactNumericNodeTransition proofNode certificateNode
        (sourceTasks.drop 1) sourceValues =
          some ((nextProof, nextCertificate), (targetTasks, targetValues)) ∧
      nextTaskTableWidth = currentTaskTableWidth ∧
      nextTaskValueBound = currentTaskValueBound ∧
      nextValueTableWidth = currentValueTableWidth ∧
      nextValueValueBound = currentValueValueBound ∧
      nextStatusTag = 0 := by
  rcases CompactNumericVerifierPAAxiomLeafStateGraph.sound hgraph
      hproofLayout hcertificateLayout hproofSuffix hcertificateSuffix
      hactualGamma hactualCandidate hactualAxiom hnextProof hnextCertificate
      hsourceTaskRows htargetTaskRows hsourceValueRows htargetValueRows with
    ⟨_candidate, _certificate, _hcandidate, _hcertificate,
      hproofTagOne, _hcertificateTagOne, _hresult, _hparse,
      hnextProofValue, hnextCertificateValue, htargetTasksValue,
      htargetValuesValue, htaskWidth, htaskBound, hvalueWidth, hvalueBound,
      hstatus⟩
  have hparseGraph := hgraph.1.1
  rcases
      FoundationCompactNumericListedDirectVerifierPAAxiomLeafParsedSemantics.CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph.realize_pa_leaf_fields
        hparseGraph hproofTagOne with
    ⟨proofInput, proofNode, _parsedCandidate, _parsedCertificate,
      certificateInput, parsedAxiomTokens, parsedCertificateSuffix,
      hproofInput, hproofNode, hproofParser, hproofNodeTagOne,
      _hparsedGamma, _hparsedCandidate, _hproofNodeCandidate,
      hcertificateInput, hparsedAxiom, hparsedCertificateSuffix,
      hcertificateParser, _hparsedAxiomTokens, _hcertificateTagOne⟩
  let certificateNode : CompactNumericCertificateNode :=
    (1, (parsedAxiomTokens, parsedCertificateSuffix))
  have hproofInputValue : proofInput = proofTokens :=
    hparseGraph.1.1.natListValues_eq hproofLayout hproofInput
  have hcertificateInputValue : certificateInput = certificateTokens :=
    hparseGraph.1.2.1.natListValues_eq
      hcertificateLayout hcertificateInput
  have hproofParserState :
      compactListedProofNodeFieldsParser proofTokens = some proofNode := by
    simpa only [hproofInputValue] using hproofParser
  have hcertificateParserState :
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode := by
    simpa only [hcertificateInputValue, certificateNode] using
      hcertificateParser
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithAllFields
        hparseGraph.2 with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag, _hrealizedGamma,
      _hrealizedFirst, hrealizedSecond, hrealizedWitness, _hrealizedSuffix⟩
  have hrealizedRootValue : realizedRoot = proofNode :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hparseGraph.2 hproofNode hrealizedRoot
  subst realizedRoot
  let actualRoot : CompactNumericVerifierTask :=
    (proofTag, (actualGamma,
      (actualCandidate,
        (proofNode.2.2.2.1, (proofNode.2.2.2.2.1, proofSuffix)))))
  have hactualFields : CompactNumericNodeFieldsDirectLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) rootFinish actualRoot.2 := by
    refine ⟨rootGammaFinish, firstFinish, secondFinish, witnessFinish,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [actualRoot] using hactualGamma
    · simpa [actualRoot] using hactualCandidate
    · simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using
        hrealizedSecond
    · simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using
        hrealizedWitness
    · simpa [actualRoot] using hproofSuffix
  have hactualRoot : CompactNumericVerifierTaskDirectLayout
      proofTable proofWidth proofTokenCount rootStart rootFinish actualRoot :=
    ⟨rootStart + 1, by
      simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using
        hparseGraph.2.1,
      hactualFields⟩
  have hproofNodeValue : proofNode = actualRoot :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hparseGraph.2 hactualRoot hproofNode
  have hproofNodeGamma : proofNode.2.1 = actualGamma := by
    rw [hproofNodeValue]
  have hproofNodeCandidate : proofNode.2.2.1 = actualCandidate := by
    rw [hproofNodeValue]
  have hproofNodeSuffix :
      compactNumericNodeFieldsSuffix proofNode.2 = proofSuffix := by
    rw [hproofNodeValue]
    rfl
  have hparsedAxiomValue : parsedAxiomTokens = actualAxiomTokens :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hactualAxiom hparsedAxiom).1
  have hparsedCertificateSuffixValue :
      parsedCertificateSuffix = certificateSuffix :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hcertificateSuffix hparsedCertificateSuffix).1
  have hcertificateNodeTagOne : certificateNode.1 = 1 := by
    rfl
  have hcertificateNodeAxiom : certificateNode.2.1 = actualAxiomTokens := by
    simpa [certificateNode] using hparsedAxiomValue
  have hcertificateNodeSuffix : certificateNode.2.2 = certificateSuffix := by
    simpa [certificateNode] using hparsedCertificateSuffixValue
  have houtput :
      ((compactNumericNodeFieldsSuffix proofNode.2, certificateNode.2.2),
        (sourceTasks.drop 1,
          (proofNode.2.1,
            compactAxmRuleCheck
              (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1))) ::
                sourceValues)) =
        ((nextProof, nextCertificate), (targetTasks, targetValues)) := by
    rw [hproofNodeSuffix, hcertificateNodeSuffix, hproofNodeGamma,
      hproofNodeCandidate, hcertificateNodeAxiom, hnextProofValue,
      hnextCertificateValue, htargetTasksValue, htargetValuesValue]
  have houtputCase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode (sourceTasks.drop 1) sourceValues
        ((nextProof, nextCertificate), (targetTasks, targetValues)) := by
    unfold CompactNumericNodeTransitionOutputCase
    exact Or.inr (Or.inl
      ⟨hproofNodeTagOne, hcertificateNodeTagOne, houtput⟩)
  have htransition :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode (sourceTasks.drop 1) sourceValues
        ((nextProof, nextCertificate), (targetTasks, targetValues))).2
      houtputCase
  exact ⟨proofNode, certificateNode, hproofNodeTagOne,
    hproofParserState, hcertificateParserState, htransition,
    htaskWidth, htaskBound, hvalueWidth, hvalueBound, hstatus⟩

end FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraph

#print axioms FoundationCompactNumericListedDirectVerifierVerumLeafStateGraph.CompactNumericVerifierVerumLeafStateGraph.sound_exact
#print axioms FoundationCompactNumericListedDirectVerifierClosedLeafStateGraph.CompactNumericVerifierClosedLeafStateGraph.sound_exact
#print axioms FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraph.CompactNumericVerifierPAAxiomLeafStateGraph.sound_exact
