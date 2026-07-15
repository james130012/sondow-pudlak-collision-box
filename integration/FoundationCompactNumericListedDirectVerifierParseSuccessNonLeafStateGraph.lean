import integration.FoundationCompactNumericListedDirectVerifierOneParseSuccessNonLeafStateGraph
import integration.FoundationCompactNumericListedDirectVerifierTwoParseSuccessNonLeafStateGraph

/-!
# Complete parse-success non-leaf state graph

The aggregate graph covers every non-leaf successful parser tag.  Tags 4--8
use the one-parse schedule; tags 3 and 9 use the two-parse schedule.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateGraph

open FoundationCompactNumericListedDirectVerifierOneParseSuccessNonLeafStateGraph
open FoundationCompactNumericListedDirectVerifierTwoParseSuccessNonLeafStateGraph
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula

variable
  (stateTable stateWidth stateTokenCount
    stateProofStart stateProofFinish stateCertificateStart
      stateCertificateFinish
    proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
    rootStart rootFinish proofTag proofEndpointBound
    certificateTable certificateWidth certificateTokenCount
    certificateInputStart certificateInputFinish
    axiomStart axiomFinish formulaStart formulaFinish
    suffixStart suffixFinish certificateTag certificateEndpointBound
    gammaFinish gammaCount gammaBoundary firstFinish firstCount
    secondFinish secondCount witnessFinish witnessCount suffixCount
    gammaBoundarySize
    sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
    sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
    currentTaskTableWidth currentTaskValueBound
    currentValueTableWidth currentValueValueBound
    nextTaskTableWidth nextTaskValueBound
    nextValueTableWidth nextValueValueBound
    nextStart nextProofFinish nextCertificateFinish nextStatusTag : Nat)
  (firstParseCoordinates secondParseCoordinates combineCoordinates :
    CompactNumericVerifierTaskRowCoordinates)
  (firstParseSize secondParseSize combineSize :
    CompactNumericVerifierTaskSizeWitness)

def CompactNumericVerifierParseSuccessNonLeafStateGraph : Prop :=
  CompactNumericVerifierOneParseSuccessNonLeafStateGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      firstParseCoordinates combineCoordinates firstParseSize combineSize ∨
  CompactNumericVerifierTwoParseSuccessNonLeafStateGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      firstParseCoordinates secondParseCoordinates combineCoordinates
      firstParseSize secondParseSize combineSize

def compactNumericVerifierParseSuccessNonLeafStateGraphDef :
    𝚺₀.Semisentence 102 := .mkSigma
  ((compactNumericVerifierOneParseSuccessNonLeafStateGraphDef.val ⇜
      ![(#0 : Semiterm ℒₒᵣ Empty 102), #1, #2, #3, #4, #5, #6, #7,
        #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18, #19,
        #20, #21, #22, #23, #24, #25, #26, #27, #28, #29, #30, #31,
        #32, #33, #34, #35, #36, #37, #38, #39, #40, #41, #42, #43,
        #44, #45, #46, #47, #48, #49, #50, #51, #52, #53, #54, #55,
        #56, #57, #58, #59, #60, #61, #62, #63, #64, #65, #66, #67,
        #68, #69, #70, #71, #72, #73, #88, #89, #90, #91, #92, #93,
        #94, #95, #96, #97, #98, #99, #100, #101]) ⋎
    (compactNumericVerifierTwoParseSuccessNonLeafStateGraphDef.val ⇜
      (fun index : Fin 102 =>
        (#index : Semiterm ℒₒᵣ Empty 102)))) (by simp)

def compactNumericVerifierParseSuccessNonLeafStateGraphEnvironment :
    Fin 102 -> Nat :=
  compactNumericVerifierTwoParseSuccessNonLeafStateGraphEnvironment
    stateTable stateWidth stateTokenCount
    stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
    proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
    rootStart rootFinish proofTag proofEndpointBound
    certificateTable certificateWidth certificateTokenCount
    certificateInputStart certificateInputFinish
    axiomStart axiomFinish formulaStart formulaFinish
    suffixStart suffixFinish certificateTag certificateEndpointBound
    gammaFinish gammaCount gammaBoundary firstFinish firstCount
    secondFinish secondCount witnessFinish witnessCount suffixCount
    gammaBoundarySize
    sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
    sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
    currentTaskTableWidth currentTaskValueBound
    currentValueTableWidth currentValueValueBound
    nextTaskTableWidth nextTaskValueBound
    nextValueTableWidth nextValueValueBound
    nextStart nextProofFinish nextCertificateFinish nextStatusTag
    firstParseCoordinates secondParseCoordinates combineCoordinates
    firstParseSize secondParseSize combineSize

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
@[simp] theorem compactNumericVerifierParseSuccessNonLeafStateGraphDef_spec :
    compactNumericVerifierParseSuccessNonLeafStateGraphDef.val.Evalb
        (compactNumericVerifierParseSuccessNonLeafStateGraphEnvironment
          stateTable stateWidth stateTokenCount
          stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound
          gammaFinish gammaCount gammaBoundary firstFinish firstCount
          secondFinish secondCount witnessFinish witnessCount suffixCount
          gammaBoundarySize
          sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
          sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
          currentTaskTableWidth currentTaskValueBound
          currentValueTableWidth currentValueValueBound
          nextTaskTableWidth nextTaskValueBound
          nextValueTableWidth nextValueValueBound
          nextStart nextProofFinish nextCertificateFinish nextStatusTag
          firstParseCoordinates secondParseCoordinates combineCoordinates
          firstParseSize secondParseSize combineSize) ↔
      CompactNumericVerifierParseSuccessNonLeafStateGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        gammaFinish gammaCount gammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        gammaBoundarySize
        sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
        sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStart nextProofFinish nextCertificateFinish nextStatusTag
        firstParseCoordinates secondParseCoordinates combineCoordinates
        firstParseSize secondParseSize combineSize := by
  let env := compactNumericVerifierParseSuccessNonLeafStateGraphEnvironment
    stateTable stateWidth stateTokenCount
    stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
    proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
    rootStart rootFinish proofTag proofEndpointBound
    certificateTable certificateWidth certificateTokenCount
    certificateInputStart certificateInputFinish
    axiomStart axiomFinish formulaStart formulaFinish
    suffixStart suffixFinish certificateTag certificateEndpointBound
    gammaFinish gammaCount gammaBoundary firstFinish firstCount
    secondFinish secondCount witnessFinish witnessCount suffixCount
    gammaBoundarySize
    sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
    sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
    currentTaskTableWidth currentTaskValueBound
    currentValueTableWidth currentValueValueBound
    nextTaskTableWidth nextTaskValueBound
    nextValueTableWidth nextValueValueBound
    nextStart nextProofFinish nextCertificateFinish nextStatusTag
    firstParseCoordinates secondParseCoordinates combineCoordinates
    firstParseSize secondParseSize combineSize
  have honeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 102), #1, #2, #3, #4, #5, #6, #7,
          #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18, #19,
          #20, #21, #22, #23, #24, #25, #26, #27, #28, #29, #30, #31,
          #32, #33, #34, #35, #36, #37, #38, #39, #40, #41, #42, #43,
          #44, #45, #46, #47, #48, #49, #50, #51, #52, #53, #54, #55,
          #56, #57, #58, #59, #60, #61, #62, #63, #64, #65, #66, #67,
          #68, #69, #70, #71, #72, #73, #88, #89, #90, #91, #92, #93,
          #94, #95, #96, #97, #98, #99, #100, #101]) =
        compactNumericVerifierOneParseSuccessNonLeafStateGraphEnvironment
          stateTable stateWidth stateTokenCount
          stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound
          gammaFinish gammaCount gammaBoundary firstFinish firstCount
          secondFinish secondCount witnessFinish witnessCount suffixCount
          gammaBoundarySize
          sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
          sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
          currentTaskTableWidth currentTaskValueBound
          currentValueTableWidth currentValueValueBound
          nextTaskTableWidth nextTaskValueBound
          nextValueTableWidth nextValueValueBound
          nextStart nextProofFinish nextCertificateFinish nextStatusTag
          firstParseCoordinates combineCoordinates firstParseSize combineSize := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htwoEnv :
      (Semiterm.val env Empty.elim ∘
        (fun index : Fin 102 =>
          (#index : Semiterm ℒₒᵣ Empty 102))) =
        compactNumericVerifierTwoParseSuccessNonLeafStateGraphEnvironment
          stateTable stateWidth stateTokenCount
          stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound
          gammaFinish gammaCount gammaBoundary firstFinish firstCount
          secondFinish secondCount witnessFinish witnessCount suffixCount
          gammaBoundarySize
          sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
          sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
          currentTaskTableWidth currentTaskValueBound
          currentValueTableWidth currentValueValueBound
          nextTaskTableWidth nextTaskValueBound
          nextValueTableWidth nextValueValueBound
          nextStart nextProofFinish nextCertificateFinish nextStatusTag
          firstParseCoordinates secondParseCoordinates combineCoordinates
          firstParseSize secondParseSize combineSize := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have honeSpec := compactNumericVerifierOneParseSuccessNonLeafStateGraphDef_spec
    stateTable stateWidth stateTokenCount
    stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
    proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
    rootStart rootFinish proofTag proofEndpointBound
    certificateTable certificateWidth certificateTokenCount
    certificateInputStart certificateInputFinish
    axiomStart axiomFinish formulaStart formulaFinish
    suffixStart suffixFinish certificateTag certificateEndpointBound
    gammaFinish gammaCount gammaBoundary firstFinish firstCount
    secondFinish secondCount witnessFinish witnessCount suffixCount
    gammaBoundarySize
    sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
    sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
    currentTaskTableWidth currentTaskValueBound
    currentValueTableWidth currentValueValueBound
    nextTaskTableWidth nextTaskValueBound
    nextValueTableWidth nextValueValueBound
    nextStart nextProofFinish nextCertificateFinish nextStatusTag
    firstParseCoordinates combineCoordinates firstParseSize combineSize
  have htwoSpec := compactNumericVerifierTwoParseSuccessNonLeafStateGraphDef_spec
    stateTable stateWidth stateTokenCount
    stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
    proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
    rootStart rootFinish proofTag proofEndpointBound
    certificateTable certificateWidth certificateTokenCount
    certificateInputStart certificateInputFinish
    axiomStart axiomFinish formulaStart formulaFinish
    suffixStart suffixFinish certificateTag certificateEndpointBound
    gammaFinish gammaCount gammaBoundary firstFinish firstCount
    secondFinish secondCount witnessFinish witnessCount suffixCount
    gammaBoundarySize
    sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
    sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
    currentTaskTableWidth currentTaskValueBound
    currentValueTableWidth currentValueValueBound
    nextTaskTableWidth nextTaskValueBound
    nextValueTableWidth nextValueValueBound
    nextStart nextProofFinish nextCertificateFinish nextStatusTag
    firstParseCoordinates secondParseCoordinates combineCoordinates
    firstParseSize secondParseSize combineSize
  change compactNumericVerifierParseSuccessNonLeafStateGraphDef.val.Evalb env ↔ _
  simp [compactNumericVerifierParseSuccessNonLeafStateGraphDef,
    CompactNumericVerifierParseSuccessNonLeafStateGraph,
    Semiformula.eval_substs, honeEnv, htwoEnv, honeSpec, htwoSpec]

theorem compactNumericVerifierParseSuccessNonLeafStateGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierParseSuccessNonLeafStateGraphDef.val := by
  simp [compactNumericVerifierParseSuccessNonLeafStateGraphDef]

variable
  {proofTokens certificateTokens nextProof nextCertificate : List Nat}
  {sourceTasks targetTasks : List CompactNumericVerifierTask}
  {sourceValues targetValues : List CompactNumericChildResult}

theorem CompactNumericVerifierParseSuccessNonLeafStateGraph.sound
    (hgraph : CompactNumericVerifierParseSuccessNonLeafStateGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
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
      firstParseSize secondParseSize combineSize)
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
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
        stateTable stateWidth stateTokenCount targetValueBoundary targetValues) :
    ∃ proofNode : CompactNumericVerifierTask,
    ∃ certificateNode : CompactNumericCertificateNode,
      (proofNode.1 = 3 ∨ proofNode.1 = 4 ∨ proofNode.1 = 5 ∨
        proofNode.1 = 6 ∨ proofNode.1 = 7 ∨ proofNode.1 = 8 ∨
        proofNode.1 = 9) ∧
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
  rcases hgraph with hone | htwo
  · rcases CompactNumericVerifierOneParseSuccessNonLeafStateGraph.sound
      hone hproofLayout hcertificateLayout hnextProof hnextCertificate
      hsourceTaskRows htargetTaskRows hsourceTaskGraph htargetTaskGraph
      hsourceValueRows htargetValueRows with
      ⟨proofNode, certificateNode, htag, _hcertificateTag, hproofParser,
        hcertificateParser, htransition, htaskWidth, htaskBound, hvalueWidth,
        hvalueBound, hstatus⟩
    have htagAll : proofNode.1 = 3 ∨ proofNode.1 = 4 ∨ proofNode.1 = 5 ∨
        proofNode.1 = 6 ∨ proofNode.1 = 7 ∨ proofNode.1 = 8 ∨
        proofNode.1 = 9 := by
      rcases htag with hfour | hfive | hsix | hseven | height
      · exact Or.inr (Or.inl hfour)
      · exact Or.inr (Or.inr (Or.inl hfive))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hsix)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hseven))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl height)))))
    exact ⟨proofNode, certificateNode, htagAll, hproofParser,
      hcertificateParser, htransition, htaskWidth, htaskBound, hvalueWidth,
      hvalueBound, hstatus⟩
  · rcases CompactNumericVerifierTwoParseSuccessNonLeafStateGraph.sound
      htwo hproofLayout hcertificateLayout hnextProof hnextCertificate
      hsourceTaskRows htargetTaskRows hsourceTaskGraph htargetTaskGraph
      hsourceValueRows htargetValueRows with
      ⟨proofNode, certificateNode, htag, _hcertificateTag, hproofParser,
        hcertificateParser, htransition, htaskWidth, htaskBound, hvalueWidth,
        hvalueBound, hstatus⟩
    have htagAll : proofNode.1 = 3 ∨ proofNode.1 = 4 ∨ proofNode.1 = 5 ∨
        proofNode.1 = 6 ∨ proofNode.1 = 7 ∨ proofNode.1 = 8 ∨
        proofNode.1 = 9 := by
      rcases htag with hthree | hnine
      · exact Or.inl hthree
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hnine)))))
    exact ⟨proofNode, certificateNode, htagAll, hproofParser,
      hcertificateParser, htransition, htaskWidth, htaskBound, hvalueWidth,
      hvalueBound, hstatus⟩

theorem exists_compactNumericVerifierParseSuccessNonLeafStateGraph_of_transition
    {proofNode : CompactNumericVerifierTask}
    {certificateNode : CompactNumericCertificateNode}
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens = some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser certificateTokens =
      some certificateNode)
    (hproofTag : proofNode.1 = 3 ∨ proofNode.1 = 4 ∨ proofNode.1 = 5 ∨
      proofNode.1 = 6 ∨ proofNode.1 = 7 ∨ proofNode.1 = 8 ∨ proofNode.1 = 9)
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
    (hsourceTaskNonempty : 1 ≤ sourceTasks.length)
    (htaskTableWidth : nextTaskTableWidth = currentTaskTableWidth)
    (htaskValueBound : nextTaskValueBound = currentTaskValueBound)
    (hvalueTableWidth : nextValueTableWidth = currentValueTableWidth)
    (hvalueValueBound : nextValueValueBound = currentValueValueBound)
    (hnextStatus : nextStatusTag = 0) :
    ∃ proofTable proofWidth proofTokenCount proofInputStart proofInputFinish,
    ∃ rootStart rootFinish proofTag proofEndpointBound,
    ∃ certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish certificateTag certificateEndpointBound,
    ∃ gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize,
    ∃ firstParseCoordinates secondParseCoordinates combineCoordinates,
    ∃ firstParseSize secondParseSize combineSize,
      CompactNumericVerifierParseSuccessNonLeafStateGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
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
        firstParseSize secondParseSize combineSize := by
  by_cases htwo : proofNode.1 = 3 ∨ proofNode.1 = 9
  · rcases exists_compactNumericVerifierTwoParseSuccessNonLeafStateGraph_of_transition
      hproofLayout hcertificateLayout hproofParser hcertificateParser htwo
      htransition hnextProof hnextCertificate hsourceTaskRows htargetTaskRows
      hsourceTaskGraph htargetTaskGraph hsourceValueRows htargetValueRows
      hsourceValueGraph htargetValueGraph hsourceTaskNonempty htaskTableWidth
      htaskValueBound hvalueTableWidth hvalueValueBound hnextStatus with
      ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
        rootStart, rootFinish, proofTag, proofEndpointBound,
        certificateTable, certificateWidth, certificateTokenCount,
        certificateInputStart, certificateInputFinish,
        axiomStart, axiomFinish, formulaStart, formulaFinish,
        suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
        gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
        secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
        gammaBoundarySize, firstParseCoordinates, secondParseCoordinates,
        combineCoordinates, firstParseSize, secondParseSize, combineSize, hgraph⟩
    exact ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
      secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
      gammaBoundarySize, firstParseCoordinates, secondParseCoordinates,
      combineCoordinates, firstParseSize, secondParseSize, combineSize, Or.inr hgraph⟩
  · have hone : proofNode.1 = 4 ∨ proofNode.1 = 5 ∨ proofNode.1 = 6 ∨
        proofNode.1 = 7 ∨ proofNode.1 = 8 := by
      rcases hproofTag with hthree | hfour | hfive | hsix | hseven | height | hnine
      · exact False.elim (htwo (Or.inl hthree))
      · exact Or.inl hfour
      · exact Or.inr (Or.inl hfive)
      · exact Or.inr (Or.inr (Or.inl hsix))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hseven)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr height)))
      · exact False.elim (htwo (Or.inr hnine))
    rcases exists_compactNumericVerifierOneParseSuccessNonLeafStateGraph_of_transition
      hproofLayout hcertificateLayout hproofParser hcertificateParser hone
      htransition hnextProof hnextCertificate hsourceTaskRows htargetTaskRows
      hsourceTaskGraph htargetTaskGraph hsourceValueRows htargetValueRows
      hsourceValueGraph htargetValueGraph hsourceTaskNonempty htaskTableWidth
      htaskValueBound hvalueTableWidth hvalueValueBound hnextStatus with
      ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
        rootStart, rootFinish, proofTag, proofEndpointBound,
        certificateTable, certificateWidth, certificateTokenCount,
        certificateInputStart, certificateInputFinish,
        axiomStart, axiomFinish, formulaStart, formulaFinish,
        suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
        gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
        secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
        gammaBoundarySize, firstParseCoordinates, combineCoordinates,
        firstParseSize, combineSize, hgraph⟩
    exact ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
      secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
      gammaBoundarySize, firstParseCoordinates, firstParseCoordinates,
      combineCoordinates, firstParseSize, firstParseSize, combineSize, Or.inl hgraph⟩

#print axioms compactNumericVerifierParseSuccessNonLeafStateGraphDef_spec
#print axioms compactNumericVerifierParseSuccessNonLeafStateGraphDef_sigmaZero
#print axioms CompactNumericVerifierParseSuccessNonLeafStateGraph.sound
#print axioms exists_compactNumericVerifierParseSuccessNonLeafStateGraph_of_transition

end FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateGraph
