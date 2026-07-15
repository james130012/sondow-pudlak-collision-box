import integration.FoundationCompactNumericListedDirectVerifierParseScheduleRowsCompleteness
import integration.FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafCommonRows
import integration.FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateCoordinates
import integration.FoundationCompactNumericListedDirectVerifierTaskCrossTableBridgeGraph
import integration.FoundationCompactNumericListedDirectNodeTransitionCases
import integration.FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafParsedSemantics
import integration.FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization
import integration.FoundationCompactNumericListedDirectVerifierStepCases
import integration.FoundationCompactNumericListedDirectVerifierParseScheduleRowsSelfCompleteness

/-!
# Complete one-parse non-leaf state graph

This relation closes the tags 4--8 branch of a successful parse transition.
It combines the exposed parser graph, the exact one-parse task schedule, the
common stream/value transport rows, and a complete proof-table/state-table
task bridge.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierOneParseSuccessNonLeafStateGraph

open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
open FoundationCompactNumericListedDirectVerifierParseScheduleRows
open FoundationCompactNumericListedDirectVerifierParseScheduleFormula
open FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafCommonRows
open FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateCoordinates
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

def CompactNumericVerifierOneParseSuccessNonLeafStateGraph
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
    (parseCoordinates combineCoordinates :
      CompactNumericVerifierTaskRowCoordinates)
    (parseSize combineSize : CompactNumericVerifierTaskSizeWitness) : Prop :=
  CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph
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
      gammaBoundarySize ∧
    CompactNumericVerifierParseSuccessNonLeafCommonRows
      stateTable stateWidth stateTokenCount
      sourceValueBoundary sourceValueCount
      targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount witnessFinish rootFinish
      certificateTable certificateWidth certificateTokenCount
      suffixStart suffixFinish ∧
    CompactNumericVerifierOneParseScheduleRows
      stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      currentTaskValueBound
      combineCoordinates.start combineCoordinates.finish proofTag
      parseCoordinates combineCoordinates parseSize combineSize ∧
    CompactNumericVerifierTaskCrossTableBridgeGraph
      proofTable proofWidth proofTokenCount rootStart rootFinish proofTag
      gammaFinish firstFinish secondFinish witnessFinish
      stateTable stateWidth stateTokenCount
      combineCoordinates.start combineCoordinates.finish combineCoordinates.tag
      combineCoordinates.gammaFinish combineCoordinates.firstFinish
      combineCoordinates.secondFinish combineCoordinates.witnessFinish

def compactNumericVerifierOneParseSuccessNonLeafStateGraphDef :
    𝚺₀.Semisentence 88 := .mkSigma
  ((compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef.val ⇜
      (fun index : Fin 40 =>
        (#(Fin.castLE (show 40 ≤ 88 by omega) index) :
          Semiterm ℒₒᵣ Empty 88))) ⋏
    (compactNumericVerifierParseSuccessNonLeafCommonRowsDef.val ⇜
      ![(#0 : Semiterm ℒₒᵣ Empty 88), #1, #2,
        #44, #45, #46, #47, #48, #49, #50, #51,
        #52, #53, #54, #55, #56, #57, #58, #59,
        #7, #8, #9, #36, #13, #16, #17, #18, #25, #26]) ⋏
    (compactNumericVerifierOneParseScheduleRowsDef.val ⇜
      ![(#0 : Semiterm ℒₒᵣ Empty 88), #1, #2,
        #40, #41, #42, #43, #49, #74, #75, #14,
        #60, #61, #62, #63, #64, #65, #66, #67, #68, #69,
        #70, #71, #72, #73,
        #74, #75, #76, #77, #78, #79, #80, #81, #82, #83,
        #84, #85, #86, #87]) ⋏
    (compactNumericVerifierTaskCrossTableBridgeGraphDef.val ⇜
      ![(#7 : Semiterm ℒₒᵣ Empty 88), #8, #9, #12, #13, #14,
        #29, #32, #34, #36,
        #0, #1, #2, #74, #75, #76, #77, #80, #82, #84])) (by simp)

def compactNumericVerifierOneParseSuccessNonLeafStateGraphEnvironment
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
    (parseCoordinates combineCoordinates :
      CompactNumericVerifierTaskRowCoordinates)
    (parseSize combineSize : CompactNumericVerifierTaskSizeWitness) :
    Fin 88 -> Nat :=
  Matrix.vecAppend rfl
    (compactNumericVerifierParseSuccessNonLeafBaseEnvironment
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
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag)
    (Matrix.vecAppend rfl
      (compactNumericVerifierTaskScheduleEnvironment parseCoordinates parseSize)
      (compactNumericVerifierTaskScheduleEnvironment combineCoordinates combineSize))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
@[simp] theorem compactNumericVerifierOneParseSuccessNonLeafStateGraphDef_spec
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
    (parseCoordinates combineCoordinates :
      CompactNumericVerifierTaskRowCoordinates)
    (parseSize combineSize : CompactNumericVerifierTaskSizeWitness) :
    compactNumericVerifierOneParseSuccessNonLeafStateGraphDef.val.Evalb
        (compactNumericVerifierOneParseSuccessNonLeafStateGraphEnvironment
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
          sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
          sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
          currentTaskTableWidth currentTaskValueBound
          currentValueTableWidth currentValueValueBound
          nextTaskTableWidth nextTaskValueBound
          nextValueTableWidth nextValueValueBound
          nextStart nextProofFinish nextCertificateFinish nextStatusTag
          parseCoordinates combineCoordinates parseSize combineSize) ↔
      CompactNumericVerifierOneParseSuccessNonLeafStateGraph
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
        sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
        sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStart nextProofFinish nextCertificateFinish nextStatusTag
        parseCoordinates combineCoordinates parseSize combineSize := by
  let env := compactNumericVerifierOneParseSuccessNonLeafStateGraphEnvironment
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
    parseCoordinates combineCoordinates parseSize combineSize
  have hparseEnv :
      (Semiterm.val env Empty.elim ∘
        (fun index : Fin 40 =>
          (#(Fin.castLE (show 40 ≤ 88 by omega) index) :
            Semiterm ℒₒᵣ Empty 88))) =
        compactNumericParsePayloadSuccessExposedSeparatedTablesGraphEnvironment
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
          gammaBoundarySize := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcommonEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 88), #1, #2,
          #44, #45, #46, #47, #48, #49, #50, #51,
          #52, #53, #54, #55, #56, #57, #58, #59,
          #7, #8, #9, #36, #13, #16, #17, #18, #25, #26]) =
        compactNumericVerifierParseSuccessNonLeafCommonRowsEnvironment
          stateTable stateWidth stateTokenCount
          sourceValueBoundary sourceValueCount
          targetValueBoundary targetValueCount
          currentTaskTableWidth currentTaskValueBound
          currentValueTableWidth currentValueValueBound
          nextTaskTableWidth nextTaskValueBound
          nextValueTableWidth nextValueValueBound
          nextStart nextProofFinish nextCertificateFinish nextStatusTag
          proofTable proofWidth proofTokenCount witnessFinish rootFinish
          certificateTable certificateWidth certificateTokenCount
          suffixStart suffixFinish := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hscheduleEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 88), #1, #2,
          #40, #41, #42, #43, #49, #74, #75, #14,
          #60, #61, #62, #63, #64, #65, #66, #67, #68, #69,
          #70, #71, #72, #73,
          #74, #75, #76, #77, #78, #79, #80, #81, #82, #83,
          #84, #85, #86, #87]) =
        compactNumericVerifierOneParseScheduleRowsEnvironment
          stateTable stateWidth stateTokenCount
          sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
          currentTaskValueBound
          combineCoordinates.start combineCoordinates.finish proofTag
          parseCoordinates.start parseCoordinates.finish parseCoordinates.tag
          parseCoordinates.gammaFinish parseCoordinates.gammaCount
          parseCoordinates.gammaBoundary parseCoordinates.firstFinish
          parseCoordinates.firstCount parseCoordinates.secondFinish
          parseCoordinates.secondCount parseCoordinates.witnessFinish
          parseCoordinates.witnessCount parseCoordinates.suffixCount
          parseSize.gammaBoundarySize
          combineCoordinates.start combineCoordinates.finish combineCoordinates.tag
          combineCoordinates.gammaFinish combineCoordinates.gammaCount
          combineCoordinates.gammaBoundary combineCoordinates.firstFinish
          combineCoordinates.firstCount combineCoordinates.secondFinish
          combineCoordinates.secondCount combineCoordinates.witnessFinish
          combineCoordinates.witnessCount combineCoordinates.suffixCount
          combineSize.gammaBoundarySize := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hbridgeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#7 : Semiterm ℒₒᵣ Empty 88), #8, #9, #12, #13, #14,
          #29, #32, #34, #36,
          #0, #1, #2, #74, #75, #76, #77, #80, #82, #84]) =
        compactNumericVerifierTaskCrossTableBridgeGraphEnvironment
          proofTable proofWidth proofTokenCount rootStart rootFinish proofTag
          gammaFinish firstFinish secondFinish witnessFinish
          stateTable stateWidth stateTokenCount
          combineCoordinates.start combineCoordinates.finish
          combineCoordinates.tag combineCoordinates.gammaFinish
          combineCoordinates.firstFinish combineCoordinates.secondFinish
          combineCoordinates.witnessFinish := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hparseSpec :=
    compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef_spec
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
  have hcommonSpec :=
    compactNumericVerifierParseSuccessNonLeafCommonRowsDef_spec
      stateTable stateWidth stateTokenCount
      sourceValueBoundary sourceValueCount
      targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount witnessFinish rootFinish
      certificateTable certificateWidth certificateTokenCount
      suffixStart suffixFinish
  have hscheduleSpec := compactNumericVerifierOneParseScheduleRowsDef_spec
    stateTable stateWidth stateTokenCount
    sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
    currentTaskValueBound
    combineCoordinates.start combineCoordinates.finish proofTag
    parseCoordinates.start parseCoordinates.finish parseCoordinates.tag
    parseCoordinates.gammaFinish parseCoordinates.gammaCount
    parseCoordinates.gammaBoundary parseCoordinates.firstFinish
    parseCoordinates.firstCount parseCoordinates.secondFinish
    parseCoordinates.secondCount parseCoordinates.witnessFinish
    parseCoordinates.witnessCount parseCoordinates.suffixCount
    parseSize.gammaBoundarySize
    combineCoordinates.start combineCoordinates.finish combineCoordinates.tag
    combineCoordinates.gammaFinish combineCoordinates.gammaCount
    combineCoordinates.gammaBoundary combineCoordinates.firstFinish
    combineCoordinates.firstCount combineCoordinates.secondFinish
    combineCoordinates.secondCount combineCoordinates.witnessFinish
    combineCoordinates.witnessCount combineCoordinates.suffixCount
    combineSize.gammaBoundarySize
  have hbridgeSpec := compactNumericVerifierTaskCrossTableBridgeGraphDef_spec
    proofTable proofWidth proofTokenCount rootStart rootFinish proofTag
    gammaFinish firstFinish secondFinish witnessFinish
    stateTable stateWidth stateTokenCount
    combineCoordinates.start combineCoordinates.finish combineCoordinates.tag
    combineCoordinates.gammaFinish combineCoordinates.firstFinish
    combineCoordinates.secondFinish combineCoordinates.witnessFinish
  have hparseCoordinates :
      compactNumericVerifierTaskRowCoordinatesOf
        parseCoordinates.start parseCoordinates.finish parseCoordinates.tag
        parseCoordinates.gammaFinish parseCoordinates.gammaCount
        parseCoordinates.gammaBoundary parseCoordinates.firstFinish
        parseCoordinates.firstCount parseCoordinates.secondFinish
        parseCoordinates.secondCount parseCoordinates.witnessFinish
        parseCoordinates.witnessCount parseCoordinates.suffixCount =
      parseCoordinates := by
    cases parseCoordinates
    rfl
  have hcombineCoordinates :
      compactNumericVerifierTaskRowCoordinatesOf
        combineCoordinates.start combineCoordinates.finish combineCoordinates.tag
        combineCoordinates.gammaFinish combineCoordinates.gammaCount
        combineCoordinates.gammaBoundary combineCoordinates.firstFinish
        combineCoordinates.firstCount combineCoordinates.secondFinish
        combineCoordinates.secondCount combineCoordinates.witnessFinish
        combineCoordinates.witnessCount combineCoordinates.suffixCount =
      combineCoordinates := by
    cases combineCoordinates
    rfl
  change (Semiformula.Eval
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
        gammaBoundarySize) Empty.elim)
      compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef.val ↔ _
    at hparseSpec
  change compactNumericVerifierOneParseSuccessNonLeafStateGraphDef.val.Evalb env ↔ _
  simp [compactNumericVerifierOneParseSuccessNonLeafStateGraphDef,
    CompactNumericVerifierOneParseSuccessNonLeafStateGraph,
    Semiformula.eval_substs, hparseEnv, hcommonEnv, hscheduleEnv, hbridgeEnv,
    hparseSpec, hcommonSpec, hscheduleSpec, hbridgeSpec,
    hparseCoordinates, hcombineCoordinates]

theorem compactNumericVerifierOneParseSuccessNonLeafStateGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierOneParseSuccessNonLeafStateGraphDef.val := by
  simp [compactNumericVerifierOneParseSuccessNonLeafStateGraphDef]

private theorem oneParseOutput_of_outputCase
    {proofNode : CompactNumericVerifierTask}
    {certificateNode : CompactNumericCertificateNode}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    {output : CompactNumericRunningPayload}
    (hcase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode restTasks values output)
    (htag : proofNode.1 = 4 ∨ proofNode.1 = 5 ∨ proofNode.1 = 6 ∨
      proofNode.1 = 7 ∨ proofNode.1 = 8) :
    certificateNode.1 = 2 ∧
      ((proofNode.2.2.2.2.2, certificateNode.2.2),
        (compactNumericParseTask ::
          compactNumericCombineTask proofNode.1 proofNode.2 :: restTasks,
          values)) = output := by
  rcases proofNode with ⟨proofTag, fields⟩
  rcases certificateNode with ⟨certificateTag, certificatePayload⟩
  change proofTag = 4 ∨ proofTag = 5 ∨ proofTag = 6 ∨
    proofTag = 7 ∨ proofTag = 8 at htag
  rcases htag with htag | htag | htag | htag | htag <;>
    subst proofTag <;>
    simpa [CompactNumericNodeTransitionOutputCase,
      compactNumericNodeFieldsSuffix] using hcase

private theorem outputCase_of_oneParseOutput
    {proofNode : CompactNumericVerifierTask}
    {certificateNode : CompactNumericCertificateNode}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    {output : CompactNumericRunningPayload}
    (htag : proofNode.1 = 4 ∨ proofNode.1 = 5 ∨ proofNode.1 = 6 ∨
      proofNode.1 = 7 ∨ proofNode.1 = 8)
    (hcertificateTag : certificateNode.1 = 2)
    (houtput :
      ((proofNode.2.2.2.2.2, certificateNode.2.2),
        (compactNumericParseTask ::
          compactNumericCombineTask proofNode.1 proofNode.2 :: restTasks,
          values)) = output) :
    CompactNumericNodeTransitionOutputCase
      proofNode certificateNode restTasks values output := by
  rcases proofNode with ⟨proofTag, fields⟩
  rcases certificateNode with ⟨certificateTag, certificatePayload⟩
  change proofTag = 4 ∨ proofTag = 5 ∨ proofTag = 6 ∨
    proofTag = 7 ∨ proofTag = 8 at htag
  change certificateTag = 2 at hcertificateTag
  rcases htag with htag | htag | htag | htag | htag <;>
    subst proofTag <;>
    subst certificateTag <;>
    simpa [CompactNumericNodeTransitionOutputCase,
      compactNumericNodeFieldsSuffix] using houtput

theorem CompactNumericVerifierOneParseSuccessNonLeafStateGraph.sound
    {stateTable stateWidth stateTokenCount
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
      sourceTaskBoundary targetTaskBoundary
      sourceValueBoundary targetValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag : Nat}
    {parseCoordinates combineCoordinates :
      CompactNumericVerifierTaskRowCoordinates}
    {parseSize combineSize : CompactNumericVerifierTaskSizeWitness}
    {proofTokens certificateTokens nextProof nextCertificate : List Nat}
    {sourceTasks targetTasks : List CompactNumericVerifierTask}
    {sourceValues targetValues : List CompactNumericChildResult}
    (hgraph : CompactNumericVerifierOneParseSuccessNonLeafStateGraph
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
      parseCoordinates combineCoordinates parseSize combineSize)
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
      (proofNode.1 = 4 ∨ proofNode.1 = 5 ∨ proofNode.1 = 6 ∨
        proofNode.1 = 7 ∨ proofNode.1 = 8) ∧
      certificateNode.1 = 2 ∧
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
  have hparseGraph := hgraph.1
  have hcommonRows := hgraph.2.1
  have hscheduleRows := hgraph.2.2.1
  have hbridgeGraph := hgraph.2.2.2
  have htagCases : proofTag = 4 ∨ proofTag = 5 ∨ proofTag = 6 ∨
      proofTag = 7 ∨ proofTag = 8 := hscheduleRows.1
  rcases hparseGraph.realize_nonleaf_fields with
    ⟨proofInput, proofNode, certificateInput, certificateNode,
      proofSuffix, certificateSuffix,
      hproofInput, hproofNode, hproofParser, hproofNodeTag,
      hproofSuffix, hproofSuffixValue,
      hcertificateInput, hcertificateSuffix, hcertificateParser,
      hcertificateNodeTag, hcertificateSuffixValue⟩
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
  have htagMatch := hparseGraph.1.2.2.2.2
  have hcertificateTagTwo : certificateTag = 2 := by
    rcases htagCases with htag | htag | htag | htag | htag <;>
      simp [CompactNumericNodeTransitionTagMatch, htag] at htagMatch
    all_goals assumption
  have hcertificateNodeTagTwo : certificateNode.1 = 2 :=
    hcertificateNodeTag.trans hcertificateTagTwo
  have hproofNodeTagCases : proofNode.1 = 4 ∨ proofNode.1 = 5 ∨
      proofNode.1 = 6 ∨ proofNode.1 = 7 ∨ proofNode.1 = 8 := by
    simpa only [hproofNodeTag] using htagCases
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithAllFields
        hparseGraph.2 with
    ⟨sourceRoot, hsourceRoot, hsourceRootTag,
      hsourceGamma, hsourceFirst, hsourceSecond,
      hsourceWitness, hsourceSuffix⟩
  have hsourceRootTag' : sourceRoot.1 = proofTag := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using hsourceRootTag
  have hsourceRootValue : sourceRoot = proofNode :=
    FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hparseGraph.2 hproofNode hsourceRoot
  have hcombineAt := hscheduleRows.2.2.2.2.1
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithAllFields
        hcombineAt.core with
    ⟨combineRoot, hcombineRoot, hcombineRootTag,
      hcombineGamma, hcombineFirst, hcombineSecond,
      hcombineWitness, hcombineSuffix⟩
  have hbridgeTyped : CompactNumericVerifierTaskCrossTableBridgeGraph
      proofTable proofWidth proofTokenCount rootStart rootFinish sourceRoot.1
      gammaFinish firstFinish secondFinish witnessFinish
      stateTable stateWidth stateTokenCount
      combineCoordinates.start combineCoordinates.finish combineRoot.1
      combineCoordinates.gammaFinish combineCoordinates.firstFinish
      combineCoordinates.secondFinish combineCoordinates.witnessFinish := by
    simpa only [hsourceRootTag', hcombineRootTag] using hbridgeGraph
  have hcombineSource : combineRoot = sourceRoot :=
    hbridgeTyped.sound hsourceRoot hcombineRoot
      hsourceGamma hcombineGamma hsourceFirst hcombineFirst
      hsourceSecond hcombineSecond hsourceWitness hcombineWitness
      hsourceSuffix hcombineSuffix
  have hcombineProof : combineRoot = proofNode :=
    hcombineSource.trans hsourceRootValue
  have hcombineTag : combineRoot.1 = proofTag :=
    (congrArg Prod.fst hcombineProof).trans hproofNodeTag
  have hscheduleSound := hscheduleRows.sound
    hsourceTaskRows htargetTaskRows hsourceTaskGraph htargetTaskGraph
    hcombineRoot hcombineTag
  have htargetTasks : targetTasks = compactNumericParseTask ::
      compactNumericCombineTask proofNode.1 proofNode.2 ::
        sourceTasks.drop 1 := by
    have hscheduleTarget := hscheduleSound.2
    rw [hcombineProof] at hscheduleTarget
    simpa [compactNumericCombineTask] using hscheduleTarget
  have hcommonSound := hcommonRows.sound
    hproofSuffix hcertificateSuffix hnextProof hnextCertificate
    hsourceValueRows htargetValueRows
  have hnextProofValue : nextProof = proofNode.2.2.2.2.2 :=
    hcommonSound.1.trans hproofSuffixValue
  have hnextCertificateValue : nextCertificate = certificateNode.2.2 :=
    hcommonSound.2.1.trans hcertificateSuffixValue
  have htargetValues : targetValues = sourceValues := hcommonSound.2.2.1
  have houtput :
      ((proofNode.2.2.2.2.2, certificateNode.2.2),
        (compactNumericParseTask ::
          compactNumericCombineTask proofNode.1 proofNode.2 ::
            sourceTasks.drop 1, sourceValues)) =
        ((nextProof, nextCertificate), (targetTasks, targetValues)) := by
    simp [hnextProofValue, hnextCertificateValue, htargetTasks, htargetValues]
  have houtputCase := outputCase_of_oneParseOutput
    hproofNodeTagCases hcertificateNodeTagTwo houtput
  have htransition :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode (sourceTasks.drop 1) sourceValues
      ((nextProof, nextCertificate), (targetTasks, targetValues))).2 houtputCase
  exact ⟨proofNode, certificateNode, hproofNodeTagCases,
    hcertificateNodeTagTwo, hproofParserState, hcertificateParserState,
    htransition, hcommonSound.2.2.2.1, hcommonSound.2.2.2.2.1,
    hcommonSound.2.2.2.2.2.1, hcommonSound.2.2.2.2.2.2.1,
    hcommonSound.2.2.2.2.2.2.2⟩

theorem exists_compactNumericVerifierOneParseSuccessNonLeafStateGraph_of_transition
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish
      sourceTaskBoundary targetTaskBoundary
      sourceValueBoundary targetValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag : Nat}
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
    (hproofParser : compactListedProofNodeFieldsParser proofTokens = some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser certificateTokens =
      some certificateNode)
    (hproofTag : proofNode.1 = 4 ∨ proofNode.1 = 5 ∨ proofNode.1 = 6 ∨
      proofNode.1 = 7 ∨ proofNode.1 = 8)
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
    ∃ parseCoordinates combineCoordinates,
    ∃ parseSize combineSize,
      CompactNumericVerifierOneParseSuccessNonLeafStateGraph
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
        parseCoordinates combineCoordinates parseSize combineSize := by
  have houtputCase :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode (sourceTasks.drop 1) sourceValues
      ((nextProof, nextCertificate), (targetTasks, targetValues))).1 htransition
  rcases oneParseOutput_of_outputCase houtputCase hproofTag with
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
      compactNumericCombineTask proofNode.1 proofNode.2 ::
        sourceTasks.drop 1 := by
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
      exists_compactNumericParsePayloadSuccessExposedSeparatedTablesGraph_of_exists_some
        hproofLayout hcertificateLayout
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
      gammaBoundarySize, hparseGraph⟩
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
      CompactNumericVerifierOneParseScheduleRows.of_components_self_root
        hsourceTaskRows htargetTaskRows hsourceTaskGraph htargetTaskGraph
        hproofTag hsourceNonempty htargetTasks with
    ⟨parseCoordinates, combineCoordinates, parseSize, combineSize,
      hscheduleRowsActualTag⟩
  have hscheduleRows : CompactNumericVerifierOneParseScheduleRows
      stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTasks.length targetTaskBoundary targetTasks.length
      currentTaskValueBound
      combineCoordinates.start combineCoordinates.finish proofTag
      parseCoordinates combineCoordinates parseSize combineSize := by
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
  have hcombineAt := hscheduleRows.2.2.2.2.1
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFullFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithAllFields
        hcombineAt.core with
    ⟨targetRoot, htargetRoot, htargetRootTag,
      htargetGamma, htargetFirst, htargetSecond,
      htargetWitness, htargetSuffix⟩
  have htargetIndex : 1 < targetTasks.length := by
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
  have htargetAt : targetTasks.getI 1 = proofNode := by
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
  exact ⟨proofTable, proofWidth, proofTokenCount, proofInputStart,
    proofInputFinish, rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
    gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    gammaBoundarySize, parseCoordinates, combineCoordinates,
    parseSize, combineSize, hparseGraph, hcommonRows,
    hscheduleRows, hbridgeRows⟩

#print axioms compactNumericVerifierOneParseSuccessNonLeafStateGraphDef_spec
#print axioms compactNumericVerifierOneParseSuccessNonLeafStateGraphDef_sigmaZero
#print axioms CompactNumericVerifierOneParseSuccessNonLeafStateGraph.sound
#print axioms exists_compactNumericVerifierOneParseSuccessNonLeafStateGraph_of_transition

end FoundationCompactNumericListedDirectVerifierOneParseSuccessNonLeafStateGraph
