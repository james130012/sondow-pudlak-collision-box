import integration.FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportGraph
import integration.FoundationCompactNumericListedDirectVerifierClosedLeafParsedRuleGraph

/-!
# Same-object parsed closed-leaf state graph

The successful parser transport and the independently checked closed-rule table
share the exposed proof root through bounded cross-table equalities.  The graph
therefore records one parsed object, one rule result, and the exact state output.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

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
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectVerifierStepCases
open FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportGraph
open FoundationCompactNumericListedDirectVerifierClosedLeafParsedRuleGraph
open FoundationCompactNumericListedDirectVerifierClosedLeafRuleSelfContainedGraph
open FoundationCompactNumericListedDirectVerifierClosedLeafCrossTableBridgeGraph
open FoundationCompactNumericListedDirectProofRootLeafFieldSemantics
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactSyntaxTokenMachine

def CompactNumericVerifierClosedLeafStateGraph
    (stateTable stateWidth stateTokenCount
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
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
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
      ruleTableWidth ruleValueBound : Nat) : Prop :=
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
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool ∧
    CompactNumericVerifierClosedLeafParsedRuleGraph
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
      rootGammaBoundarySize resultBool
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound

def compactNumericVerifierClosedLeafStateGraphDef :
    𝚺₀.Semisentence 96 := .mkSigma
  “stateTable stateWidth stateTokenCount
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
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
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
      ruleTableWidth ruleValueBound.
    !(compactNumericVerifierLeafParseSuccessTransportGraphDef)
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
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool ∧
    !(compactNumericVerifierClosedLeafParsedRuleGraphDef)
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
      rootGammaBoundarySize resultBool
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound”

def compactNumericVerifierClosedLeafStateGraphEnvironment
    (stateTable stateWidth stateTokenCount
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
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
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
      ruleTableWidth ruleValueBound : Nat) : Fin 96 → Nat :=
  ![stateTable, stateWidth, stateTokenCount,
    stateProofStart, stateProofFinish, stateCertificateStart, stateCertificateFinish,
    proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
    rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
    rootGammaFinish, rootGammaCount, rootGammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    rootGammaBoundarySize,
    sourceTaskBoundary, sourceTaskCount, targetTaskBoundary, targetTaskCount,
    sourceValueBoundary, sourceValueCount, targetValueBoundary, targetValueCount,
    currentTaskTableWidth, currentTaskValueBound,
    currentValueTableWidth, currentValueValueBound,
    nextTaskTableWidth, nextTaskValueBound,
    nextValueTableWidth, nextValueValueBound,
    nextStart, nextProofFinish, nextCertificateFinish, nextStatusTag,
    targetStart, targetFinish, targetGammaFinish, targetGammaCount,
    targetGammaBoundary, targetBool, targetGammaBoundarySize, resultBool,
    ruleTable, ruleWidth, ruleTokenCount, ruleProofTag, ruleCertificateTag,
    ruleGammaStart, ruleGammaFinish, ruleGammaBoundary, ruleGammaCount,
    ruleGammaBoundarySize,
    ruleFormulaStart, ruleFormulaFinish, ruleFormulaBoundary, ruleFormulaCount,
    ruleFormulaBoundarySize,
    ruleNegatedStart, ruleNegatedFinish, ruleNegatedBoundary, ruleNegatedCount,
    ruleNegatedBoundarySize, ruleStateBoundary, ruleStateCount,
    ruleEmptyStart, ruleEmptyFinish, ruleEmptyBoundary, ruleEmptyBoundarySize,
    ruleTableWidth, ruleValueBound]

set_option maxRecDepth 65536 in
@[simp] theorem compactNumericVerifierClosedLeafStateGraphDef_spec
    (stateTable stateWidth stateTokenCount
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
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
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
      ruleTableWidth ruleValueBound : Nat) :
    compactNumericVerifierClosedLeafStateGraphDef.val.Evalb
        (compactNumericVerifierClosedLeafStateGraphEnvironment
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
          sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
          sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
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
          ruleTableWidth ruleValueBound) ↔
      CompactNumericVerifierClosedLeafStateGraph
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
        sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
        sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
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
        ruleTableWidth ruleValueBound := by
  let env := compactNumericVerifierClosedLeafStateGraphEnvironment
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
    sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
    sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
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
    ruleTableWidth ruleValueBound
  change compactNumericVerifierClosedLeafStateGraphDef.val.Evalb env ↔ _
  have htransportEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 96), #1, #2, #3, #4, #5, #6,
          #7, #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
          #19, #20, #21, #22, #23, #24, #25, #26, #27, #28, #29,
          #30, #31, #32, #33, #34, #35, #36, #37, #38, #39, #40,
          #41, #42, #43, #44, #45, #46, #47, #48, #49, #50, #51,
          #52, #53, #54, #55, #56, #57, #58, #59, #60, #61, #62,
          #63, #64, #65, #66, #67]) =
        compactNumericVerifierLeafParseSuccessTransportGraphEnvironment
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
          sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
          sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
          currentTaskTableWidth currentTaskValueBound
          currentValueTableWidth currentValueValueBound
          nextTaskTableWidth nextTaskValueBound
          nextValueTableWidth nextValueValueBound
          nextStart nextProofFinish nextCertificateFinish nextStatusTag
          targetStart targetFinish targetGammaFinish targetGammaCount
          targetGammaBoundary targetBool targetGammaBoundarySize resultBool := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htransport := compactNumericVerifierLeafParseSuccessTransportGraphDef_spec
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
    sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
    sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
    currentTaskTableWidth currentTaskValueBound
    currentValueTableWidth currentValueValueBound
    nextTaskTableWidth nextTaskValueBound
    nextValueTableWidth nextValueValueBound
    nextStart nextProofFinish nextCertificateFinish nextStatusTag
    targetStart targetFinish targetGammaFinish targetGammaCount
    targetGammaBoundary targetBool targetGammaBoundarySize resultBool
  have hclosedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 96), #1, #2, #3, #4, #5, #6,
          #7, #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
          #19, #20, #21, #22, #23, #24, #25, #26, #27, #28, #29,
          #30, #31, #32, #33, #34, #35, #36, #37, #38, #39, #67,
          #68, #69, #70, #71, #72, #73, #74, #75, #76, #77, #78,
          #79, #80, #81, #82, #83, #84, #85, #86, #87, #88, #89,
          #90, #91, #92, #93, #94, #95]) =
        compactNumericVerifierClosedLeafParsedRuleGraphEnvironment
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
          rootGammaBoundarySize resultBool
          ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
          ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
          ruleGammaBoundarySize
          ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
          ruleFormulaBoundarySize
          ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
          ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
          ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
          ruleTableWidth ruleValueBound := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hclosed := compactNumericVerifierClosedLeafParsedRuleGraphDef_spec
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
    rootGammaBoundarySize resultBool
    ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
    ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
    ruleGammaBoundarySize
    ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
    ruleFormulaBoundarySize
    ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
    ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
    ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
    ruleTableWidth ruleValueBound
  simp only [compactNumericVerifierClosedLeafStateGraphDef,
    CompactNumericVerifierClosedLeafStateGraph]
  apply and_congr
  · refine (Semiformula.eval_substs (b := env) (f := Empty.elim)
      ![(#0 : Semiterm ℒₒᵣ Empty 96), #1, #2, #3, #4, #5, #6,
        #7, #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
        #19, #20, #21, #22, #23, #24, #25, #26, #27, #28, #29,
        #30, #31, #32, #33, #34, #35, #36, #37, #38, #39, #40,
        #41, #42, #43, #44, #45, #46, #47, #48, #49, #50, #51,
        #52, #53, #54, #55, #56, #57, #58, #59, #60, #61, #62,
        #63, #64, #65, #66, #67]
      compactNumericVerifierLeafParseSuccessTransportGraphDef.val).trans ?_
    rw [htransportEnv]
    exact htransport
  · refine (Semiformula.eval_substs (b := env) (f := Empty.elim)
      ![(#0 : Semiterm ℒₒᵣ Empty 96), #1, #2, #3, #4, #5, #6,
        #7, #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
        #19, #20, #21, #22, #23, #24, #25, #26, #27, #28, #29,
        #30, #31, #32, #33, #34, #35, #36, #37, #38, #39, #67,
        #68, #69, #70, #71, #72, #73, #74, #75, #76, #77, #78,
        #79, #80, #81, #82, #83, #84, #85, #86, #87, #88, #89,
        #90, #91, #92, #93, #94, #95]
      compactNumericVerifierClosedLeafParsedRuleGraphDef.val).trans ?_
    rw [hclosedEnv]
    exact hclosed

theorem compactNumericVerifierClosedLeafStateGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierClosedLeafStateGraphDef.val := by
  simp [compactNumericVerifierClosedLeafStateGraphDef]

theorem CompactNumericVerifierClosedLeafStateGraph.sound
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
      stateTable stateWidth stateTokenCount stateProofStart stateProofFinish proofTokens)
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
    resultBool = compactAdditiveBoolTag
      (compactClosedRuleCheck (rootGamma, rootFormula)) ∧
    proofTag = 0 ∧ certificateTag = 0 ∧
    (∃ parsed, compactNumericParsePayload
      ((proofTokens, certificateTokens), (sourceTasks.drop 1, sourceValues)) =
        some parsed) ∧
      nextProof = proofSuffix ∧
      nextCertificate = certificateSuffix ∧
      targetTasks = sourceTasks.drop 1 ∧
      targetValues =
        (rootGamma, compactClosedRuleCheck (rootGamma, rootFormula)) ::
          sourceValues ∧
      nextTaskTableWidth = currentTaskTableWidth ∧
      nextTaskValueBound = currentTaskValueBound ∧
      nextValueTableWidth = currentValueTableWidth ∧
      nextValueValueBound = currentValueValueBound ∧
      nextStatusTag = 0 := by
  have hclosed := hgraph.2
  rcases CompactNumericVerifierClosedLeafRuleSelfContainedGraph.sound
      hclosed.2.1 with
    ⟨ruleGamma, ruleFormula, _ruleNegated, _ruleEmpty,
      _hruleGammaLength, _hruleFormulaLength, _hruleNegatedLength,
      _hruleEmpty, hruleGammaLayout, _hruleGammaRows,
      hruleFormulaLayout, _hruleFormulaRows,
      _hruleNegatedLayout, _hruleNegatedRows,
      _hruleEmptyLayout, _hruleEmptyRows,
      hruleProofTag, hruleCertificateTag, hruleResult⟩
  have hproofTagZero : proofTag = 0 :=
    hclosed.2.2.1.trans hruleProofTag
  have hcertificateTagZero : certificateTag = 0 :=
    hclosed.2.2.2.1.trans hruleCertificateTag
  have hcore := hclosed.1.2
  rcases CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
      hcore with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag, _hrealizedGammaRows,
      _hrealizedGammaLength, _hrealizedFirst, _hrealizedFirstLength,
      hfieldSecond, _hfieldSecondLength, hfieldWitness,
      _hfieldWitnessLength, hfieldSuffix, _hfieldSuffixLength⟩
  let actualRoot : CompactNumericVerifierTask :=
    (proofTag, (rootGamma, (rootFormula,
      (realizedRoot.2.2.2.1,
        (realizedRoot.2.2.2.2.1, realizedRoot.2.2.2.2.2)))))
  rcases hcore with
    ⟨htag, hgammaLayout, hgammaRows, hgammaSizeEq, hgammaSize,
      hfirst, hsecond, hwitness, hsuffix⟩
  have hactualFields : CompactNumericNodeFieldsDirectLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) rootFinish actualRoot.2 := by
    refine ⟨rootGammaFinish, firstFinish, secondFinish, witnessFinish,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [actualRoot] using hrootGamma
    · simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using
        hrootFormula
    · simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using
        hfieldSecond
    · simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using
        hfieldWitness
    · simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using
        hfieldSuffix
  have hactualRoot : CompactNumericVerifierTaskDirectLayout
      proofTable proofWidth proofTokenCount rootStart rootFinish actualRoot :=
    ⟨rootStart + 1, by
      simpa [actualRoot, compactNumericVerifierTaskRowCoordinatesOf] using htag,
      hactualFields⟩
  have hrootEq : realizedRoot = actualRoot :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      (show CompactNumericVerifierTaskCoreGraph
        proofTable proofWidth proofTokenCount
        (compactNumericVerifierTaskRowCoordinatesOf
          rootStart rootFinish proofTag rootGammaFinish rootGammaCount
          rootGammaBoundary firstFinish firstCount secondFinish secondCount
          witnessFinish witnessCount suffixCount)
        { gammaBoundarySize := rootGammaBoundarySize } from
        ⟨htag, hgammaLayout, hgammaRows, hgammaSizeEq, hgammaSize,
          hfirst, hsecond, hwitness, hsuffix⟩)
      hactualRoot hrealizedRoot
  have hsuccess := hclosed.1
  rcases hsuccess.1.2.2.1.sound with
    ⟨decodedProofTokens, decodedRoot, hdecodedProofLayout,
      hdecodedRootLayout, hdecodedProof, hdecodedTag⟩
  have hdecodedProofTokensEq : decodedProofTokens = proofTokens :=
    hsuccess.1.1.natListValues_eq hproofLayout hdecodedProofLayout
  subst decodedProofTokens
  have hdecodedRootEq : decodedRoot = realizedRoot :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      (show CompactNumericVerifierTaskCoreGraph
        proofTable proofWidth proofTokenCount
        (compactNumericVerifierTaskRowCoordinatesOf
          rootStart rootFinish proofTag rootGammaFinish rootGammaCount
          rootGammaBoundary firstFinish firstCount secondFinish secondCount
          witnessFinish witnessCount suffixCount)
        { gammaBoundarySize := rootGammaBoundarySize } from
        ⟨htag, hgammaLayout, hgammaRows, hgammaSizeEq, hgammaSize,
          hfirst, hsecond, hwitness, hsuffix⟩)
      hrealizedRoot hdecodedRootLayout
  have hdecodedTagZero : decodedRoot.1 = 0 :=
    hdecodedTag.trans hproofTagZero
  rcases compactListedProofNodeFieldsParser_tag_zero_firstFormula
      hdecodedProof hdecodedTagZero with
    ⟨parsedFormula, hdecodedFormula⟩
  have hrootFormulaParsed :
      rootFormula = compactArithmeticFormulaTokens parsedFormula := by
    have hdecodedFormulaValue : decodedRoot.2.2.1 = rootFormula := by
      rw [hdecodedRootEq, hrootEq]
    exact hdecodedFormulaValue.symm.trans hdecodedFormula
  rcases CompactNumericVerifierClosedLeafCrossTableBridgeGraph.sound
      hclosed.2.2.2.2 hrootGamma hruleGammaLayout
        hrootFormula hruleFormulaLayout with
    ⟨hruleGammaEq, hruleFormulaEq⟩
  have hresultRule := hruleResult
    ⟨parsedFormula, hruleFormulaEq.trans hrootFormulaParsed⟩
  have hresult : resultBool = compactAdditiveBoolTag
      (compactClosedRuleCheck (rootGamma, rootFormula)) := by
    simpa [hruleGammaEq, hruleFormulaEq] using hresultRule
  refine ⟨hresult, hproofTagZero, hcertificateTagZero, ?_⟩
  have htransport : CompactNumericVerifierLeafParseSuccessTransportGraph
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
      (compactAdditiveBoolTag
        (compactClosedRuleCheck (rootGamma, rootFormula))) := by
    simpa [hresult] using hgraph.1
  exact CompactNumericVerifierLeafParseSuccessTransportGraph.sound htransport
    hproofLayout hcertificateLayout hproofSuffix hcertificateSuffix hrootGamma
    hnextProof hnextCertificate hsourceTaskRows htargetTaskRows hsourceValueRows
    htargetValueRows

theorem exists_compactNumericVerifierClosedLeafStateGraph_of_success_and_transition
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      sourceTaskBoundary targetTaskBoundary sourceValueBoundary targetValueBoundary
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
      stateTable stateWidth stateTokenCount stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens = some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser certificateTokens =
      some certificateNode)
    (hproofTag : proofNode.1 = 0)
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
    ∃ rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize,
    ∃ targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize,
    ∃ ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag,
    ∃ ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize,
    ∃ ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize,
    ∃ ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount,
    ∃ ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound,
      CompactNumericVerifierClosedLeafStateGraph
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
        (compactAdditiveBoolTag
          (compactClosedRuleCheck (proofNode.2.1, proofNode.2.2.1)))
        ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
        ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
        ruleGammaBoundarySize
        ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
        ruleFormulaBoundarySize
        ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
        ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
        ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
        ruleTableWidth ruleValueBound := by
  have houtputCase :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode (sourceTasks.drop 1) sourceValues
      ((nextProof, nextCertificate), (targetTasks, targetValues))).1 htransition
  have hclosedOutput :
      certificateNode.1 = 0 ∧
      ((proofNode.2.2.2.2.2, certificateNode.2.2),
        (sourceTasks.drop 1,
          (proofNode.2.1,
            compactClosedRuleCheck (proofNode.2.1, proofNode.2.2.1)) ::
              sourceValues)) =
        ((nextProof, nextCertificate), (targetTasks, targetValues)) := by
    simpa [CompactNumericNodeTransitionOutputCase, hproofTag,
      compactNumericNodeFieldsSuffix] using houtputCase
  rcases hclosedOutput with ⟨_hcertificateNodeTag, houtput⟩
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
      (proofNode.2.1,
        compactClosedRuleCheck (proofNode.2.1, proofNode.2.2.1)) ::
          sourceValues := by
    have h := congrArg (fun output : CompactNumericRunningPayload => output.2.2)
      houtput
    simpa using h.symm
  rcases exists_compactNumericVerifierLeafParseSuccessTransportGraph_of_success_and_transition
      hproofLayout hcertificateLayout hproofParser hcertificateParser htransition
      rfl rfl rfl hnextProof hnextCertificate hsourceTaskRows htargetTaskRows
      hsourceValueRows htargetValueRows hsourceTaskGraph htargetTaskGraph
      hsourceValueGraph htargetValueGraph hsourceTaskNonempty htasks hvalues
      hnextProofValue hnextCertificateValue htaskTableWidth htaskValueBound
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
      targetGammaBoundary, targetBool, targetGammaBoundarySize, htransport⟩
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
  have hproofTagCoord : proofTag = 0 := hdecodedTag.symm.trans hproofTag
  have hcoordTagMatch := hsuccess.1.2.2.2.2
  have hcertificateTagCoord : certificateTag = 0 := by
    rw [hproofTagCoord] at hcoordTagMatch
    simpa [CompactNumericNodeTransitionTagMatch] using hcoordTagMatch
  rcases CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
      hsuccess.2 with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag,
      hgammaRows, hgammaLength, hfirstLayout, _hfirstLength,
      _hsecondLayout, _hsecondLength, _hwitnessLayout, _hwitnessLength,
      _hsuffixLayout, _hsuffixLength⟩
  have hrealizedRootEq : realizedRoot = proofNode :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hsuccess.2 hdecodedRootLayout hrealizedRoot
  subst realizedRoot
  rcases compactListedProofNodeFieldsParser_tag_zero_firstFormula
      hproofParser hproofTag with ⟨parsedFormula, hparsedFormula⟩
  have hcoreSaved := hsuccess.2
  rcases hcoreSaved with
    ⟨_hrootTagCell, hgammaStructureRaw, _hgammaRowsRaw,
      hgammaSizeEqRaw, hgammaSizeRaw,
      _hfirstSlice, _hsecondSlice, _hwitnessSlice, _hsuffixSlice⟩
  have hgammaLength' : proofNode.2.1.length = rootGammaCount := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using hgammaLength
  have hgammaStructure : CompactAdditiveStructuredListLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) proofNode.2.1.length
        rootGammaFinish rootGammaBoundary := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf, hgammaLength'] using
      hgammaStructureRaw
  have hgammaSizeEq : rootGammaBoundarySize = Nat.size rootGammaBoundary := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using hgammaSizeEqRaw
  have hgammaSize :
      rootGammaBoundarySize ≤ (rootGammaCount + 1) * proofTokenCount := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using hgammaSizeRaw
  have hgammaBoundaryBound : Nat.size rootGammaBoundary ≤
      (proofNode.2.1.length + 1) * proofTokenCount := by
    rw [hgammaLength', ← hgammaSizeEq]
    exact hgammaSize
  have hrootGammaLayout : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) rootGammaFinish proofNode.2.1 :=
    ⟨rootGammaBoundary, hgammaStructure, hgammaRows, hgammaBoundaryBound⟩
  have hrootFormulaLayout : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount rootGammaFinish firstFinish
        (compactArithmeticFormulaTokens parsedFormula) := by
    simpa [hparsedFormula, compactNumericVerifierTaskRowCoordinatesOf] using
      hfirstLayout
  rcases exists_closedRuleTable_with_rootLayouts proofNode.2.1 parsedFormula with
    ⟨ruleTable, ruleWidth, ruleTokenCount,
      ruleGammaStart, ruleGammaFinish, ruleGammaBoundary,
      ruleGammaBoundarySize,
      ruleFormulaStart, ruleFormulaFinish, ruleFormulaBoundary,
      ruleFormulaBoundarySize,
      ruleNegatedStart, ruleNegatedFinish, ruleNegatedBoundary,
      ruleNegatedBoundarySize, ruleStateBoundary,
      ruleEmptyStart, ruleEmptyFinish, ruleEmptyBoundary,
      ruleEmptyBoundarySize, ruleTableWidth, ruleValueBound,
      hrule, hruleGammaLayout, hruleFormulaLayout⟩
  have hbridge :=
    CompactNumericVerifierClosedLeafCrossTableBridgeGraph.of_layouts
      hrootGammaLayout hruleGammaLayout
      hrootFormulaLayout hruleFormulaLayout
  have hrule' : CompactNumericVerifierClosedLeafRuleSelfContainedGraph
      ruleTable ruleWidth ruleTokenCount 0 0
      ruleGammaStart ruleGammaFinish ruleGammaBoundary proofNode.2.1.length
        ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary
        proofNode.2.2.1.length ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary
        (compactArithmeticFormulaTokens (∼parsedFormula)).length
        ruleNegatedBoundarySize
      ruleStateBoundary (compactSyntaxRunFuelBound proofNode.2.2.1 + 1)
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound
      (compactAdditiveBoolTag
        (compactClosedRuleCheck (proofNode.2.1, proofNode.2.2.1))) := by
    simpa [hparsedFormula] using hrule
  have hclosed : CompactNumericVerifierClosedLeafParsedRuleGraph
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
      (compactAdditiveBoolTag
        (compactClosedRuleCheck (proofNode.2.1, proofNode.2.2.1)))
      ruleTable ruleWidth ruleTokenCount 0 0
      ruleGammaStart ruleGammaFinish ruleGammaBoundary proofNode.2.1.length
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary
        proofNode.2.2.1.length ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary
        (compactArithmeticFormulaTokens (∼parsedFormula)).length
      ruleNegatedBoundarySize
      ruleStateBoundary (compactSyntaxRunFuelBound proofNode.2.2.1 + 1)
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound :=
    ⟨hsuccess, hrule', hproofTagCoord, hcertificateTagCoord, hbridge⟩
  exact ⟨proofTable, proofWidth, proofTokenCount, proofInputStart,
    proofInputFinish, rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
    rootGammaFinish, rootGammaCount, rootGammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    rootGammaBoundarySize,
    targetStart, targetFinish, targetGammaFinish, targetGammaCount,
    targetGammaBoundary, targetBool, targetGammaBoundarySize,
    ruleTable, ruleWidth, ruleTokenCount, 0, 0,
    ruleGammaStart, ruleGammaFinish, ruleGammaBoundary, proofNode.2.1.length,
    ruleGammaBoundarySize,
    ruleFormulaStart, ruleFormulaFinish, ruleFormulaBoundary,
    proofNode.2.2.1.length, ruleFormulaBoundarySize,
    ruleNegatedStart, ruleNegatedFinish, ruleNegatedBoundary,
    (compactArithmeticFormulaTokens (∼parsedFormula)).length,
    ruleNegatedBoundarySize, ruleStateBoundary,
    compactSyntaxRunFuelBound proofNode.2.2.1 + 1,
    ruleEmptyStart, ruleEmptyFinish, ruleEmptyBoundary,
    ruleEmptyBoundarySize, ruleTableWidth, ruleValueBound,
    htransport, hclosed⟩

#print axioms compactNumericVerifierClosedLeafStateGraphDef_spec
#print axioms compactNumericVerifierClosedLeafStateGraphDef_sigmaZero
#print axioms CompactNumericVerifierClosedLeafStateGraph.sound
#print axioms exists_compactNumericVerifierClosedLeafStateGraph_of_success_and_transition

end FoundationCompactNumericListedDirectVerifierClosedLeafStateGraph
