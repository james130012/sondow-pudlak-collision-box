import integration.FoundationCompactNumericListedDirectVerifierParseStateFormula
import integration.FoundationCompactNumericListedDirectVerifierCombineStateGraph
import integration.FoundationCompactNumericListedDirectVerifierHaltedFormula
import integration.FoundationCompactNumericListedDirectVerifierFinishFormula

/-!
# Complete bounded formula for one public verifier step

The 429-column schema reuses the complete parse layout.  Combine occupies the
first 93 columns, while halted and finish reuse the two state-core blocks.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStepFormula

open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierCombineBranchRows
open FoundationCompactNumericListedDirectVerifierCombineStateGraph
open FoundationCompactNumericListedDirectVerifierHaltedFormula
open FoundationCompactNumericListedDirectVerifierFinishFormula
open FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness

def compactNumericVerifierStepCombineRuleWitness
    (proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize targetStart : Nat) :
    CompactNumericVerifierCombineRuleWitness :=
  compactNumericVerifierCombineRuleWitnessOf
    proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
    rootStart rootFinish proofTag proofEndpointBound
    certificateTable certificateWidth certificateTokenCount
    certificateInputStart certificateInputFinish
    axiomStart axiomFinish formulaStart formulaFinish
    suffixStart suffixFinish certificateTag certificateEndpointBound
    rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
    secondFinish secondCount witnessFinish witnessCount suffixCount
    rootGammaBoundarySize targetStart

def CompactNumericVerifierStepGraph
    (stateTable stateWidth stateTokenCount : Nat)
    (currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates)
    (currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness)
    (taskCoordinates : CompactNumericVerifierTaskRowCoordinates)
    (taskSizeWitness : CompactNumericVerifierTaskSizeWitness)
    (proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
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
      ruleTableWidth ruleValueBound : Nat)
    (paCoordinates : CompactNumericVerifierPAAxiomJointLeafCoordinates)
    (firstParseCoordinates secondParseCoordinates combineCoordinates :
      CompactNumericVerifierTaskRowCoordinates)
    (firstParseSize secondParseSize combineSize :
      CompactNumericVerifierTaskSizeWitness) : Prop :=
  (CompactNumericVerifierStateCoreGraph
      stateTable stateWidth stateTokenCount
      currentCoordinates currentSizeWitness ∧
    CompactNumericVerifierStateCoreGraph
      stateTable stateWidth stateTokenCount nextCoordinates nextSizeWitness ∧
    CompactNumericVerifierHaltedRows
      stateTable stateWidth stateTokenCount
      currentCoordinates.start currentCoordinates.finish
      currentCoordinates.statusTag
      nextCoordinates.start nextCoordinates.finish) ∨
  (CompactNumericVerifierStateCoreGraph
      stateTable stateWidth stateTokenCount
      currentCoordinates currentSizeWitness ∧
    CompactNumericVerifierStateCoreGraph
      stateTable stateWidth stateTokenCount nextCoordinates nextSizeWitness ∧
    CompactNumericVerifierFinishRows
      stateTable stateWidth stateTokenCount
      currentCoordinates.start currentCoordinates.valuesFinish
      currentCoordinates.proofCount currentCoordinates.certificateCount
      currentCoordinates.taskCount currentCoordinates.valueCount
      currentCoordinates.valueBoundary currentSizeWitness.valueValueBound
      currentCoordinates.statusTag
      nextCoordinates.start nextCoordinates.valuesFinish
      nextCoordinates.proofCount nextCoordinates.certificateCount
      nextCoordinates.taskCount nextCoordinates.valueCount
      nextCoordinates.statusTag nextCoordinates.statusBool) ∨
  CompactNumericVerifierParseStateGraph
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
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
      ruleTableWidth ruleValueBound paCoordinates
      firstParseCoordinates secondParseCoordinates combineCoordinates
      firstParseSize secondParseSize combineSize ∨
  CompactNumericVerifierCombineStateGraph
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness
      (compactNumericVerifierStepCombineRuleWitness
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize targetStart)

def compactNumericVerifierStepHaltedTerms :
    Fin 8 → Semiterm ℒₒᵣ Empty 429 :=
  ![(#0 : Semiterm ℒₒᵣ Empty 429), #1, #2, #3, #4, #15, #24, #25]

def compactNumericVerifierStepFinishTerms :
    Fin 20 → Semiterm ℒₒᵣ Empty 429 :=
  ![(#0 : Semiterm ℒₒᵣ Empty 429), #1, #2,
    #3, #12, #6, #8, #10, #13, #14, #23, #15,
    #24, #33, #27, #29, #31, #34, #36, #38]

def compactNumericVerifierStepCombineTerms :
    Fin 93 → Semiterm ℒₒᵣ Empty 429 :=
  fun index =>
    (#(Fin.castLE (show 93 ≤ 429 by omega) index) :
      Semiterm ℒₒᵣ Empty 429)

def compactNumericVerifierStepGraphDef :
    𝚺₀.Semisentence 429 := .mkSigma
  (((compactNumericVerifierStateCoreGraphDef.val ⇜
        compactNumericVerifierParseCurrentStateTerms) ⋏
      (compactNumericVerifierStateCoreGraphDef.val ⇜
        compactNumericVerifierParseNextStateTerms) ⋏
      (compactNumericVerifierHaltedRowsDef.val ⇜
        compactNumericVerifierStepHaltedTerms)) ⋎
    ((compactNumericVerifierStateCoreGraphDef.val ⇜
        compactNumericVerifierParseCurrentStateTerms) ⋏
      (compactNumericVerifierStateCoreGraphDef.val ⇜
        compactNumericVerifierParseNextStateTerms) ⋏
      (compactNumericVerifierFinishRowsDef.val ⇜
        compactNumericVerifierStepFinishTerms)) ⋎
    compactNumericVerifierParseStateGraphDef.val ⋎
    (compactNumericVerifierCombineStateGraphDef.val ⇜
      compactNumericVerifierStepCombineTerms)) (by simp)

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
@[simp] theorem compactNumericVerifierStepGraphDef_spec
    (stateTable stateWidth stateTokenCount : Nat)
    (currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates)
    (currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness)
    (taskCoordinates : CompactNumericVerifierTaskRowCoordinates)
    (taskSizeWitness : CompactNumericVerifierTaskSizeWitness)
    (proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
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
      ruleTableWidth ruleValueBound : Nat)
    (paCoordinates : CompactNumericVerifierPAAxiomJointLeafCoordinates)
    (firstParseCoordinates secondParseCoordinates combineCoordinates :
      CompactNumericVerifierTaskRowCoordinates)
    (firstParseSize secondParseSize combineSize :
      CompactNumericVerifierTaskSizeWitness) :
    compactNumericVerifierStepGraphDef.val.Evalb
        (compactNumericVerifierParseStateGraphEnvironment
          stateTable stateWidth stateTokenCount
          currentCoordinates nextCoordinates
          currentSizeWitness nextSizeWitness
          taskCoordinates taskSizeWitness
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound
          rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
          secondFinish secondCount witnessFinish witnessCount suffixCount
          rootGammaBoundarySize
          targetStart targetFinish targetGammaFinish targetGammaCount
          targetGammaBoundary targetBool targetGammaBoundarySize resultBool
          ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
          ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
          ruleGammaBoundarySize
          ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
          ruleFormulaBoundarySize
          ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary
          ruleNegatedCount ruleNegatedBoundarySize
          ruleStateBoundary ruleStateCount
          ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
          ruleTableWidth ruleValueBound paCoordinates
          firstParseCoordinates secondParseCoordinates combineCoordinates
          firstParseSize secondParseSize combineSize) ↔
      CompactNumericVerifierStepGraph
        stateTable stateWidth stateTokenCount
        currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
        taskCoordinates taskSizeWitness
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize
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
        ruleTableWidth ruleValueBound paCoordinates
        firstParseCoordinates secondParseCoordinates combineCoordinates
        firstParseSize secondParseSize combineSize := by
  let env := compactNumericVerifierParseStateGraphEnvironment
    stateTable stateWidth stateTokenCount
    currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
    taskCoordinates taskSizeWitness
    proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
    rootStart rootFinish proofTag proofEndpointBound
    certificateTable certificateWidth certificateTokenCount
    certificateInputStart certificateInputFinish
    axiomStart axiomFinish formulaStart formulaFinish
    suffixStart suffixFinish certificateTag certificateEndpointBound
    rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
    secondFinish secondCount witnessFinish witnessCount suffixCount
    rootGammaBoundarySize
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
    ruleTableWidth ruleValueBound paCoordinates
    firstParseCoordinates secondParseCoordinates combineCoordinates
    firstParseSize secondParseSize combineSize
  change compactNumericVerifierStepGraphDef.val.Evalb env ↔ _
  have hcurrentEnv :
      (Semiterm.val env Empty.elim ∘
        compactNumericVerifierParseCurrentStateTerms) =
        compactNumericVerifierStateCoreFormulaEnvironment
          stateTable stateWidth stateTokenCount
          currentCoordinates.start currentCoordinates.finish
          currentCoordinates.proofFinish currentCoordinates.proofCount
          currentCoordinates.certificateFinish
            currentCoordinates.certificateCount
          currentCoordinates.tasksFinish currentCoordinates.taskCount
          currentCoordinates.taskBoundary currentCoordinates.valuesFinish
          currentCoordinates.valueCount currentCoordinates.valueBoundary
          currentCoordinates.statusTag currentCoordinates.statusPayloadStart
          currentCoordinates.statusBool
          currentSizeWitness.taskBoundarySize
            currentSizeWitness.valueBoundarySize
          currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
          currentSizeWitness.valueTableWidth
            currentSizeWitness.valueValueBound := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hnextEnv :
      (Semiterm.val env Empty.elim ∘
        compactNumericVerifierParseNextStateTerms) =
        compactNumericVerifierStateCoreFormulaEnvironment
          stateTable stateWidth stateTokenCount
          nextCoordinates.start nextCoordinates.finish
          nextCoordinates.proofFinish nextCoordinates.proofCount
          nextCoordinates.certificateFinish nextCoordinates.certificateCount
          nextCoordinates.tasksFinish nextCoordinates.taskCount
          nextCoordinates.taskBoundary nextCoordinates.valuesFinish
          nextCoordinates.valueCount nextCoordinates.valueBoundary
          nextCoordinates.statusTag nextCoordinates.statusPayloadStart
          nextCoordinates.statusBool
          nextSizeWitness.taskBoundarySize nextSizeWitness.valueBoundarySize
          nextSizeWitness.taskTableWidth nextSizeWitness.taskValueBound
          nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hhaltedEnv :
      (Semiterm.val env Empty.elim ∘
        compactNumericVerifierStepHaltedTerms) =
        ![stateTable, stateWidth, stateTokenCount,
          currentCoordinates.start, currentCoordinates.finish,
          currentCoordinates.statusTag,
          nextCoordinates.start, nextCoordinates.finish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hfinishEnv :
      (Semiterm.val env Empty.elim ∘
        compactNumericVerifierStepFinishTerms) =
        ![stateTable, stateWidth, stateTokenCount,
          currentCoordinates.start, currentCoordinates.valuesFinish,
          currentCoordinates.proofCount,
          currentCoordinates.certificateCount,
          currentCoordinates.taskCount, currentCoordinates.valueCount,
          currentCoordinates.valueBoundary,
          currentSizeWitness.valueValueBound,
          currentCoordinates.statusTag,
          nextCoordinates.start, nextCoordinates.valuesFinish,
          nextCoordinates.proofCount, nextCoordinates.certificateCount,
          nextCoordinates.taskCount, nextCoordinates.valueCount,
          nextCoordinates.statusTag, nextCoordinates.statusBool] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcombineEnv :
      (Semiterm.val env Empty.elim ∘
        compactNumericVerifierStepCombineTerms) =
        compactNumericVerifierCombineStateGraphEnvironment
          stateTable stateWidth stateTokenCount
          currentCoordinates.start currentCoordinates.finish
          currentCoordinates.proofFinish currentCoordinates.proofCount
          currentCoordinates.certificateFinish
            currentCoordinates.certificateCount
          currentCoordinates.tasksFinish currentCoordinates.taskCount
          currentCoordinates.taskBoundary currentCoordinates.valuesFinish
          currentCoordinates.valueCount currentCoordinates.valueBoundary
          currentCoordinates.statusTag currentCoordinates.statusPayloadStart
          currentCoordinates.statusBool
          currentSizeWitness.taskBoundarySize
            currentSizeWitness.valueBoundarySize
          currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
          currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
          nextCoordinates.start nextCoordinates.finish
          nextCoordinates.proofFinish nextCoordinates.proofCount
          nextCoordinates.certificateFinish nextCoordinates.certificateCount
          nextCoordinates.tasksFinish nextCoordinates.taskCount
          nextCoordinates.taskBoundary nextCoordinates.valuesFinish
          nextCoordinates.valueCount nextCoordinates.valueBoundary
          nextCoordinates.statusTag nextCoordinates.statusPayloadStart
          nextCoordinates.statusBool
          nextSizeWitness.taskBoundarySize nextSizeWitness.valueBoundarySize
          nextSizeWitness.taskTableWidth nextSizeWitness.taskValueBound
          nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound
          taskCoordinates.start taskCoordinates.finish taskCoordinates.tag
          taskCoordinates.gammaFinish taskCoordinates.gammaCount
          taskCoordinates.gammaBoundary taskCoordinates.firstFinish
          taskCoordinates.firstCount taskCoordinates.secondFinish
          taskCoordinates.secondCount taskCoordinates.witnessFinish
          taskCoordinates.witnessCount taskCoordinates.suffixCount
          taskSizeWitness.gammaBoundarySize
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound
          rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
          secondFinish secondCount witnessFinish witnessCount suffixCount
          rootGammaBoundarySize targetStart := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierStepGraphDef,
    CompactNumericVerifierStepGraph, Semiformula.eval_substs,
    compactNumericVerifierStateRowCoordinatesOf,
    compactNumericVerifierTaskRowCoordinatesOf,
    compactNumericVerifierStepCombineRuleWitness,
    compactNumericVerifierCombineRuleWitnessOf,
    env, hcurrentEnv, hnextEnv, hhaltedEnv, hfinishEnv, hcombineEnv]

set_option maxRecDepth 65536 in
theorem compactNumericVerifierStepGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierStepGraphDef.val := by
  simp [compactNumericVerifierStepGraphDef]

#print axioms compactNumericVerifierStepGraphDef_spec
#print axioms compactNumericVerifierStepGraphDef_sigmaZero

end FoundationCompactNumericListedDirectVerifierStepFormula
