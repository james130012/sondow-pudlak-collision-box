import integration.FoundationCompactNumericListedDirectVerifierStepFormula
import integration.FoundationCompactNumericListedDirectVerifierHaltedExactness
import integration.FoundationCompactNumericListedDirectVerifierFinishExactness
import integration.FoundationCompactNumericListedDirectVerifierParseStateExactness

/-!
# Exact semantic realization of the complete verifier-step graph

Every satisfying assignment of the 429-column bounded graph belongs to one of
the four executable verifier branches and therefore realizes one public step.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStepExactness

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierHaltedExactness
open FoundationCompactNumericListedDirectVerifierFinishExactness
open FoundationCompactNumericListedDirectVerifierParseStateExactness
open FoundationCompactNumericListedDirectVerifierCombineStateGraph

theorem CompactNumericVerifierStepGraph.realizeExactStep
    {stateTable stateWidth stateTokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
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
      ruleTableWidth ruleValueBound : Nat}
    {paCoordinates : CompactNumericVerifierPAAxiomJointLeafCoordinates}
    {firstParseCoordinates secondParseCoordinates combineCoordinates :
      CompactNumericVerifierTaskRowCoordinates}
    {firstParseSize secondParseSize combineSize :
      CompactNumericVerifierTaskSizeWitness}
    (hgraph : CompactNumericVerifierStepGraph
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
      firstParseSize secondParseSize combineSize) :
    ∃ currentState nextState : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
        stateTable stateWidth stateTokenCount currentCoordinates.start
          currentCoordinates.finish currentState ∧
      CompactNumericVerifierStateDirectLayout
        stateTable stateWidth stateTokenCount nextCoordinates.start
          nextCoordinates.finish nextState ∧
      nextState = compactNumericVerifierStep currentState := by
  rcases hgraph with hhalted | hfinish | hparse | hcombine
  · exact CompactNumericVerifierHaltedRows.realizeExactStep
      hhalted.1 hhalted.2.1 hhalted.2.2
  · exact CompactNumericVerifierFinishRows.realizeExactStep
      hfinish.1 hfinish.2.1 hfinish.2.2
  · exact CompactNumericVerifierParseStateGraph.realizeExactStep hparse
  · exact CompactNumericVerifierCombineStateGraph.realizeExactStep hcombine

#print axioms CompactNumericVerifierStepGraph.realizeExactStep

end FoundationCompactNumericListedDirectVerifierStepExactness
