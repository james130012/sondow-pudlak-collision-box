import integration.FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateGraph
import integration.FoundationCompactNumericListedDirectVerifierVerumLeafStateGraph
import integration.FoundationCompactNumericListedDirectVerifierClosedLeafStateGraph
import integration.FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraph
import integration.FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateGraph
import integration.FoundationCompactNumericListedDirectVerifierStateFormula
import integration.FoundationCompactNumericListedDirectVerifierTaskFormula
import integration.FoundationCompactNumericListedDirectVerifierParseStateFrameRows
import integration.FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula

/-!
# Complete bounded formula for verifier parse-state transitions

The 429 coordinates keep every branch-local witness block disjoint.  The
failure branch occupies the common 81-coordinate prefix.  Successful branches
share the state, head, parser, parsed-root, and leaf-output coordinates, then
use independent Closed, PA, and non-leaf schedule tails.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseStateFormula

open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierParseStateFrameRows
open FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateGraph
open FoundationCompactNumericListedDirectVerifierVerumLeafStateGraph
open FoundationCompactNumericListedDirectVerifierClosedLeafStateGraph
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraph
open FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateGraph
open FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness
open FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateCoordinates

def CompactNumericVerifierParseSuccessStateGraph
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
  CompactNumericVerifierStateCoreGraph
      stateTable stateWidth stateTokenCount
      currentCoordinates currentSizeWitness ∧
    CompactNumericVerifierStateCoreGraph
      stateTable stateWidth stateTokenCount
      nextCoordinates nextSizeWitness ∧
    CompactNumericVerifierTaskBoundedHead
      stateTable stateWidth stateTokenCount
      currentCoordinates.taskBoundary currentSizeWitness.taskValueBound
      taskCoordinates taskSizeWitness ∧
    CompactNumericVerifierParseStateFrameRows
      currentCoordinates.taskCount currentCoordinates.statusTag
      taskCoordinates ∧
    (CompactNumericVerifierVerumLeafStateGraph
        stateTable stateWidth stateTokenCount
        currentCoordinates.start currentCoordinates.proofFinish
          currentCoordinates.proofFinish currentCoordinates.certificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize
        currentCoordinates.taskBoundary currentCoordinates.taskCount
        nextCoordinates.taskBoundary nextCoordinates.taskCount
        currentCoordinates.valueBoundary currentCoordinates.valueCount
        nextCoordinates.valueBoundary nextCoordinates.valueCount
        currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
        currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
        nextSizeWitness.taskTableWidth nextSizeWitness.taskValueBound
        nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound
        nextCoordinates.start nextCoordinates.proofFinish
        nextCoordinates.certificateFinish nextCoordinates.statusTag
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBool targetGammaBoundarySize resultBool ∨
      CompactNumericVerifierClosedLeafStateGraph
        stateTable stateWidth stateTokenCount
        currentCoordinates.start currentCoordinates.proofFinish
          currentCoordinates.proofFinish currentCoordinates.certificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize
        currentCoordinates.taskBoundary currentCoordinates.taskCount
        nextCoordinates.taskBoundary nextCoordinates.taskCount
        currentCoordinates.valueBoundary currentCoordinates.valueCount
        nextCoordinates.valueBoundary nextCoordinates.valueCount
        currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
        currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
        nextSizeWitness.taskTableWidth nextSizeWitness.taskValueBound
        nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound
        nextCoordinates.start nextCoordinates.proofFinish
        nextCoordinates.certificateFinish nextCoordinates.statusTag
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
        ruleTableWidth ruleValueBound ∨
      CompactNumericVerifierPAAxiomLeafStateGraph
        stateTable stateWidth stateTokenCount
        currentCoordinates.start currentCoordinates.proofFinish
          currentCoordinates.proofFinish currentCoordinates.certificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize
        currentCoordinates.taskBoundary currentCoordinates.taskCount
        nextCoordinates.taskBoundary nextCoordinates.taskCount
        currentCoordinates.valueBoundary currentCoordinates.valueCount
        nextCoordinates.valueBoundary nextCoordinates.valueCount
        currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
        currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
        nextSizeWitness.taskTableWidth nextSizeWitness.taskValueBound
        nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound
        nextCoordinates.start nextCoordinates.proofFinish
        nextCoordinates.certificateFinish nextCoordinates.statusTag
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBool targetGammaBoundarySize resultBool
        paCoordinates ∨
      CompactNumericVerifierParseSuccessNonLeafStateGraph
        stateTable stateWidth stateTokenCount
        currentCoordinates.start currentCoordinates.proofFinish
          currentCoordinates.proofFinish currentCoordinates.certificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize
        currentCoordinates.taskBoundary currentCoordinates.taskCount
        nextCoordinates.taskBoundary nextCoordinates.taskCount
        currentCoordinates.valueBoundary currentCoordinates.valueCount
        nextCoordinates.valueBoundary nextCoordinates.valueCount
        currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
        currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
        nextSizeWitness.taskTableWidth nextSizeWitness.taskValueBound
        nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound
        nextCoordinates.start nextCoordinates.proofFinish
        nextCoordinates.certificateFinish nextCoordinates.statusTag
        firstParseCoordinates secondParseCoordinates combineCoordinates
        firstParseSize secondParseSize combineSize)

def CompactNumericVerifierParseStateGraph
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
  CompactNumericVerifierParseFailureSeparatedTablesStateGraph
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound ∨
    CompactNumericVerifierParseSuccessStateGraph
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

def compactNumericVerifierParseFailureTerms :
    Fin 81 → Semiterm ℒₒᵣ Empty 429 :=
  fun index =>
    (#(Fin.castLE (show 81 ≤ 429 by omega) index) :
      Semiterm ℒₒᵣ Empty 429)

def compactNumericVerifierParseCurrentStateTerms :
    Fin 24 → Semiterm ℒₒᵣ Empty 429 :=
  ![(#0 : Semiterm ℒₒᵣ Empty 429), #1, #2, #3, #4, #5, #6,
    #7, #8, #9, #10, #11, #12, #13, #14, #15, #16, #17,
    #18, #19, #20, #21, #22, #23]

def compactNumericVerifierParseNextStateTerms :
    Fin 24 → Semiterm ℒₒᵣ Empty 429 :=
  ![(#0 : Semiterm ℒₒᵣ Empty 429), #1, #2, #24, #25, #26,
    #27, #28, #29, #30, #31, #32, #33, #34, #35, #36,
    #37, #38, #39, #40, #41, #42, #43, #44]

def compactNumericVerifierParseHeadTerms :
    Fin 19 → Semiterm ℒₒᵣ Empty 429 :=
  ![(#0 : Semiterm ℒₒᵣ Empty 429), #1, #2, #11, #21,
    #45, #46, #47, #48, #49, #50, #51, #52, #53, #54,
    #55, #56, #57, #58]

def compactNumericVerifierParseFrameTerms :
    Fin 8 → Semiterm ℒₒᵣ Empty 429 :=
  ![(#10 : Semiterm ℒₒᵣ Empty 429), #15, #47, #49,
    #52, #54, #56, #57]

def compactNumericVerifierParseSuccessCommonTerms :
    Fin 60 → Semiterm ℒₒᵣ Empty 429 :=
  ![(#0 : Semiterm ℒₒᵣ Empty 429), #1, #2, #3, #5, #5, #7,
    #59, #60, #61, #62, #63, #64, #65, #66, #67, #68,
    #69, #70, #71, #72, #73, #74, #75, #76, #77, #78,
    #79, #80,
    #81, #82, #83, #84, #85, #86, #87, #88, #89, #90, #91,
    #11, #10, #32, #31, #14, #13, #35, #34,
    #20, #21, #22, #23, #41, #42, #43, #44,
    #24, #26, #28, #36]

def compactNumericVerifierParseLeafOutputTerms :
    Fin 8 → Semiterm ℒₒᵣ Empty 429 :=
  ![(#92 : Semiterm ℒₒᵣ Empty 429), #93, #94, #95,
    #96, #97, #98, #99]

def compactNumericVerifierParseClosedExtraTerms :
    Fin 28 → Semiterm ℒₒᵣ Empty 429 :=
  ![(#100 : Semiterm ℒₒᵣ Empty 429), #101, #102, #103, #104,
    #105, #106, #107, #108, #109,
    #110, #111, #112, #113, #114,
    #115, #116, #117, #118, #119, #120, #121,
    #122, #123, #124, #125, #126, #127]

def compactNumericVerifierParsePATerms :
    Fin 259 → Semiterm ℒₒᵣ Empty 429 :=
  fun index =>
    (#(Fin.castLE (show 128 + 259 ≤ 429 by omega)
      (Fin.natAdd 128 index)) : Semiterm ℒₒᵣ Empty 429)

def compactNumericVerifierParseNonLeafTerms :
    Fin 42 → Semiterm ℒₒᵣ Empty 429 :=
  fun index =>
    (#(Fin.natAdd 387 index) : Semiterm ℒₒᵣ Empty 429)

def compactNumericVerifierParseVerumTerms :
    Fin 68 → Semiterm ℒₒᵣ Empty 429 :=
  Matrix.vecAppend rfl compactNumericVerifierParseSuccessCommonTerms
    compactNumericVerifierParseLeafOutputTerms

def compactNumericVerifierParseClosedTerms :
    Fin 96 → Semiterm ℒₒᵣ Empty 429 :=
  Matrix.vecAppend rfl compactNumericVerifierParseVerumTerms
    compactNumericVerifierParseClosedExtraTerms

def compactNumericVerifierParsePABranchTerms :
    Fin 327 → Semiterm ℒₒᵣ Empty 429 :=
  Matrix.vecAppend rfl compactNumericVerifierParseVerumTerms
    compactNumericVerifierParsePATerms

def compactNumericVerifierParseSuccessNonLeafTerms :
    Fin 102 → Semiterm ℒₒᵣ Empty 429 :=
  Matrix.vecAppend rfl compactNumericVerifierParseSuccessCommonTerms
    compactNumericVerifierParseNonLeafTerms

def compactNumericVerifierParseStateGraphDef :
    𝚺₀.Semisentence 429 := .mkSigma
  ((compactNumericVerifierParseFailureSeparatedTablesStateGraphDef.val ⇜
      compactNumericVerifierParseFailureTerms) ⋎
    ((compactNumericVerifierStateCoreGraphDef.val ⇜
        compactNumericVerifierParseCurrentStateTerms) ⋏
      (compactNumericVerifierStateCoreGraphDef.val ⇜
        compactNumericVerifierParseNextStateTerms) ⋏
      (compactNumericVerifierTaskBoundedHeadDef.val ⇜
        compactNumericVerifierParseHeadTerms) ⋏
      (compactNumericVerifierParseStateFrameRowsDef.val ⇜
        compactNumericVerifierParseFrameTerms) ⋏
      ((compactNumericVerifierVerumLeafStateGraphDef.val ⇜
          compactNumericVerifierParseVerumTerms) ⋎
        (compactNumericVerifierClosedLeafStateGraphDef.val ⇜
          compactNumericVerifierParseClosedTerms) ⋎
        (compactNumericVerifierPAAxiomLeafStateGraphDef.val ⇜
          compactNumericVerifierParsePABranchTerms) ⋎
        (compactNumericVerifierParseSuccessNonLeafStateGraphDef.val ⇜
          compactNumericVerifierParseSuccessNonLeafTerms))))
  (by simp)

def compactNumericVerifierParseSuccessParsedEnvironment
    (rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize : Nat) : Fin 11 → Nat :=
  ![rootGammaFinish, rootGammaCount, rootGammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    rootGammaBoundarySize]

def compactNumericVerifierParseLeafOutputEnvironment
    (targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool : Nat) :
    Fin 8 → Nat :=
  ![targetStart, targetFinish, targetGammaFinish, targetGammaCount,
    targetGammaBoundary, targetBool, targetGammaBoundarySize, resultBool]

def compactNumericVerifierParseClosedExtraEnvironment
    (ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound : Nat) : Fin 28 → Nat :=
  ![ruleTable, ruleWidth, ruleTokenCount, ruleProofTag, ruleCertificateTag,
    ruleGammaStart, ruleGammaFinish, ruleGammaBoundary, ruleGammaCount,
    ruleGammaBoundarySize,
    ruleFormulaStart, ruleFormulaFinish, ruleFormulaBoundary, ruleFormulaCount,
    ruleFormulaBoundarySize,
    ruleNegatedStart, ruleNegatedFinish, ruleNegatedBoundary, ruleNegatedCount,
    ruleNegatedBoundarySize, ruleStateBoundary, ruleStateCount,
    ruleEmptyStart, ruleEmptyFinish, ruleEmptyBoundary, ruleEmptyBoundarySize,
    ruleTableWidth, ruleValueBound]

def compactNumericVerifierParseNonLeafEnvironment
    (firstParseCoordinates secondParseCoordinates combineCoordinates :
      CompactNumericVerifierTaskRowCoordinates)
    (firstParseSize secondParseSize combineSize :
      CompactNumericVerifierTaskSizeWitness) : Fin 42 → Nat :=
  Matrix.vecAppend rfl
    (compactNumericVerifierTaskScheduleEnvironment
      firstParseCoordinates firstParseSize)
    (Matrix.vecAppend rfl
      (compactNumericVerifierTaskScheduleEnvironment
        secondParseCoordinates secondParseSize)
      (compactNumericVerifierTaskScheduleEnvironment
        combineCoordinates combineSize))

def compactNumericVerifierParseStateGraphEnvironment
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
      CompactNumericVerifierTaskSizeWitness) : Fin 429 → Nat :=
  Matrix.vecAppend rfl
    (compactNumericVerifierParseFailureSeparatedTablesStateGraphEnvironment
      stateTable stateWidth stateTokenCount
      currentCoordinates.start currentCoordinates.finish
      currentCoordinates.proofFinish currentCoordinates.proofCount
      currentCoordinates.certificateFinish currentCoordinates.certificateCount
      currentCoordinates.tasksFinish currentCoordinates.taskCount
      currentCoordinates.taskBoundary currentCoordinates.valuesFinish
      currentCoordinates.valueCount currentCoordinates.valueBoundary
      currentCoordinates.statusTag currentCoordinates.statusPayloadStart
      currentCoordinates.statusBool
      currentSizeWitness.taskBoundarySize currentSizeWitness.valueBoundarySize
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
      suffixStart suffixFinish certificateTag certificateEndpointBound)
    (Matrix.vecAppend rfl
      (compactNumericVerifierParseSuccessParsedEnvironment
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize)
      (Matrix.vecAppend rfl
        (compactNumericVerifierParseLeafOutputEnvironment
          targetStart targetFinish targetGammaFinish targetGammaCount
          targetGammaBoundary targetBool targetGammaBoundarySize resultBool)
        (Matrix.vecAppend rfl
          (compactNumericVerifierParseClosedExtraEnvironment
            ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
            ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
            ruleGammaBoundarySize
            ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
            ruleFormulaBoundarySize
            ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary
            ruleNegatedCount ruleNegatedBoundarySize
            ruleStateBoundary ruleStateCount
            ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary
            ruleEmptyBoundarySize ruleTableWidth ruleValueBound)
          (Matrix.vecAppend rfl
            (compactNumericVerifierPAAxiomJointLeafRowsEnvironment paCoordinates)
            (compactNumericVerifierParseNonLeafEnvironment
              firstParseCoordinates secondParseCoordinates combineCoordinates
              firstParseSize secondParseSize combineSize)))))

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
@[simp] theorem compactNumericVerifierParseStateGraphDef_spec
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
    compactNumericVerifierParseStateGraphDef.val.Evalb
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
  change compactNumericVerifierParseStateGraphDef.val.Evalb env ↔ _
  have hfailureEnv :
      (Semiterm.val env Empty.elim ∘
        compactNumericVerifierParseFailureTerms) =
        compactNumericVerifierParseFailureSeparatedTablesStateGraphEnvironment
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
          suffixStart suffixFinish certificateTag certificateEndpointBound := by
    funext coordinate
    fin_cases coordinate <;> rfl
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
  have hheadEnv :
      (Semiterm.val env Empty.elim ∘
        compactNumericVerifierParseHeadTerms) =
        compactNumericVerifierTaskBoundedHeadEnvironment
          stateTable stateWidth stateTokenCount
          currentCoordinates.taskBoundary currentSizeWitness.taskValueBound
          taskCoordinates.start taskCoordinates.finish taskCoordinates.tag
          taskCoordinates.gammaFinish taskCoordinates.gammaCount
          taskCoordinates.gammaBoundary taskCoordinates.firstFinish
          taskCoordinates.firstCount taskCoordinates.secondFinish
          taskCoordinates.secondCount taskCoordinates.witnessFinish
          taskCoordinates.witnessCount taskCoordinates.suffixCount
          taskSizeWitness.gammaBoundarySize := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hframeEnv :
      (Semiterm.val env Empty.elim ∘
        compactNumericVerifierParseFrameTerms) =
        ![currentCoordinates.taskCount, currentCoordinates.statusTag,
          taskCoordinates.tag, taskCoordinates.gammaCount,
          taskCoordinates.firstCount, taskCoordinates.secondCount,
          taskCoordinates.witnessCount, taskCoordinates.suffixCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hverumEnv :
      (Semiterm.val env Empty.elim ∘
        compactNumericVerifierParseVerumTerms) =
        compactNumericVerifierVerumLeafStateGraphEnvironment
          stateTable stateWidth stateTokenCount
          currentCoordinates.start currentCoordinates.proofFinish
            currentCoordinates.proofFinish
            currentCoordinates.certificateFinish
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound
          rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
          secondFinish secondCount witnessFinish witnessCount suffixCount
          rootGammaBoundarySize
          currentCoordinates.taskBoundary currentCoordinates.taskCount
          nextCoordinates.taskBoundary nextCoordinates.taskCount
          currentCoordinates.valueBoundary currentCoordinates.valueCount
          nextCoordinates.valueBoundary nextCoordinates.valueCount
          currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
          currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
          nextSizeWitness.taskTableWidth nextSizeWitness.taskValueBound
          nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound
          nextCoordinates.start nextCoordinates.proofFinish
          nextCoordinates.certificateFinish nextCoordinates.statusTag
          targetStart targetFinish targetGammaFinish targetGammaCount
          targetGammaBoundary targetBool targetGammaBoundarySize resultBool := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hclosedEnv :
      (Semiterm.val env Empty.elim ∘
        compactNumericVerifierParseClosedTerms) =
        compactNumericVerifierClosedLeafStateGraphEnvironment
          stateTable stateWidth stateTokenCount
          currentCoordinates.start currentCoordinates.proofFinish
            currentCoordinates.proofFinish
            currentCoordinates.certificateFinish
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound
          rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
          secondFinish secondCount witnessFinish witnessCount suffixCount
          rootGammaBoundarySize
          currentCoordinates.taskBoundary currentCoordinates.taskCount
          nextCoordinates.taskBoundary nextCoordinates.taskCount
          currentCoordinates.valueBoundary currentCoordinates.valueCount
          nextCoordinates.valueBoundary nextCoordinates.valueCount
          currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
          currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
          nextSizeWitness.taskTableWidth nextSizeWitness.taskValueBound
          nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound
          nextCoordinates.start nextCoordinates.proofFinish
          nextCoordinates.certificateFinish nextCoordinates.statusTag
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
          ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary
          ruleEmptyBoundarySize ruleTableWidth ruleValueBound := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hpaEnv :
      (Semiterm.val env Empty.elim ∘
        compactNumericVerifierParsePABranchTerms) =
        compactNumericVerifierPAAxiomLeafStateGraphEnvironment
          stateTable stateWidth stateTokenCount
          currentCoordinates.start currentCoordinates.proofFinish
            currentCoordinates.proofFinish
            currentCoordinates.certificateFinish
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound
          rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
          secondFinish secondCount witnessFinish witnessCount suffixCount
          rootGammaBoundarySize
          currentCoordinates.taskBoundary currentCoordinates.taskCount
          nextCoordinates.taskBoundary nextCoordinates.taskCount
          currentCoordinates.valueBoundary currentCoordinates.valueCount
          nextCoordinates.valueBoundary nextCoordinates.valueCount
          currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
          currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
          nextSizeWitness.taskTableWidth nextSizeWitness.taskValueBound
          nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound
          nextCoordinates.start nextCoordinates.proofFinish
          nextCoordinates.certificateFinish nextCoordinates.statusTag
          targetStart targetFinish targetGammaFinish targetGammaCount
          targetGammaBoundary targetBool targetGammaBoundarySize resultBool
          paCoordinates := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hnonLeafEnv :
      (Semiterm.val env Empty.elim ∘
        compactNumericVerifierParseSuccessNonLeafTerms) =
        compactNumericVerifierParseSuccessNonLeafStateGraphEnvironment
          stateTable stateWidth stateTokenCount
          currentCoordinates.start currentCoordinates.proofFinish
            currentCoordinates.proofFinish
            currentCoordinates.certificateFinish
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound
          rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
          secondFinish secondCount witnessFinish witnessCount suffixCount
          rootGammaBoundarySize
          currentCoordinates.taskBoundary currentCoordinates.taskCount
          nextCoordinates.taskBoundary nextCoordinates.taskCount
          currentCoordinates.valueBoundary currentCoordinates.valueCount
          nextCoordinates.valueBoundary nextCoordinates.valueCount
          currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
          currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
          nextSizeWitness.taskTableWidth nextSizeWitness.taskValueBound
          nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound
          nextCoordinates.start nextCoordinates.proofFinish
          nextCoordinates.certificateFinish nextCoordinates.statusTag
          firstParseCoordinates secondParseCoordinates combineCoordinates
          firstParseSize secondParseSize combineSize := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierParseStateGraphDef,
    CompactNumericVerifierParseStateGraph,
    CompactNumericVerifierParseSuccessStateGraph,
    Semiformula.eval_substs,
    compactNumericVerifierStateRowCoordinatesOf,
    compactNumericVerifierTaskRowCoordinatesOf,
    CompactNumericVerifierParseStateFrameRows,
    hfailureEnv, hcurrentEnv, hnextEnv, hheadEnv, hframeEnv,
    hverumEnv, hclosedEnv, hpaEnv, hnonLeafEnv]

set_option maxRecDepth 65536 in
theorem compactNumericVerifierParseStateGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierParseStateGraphDef.val := by
  simp [compactNumericVerifierParseStateGraphDef]

#print axioms compactNumericVerifierParseStateGraphDef_spec
#print axioms compactNumericVerifierParseStateGraphDef_sigmaZero

end FoundationCompactNumericListedDirectVerifierParseStateFormula
