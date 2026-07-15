import integration.FoundationCompactNumericListedDirectSimpleCombineTransitionRows
import integration.FoundationCompactNumericListedDirectAllShiftCombineRuleRows
import integration.FoundationCompactNumericListedDirectExsCutCombineRuleRows

/-!
# Bounded successful verifier-combine branches

The local rule rows compute the new child-result stack.  A successful public
combine state also stores status `none`, whose direct status tag is zero.
These three wrappers make that final state condition part of each bounded
branch formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineSuccessRows

open FoundationCompactNumericListedDirectSimpleCombineRuleRows
open FoundationCompactNumericListedDirectSimpleCombineTransitionRows
open FoundationCompactNumericListedDirectAllShiftCombineRuleRows
open FoundationCompactNumericListedDirectExsCutCombineRuleRows

def CompactNumericSimpleCombineSuccessRows
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue nextStatusTag : Nat) : Prop :=
  CompactNumericSimpleCombineTransitionRows
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue ∧
    nextStatusTag = 0

def compactNumericSimpleCombineSuccessRowsDef :
    𝚺₀.Semisentence 25 := .mkSigma
  “tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue nextStatusTag.
    !(compactNumericSimpleCombineTransitionRowsDef)
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue ∧
    nextStatusTag = 0”

@[simp] theorem compactNumericSimpleCombineSuccessRowsDef_spec
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue nextStatusTag : Nat) :
    compactNumericSimpleCombineSuccessRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          taskTag, gammaFinish, gammaCount, gammaBoundary,
          firstFinish, firstCount, secondFinish, secondCount,
          rightGammaCount, rightGammaBoundary, rightBoolValue,
          leftGammaCount, leftGammaBoundary, leftBoolValue,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          tableWidth, valueBound, resultBoolValue, nextStatusTag] ↔
      CompactNumericSimpleCombineSuccessRows
        tokenTable width tokenCount
        taskTag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount
        rightGammaCount rightGammaBoundary rightBoolValue
        leftGammaCount leftGammaBoundary leftBoolValue
        sourceBoundary sourceCount targetBoundary targetCount
        tableWidth valueBound resultBoolValue nextStatusTag := by
  have hbaseEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount,
            taskTag, gammaFinish, gammaCount, gammaBoundary,
            firstFinish, firstCount, secondFinish, secondCount,
            rightGammaCount, rightGammaBoundary, rightBoolValue,
            leftGammaCount, leftGammaBoundary, leftBoolValue,
            sourceBoundary, sourceCount, targetBoundary, targetCount,
            tableWidth, valueBound, resultBoolValue, nextStatusTag]
          Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #3, #4, #5, #6,
          #7, #8, #9, #10, #11, #12, #13, #14, #15, #16,
          #17, #18, #19, #20, #21, #22, #23]) =
        ![tokenTable, width, tokenCount,
          taskTag, gammaFinish, gammaCount, gammaBoundary,
          firstFinish, firstCount, secondFinish, secondCount,
          rightGammaCount, rightGammaBoundary, rightBoolValue,
          leftGammaCount, leftGammaBoundary, leftBoolValue,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          tableWidth, valueBound, resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hbaseSpec :
      compactNumericSimpleCombineTransitionRowsDef.val.Evalb
          ![tokenTable, width, tokenCount,
            taskTag, gammaFinish, gammaCount, gammaBoundary,
            firstFinish, firstCount, secondFinish, secondCount,
            rightGammaCount, rightGammaBoundary, rightBoolValue,
            leftGammaCount, leftGammaBoundary, leftBoolValue,
            sourceBoundary, sourceCount, targetBoundary, targetCount,
            tableWidth, valueBound, resultBoolValue] ↔
        CompactNumericSimpleCombineTransitionRows
          tokenTable width tokenCount
          taskTag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount
          rightGammaCount rightGammaBoundary rightBoolValue
          leftGammaCount leftGammaBoundary leftBoolValue
          sourceBoundary sourceCount targetBoundary targetCount
          tableWidth valueBound resultBoolValue := by
    simpa only [compactNumericSimpleCombineRuleRowsEnvironment] using
      compactNumericSimpleCombineTransitionRowsDef_spec
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue
  simp [compactNumericSimpleCombineSuccessRowsDef,
    CompactNumericSimpleCombineSuccessRows, hbaseEnv, hbaseSpec]

set_option maxRecDepth 8192 in
theorem compactNumericSimpleCombineSuccessRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericSimpleCombineSuccessRowsDef.val := by
  simp [compactNumericSimpleCombineSuccessRowsDef]

def CompactNumericAllShiftCombineSuccessRows
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      tableWidth valueBound resultBoolValue nextStatusTag : Nat) : Prop :=
  CompactNumericAllShiftCombineRuleRows
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      tableWidth valueBound resultBoolValue ∧
    nextStatusTag = 0

def compactNumericAllShiftCombineSuccessRowsDef :
    𝚺₀.Semisentence 40 := .mkSigma
  “tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      tableWidth valueBound resultBoolValue nextStatusTag.
    !(compactNumericAllShiftCombineRuleRowsDef)
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      tableWidth valueBound resultBoolValue ∧
    nextStatusTag = 0”

set_option maxRecDepth 8192 in
@[simp] theorem compactNumericAllShiftCombineSuccessRowsDef_spec
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      tableWidth valueBound resultBoolValue nextStatusTag : Nat) :
    compactNumericAllShiftCombineSuccessRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          taskTag, gammaFinish, gammaCount, gammaBoundary,
          firstFinish, firstCount,
          premiseGammaCount, premiseGammaBoundary, premiseBoolValue,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          formulaBoundary, formulaBoundarySize,
          freedStart, freedFinish, freedBoundary, freedCount,
          freedBoundarySize, freeStateBoundary, freeStateCount,
          shiftCandidateBoundary, shiftSuccessTable,
          shiftedBoundary, shiftedCount,
          emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
          shiftWitnessBound, freeTableWidth, freeValueBound,
          tableWidth, valueBound, resultBoolValue, nextStatusTag] ↔
      CompactNumericAllShiftCombineSuccessRows
        tokenTable width tokenCount
        taskTag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount
        premiseGammaCount premiseGammaBoundary premiseBoolValue
        sourceBoundary sourceCount targetBoundary targetCount
        formulaBoundary formulaBoundarySize
        freedStart freedFinish freedBoundary freedCount freedBoundarySize
        freeStateBoundary freeStateCount
        shiftCandidateBoundary shiftSuccessTable
        shiftedBoundary shiftedCount
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        shiftWitnessBound freeTableWidth freeValueBound
        tableWidth valueBound resultBoolValue nextStatusTag := by
  have hbaseEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount,
            taskTag, gammaFinish, gammaCount, gammaBoundary,
            firstFinish, firstCount,
            premiseGammaCount, premiseGammaBoundary, premiseBoolValue,
            sourceBoundary, sourceCount, targetBoundary, targetCount,
            formulaBoundary, formulaBoundarySize,
            freedStart, freedFinish, freedBoundary, freedCount,
            freedBoundarySize, freeStateBoundary, freeStateCount,
            shiftCandidateBoundary, shiftSuccessTable,
            shiftedBoundary, shiftedCount,
            emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
            shiftWitnessBound, freeTableWidth, freeValueBound,
            tableWidth, valueBound, resultBoolValue, nextStatusTag]
          Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 40), #1, #2, #3, #4, #5, #6,
          #7, #8, #9, #10, #11, #12, #13, #14, #15, #16,
          #17, #18, #19, #20, #21, #22, #23, #24, #25, #26,
          #27, #28, #29, #30, #31, #32, #33, #34, #35, #36,
          #37, #38]) =
        ![tokenTable, width, tokenCount,
          taskTag, gammaFinish, gammaCount, gammaBoundary,
          firstFinish, firstCount,
          premiseGammaCount, premiseGammaBoundary, premiseBoolValue,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          formulaBoundary, formulaBoundarySize,
          freedStart, freedFinish, freedBoundary, freedCount,
          freedBoundarySize, freeStateBoundary, freeStateCount,
          shiftCandidateBoundary, shiftSuccessTable,
          shiftedBoundary, shiftedCount,
          emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
          shiftWitnessBound, freeTableWidth, freeValueBound,
          tableWidth, valueBound, resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hbaseSpec :
      compactNumericAllShiftCombineRuleRowsDef.val.Evalb
          ![tokenTable, width, tokenCount,
            taskTag, gammaFinish, gammaCount, gammaBoundary,
            firstFinish, firstCount,
            premiseGammaCount, premiseGammaBoundary, premiseBoolValue,
            sourceBoundary, sourceCount, targetBoundary, targetCount,
            formulaBoundary, formulaBoundarySize,
            freedStart, freedFinish, freedBoundary, freedCount,
            freedBoundarySize, freeStateBoundary, freeStateCount,
            shiftCandidateBoundary, shiftSuccessTable,
            shiftedBoundary, shiftedCount,
            emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
            shiftWitnessBound, freeTableWidth, freeValueBound,
            tableWidth, valueBound, resultBoolValue] ↔
        CompactNumericAllShiftCombineRuleRows
          tokenTable width tokenCount
          taskTag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount
          premiseGammaCount premiseGammaBoundary premiseBoolValue
          sourceBoundary sourceCount targetBoundary targetCount
          formulaBoundary formulaBoundarySize
          freedStart freedFinish freedBoundary freedCount freedBoundarySize
          freeStateBoundary freeStateCount
          shiftCandidateBoundary shiftSuccessTable
          shiftedBoundary shiftedCount
          emptyStart emptyFinish emptyBoundary emptyBoundarySize
          shiftWitnessBound freeTableWidth freeValueBound
          tableWidth valueBound resultBoolValue := by
    simpa only [compactNumericAllShiftCombineRuleRowsEnvironment] using
      compactNumericAllShiftCombineRuleRowsDef_spec
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      tableWidth valueBound resultBoolValue
  simp [compactNumericAllShiftCombineSuccessRowsDef,
    CompactNumericAllShiftCombineSuccessRows, hbaseEnv, hbaseSpec]

set_option maxRecDepth 8192 in
theorem compactNumericAllShiftCombineSuccessRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericAllShiftCombineSuccessRowsDef.val := by
  simp [compactNumericAllShiftCombineSuccessRowsDef]

def CompactNumericExsCutCombineSuccessRows
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish witnessFinish witnessCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      tableWidth valueBound resultBoolValue nextStatusTag : Nat) : Prop :=
  CompactNumericExsCutCombineRuleRows
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish witnessFinish witnessCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      tableWidth valueBound resultBoolValue ∧
    nextStatusTag = 0

def compactNumericExsCutCombineSuccessRowsDef :
    𝚺₀.Semisentence 41 := .mkSigma
  “tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish witnessFinish witnessCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      tableWidth valueBound resultBoolValue nextStatusTag.
    !(compactNumericExsCutCombineRuleRowsDef)
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish witnessFinish witnessCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      tableWidth valueBound resultBoolValue ∧
    nextStatusTag = 0”

set_option maxRecDepth 8192 in
@[simp] theorem compactNumericExsCutCombineSuccessRowsDef_spec
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish witnessFinish witnessCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      tableWidth valueBound resultBoolValue nextStatusTag : Nat) :
    compactNumericExsCutCombineSuccessRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          taskTag, gammaFinish, gammaCount, gammaBoundary,
          firstFinish, firstCount, secondFinish, witnessFinish, witnessCount,
          rightGammaCount, rightGammaBoundary, rightBoolValue,
          leftGammaCount, leftGammaBoundary, leftBoolValue,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          formulaBoundary, formulaBoundarySize,
          transformedStart, transformedFinish, transformedBoundary,
          transformedCount, transformedBoundarySize,
          transformStateBoundary, transformStateCount,
          emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
          transformTableWidth, transformValueBound,
          tableWidth, valueBound, resultBoolValue, nextStatusTag] ↔
      CompactNumericExsCutCombineSuccessRows
        tokenTable width tokenCount
        taskTag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish witnessFinish witnessCount
        rightGammaCount rightGammaBoundary rightBoolValue
        leftGammaCount leftGammaBoundary leftBoolValue
        sourceBoundary sourceCount targetBoundary targetCount
        formulaBoundary formulaBoundarySize
        transformedStart transformedFinish transformedBoundary
        transformedCount transformedBoundarySize
        transformStateBoundary transformStateCount
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        transformTableWidth transformValueBound
        tableWidth valueBound resultBoolValue nextStatusTag := by
  have hbaseEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount,
            taskTag, gammaFinish, gammaCount, gammaBoundary,
            firstFinish, firstCount, secondFinish, witnessFinish, witnessCount,
            rightGammaCount, rightGammaBoundary, rightBoolValue,
            leftGammaCount, leftGammaBoundary, leftBoolValue,
            sourceBoundary, sourceCount, targetBoundary, targetCount,
            formulaBoundary, formulaBoundarySize,
            transformedStart, transformedFinish, transformedBoundary,
            transformedCount, transformedBoundarySize,
            transformStateBoundary, transformStateCount,
            emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
            transformTableWidth, transformValueBound,
            tableWidth, valueBound, resultBoolValue, nextStatusTag]
          Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 41), #1, #2, #3, #4, #5, #6,
          #7, #8, #9, #10, #11, #12, #13, #14, #15, #16,
          #17, #18, #19, #20, #21, #22, #23, #24, #25, #26,
          #27, #28, #29, #30, #31, #32, #33, #34, #35, #36,
          #37, #38, #39]) =
        ![tokenTable, width, tokenCount,
          taskTag, gammaFinish, gammaCount, gammaBoundary,
          firstFinish, firstCount, secondFinish, witnessFinish, witnessCount,
          rightGammaCount, rightGammaBoundary, rightBoolValue,
          leftGammaCount, leftGammaBoundary, leftBoolValue,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          formulaBoundary, formulaBoundarySize,
          transformedStart, transformedFinish, transformedBoundary,
          transformedCount, transformedBoundarySize,
          transformStateBoundary, transformStateCount,
          emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
          transformTableWidth, transformValueBound,
          tableWidth, valueBound, resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hbaseSpec :
      compactNumericExsCutCombineRuleRowsDef.val.Evalb
          ![tokenTable, width, tokenCount,
            taskTag, gammaFinish, gammaCount, gammaBoundary,
            firstFinish, firstCount, secondFinish, witnessFinish, witnessCount,
            rightGammaCount, rightGammaBoundary, rightBoolValue,
            leftGammaCount, leftGammaBoundary, leftBoolValue,
            sourceBoundary, sourceCount, targetBoundary, targetCount,
            formulaBoundary, formulaBoundarySize,
            transformedStart, transformedFinish, transformedBoundary,
            transformedCount, transformedBoundarySize,
            transformStateBoundary, transformStateCount,
            emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
            transformTableWidth, transformValueBound,
            tableWidth, valueBound, resultBoolValue] ↔
        CompactNumericExsCutCombineRuleRows
          tokenTable width tokenCount
          taskTag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish witnessFinish witnessCount
          rightGammaCount rightGammaBoundary rightBoolValue
          leftGammaCount leftGammaBoundary leftBoolValue
          sourceBoundary sourceCount targetBoundary targetCount
          formulaBoundary formulaBoundarySize
          transformedStart transformedFinish transformedBoundary
          transformedCount transformedBoundarySize
          transformStateBoundary transformStateCount
          emptyStart emptyFinish emptyBoundary emptyBoundarySize
          transformTableWidth transformValueBound
          tableWidth valueBound resultBoolValue := by
    simpa only [compactNumericExsCutCombineRuleRowsEnvironment] using
      compactNumericExsCutCombineRuleRowsDef_spec
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish witnessFinish witnessCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      tableWidth valueBound resultBoolValue
  simp [compactNumericExsCutCombineSuccessRowsDef,
    CompactNumericExsCutCombineSuccessRows, hbaseEnv, hbaseSpec]

set_option maxRecDepth 8192 in
theorem compactNumericExsCutCombineSuccessRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericExsCutCombineSuccessRowsDef.val := by
  simp [compactNumericExsCutCombineSuccessRowsDef]

#print axioms compactNumericSimpleCombineSuccessRowsDef_spec
#print axioms compactNumericSimpleCombineSuccessRowsDef_sigmaZero
#print axioms compactNumericAllShiftCombineSuccessRowsDef_spec
#print axioms compactNumericAllShiftCombineSuccessRowsDef_sigmaZero
#print axioms compactNumericExsCutCombineSuccessRowsDef_spec
#print axioms compactNumericExsCutCombineSuccessRowsDef_sigmaZero

end FoundationCompactNumericListedDirectVerifierCombineSuccessRows
