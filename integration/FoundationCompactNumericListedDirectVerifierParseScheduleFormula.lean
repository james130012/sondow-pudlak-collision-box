import integration.FoundationCompactNumericListedDirectTokenSliceEquality
import integration.FoundationCompactNumericListedDirectVerifierParseScheduleRows

/-!
# Bounded formulas for successful parse-task scheduling

These formulas flatten the one-parse and two-parse schedule relations into
fixed arithmetic coordinates.  All task rows, the preserved tail, and the
proof-root slice equality remain inside Delta-zero arithmetic.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseScheduleFormula

open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedAtFormula
open FoundationCompactNumericListedDirectVerifierTaskListReplaceHeadRows
open FoundationCompactNumericListedDirectVerifierParseScheduleRows

def compactNumericVerifierOneParseScheduleRowsDef :
    𝚺₀.Semisentence 39 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount valueBound
      rootStart rootFinish rootTag
      parseStart parseFinish parseTag
      parseGammaFinish parseGammaCount parseGammaBoundary
      parseFirstFinish parseFirstCount
      parseSecondFinish parseSecondCount
      parseWitnessFinish parseWitnessCount parseSuffixCount
      parseGammaBoundarySize
      combineStart combineFinish combineTag
      combineGammaFinish combineGammaCount combineGammaBoundary
      combineFirstFinish combineFirstCount
      combineSecondFinish combineSecondCount
      combineWitnessFinish combineWitnessCount combineSuffixCount
      combineGammaBoundarySize.
    (rootTag = 4 ∨ rootTag = 5 ∨ rootTag = 6 ∨
      rootTag = 7 ∨ rootTag = 8) ∧
    !(compactNumericVerifierTaskListReplaceHeadRowsDef)
      tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount valueBound 2 ∧
    !(compactNumericVerifierTaskBoundedAtDef)
      tokenTable width tokenCount targetBoundary valueBound 0
      parseStart parseFinish parseTag
      parseGammaFinish parseGammaCount parseGammaBoundary
      parseFirstFinish parseFirstCount
      parseSecondFinish parseSecondCount
      parseWitnessFinish parseWitnessCount parseSuffixCount
      parseGammaBoundarySize ∧
    (parseTag = 10 ∧ parseGammaCount = 0 ∧
      parseFirstCount = 0 ∧ parseSecondCount = 0 ∧
      parseWitnessCount = 0 ∧ parseSuffixCount = 0) ∧
    !(compactNumericVerifierTaskBoundedAtDef)
      tokenTable width tokenCount targetBoundary valueBound 1
      combineStart combineFinish combineTag
      combineGammaFinish combineGammaCount combineGammaBoundary
      combineFirstFinish combineFirstCount
      combineSecondFinish combineSecondCount
      combineWitnessFinish combineWitnessCount combineSuffixCount
      combineGammaBoundarySize ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
        rootStart rootFinish combineStart combineFinish”

def compactNumericVerifierOneParseScheduleRowsEnvironment
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount valueBound
      rootStart rootFinish rootTag
      parseStart parseFinish parseTag
      parseGammaFinish parseGammaCount parseGammaBoundary
      parseFirstFinish parseFirstCount
      parseSecondFinish parseSecondCount
      parseWitnessFinish parseWitnessCount parseSuffixCount
      parseGammaBoundarySize
      combineStart combineFinish combineTag
      combineGammaFinish combineGammaCount combineGammaBoundary
      combineFirstFinish combineFirstCount
      combineSecondFinish combineSecondCount
      combineWitnessFinish combineWitnessCount combineSuffixCount
      combineGammaBoundarySize : Nat) : Fin 39 → Nat :=
  ![tokenTable, width, tokenCount,
    sourceBoundary, sourceCount, targetBoundary, targetCount, valueBound,
    rootStart, rootFinish, rootTag,
    parseStart, parseFinish, parseTag,
    parseGammaFinish, parseGammaCount, parseGammaBoundary,
    parseFirstFinish, parseFirstCount,
    parseSecondFinish, parseSecondCount,
    parseWitnessFinish, parseWitnessCount, parseSuffixCount,
    parseGammaBoundarySize,
    combineStart, combineFinish, combineTag,
    combineGammaFinish, combineGammaCount, combineGammaBoundary,
    combineFirstFinish, combineFirstCount,
    combineSecondFinish, combineSecondCount,
    combineWitnessFinish, combineWitnessCount, combineSuffixCount,
    combineGammaBoundarySize]

set_option maxRecDepth 8192 in
@[simp] theorem compactNumericVerifierOneParseScheduleRowsDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount valueBound
      rootStart rootFinish rootTag
      parseStart parseFinish parseTag
      parseGammaFinish parseGammaCount parseGammaBoundary
      parseFirstFinish parseFirstCount
      parseSecondFinish parseSecondCount
      parseWitnessFinish parseWitnessCount parseSuffixCount
      parseGammaBoundarySize
      combineStart combineFinish combineTag
      combineGammaFinish combineGammaCount combineGammaBoundary
      combineFirstFinish combineFirstCount
      combineSecondFinish combineSecondCount
      combineWitnessFinish combineWitnessCount combineSuffixCount
      combineGammaBoundarySize : Nat) :
    compactNumericVerifierOneParseScheduleRowsDef.val.Evalb
        (compactNumericVerifierOneParseScheduleRowsEnvironment
          tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount valueBound
          rootStart rootFinish rootTag
          parseStart parseFinish parseTag
          parseGammaFinish parseGammaCount parseGammaBoundary
          parseFirstFinish parseFirstCount
          parseSecondFinish parseSecondCount
          parseWitnessFinish parseWitnessCount parseSuffixCount
          parseGammaBoundarySize
          combineStart combineFinish combineTag
          combineGammaFinish combineGammaCount combineGammaBoundary
          combineFirstFinish combineFirstCount
          combineSecondFinish combineSecondCount
          combineWitnessFinish combineWitnessCount combineSuffixCount
          combineGammaBoundarySize) ↔
      CompactNumericVerifierOneParseScheduleRows
        tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount valueBound
        rootStart rootFinish rootTag
        (compactNumericVerifierTaskRowCoordinatesOf
          parseStart parseFinish parseTag
          parseGammaFinish parseGammaCount parseGammaBoundary
          parseFirstFinish parseFirstCount
          parseSecondFinish parseSecondCount
          parseWitnessFinish parseWitnessCount parseSuffixCount)
        (compactNumericVerifierTaskRowCoordinatesOf
          combineStart combineFinish combineTag
          combineGammaFinish combineGammaCount combineGammaBoundary
          combineFirstFinish combineFirstCount
          combineSecondFinish combineSecondCount
          combineWitnessFinish combineWitnessCount combineSuffixCount)
        { gammaBoundarySize := parseGammaBoundarySize }
        { gammaBoundarySize := combineGammaBoundarySize } := by
  let env := compactNumericVerifierOneParseScheduleRowsEnvironment
    tokenTable width tokenCount
    sourceBoundary sourceCount targetBoundary targetCount valueBound
    rootStart rootFinish rootTag
    parseStart parseFinish parseTag
    parseGammaFinish parseGammaCount parseGammaBoundary
    parseFirstFinish parseFirstCount
    parseSecondFinish parseSecondCount
    parseWitnessFinish parseWitnessCount parseSuffixCount
    parseGammaBoundarySize
    combineStart combineFinish combineTag
    combineGammaFinish combineGammaCount combineGammaBoundary
    combineFirstFinish combineFirstCount
    combineSecondFinish combineSecondCount
    combineWitnessFinish combineWitnessCount combineSuffixCount
    combineGammaBoundarySize
  change compactNumericVerifierOneParseScheduleRowsDef.val.Evalb env ↔ _
  have hreplaceEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 39), #1, #2, #3, #4, #5, #6, #7,
          ‘2’]) =
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          valueBound, 2] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hparseEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 39), #1, #2, #5, #7, ‘0’,
          #11, #12, #13, #14, #15, #16, #17, #18, #19, #20,
          #21, #22, #23, #24]) =
        compactNumericVerifierTaskBoundedAtEnvironment
          tokenTable width tokenCount targetBoundary valueBound 0
          parseStart parseFinish parseTag
          parseGammaFinish parseGammaCount parseGammaBoundary
          parseFirstFinish parseFirstCount
          parseSecondFinish parseSecondCount
          parseWitnessFinish parseWitnessCount parseSuffixCount
          parseGammaBoundarySize := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcombineEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 39), #1, #2, #5, #7, ‘1’,
          #25, #26, #27, #28, #29, #30, #31, #32, #33, #34,
          #35, #36, #37, #38]) =
        compactNumericVerifierTaskBoundedAtEnvironment
          tokenTable width tokenCount targetBoundary valueBound 1
          combineStart combineFinish combineTag
          combineGammaFinish combineGammaCount combineGammaBoundary
          combineFirstFinish combineFirstCount
          combineSecondFinish combineSecondCount
          combineWitnessFinish combineWitnessCount combineSuffixCount
          combineGammaBoundarySize := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hslicesEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 39), #1, #2, #8, #9, #25, #26]) =
        ![tokenTable, width, tokenCount,
          rootStart, rootFinish, combineStart, combineFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hreplaceSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 39), #1, #2, #3, #4, #5, #6, #7,
              ‘2’])
          Empty.elim) compactNumericVerifierTaskListReplaceHeadRowsDef.val ↔
        CompactNumericVerifierTaskListReplaceHeadRows
          tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount
          valueBound 2 := by
    rw [hreplaceEnv]
    exact compactNumericVerifierTaskListReplaceHeadRowsDef_spec
      tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount valueBound 2
  have hparseSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 39), #1, #2, #5, #7, ‘0’,
              #11, #12, #13, #14, #15, #16, #17, #18, #19, #20,
              #21, #22, #23, #24])
          Empty.elim) compactNumericVerifierTaskBoundedAtDef.val ↔
        CompactNumericVerifierTaskBoundedAt
          tokenTable width tokenCount targetBoundary valueBound 0
          (compactNumericVerifierTaskRowCoordinatesOf
            parseStart parseFinish parseTag
            parseGammaFinish parseGammaCount parseGammaBoundary
            parseFirstFinish parseFirstCount
            parseSecondFinish parseSecondCount
            parseWitnessFinish parseWitnessCount parseSuffixCount)
          { gammaBoundarySize := parseGammaBoundarySize } := by
    rw [hparseEnv]
    exact compactNumericVerifierTaskBoundedAtDef_spec
      tokenTable width tokenCount targetBoundary valueBound 0
      parseStart parseFinish parseTag
      parseGammaFinish parseGammaCount parseGammaBoundary
      parseFirstFinish parseFirstCount
      parseSecondFinish parseSecondCount
      parseWitnessFinish parseWitnessCount parseSuffixCount
      parseGammaBoundarySize
  have hcombineSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 39), #1, #2, #5, #7, ‘1’,
              #25, #26, #27, #28, #29, #30, #31, #32, #33, #34,
              #35, #36, #37, #38])
          Empty.elim) compactNumericVerifierTaskBoundedAtDef.val ↔
        CompactNumericVerifierTaskBoundedAt
          tokenTable width tokenCount targetBoundary valueBound 1
          (compactNumericVerifierTaskRowCoordinatesOf
            combineStart combineFinish combineTag
            combineGammaFinish combineGammaCount combineGammaBoundary
            combineFirstFinish combineFirstCount
            combineSecondFinish combineSecondCount
            combineWitnessFinish combineWitnessCount combineSuffixCount)
          { gammaBoundarySize := combineGammaBoundarySize } := by
    rw [hcombineEnv]
    exact compactNumericVerifierTaskBoundedAtDef_spec
      tokenTable width tokenCount targetBoundary valueBound 1
      combineStart combineFinish combineTag
      combineGammaFinish combineGammaCount combineGammaBoundary
      combineFirstFinish combineFirstCount
      combineSecondFinish combineSecondCount
      combineWitnessFinish combineWitnessCount combineSuffixCount
      combineGammaBoundarySize
  have hslicesSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 39), #1, #2, #8, #9, #25, #26])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          rootStart rootFinish combineStart combineFinish := by
    rw [hslicesEnv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount
      rootStart rootFinish combineStart combineFinish
  simp [compactNumericVerifierOneParseScheduleRowsDef,
    CompactNumericVerifierOneParseScheduleRows,
    CompactNumericParseTaskShape,
    compactNumericVerifierTaskRowCoordinatesOf,
    hreplaceSpec, hparseSpec, hcombineSpec, hslicesSpec]
  simp [env, compactNumericVerifierOneParseScheduleRowsEnvironment]
  intros
  rfl

def compactNumericVerifierTwoParseScheduleRowsDef :
    𝚺₀.Semisentence 53 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount valueBound
      rootStart rootFinish rootTag
      firstStart firstFinish firstTag
      firstGammaFinish firstGammaCount firstGammaBoundary
      firstFormulaFinish firstFormulaCount
      firstSecondFinish firstSecondCount
      firstWitnessFinish firstWitnessCount firstSuffixCount
      firstGammaBoundarySize
      secondStart secondFinish secondTag
      secondGammaFinish secondGammaCount secondGammaBoundary
      secondFormulaFinish secondFormulaCount
      secondSecondFinish secondSecondCount
      secondWitnessFinish secondWitnessCount secondSuffixCount
      secondGammaBoundarySize
      combineStart combineFinish combineTag
      combineGammaFinish combineGammaCount combineGammaBoundary
      combineFirstFinish combineFirstCount
      combineSecondFinish combineSecondCount
      combineWitnessFinish combineWitnessCount combineSuffixCount
      combineGammaBoundarySize.
    (rootTag = 3 ∨ rootTag = 9) ∧
    !(compactNumericVerifierTaskListReplaceHeadRowsDef)
      tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount valueBound 3 ∧
    !(compactNumericVerifierTaskBoundedAtDef)
      tokenTable width tokenCount targetBoundary valueBound 0
      firstStart firstFinish firstTag
      firstGammaFinish firstGammaCount firstGammaBoundary
      firstFormulaFinish firstFormulaCount
      firstSecondFinish firstSecondCount
      firstWitnessFinish firstWitnessCount firstSuffixCount
      firstGammaBoundarySize ∧
    (firstTag = 10 ∧ firstGammaCount = 0 ∧
      firstFormulaCount = 0 ∧ firstSecondCount = 0 ∧
      firstWitnessCount = 0 ∧ firstSuffixCount = 0) ∧
    !(compactNumericVerifierTaskBoundedAtDef)
      tokenTable width tokenCount targetBoundary valueBound 1
      secondStart secondFinish secondTag
      secondGammaFinish secondGammaCount secondGammaBoundary
      secondFormulaFinish secondFormulaCount
      secondSecondFinish secondSecondCount
      secondWitnessFinish secondWitnessCount secondSuffixCount
      secondGammaBoundarySize ∧
    (secondTag = 10 ∧ secondGammaCount = 0 ∧
      secondFormulaCount = 0 ∧ secondSecondCount = 0 ∧
      secondWitnessCount = 0 ∧ secondSuffixCount = 0) ∧
    !(compactNumericVerifierTaskBoundedAtDef)
      tokenTable width tokenCount targetBoundary valueBound 2
      combineStart combineFinish combineTag
      combineGammaFinish combineGammaCount combineGammaBoundary
      combineFirstFinish combineFirstCount
      combineSecondFinish combineSecondCount
      combineWitnessFinish combineWitnessCount combineSuffixCount
      combineGammaBoundarySize ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
        rootStart rootFinish combineStart combineFinish”

def compactNumericVerifierTwoParseScheduleRowsEnvironment
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount valueBound
      rootStart rootFinish rootTag
      firstStart firstFinish firstTag
      firstGammaFinish firstGammaCount firstGammaBoundary
      firstFormulaFinish firstFormulaCount
      firstSecondFinish firstSecondCount
      firstWitnessFinish firstWitnessCount firstSuffixCount
      firstGammaBoundarySize
      secondStart secondFinish secondTag
      secondGammaFinish secondGammaCount secondGammaBoundary
      secondFormulaFinish secondFormulaCount
      secondSecondFinish secondSecondCount
      secondWitnessFinish secondWitnessCount secondSuffixCount
      secondGammaBoundarySize
      combineStart combineFinish combineTag
      combineGammaFinish combineGammaCount combineGammaBoundary
      combineFirstFinish combineFirstCount
      combineSecondFinish combineSecondCount
      combineWitnessFinish combineWitnessCount combineSuffixCount
      combineGammaBoundarySize : Nat) : Fin 53 → Nat :=
  ![tokenTable, width, tokenCount,
    sourceBoundary, sourceCount, targetBoundary, targetCount, valueBound,
    rootStart, rootFinish, rootTag,
    firstStart, firstFinish, firstTag,
    firstGammaFinish, firstGammaCount, firstGammaBoundary,
    firstFormulaFinish, firstFormulaCount,
    firstSecondFinish, firstSecondCount,
    firstWitnessFinish, firstWitnessCount, firstSuffixCount,
    firstGammaBoundarySize,
    secondStart, secondFinish, secondTag,
    secondGammaFinish, secondGammaCount, secondGammaBoundary,
    secondFormulaFinish, secondFormulaCount,
    secondSecondFinish, secondSecondCount,
    secondWitnessFinish, secondWitnessCount, secondSuffixCount,
    secondGammaBoundarySize,
    combineStart, combineFinish, combineTag,
    combineGammaFinish, combineGammaCount, combineGammaBoundary,
    combineFirstFinish, combineFirstCount,
    combineSecondFinish, combineSecondCount,
    combineWitnessFinish, combineWitnessCount, combineSuffixCount,
    combineGammaBoundarySize]

set_option maxRecDepth 8192 in
@[simp] theorem compactNumericVerifierTwoParseScheduleRowsDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount valueBound
      rootStart rootFinish rootTag
      firstStart firstFinish firstTag
      firstGammaFinish firstGammaCount firstGammaBoundary
      firstFormulaFinish firstFormulaCount
      firstSecondFinish firstSecondCount
      firstWitnessFinish firstWitnessCount firstSuffixCount
      firstGammaBoundarySize
      secondStart secondFinish secondTag
      secondGammaFinish secondGammaCount secondGammaBoundary
      secondFormulaFinish secondFormulaCount
      secondSecondFinish secondSecondCount
      secondWitnessFinish secondWitnessCount secondSuffixCount
      secondGammaBoundarySize
      combineStart combineFinish combineTag
      combineGammaFinish combineGammaCount combineGammaBoundary
      combineFirstFinish combineFirstCount
      combineSecondFinish combineSecondCount
      combineWitnessFinish combineWitnessCount combineSuffixCount
      combineGammaBoundarySize : Nat) :
    compactNumericVerifierTwoParseScheduleRowsDef.val.Evalb
        (compactNumericVerifierTwoParseScheduleRowsEnvironment
          tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount valueBound
          rootStart rootFinish rootTag
          firstStart firstFinish firstTag
          firstGammaFinish firstGammaCount firstGammaBoundary
          firstFormulaFinish firstFormulaCount
          firstSecondFinish firstSecondCount
          firstWitnessFinish firstWitnessCount firstSuffixCount
          firstGammaBoundarySize
          secondStart secondFinish secondTag
          secondGammaFinish secondGammaCount secondGammaBoundary
          secondFormulaFinish secondFormulaCount
          secondSecondFinish secondSecondCount
          secondWitnessFinish secondWitnessCount secondSuffixCount
          secondGammaBoundarySize
          combineStart combineFinish combineTag
          combineGammaFinish combineGammaCount combineGammaBoundary
          combineFirstFinish combineFirstCount
          combineSecondFinish combineSecondCount
          combineWitnessFinish combineWitnessCount combineSuffixCount
          combineGammaBoundarySize) ↔
      CompactNumericVerifierTwoParseScheduleRows
        tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount valueBound
        rootStart rootFinish rootTag
        (compactNumericVerifierTaskRowCoordinatesOf
          firstStart firstFinish firstTag
          firstGammaFinish firstGammaCount firstGammaBoundary
          firstFormulaFinish firstFormulaCount
          firstSecondFinish firstSecondCount
          firstWitnessFinish firstWitnessCount firstSuffixCount)
        (compactNumericVerifierTaskRowCoordinatesOf
          secondStart secondFinish secondTag
          secondGammaFinish secondGammaCount secondGammaBoundary
          secondFormulaFinish secondFormulaCount
          secondSecondFinish secondSecondCount
          secondWitnessFinish secondWitnessCount secondSuffixCount)
        (compactNumericVerifierTaskRowCoordinatesOf
          combineStart combineFinish combineTag
          combineGammaFinish combineGammaCount combineGammaBoundary
          combineFirstFinish combineFirstCount
          combineSecondFinish combineSecondCount
          combineWitnessFinish combineWitnessCount combineSuffixCount)
        { gammaBoundarySize := firstGammaBoundarySize }
        { gammaBoundarySize := secondGammaBoundarySize }
        { gammaBoundarySize := combineGammaBoundarySize } := by
  let env := compactNumericVerifierTwoParseScheduleRowsEnvironment
    tokenTable width tokenCount
    sourceBoundary sourceCount targetBoundary targetCount valueBound
    rootStart rootFinish rootTag
    firstStart firstFinish firstTag
    firstGammaFinish firstGammaCount firstGammaBoundary
    firstFormulaFinish firstFormulaCount
    firstSecondFinish firstSecondCount
    firstWitnessFinish firstWitnessCount firstSuffixCount
    firstGammaBoundarySize
    secondStart secondFinish secondTag
    secondGammaFinish secondGammaCount secondGammaBoundary
    secondFormulaFinish secondFormulaCount
    secondSecondFinish secondSecondCount
    secondWitnessFinish secondWitnessCount secondSuffixCount
    secondGammaBoundarySize
    combineStart combineFinish combineTag
    combineGammaFinish combineGammaCount combineGammaBoundary
    combineFirstFinish combineFirstCount
    combineSecondFinish combineSecondCount
    combineWitnessFinish combineWitnessCount combineSuffixCount
    combineGammaBoundarySize
  change compactNumericVerifierTwoParseScheduleRowsDef.val.Evalb env ↔ _
  have hreplaceEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 53), #1, #2, #3, #4, #5, #6, #7,
          ‘3’]) =
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          valueBound, 3] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hfirstEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 53), #1, #2, #5, #7, ‘0’,
          #11, #12, #13, #14, #15, #16, #17, #18, #19, #20,
          #21, #22, #23, #24]) =
        compactNumericVerifierTaskBoundedAtEnvironment
          tokenTable width tokenCount targetBoundary valueBound 0
          firstStart firstFinish firstTag
          firstGammaFinish firstGammaCount firstGammaBoundary
          firstFormulaFinish firstFormulaCount
          firstSecondFinish firstSecondCount
          firstWitnessFinish firstWitnessCount firstSuffixCount
          firstGammaBoundarySize := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsecondEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 53), #1, #2, #5, #7, ‘1’,
          #25, #26, #27, #28, #29, #30, #31, #32, #33, #34,
          #35, #36, #37, #38]) =
        compactNumericVerifierTaskBoundedAtEnvironment
          tokenTable width tokenCount targetBoundary valueBound 1
          secondStart secondFinish secondTag
          secondGammaFinish secondGammaCount secondGammaBoundary
          secondFormulaFinish secondFormulaCount
          secondSecondFinish secondSecondCount
          secondWitnessFinish secondWitnessCount secondSuffixCount
          secondGammaBoundarySize := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcombineEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 53), #1, #2, #5, #7, ‘2’,
          #39, #40, #41, #42, #43, #44, #45, #46, #47, #48,
          #49, #50, #51, #52]) =
        compactNumericVerifierTaskBoundedAtEnvironment
          tokenTable width tokenCount targetBoundary valueBound 2
          combineStart combineFinish combineTag
          combineGammaFinish combineGammaCount combineGammaBoundary
          combineFirstFinish combineFirstCount
          combineSecondFinish combineSecondCount
          combineWitnessFinish combineWitnessCount combineSuffixCount
          combineGammaBoundarySize := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hslicesEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 53), #1, #2, #8, #9, #39, #40]) =
        ![tokenTable, width, tokenCount,
          rootStart, rootFinish, combineStart, combineFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hreplaceSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 53), #1, #2, #3, #4, #5, #6, #7,
              ‘3’])
          Empty.elim) compactNumericVerifierTaskListReplaceHeadRowsDef.val ↔
        CompactNumericVerifierTaskListReplaceHeadRows
          tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount
          valueBound 3 := by
    rw [hreplaceEnv]
    exact compactNumericVerifierTaskListReplaceHeadRowsDef_spec
      tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount valueBound 3
  have hfirstSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 53), #1, #2, #5, #7, ‘0’,
              #11, #12, #13, #14, #15, #16, #17, #18, #19, #20,
              #21, #22, #23, #24])
          Empty.elim) compactNumericVerifierTaskBoundedAtDef.val ↔
        CompactNumericVerifierTaskBoundedAt
          tokenTable width tokenCount targetBoundary valueBound 0
          (compactNumericVerifierTaskRowCoordinatesOf
            firstStart firstFinish firstTag
            firstGammaFinish firstGammaCount firstGammaBoundary
            firstFormulaFinish firstFormulaCount
            firstSecondFinish firstSecondCount
            firstWitnessFinish firstWitnessCount firstSuffixCount)
          { gammaBoundarySize := firstGammaBoundarySize } := by
    rw [hfirstEnv]
    exact compactNumericVerifierTaskBoundedAtDef_spec
      tokenTable width tokenCount targetBoundary valueBound 0
      firstStart firstFinish firstTag
      firstGammaFinish firstGammaCount firstGammaBoundary
      firstFormulaFinish firstFormulaCount
      firstSecondFinish firstSecondCount
      firstWitnessFinish firstWitnessCount firstSuffixCount
      firstGammaBoundarySize
  have hsecondSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 53), #1, #2, #5, #7, ‘1’,
              #25, #26, #27, #28, #29, #30, #31, #32, #33, #34,
              #35, #36, #37, #38])
          Empty.elim) compactNumericVerifierTaskBoundedAtDef.val ↔
        CompactNumericVerifierTaskBoundedAt
          tokenTable width tokenCount targetBoundary valueBound 1
          (compactNumericVerifierTaskRowCoordinatesOf
            secondStart secondFinish secondTag
            secondGammaFinish secondGammaCount secondGammaBoundary
            secondFormulaFinish secondFormulaCount
            secondSecondFinish secondSecondCount
            secondWitnessFinish secondWitnessCount secondSuffixCount)
          { gammaBoundarySize := secondGammaBoundarySize } := by
    rw [hsecondEnv]
    exact compactNumericVerifierTaskBoundedAtDef_spec
      tokenTable width tokenCount targetBoundary valueBound 1
      secondStart secondFinish secondTag
      secondGammaFinish secondGammaCount secondGammaBoundary
      secondFormulaFinish secondFormulaCount
      secondSecondFinish secondSecondCount
      secondWitnessFinish secondWitnessCount secondSuffixCount
      secondGammaBoundarySize
  have hcombineSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 53), #1, #2, #5, #7, ‘2’,
              #39, #40, #41, #42, #43, #44, #45, #46, #47, #48,
              #49, #50, #51, #52])
          Empty.elim) compactNumericVerifierTaskBoundedAtDef.val ↔
        CompactNumericVerifierTaskBoundedAt
          tokenTable width tokenCount targetBoundary valueBound 2
          (compactNumericVerifierTaskRowCoordinatesOf
            combineStart combineFinish combineTag
            combineGammaFinish combineGammaCount combineGammaBoundary
            combineFirstFinish combineFirstCount
            combineSecondFinish combineSecondCount
            combineWitnessFinish combineWitnessCount combineSuffixCount)
          { gammaBoundarySize := combineGammaBoundarySize } := by
    rw [hcombineEnv]
    exact compactNumericVerifierTaskBoundedAtDef_spec
      tokenTable width tokenCount targetBoundary valueBound 2
      combineStart combineFinish combineTag
      combineGammaFinish combineGammaCount combineGammaBoundary
      combineFirstFinish combineFirstCount
      combineSecondFinish combineSecondCount
      combineWitnessFinish combineWitnessCount combineSuffixCount
      combineGammaBoundarySize
  have hslicesSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 53), #1, #2, #8, #9, #39, #40])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          rootStart rootFinish combineStart combineFinish := by
    rw [hslicesEnv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount
      rootStart rootFinish combineStart combineFinish
  simp [compactNumericVerifierTwoParseScheduleRowsDef,
    CompactNumericVerifierTwoParseScheduleRows,
    CompactNumericParseTaskShape,
    compactNumericVerifierTaskRowCoordinatesOf,
    hreplaceSpec, hfirstSpec, hsecondSpec, hcombineSpec, hslicesSpec]
  simp [env, compactNumericVerifierTwoParseScheduleRowsEnvironment]
  intros
  rfl

set_option maxRecDepth 8192 in
theorem compactNumericVerifierOneParseScheduleRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierOneParseScheduleRowsDef.val := by
  simp [compactNumericVerifierOneParseScheduleRowsDef]

set_option maxRecDepth 8192 in
theorem compactNumericVerifierTwoParseScheduleRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierTwoParseScheduleRowsDef.val := by
  simp [compactNumericVerifierTwoParseScheduleRowsDef]

#print axioms compactNumericVerifierOneParseScheduleRowsDef_spec
#print axioms compactNumericVerifierTwoParseScheduleRowsDef_spec
#print axioms compactNumericVerifierOneParseScheduleRowsDef_sigmaZero
#print axioms compactNumericVerifierTwoParseScheduleRowsDef_sigmaZero

end FoundationCompactNumericListedDirectVerifierParseScheduleFormula
