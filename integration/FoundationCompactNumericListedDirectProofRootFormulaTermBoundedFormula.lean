import integration.FoundationCompactNumericListedDirectProofRootFormulaTermEndpoint

/-!
# Bounded arithmetic formula for the formula-term proof-root endpoint

The tag 6 endpoint is exposed as one sixty-eight-column Delta-zero graph.
Its fifty-nine local coordinates are bounded by one public witness.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootFormulaTermBoundedFormula

open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectSequentFormulaEndpointFormula
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula
open FoundationCompactNumericListedDirectProofRootFormulaTermEndpoint

def compactProofRootFormulaTermEndpointGraphDef : 𝚺₀.Semisentence 68 :=
  .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish
      inputBoundary inputCount inputBoundarySize
      taskStart taskFinish taskTag taskGammaFinish taskGammaCount
      taskGammaBoundary taskFirstFinish taskFirstCount
      taskSecondFinish taskSecondCount taskWitnessFinish taskWitnessCount
      taskSuffixCount taskGammaBoundarySize
      finalStart finalFinish
      sequentInputBoundary sequentInputCount sequentInputBoundarySize
      sequentFirstStart sequentFirstFinish sequentFirstBoundary
      sequentFirstCount sequentFirstBoundarySize
      sequentSuffixBoundary sequentSuffixCount
      sequentValueBoundary sequentValueCount sequentValueBoundarySize
      sequentFinalBoundary sequentFinalCount sequentFinalBoundarySize
      sequentTraceTableWidth sequentTraceValueBound
      firstInputBoundary firstInputCount firstInputBoundarySize
      firstExpectedBoundary firstExpectedCount firstExpectedBoundarySize
      firstStateBoundary firstStateCount firstTableWidth firstValueBound
      middleStart middleFinish
      secondInputBoundary secondInputCount secondInputBoundarySize
      secondExpectedBoundary secondExpectedCount secondExpectedBoundarySize
      secondStateBoundary secondStateCount secondTableWidth secondValueBound.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    taskStart = rootStart ∧
    taskFinish = rootFinish ∧
    !(compactNumericVerifierTaskCoreGraphDef)
      tokenTable width tokenCount
      taskStart taskFinish taskTag taskGammaFinish taskGammaCount
      taskGammaBoundary taskFirstFinish taskFirstCount
      taskSecondFinish taskSecondCount taskWitnessFinish taskWitnessCount
      taskSuffixCount taskGammaBoundarySize ∧
    taskTag = 6 ∧
    taskSecondCount = 0 ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount
      sequentInputBoundary sequentInputCount
      inputBoundary inputCount taskTag ∧
    !(compactSequentFormulaEndpointGraphDef)
      tokenTable width tokenCount bodyStart bodyFinish
      (taskStart + 1) taskGammaFinish finalStart finalFinish
      sequentInputBoundary sequentInputCount sequentInputBoundarySize
      sequentFirstStart sequentFirstFinish sequentFirstBoundary
      sequentFirstCount sequentFirstBoundarySize
      sequentSuffixBoundary sequentSuffixCount
      sequentValueBoundary sequentValueCount sequentValueBoundarySize
      sequentFinalBoundary sequentFinalCount sequentFinalBoundarySize
      sequentTraceTableWidth sequentTraceValueBound ∧
    !(compactParserSyntaxExactEndpointGraphDef)
      tokenTable width tokenCount finalStart finalFinish
      middleStart middleFinish 1 1 0
      firstInputBoundary firstInputCount firstInputBoundarySize
      firstExpectedBoundary firstExpectedCount firstExpectedBoundarySize
      firstStateBoundary firstStateCount firstTableWidth firstValueBound ∧
    !(compactParserSyntaxExactEndpointGraphDef)
      tokenTable width tokenCount middleStart middleFinish
      taskWitnessFinish taskFinish 0 0 0
      secondInputBoundary secondInputCount secondInputBoundarySize
      secondExpectedBoundary secondExpectedCount secondExpectedBoundarySize
      secondStateBoundary secondStateCount secondTableWidth secondValueBound ∧
    !(compactAdditiveNatListAppendSlicesDef)
      tokenTable width tokenCount
      taskGammaFinish taskFirstFinish taskFirstCount
      middleStart middleFinish firstExpectedCount
      finalStart finalFinish firstInputCount ∧
    !(compactAdditiveNatListAppendSlicesDef)
      tokenTable width tokenCount
      taskSecondFinish taskWitnessFinish taskWitnessCount
      taskWitnessFinish taskFinish taskSuffixCount
      middleStart middleFinish secondInputCount”

def compactProofRootFormulaTermEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootFormulaTermEndpointCoordinates) :
    Fin 68 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.root.start, coordinates.root.finish, coordinates.root.tag,
    coordinates.root.gammaFinish, coordinates.root.gammaCount,
    coordinates.root.gammaBoundary, coordinates.root.firstFinish,
    coordinates.root.firstCount, coordinates.root.secondFinish,
    coordinates.root.secondCount, coordinates.root.witnessFinish,
    coordinates.root.witnessCount, coordinates.root.suffixCount,
    coordinates.rootSize.gammaBoundarySize,
    coordinates.finalStart, coordinates.finalFinish,
    coordinates.sequent.inputBoundary, coordinates.sequent.inputCount,
    coordinates.sequent.inputBoundarySize,
    coordinates.sequent.firstStart, coordinates.sequent.firstFinish,
    coordinates.sequent.firstBoundary, coordinates.sequent.firstCount,
    coordinates.sequent.firstBoundarySize,
    coordinates.sequent.suffixBoundary, coordinates.sequent.suffixCount,
    coordinates.sequent.valueBoundary, coordinates.sequent.valueCount,
    coordinates.sequent.valueBoundarySize,
    coordinates.sequent.finalBoundary, coordinates.sequent.finalCount,
    coordinates.sequent.finalBoundarySize,
    coordinates.sequent.traceTableWidth,
    coordinates.sequent.traceValueBound,
    coordinates.formula.inputBoundary,
    coordinates.formula.inputCount,
    coordinates.formula.inputBoundarySize,
    coordinates.formula.expectedBoundary,
    coordinates.formula.expectedCount,
    coordinates.formula.expectedBoundarySize,
    coordinates.formula.stateBoundary,
    coordinates.formula.stateCount,
    coordinates.formula.tableWidth,
    coordinates.formula.valueBound,
    coordinates.middleStart, coordinates.middleFinish,
    coordinates.term.inputBoundary,
    coordinates.term.inputCount,
    coordinates.term.inputBoundarySize,
    coordinates.term.expectedBoundary,
    coordinates.term.expectedCount,
    coordinates.term.expectedBoundarySize,
    coordinates.term.stateBoundary,
    coordinates.term.stateCount,
    coordinates.term.tableWidth,
    coordinates.term.valueBound]

set_option maxRecDepth 4096 in
@[simp] theorem compactProofRootFormulaTermEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootFormulaTermEndpointCoordinates) :
    compactProofRootFormulaTermEndpointGraphDef.val.Evalb
        (compactProofRootFormulaTermEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish coordinates) ↔
      CompactProofRootFormulaTermEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  let env := compactProofRootFormulaTermEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish coordinates
  change compactProofRootFormulaTermEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2, #3, #10, #4,
          #9, #11]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have htaskEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2,
          #12, #13, #14, #15, #16, #17, #18, #19, #20, #21,
          #22, #23, #24, #25]) =
        compactNumericVerifierTaskCoreFormulaEnvironment
          tokenTable width tokenCount
          coordinates.root.start coordinates.root.finish
          coordinates.root.tag coordinates.root.gammaFinish
          coordinates.root.gammaCount coordinates.root.gammaBoundary
          coordinates.root.firstFinish coordinates.root.firstCount
          coordinates.root.secondFinish coordinates.root.secondCount
          coordinates.root.witnessFinish coordinates.root.witnessCount
          coordinates.root.suffixCount
          coordinates.rootSize.gammaBoundarySize := by
    funext index
    fin_cases index <;> rfl
  have hconsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2,
          #28, #29, #9, #10, #14]) =
        ![tokenTable, width, tokenCount,
          coordinates.sequent.inputBoundary,
          coordinates.sequent.inputCount,
          coordinates.inputBoundary, coordinates.inputCount,
          coordinates.root.tag] := by
    funext index
    fin_cases index <;> rfl
  have hsequentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2, #7, #8,
          ‘(#12 + 1)’, #15, #26, #27,
          #28, #29, #30, #31, #32, #33, #34, #35,
          #36, #37, #38, #39, #40, #41, #42, #43, #44, #45]) =
        compactSequentFormulaEndpointEnvironment
          tokenTable width tokenCount bodyStart bodyFinish
          (coordinates.root.start + 1) coordinates.root.gammaFinish
          coordinates.finalStart coordinates.finalFinish
          coordinates.sequent := by
    funext index
    fin_cases index <;> simp [env,
      compactProofRootFormulaTermEndpointEnvironment,
      compactSequentFormulaEndpointEnvironment]
  have hfirstEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2, #26, #27,
          #56, #57, ‘1’, ‘1’, ‘0’,
          #46, #47, #48, #49, #50, #51, #52, #53, #54, #55]) =
        compactParserSyntaxExactEndpointEnvironment
          tokenTable width tokenCount
          coordinates.finalStart coordinates.finalFinish
          coordinates.middleStart coordinates.middleFinish 1 1 0
          coordinates.formula := by
    funext index
    fin_cases index <;> simp [env,
      compactProofRootFormulaTermEndpointEnvironment,
      compactParserSyntaxExactEndpointEnvironment]
  have hsecondEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2, #56, #57,
          #22, #13, ‘0’, ‘0’, ‘0’,
          #58, #59, #60, #61, #62, #63, #64, #65, #66, #67]) =
        compactParserSyntaxExactEndpointEnvironment
          tokenTable width tokenCount
          coordinates.middleStart coordinates.middleFinish
          coordinates.root.witnessFinish coordinates.root.finish 0 0 0
          coordinates.term := by
    funext index
    fin_cases index <;> simp [env,
      compactProofRootFormulaTermEndpointEnvironment,
      compactParserSyntaxExactEndpointEnvironment]
  have hfirstAppendEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2,
          #15, #18, #19, #56, #57, #50, #26, #27, #47]) =
        ![tokenTable, width, tokenCount,
          coordinates.root.gammaFinish, coordinates.root.firstFinish,
          coordinates.root.firstCount,
          coordinates.middleStart, coordinates.middleFinish,
          coordinates.formula.expectedCount,
          coordinates.finalStart, coordinates.finalFinish,
          coordinates.formula.inputCount] := by
    funext index
    fin_cases index <;> rfl
  have hsecondAppendEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2,
          #20, #22, #23, #22, #13, #24, #56, #57, #59]) =
        ![tokenTable, width, tokenCount,
          coordinates.root.secondFinish, coordinates.root.witnessFinish,
          coordinates.root.witnessCount,
          coordinates.root.witnessFinish, coordinates.root.finish,
          coordinates.root.suffixCount,
          coordinates.middleStart, coordinates.middleFinish,
          coordinates.term.inputCount] := by
    funext index
    fin_cases index <;> rfl
  have hrootStartValue : env 12 = coordinates.root.start := rfl
  have hrootFinishValue : env 13 = coordinates.root.finish := rfl
  have hrootStartParameterValue : env 5 = rootStart := rfl
  have hrootFinishParameterValue : env 6 = rootFinish := rfl
  have hrootTagValue : env 14 = coordinates.root.tag := rfl
  have hsecondCountValue : env 21 = coordinates.root.secondCount := rfl
  have hrootCoordinatesOf :
      compactNumericVerifierTaskRowCoordinatesOf
        coordinates.root.start coordinates.root.finish coordinates.root.tag
        coordinates.root.gammaFinish coordinates.root.gammaCount
        coordinates.root.gammaBoundary coordinates.root.firstFinish
        coordinates.root.firstCount coordinates.root.secondFinish
        coordinates.root.secondCount coordinates.root.witnessFinish
        coordinates.root.witnessCount coordinates.root.suffixCount =
          coordinates.root := by
    cases coordinates.root
    rfl
  have hrootSizeOf :
      (CompactNumericVerifierTaskSizeWitness.mk
        coordinates.rootSize.gammaBoundarySize) = coordinates.rootSize := by
    cases coordinates.rootSize
    rfl
  simp [compactProofRootFormulaTermEndpointGraphDef,
    CompactProofRootFormulaTermEndpointGraph,
    hinputEnv, htaskEnv, hconsEnv, hsequentEnv, hfirstEnv, hsecondEnv,
    hfirstAppendEnv, hsecondAppendEnv,
    hrootStartValue, hrootFinishValue, hrootStartParameterValue,
    hrootFinishParameterValue, hrootTagValue, hsecondCountValue,
    hrootCoordinatesOf, hrootSizeOf] <;> tauto

theorem compactProofRootFormulaTermEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootFormulaTermEndpointGraphDef.val := by
  simp [compactProofRootFormulaTermEndpointGraphDef]


def compactProofRootFormulaTermEndpointCoordinatesOfValues
    (
      inputBoundary inputCount inputBoundarySize
      taskStart taskFinish taskTag taskGammaFinish taskGammaCount taskGammaBoundary taskFirstFinish taskFirstCount taskSecondFinish taskSecondCount taskWitnessFinish taskWitnessCount taskSuffixCount taskGammaBoundarySize
      finalStart finalFinish
      sequentInputBoundary sequentInputCount sequentInputBoundarySize sequentFirstStart sequentFirstFinish sequentFirstBoundary sequentFirstCount sequentFirstBoundarySize sequentSuffixBoundary sequentSuffixCount sequentValueBoundary sequentValueCount sequentValueBoundarySize sequentFinalBoundary sequentFinalCount sequentFinalBoundarySize sequentTraceTableWidth sequentTraceValueBound
      firstInputBoundary firstInputCount firstInputBoundarySize firstExpectedBoundary firstExpectedCount firstExpectedBoundarySize firstStateBoundary firstStateCount firstTableWidth firstValueBound
      middleStart middleFinish
      secondInputBoundary secondInputCount secondInputBoundarySize secondExpectedBoundary secondExpectedCount secondExpectedBoundarySize secondStateBoundary secondStateCount secondTableWidth secondValueBound : Nat) :
    CompactProofRootFormulaTermEndpointCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    root :=
      { start := taskStart
        finish := taskFinish
        tag := taskTag
        gammaFinish := taskGammaFinish
        gammaCount := taskGammaCount
        gammaBoundary := taskGammaBoundary
        firstFinish := taskFirstFinish
        firstCount := taskFirstCount
        secondFinish := taskSecondFinish
        secondCount := taskSecondCount
        witnessFinish := taskWitnessFinish
        witnessCount := taskWitnessCount
        suffixCount := taskSuffixCount }
    rootSize := { gammaBoundarySize := taskGammaBoundarySize }
    finalStart := finalStart
    finalFinish := finalFinish
    middleStart := middleStart
    middleFinish := middleFinish
    sequent :=
      { inputBoundary := sequentInputBoundary
        inputCount := sequentInputCount
        inputBoundarySize := sequentInputBoundarySize
        firstStart := sequentFirstStart
        firstFinish := sequentFirstFinish
        firstBoundary := sequentFirstBoundary
        firstCount := sequentFirstCount
        firstBoundarySize := sequentFirstBoundarySize
        suffixBoundary := sequentSuffixBoundary
        suffixCount := sequentSuffixCount
        valueBoundary := sequentValueBoundary
        valueCount := sequentValueCount
        valueBoundarySize := sequentValueBoundarySize
        finalBoundary := sequentFinalBoundary
        finalCount := sequentFinalCount
        finalBoundarySize := sequentFinalBoundarySize
        traceTableWidth := sequentTraceTableWidth
        traceValueBound := sequentTraceValueBound }
    formula :=
      { inputBoundary := firstInputBoundary
        inputCount := firstInputCount
        inputBoundarySize := firstInputBoundarySize
        expectedBoundary := firstExpectedBoundary
        expectedCount := firstExpectedCount
        expectedBoundarySize := firstExpectedBoundarySize
        stateBoundary := firstStateBoundary
        stateCount := firstStateCount
        tableWidth := firstTableWidth
        valueBound := firstValueBound }
    term :=
      { inputBoundary := secondInputBoundary
        inputCount := secondInputCount
        inputBoundarySize := secondInputBoundarySize
        expectedBoundary := secondExpectedBoundary
        expectedCount := secondExpectedCount
        expectedBoundarySize := secondExpectedBoundarySize
        stateBoundary := secondStateBoundary
        stateCount := secondStateCount
        tableWidth := secondTableWidth
        valueBound := secondValueBound } }

def CompactProofRootFormulaTermEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish endpointBound : Nat) : Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ taskStart, taskStart ≤ endpointBound ∧
  ∃ taskFinish, taskFinish ≤ endpointBound ∧
  ∃ taskTag, taskTag ≤ endpointBound ∧
  ∃ taskGammaFinish, taskGammaFinish ≤ endpointBound ∧
  ∃ taskGammaCount, taskGammaCount ≤ endpointBound ∧
  ∃ taskGammaBoundary, taskGammaBoundary ≤ endpointBound ∧
  ∃ taskFirstFinish, taskFirstFinish ≤ endpointBound ∧
  ∃ taskFirstCount, taskFirstCount ≤ endpointBound ∧
  ∃ taskSecondFinish, taskSecondFinish ≤ endpointBound ∧
  ∃ taskSecondCount, taskSecondCount ≤ endpointBound ∧
  ∃ taskWitnessFinish, taskWitnessFinish ≤ endpointBound ∧
  ∃ taskWitnessCount, taskWitnessCount ≤ endpointBound ∧
  ∃ taskSuffixCount, taskSuffixCount ≤ endpointBound ∧
  ∃ taskGammaBoundarySize, taskGammaBoundarySize ≤ endpointBound ∧
  ∃ finalStart, finalStart ≤ endpointBound ∧
  ∃ finalFinish, finalFinish ≤ endpointBound ∧
  ∃ sequentInputBoundary, sequentInputBoundary ≤ endpointBound ∧
  ∃ sequentInputCount, sequentInputCount ≤ endpointBound ∧
  ∃ sequentInputBoundarySize, sequentInputBoundarySize ≤ endpointBound ∧
  ∃ sequentFirstStart, sequentFirstStart ≤ endpointBound ∧
  ∃ sequentFirstFinish, sequentFirstFinish ≤ endpointBound ∧
  ∃ sequentFirstBoundary, sequentFirstBoundary ≤ endpointBound ∧
  ∃ sequentFirstCount, sequentFirstCount ≤ endpointBound ∧
  ∃ sequentFirstBoundarySize, sequentFirstBoundarySize ≤ endpointBound ∧
  ∃ sequentSuffixBoundary, sequentSuffixBoundary ≤ endpointBound ∧
  ∃ sequentSuffixCount, sequentSuffixCount ≤ endpointBound ∧
  ∃ sequentValueBoundary, sequentValueBoundary ≤ endpointBound ∧
  ∃ sequentValueCount, sequentValueCount ≤ endpointBound ∧
  ∃ sequentValueBoundarySize, sequentValueBoundarySize ≤ endpointBound ∧
  ∃ sequentFinalBoundary, sequentFinalBoundary ≤ endpointBound ∧
  ∃ sequentFinalCount, sequentFinalCount ≤ endpointBound ∧
  ∃ sequentFinalBoundarySize, sequentFinalBoundarySize ≤ endpointBound ∧
  ∃ sequentTraceTableWidth, sequentTraceTableWidth ≤ endpointBound ∧
  ∃ sequentTraceValueBound, sequentTraceValueBound ≤ endpointBound ∧
  ∃ firstInputBoundary, firstInputBoundary ≤ endpointBound ∧
  ∃ firstInputCount, firstInputCount ≤ endpointBound ∧
  ∃ firstInputBoundarySize, firstInputBoundarySize ≤ endpointBound ∧
  ∃ firstExpectedBoundary, firstExpectedBoundary ≤ endpointBound ∧
  ∃ firstExpectedCount, firstExpectedCount ≤ endpointBound ∧
  ∃ firstExpectedBoundarySize, firstExpectedBoundarySize ≤ endpointBound ∧
  ∃ firstStateBoundary, firstStateBoundary ≤ endpointBound ∧
  ∃ firstStateCount, firstStateCount ≤ endpointBound ∧
  ∃ firstTableWidth, firstTableWidth ≤ endpointBound ∧
  ∃ firstValueBound, firstValueBound ≤ endpointBound ∧
  ∃ middleStart, middleStart ≤ endpointBound ∧
  ∃ middleFinish, middleFinish ≤ endpointBound ∧
  ∃ secondInputBoundary, secondInputBoundary ≤ endpointBound ∧
  ∃ secondInputCount, secondInputCount ≤ endpointBound ∧
  ∃ secondInputBoundarySize, secondInputBoundarySize ≤ endpointBound ∧
  ∃ secondExpectedBoundary, secondExpectedBoundary ≤ endpointBound ∧
  ∃ secondExpectedCount, secondExpectedCount ≤ endpointBound ∧
  ∃ secondExpectedBoundarySize, secondExpectedBoundarySize ≤ endpointBound ∧
  ∃ secondStateBoundary, secondStateBoundary ≤ endpointBound ∧
  ∃ secondStateCount, secondStateCount ≤ endpointBound ∧
  ∃ secondTableWidth, secondTableWidth ≤ endpointBound ∧
  ∃ secondValueBound, secondValueBound ≤ endpointBound ∧
    CompactProofRootFormulaTermEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish
        (compactProofRootFormulaTermEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize taskStart taskFinish
          taskTag taskGammaFinish taskGammaCount taskGammaBoundary taskFirstFinish
          taskFirstCount taskSecondFinish taskSecondCount taskWitnessFinish taskWitnessCount
          taskSuffixCount taskGammaBoundarySize finalStart finalFinish sequentInputBoundary
          sequentInputCount sequentInputBoundarySize sequentFirstStart sequentFirstFinish sequentFirstBoundary
          sequentFirstCount sequentFirstBoundarySize sequentSuffixBoundary sequentSuffixCount sequentValueBoundary
          sequentValueCount sequentValueBoundarySize sequentFinalBoundary sequentFinalCount sequentFinalBoundarySize
          sequentTraceTableWidth sequentTraceValueBound firstInputBoundary firstInputCount firstInputBoundarySize
          firstExpectedBoundary firstExpectedCount firstExpectedBoundarySize firstStateBoundary firstStateCount
          firstTableWidth firstValueBound middleStart middleFinish secondInputBoundary
          secondInputCount secondInputBoundarySize secondExpectedBoundary secondExpectedCount secondExpectedBoundarySize
          secondStateBoundary secondStateCount secondTableWidth secondValueBound)

def compactProofRootFormulaTermEndpointBoundedGraphDef :
    𝚺₀.Semisentence 10 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish endpointBound.
    ∃ inputBoundary <⁺ endpointBound,
    ∃ inputCount <⁺ endpointBound,
    ∃ inputBoundarySize <⁺ endpointBound,
    ∃ taskStart <⁺ endpointBound,
    ∃ taskFinish <⁺ endpointBound,
    ∃ taskTag <⁺ endpointBound,
    ∃ taskGammaFinish <⁺ endpointBound,
    ∃ taskGammaCount <⁺ endpointBound,
    ∃ taskGammaBoundary <⁺ endpointBound,
    ∃ taskFirstFinish <⁺ endpointBound,
    ∃ taskFirstCount <⁺ endpointBound,
    ∃ taskSecondFinish <⁺ endpointBound,
    ∃ taskSecondCount <⁺ endpointBound,
    ∃ taskWitnessFinish <⁺ endpointBound,
    ∃ taskWitnessCount <⁺ endpointBound,
    ∃ taskSuffixCount <⁺ endpointBound,
    ∃ taskGammaBoundarySize <⁺ endpointBound,
    ∃ finalStart <⁺ endpointBound,
    ∃ finalFinish <⁺ endpointBound,
    ∃ sequentInputBoundary <⁺ endpointBound,
    ∃ sequentInputCount <⁺ endpointBound,
    ∃ sequentInputBoundarySize <⁺ endpointBound,
    ∃ sequentFirstStart <⁺ endpointBound,
    ∃ sequentFirstFinish <⁺ endpointBound,
    ∃ sequentFirstBoundary <⁺ endpointBound,
    ∃ sequentFirstCount <⁺ endpointBound,
    ∃ sequentFirstBoundarySize <⁺ endpointBound,
    ∃ sequentSuffixBoundary <⁺ endpointBound,
    ∃ sequentSuffixCount <⁺ endpointBound,
    ∃ sequentValueBoundary <⁺ endpointBound,
    ∃ sequentValueCount <⁺ endpointBound,
    ∃ sequentValueBoundarySize <⁺ endpointBound,
    ∃ sequentFinalBoundary <⁺ endpointBound,
    ∃ sequentFinalCount <⁺ endpointBound,
    ∃ sequentFinalBoundarySize <⁺ endpointBound,
    ∃ sequentTraceTableWidth <⁺ endpointBound,
    ∃ sequentTraceValueBound <⁺ endpointBound,
    ∃ firstInputBoundary <⁺ endpointBound,
    ∃ firstInputCount <⁺ endpointBound,
    ∃ firstInputBoundarySize <⁺ endpointBound,
    ∃ firstExpectedBoundary <⁺ endpointBound,
    ∃ firstExpectedCount <⁺ endpointBound,
    ∃ firstExpectedBoundarySize <⁺ endpointBound,
    ∃ firstStateBoundary <⁺ endpointBound,
    ∃ firstStateCount <⁺ endpointBound,
    ∃ firstTableWidth <⁺ endpointBound,
    ∃ firstValueBound <⁺ endpointBound,
    ∃ middleStart <⁺ endpointBound,
    ∃ middleFinish <⁺ endpointBound,
    ∃ secondInputBoundary <⁺ endpointBound,
    ∃ secondInputCount <⁺ endpointBound,
    ∃ secondInputBoundarySize <⁺ endpointBound,
    ∃ secondExpectedBoundary <⁺ endpointBound,
    ∃ secondExpectedCount <⁺ endpointBound,
    ∃ secondExpectedBoundarySize <⁺ endpointBound,
    ∃ secondStateBoundary <⁺ endpointBound,
    ∃ secondStateCount <⁺ endpointBound,
    ∃ secondTableWidth <⁺ endpointBound,
    ∃ secondValueBound <⁺ endpointBound,
      !(compactProofRootFormulaTermEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish inputBoundary
        inputCount inputBoundarySize taskStart taskFinish taskTag
        taskGammaFinish taskGammaCount taskGammaBoundary taskFirstFinish taskFirstCount
        taskSecondFinish taskSecondCount taskWitnessFinish taskWitnessCount taskSuffixCount
        taskGammaBoundarySize finalStart finalFinish sequentInputBoundary sequentInputCount
        sequentInputBoundarySize sequentFirstStart sequentFirstFinish sequentFirstBoundary sequentFirstCount
        sequentFirstBoundarySize sequentSuffixBoundary sequentSuffixCount sequentValueBoundary sequentValueCount
        sequentValueBoundarySize sequentFinalBoundary sequentFinalCount sequentFinalBoundarySize sequentTraceTableWidth
        sequentTraceValueBound firstInputBoundary firstInputCount firstInputBoundarySize firstExpectedBoundary
        firstExpectedCount firstExpectedBoundarySize firstStateBoundary firstStateCount firstTableWidth
        firstValueBound middleStart middleFinish secondInputBoundary secondInputCount
        secondInputBoundarySize secondExpectedBoundary secondExpectedCount secondExpectedBoundarySize secondStateBoundary
        secondStateCount secondTableWidth secondValueBound”

set_option maxRecDepth 32768 in
@[simp] theorem compactProofRootFormulaTermEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish endpointBound : Nat) :
    compactProofRootFormulaTermEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          rootStart, rootFinish, bodyStart, bodyFinish, endpointBound] ↔
      CompactProofRootFormulaTermEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish endpointBound := by
  have hrow
      (
        secondValueBound secondTableWidth secondStateCount secondStateBoundary secondExpectedBoundarySize
        secondExpectedCount secondExpectedBoundary secondInputBoundarySize secondInputCount secondInputBoundary
        middleFinish middleStart firstValueBound firstTableWidth firstStateCount
        firstStateBoundary firstExpectedBoundarySize firstExpectedCount firstExpectedBoundary firstInputBoundarySize
        firstInputCount firstInputBoundary sequentTraceValueBound sequentTraceTableWidth sequentFinalBoundarySize
        sequentFinalCount sequentFinalBoundary sequentValueBoundarySize sequentValueCount sequentValueBoundary
        sequentSuffixCount sequentSuffixBoundary sequentFirstBoundarySize sequentFirstCount sequentFirstBoundary
        sequentFirstFinish sequentFirstStart sequentInputBoundarySize sequentInputCount sequentInputBoundary
        finalFinish finalStart taskGammaBoundarySize taskSuffixCount taskWitnessCount
        taskWitnessFinish taskSecondCount taskSecondFinish taskFirstCount taskFirstFinish
        taskGammaBoundary taskGammaCount taskGammaFinish taskTag taskFinish
        taskStart inputBoundarySize inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![
              secondValueBound, secondTableWidth, secondStateCount, secondStateBoundary,
              secondExpectedBoundarySize, secondExpectedCount, secondExpectedBoundary, secondInputBoundarySize,
              secondInputCount, secondInputBoundary, middleFinish, middleStart,
              firstValueBound, firstTableWidth, firstStateCount, firstStateBoundary,
              firstExpectedBoundarySize, firstExpectedCount, firstExpectedBoundary, firstInputBoundarySize,
              firstInputCount, firstInputBoundary, sequentTraceValueBound, sequentTraceTableWidth,
              sequentFinalBoundarySize, sequentFinalCount, sequentFinalBoundary, sequentValueBoundarySize,
              sequentValueCount, sequentValueBoundary, sequentSuffixCount, sequentSuffixBoundary,
              sequentFirstBoundarySize, sequentFirstCount, sequentFirstBoundary, sequentFirstFinish,
              sequentFirstStart, sequentInputBoundarySize, sequentInputCount, sequentInputBoundary,
              finalFinish, finalStart, taskGammaBoundarySize, taskSuffixCount,
              taskWitnessCount, taskWitnessFinish, taskSecondCount, taskSecondFinish,
              taskFirstCount, taskFirstFinish, taskGammaBoundary, taskGammaCount,
              taskGammaFinish, taskTag, taskFinish, taskStart,
              inputBoundarySize, inputCount, inputBoundary, tokenTable,
              width, tokenCount, inputStart, inputFinish,
              rootStart, rootFinish, bodyStart, bodyFinish,
              endpointBound]
              Empty.elim ∘
            ![
            (#59 : Semiterm ℒₒᵣ Empty 69), #60, #61, #62, #63, #64, #65, #66, #67,
            #58, #57, #56, #55, #54, #53, #52, #51, #50,
            #49, #48, #47, #46, #45, #44, #43, #42, #41,
            #40, #39, #38, #37, #36, #35, #34, #33, #32,
            #31, #30, #29, #28, #27, #26, #25, #24, #23,
            #22, #21, #20, #19, #18, #17, #16, #15, #14,
            #13, #12, #11, #10, #9, #8, #7, #6, #5,
            #4, #3, #2, #1, #0])
          Empty.elim) compactProofRootFormulaTermEndpointGraphDef.val ↔
        CompactProofRootFormulaTermEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish
            (compactProofRootFormulaTermEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize taskStart taskFinish
          taskTag taskGammaFinish taskGammaCount taskGammaBoundary taskFirstFinish
          taskFirstCount taskSecondFinish taskSecondCount taskWitnessFinish taskWitnessCount
          taskSuffixCount taskGammaBoundarySize finalStart finalFinish sequentInputBoundary
          sequentInputCount sequentInputBoundarySize sequentFirstStart sequentFirstFinish sequentFirstBoundary
          sequentFirstCount sequentFirstBoundarySize sequentSuffixBoundary sequentSuffixCount sequentValueBoundary
          sequentValueCount sequentValueBoundarySize sequentFinalBoundary sequentFinalCount sequentFinalBoundarySize
          sequentTraceTableWidth sequentTraceValueBound firstInputBoundary firstInputCount firstInputBoundarySize
          firstExpectedBoundary firstExpectedCount firstExpectedBoundarySize firstStateBoundary firstStateCount
          firstTableWidth firstValueBound middleStart middleFinish secondInputBoundary
          secondInputCount secondInputBoundarySize secondExpectedBoundary secondExpectedCount secondExpectedBoundarySize
          secondStateBoundary secondStateCount secondTableWidth secondValueBound) := by
    have henv :
        (Semiterm.val
            ![
              secondValueBound, secondTableWidth, secondStateCount, secondStateBoundary,
              secondExpectedBoundarySize, secondExpectedCount, secondExpectedBoundary, secondInputBoundarySize,
              secondInputCount, secondInputBoundary, middleFinish, middleStart,
              firstValueBound, firstTableWidth, firstStateCount, firstStateBoundary,
              firstExpectedBoundarySize, firstExpectedCount, firstExpectedBoundary, firstInputBoundarySize,
              firstInputCount, firstInputBoundary, sequentTraceValueBound, sequentTraceTableWidth,
              sequentFinalBoundarySize, sequentFinalCount, sequentFinalBoundary, sequentValueBoundarySize,
              sequentValueCount, sequentValueBoundary, sequentSuffixCount, sequentSuffixBoundary,
              sequentFirstBoundarySize, sequentFirstCount, sequentFirstBoundary, sequentFirstFinish,
              sequentFirstStart, sequentInputBoundarySize, sequentInputCount, sequentInputBoundary,
              finalFinish, finalStart, taskGammaBoundarySize, taskSuffixCount,
              taskWitnessCount, taskWitnessFinish, taskSecondCount, taskSecondFinish,
              taskFirstCount, taskFirstFinish, taskGammaBoundary, taskGammaCount,
              taskGammaFinish, taskTag, taskFinish, taskStart,
              inputBoundarySize, inputCount, inputBoundary, tokenTable,
              width, tokenCount, inputStart, inputFinish,
              rootStart, rootFinish, bodyStart, bodyFinish,
              endpointBound]
            Empty.elim ∘
          ![
            (#59 : Semiterm ℒₒᵣ Empty 69), #60, #61, #62, #63, #64, #65, #66, #67,
            #58, #57, #56, #55, #54, #53, #52, #51, #50,
            #49, #48, #47, #46, #45, #44, #43, #42, #41,
            #40, #39, #38, #37, #36, #35, #34, #33, #32,
            #31, #30, #29, #28, #27, #26, #25, #24, #23,
            #22, #21, #20, #19, #18, #17, #16, #15, #14,
            #13, #12, #11, #10, #9, #8, #7, #6, #5,
            #4, #3, #2, #1, #0]) =
          compactProofRootFormulaTermEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              rootStart rootFinish bodyStart bodyFinish
              (compactProofRootFormulaTermEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize taskStart taskFinish
          taskTag taskGammaFinish taskGammaCount taskGammaBoundary taskFirstFinish
          taskFirstCount taskSecondFinish taskSecondCount taskWitnessFinish taskWitnessCount
          taskSuffixCount taskGammaBoundarySize finalStart finalFinish sequentInputBoundary
          sequentInputCount sequentInputBoundarySize sequentFirstStart sequentFirstFinish sequentFirstBoundary
          sequentFirstCount sequentFirstBoundarySize sequentSuffixBoundary sequentSuffixCount sequentValueBoundary
          sequentValueCount sequentValueBoundarySize sequentFinalBoundary sequentFinalCount sequentFinalBoundarySize
          sequentTraceTableWidth sequentTraceValueBound firstInputBoundary firstInputCount firstInputBoundarySize
          firstExpectedBoundary firstExpectedCount firstExpectedBoundarySize firstStateBoundary firstStateCount
          firstTableWidth firstValueBound middleStart middleFinish secondInputBoundary
          secondInputCount secondInputBoundarySize secondExpectedBoundary secondExpectedCount secondExpectedBoundarySize
          secondStateBoundary secondStateCount secondTableWidth secondValueBound) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactProofRootFormulaTermEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish _
  simp [compactProofRootFormulaTermEndpointBoundedGraphDef,
    CompactProofRootFormulaTermEndpointBoundedGraph, hrow]

theorem compactProofRootFormulaTermEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootFormulaTermEndpointBoundedGraphDef.val := by
  simp [compactProofRootFormulaTermEndpointBoundedGraphDef]

theorem CompactProofRootFormulaTermEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish endpointBound : Nat}
    (hbounded : CompactProofRootFormulaTermEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish endpointBound) :
    ∃ coordinates : CompactProofRootFormulaTermEndpointCoordinates,
      CompactProofRootFormulaTermEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  unfold CompactProofRootFormulaTermEndpointBoundedGraph at hbounded
  rcases hbounded with
    ⟨
      inputBoundary, _hinputBoundary,
      inputCount, _hinputCount,
      inputBoundarySize, _hinputBoundarySize,
      taskStart, _htaskStart,
      taskFinish, _htaskFinish,
      taskTag, _htaskTag,
      taskGammaFinish, _htaskGammaFinish,
      taskGammaCount, _htaskGammaCount,
      taskGammaBoundary, _htaskGammaBoundary,
      taskFirstFinish, _htaskFirstFinish,
      taskFirstCount, _htaskFirstCount,
      taskSecondFinish, _htaskSecondFinish,
      taskSecondCount, _htaskSecondCount,
      taskWitnessFinish, _htaskWitnessFinish,
      taskWitnessCount, _htaskWitnessCount,
      taskSuffixCount, _htaskSuffixCount,
      taskGammaBoundarySize, _htaskGammaBoundarySize,
      finalStart, _hfinalStart,
      finalFinish, _hfinalFinish,
      sequentInputBoundary, _hsequentInputBoundary,
      sequentInputCount, _hsequentInputCount,
      sequentInputBoundarySize, _hsequentInputBoundarySize,
      sequentFirstStart, _hsequentFirstStart,
      sequentFirstFinish, _hsequentFirstFinish,
      sequentFirstBoundary, _hsequentFirstBoundary,
      sequentFirstCount, _hsequentFirstCount,
      sequentFirstBoundarySize, _hsequentFirstBoundarySize,
      sequentSuffixBoundary, _hsequentSuffixBoundary,
      sequentSuffixCount, _hsequentSuffixCount,
      sequentValueBoundary, _hsequentValueBoundary,
      sequentValueCount, _hsequentValueCount,
      sequentValueBoundarySize, _hsequentValueBoundarySize,
      sequentFinalBoundary, _hsequentFinalBoundary,
      sequentFinalCount, _hsequentFinalCount,
      sequentFinalBoundarySize, _hsequentFinalBoundarySize,
      sequentTraceTableWidth, _hsequentTraceTableWidth,
      sequentTraceValueBound, _hsequentTraceValueBound,
      firstInputBoundary, _hfirstInputBoundary,
      firstInputCount, _hfirstInputCount,
      firstInputBoundarySize, _hfirstInputBoundarySize,
      firstExpectedBoundary, _hfirstExpectedBoundary,
      firstExpectedCount, _hfirstExpectedCount,
      firstExpectedBoundarySize, _hfirstExpectedBoundarySize,
      firstStateBoundary, _hfirstStateBoundary,
      firstStateCount, _hfirstStateCount,
      firstTableWidth, _hfirstTableWidth,
      firstValueBound, _hfirstValueBound,
      middleStart, _hmiddleStart,
      middleFinish, _hmiddleFinish,
      secondInputBoundary, _hsecondInputBoundary,
      secondInputCount, _hsecondInputCount,
      secondInputBoundarySize, _hsecondInputBoundarySize,
      secondExpectedBoundary, _hsecondExpectedBoundary,
      secondExpectedCount, _hsecondExpectedCount,
      secondExpectedBoundarySize, _hsecondExpectedBoundarySize,
      secondStateBoundary, _hsecondStateBoundary,
      secondStateCount, _hsecondStateCount,
      secondTableWidth, _hsecondTableWidth,
      secondValueBound, _hsecondValueBound,
      hgraph⟩
  exact ⟨compactProofRootFormulaTermEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize taskStart taskFinish
          taskTag taskGammaFinish taskGammaCount taskGammaBoundary taskFirstFinish
          taskFirstCount taskSecondFinish taskSecondCount taskWitnessFinish taskWitnessCount
          taskSuffixCount taskGammaBoundarySize finalStart finalFinish sequentInputBoundary
          sequentInputCount sequentInputBoundarySize sequentFirstStart sequentFirstFinish sequentFirstBoundary
          sequentFirstCount sequentFirstBoundarySize sequentSuffixBoundary sequentSuffixCount sequentValueBoundary
          sequentValueCount sequentValueBoundarySize sequentFinalBoundary sequentFinalCount sequentFinalBoundarySize
          sequentTraceTableWidth sequentTraceValueBound firstInputBoundary firstInputCount firstInputBoundarySize
          firstExpectedBoundary firstExpectedCount firstExpectedBoundarySize firstStateBoundary firstStateCount
          firstTableWidth firstValueBound middleStart middleFinish secondInputBoundary
          secondInputCount secondInputBoundarySize secondExpectedBoundary secondExpectedCount secondExpectedBoundarySize
          secondStateBoundary secondStateCount secondTableWidth secondValueBound, hgraph⟩

theorem CompactProofRootFormulaTermEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootFormulaTermEndpointCoordinates}
    (hgraph : CompactProofRootFormulaTermEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish coordinates) :
    ∃ endpointBound,
      CompactProofRootFormulaTermEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary +
    coordinates.inputCount +
    coordinates.inputBoundarySize +
    coordinates.root.start +
    coordinates.root.finish +
    coordinates.root.tag +
    coordinates.root.gammaFinish +
    coordinates.root.gammaCount +
    coordinates.root.gammaBoundary +
    coordinates.root.firstFinish +
    coordinates.root.firstCount +
    coordinates.root.secondFinish +
    coordinates.root.secondCount +
    coordinates.root.witnessFinish +
    coordinates.root.witnessCount +
    coordinates.root.suffixCount +
    coordinates.rootSize.gammaBoundarySize +
    coordinates.finalStart +
    coordinates.finalFinish +
    coordinates.sequent.inputBoundary +
    coordinates.sequent.inputCount +
    coordinates.sequent.inputBoundarySize +
    coordinates.sequent.firstStart +
    coordinates.sequent.firstFinish +
    coordinates.sequent.firstBoundary +
    coordinates.sequent.firstCount +
    coordinates.sequent.firstBoundarySize +
    coordinates.sequent.suffixBoundary +
    coordinates.sequent.suffixCount +
    coordinates.sequent.valueBoundary +
    coordinates.sequent.valueCount +
    coordinates.sequent.valueBoundarySize +
    coordinates.sequent.finalBoundary +
    coordinates.sequent.finalCount +
    coordinates.sequent.finalBoundarySize +
    coordinates.sequent.traceTableWidth +
    coordinates.sequent.traceValueBound +
    coordinates.formula.inputBoundary +
    coordinates.formula.inputCount +
    coordinates.formula.inputBoundarySize +
    coordinates.formula.expectedBoundary +
    coordinates.formula.expectedCount +
    coordinates.formula.expectedBoundarySize +
    coordinates.formula.stateBoundary +
    coordinates.formula.stateCount +
    coordinates.formula.tableWidth +
    coordinates.formula.valueBound +
    coordinates.middleStart +
    coordinates.middleFinish +
    coordinates.term.inputBoundary +
    coordinates.term.inputCount +
    coordinates.term.inputBoundarySize +
    coordinates.term.expectedBoundary +
    coordinates.term.expectedCount +
    coordinates.term.expectedBoundarySize +
    coordinates.term.stateBoundary +
    coordinates.term.stateCount +
    coordinates.term.tableWidth +
    coordinates.term.valueBound
  refine ⟨endpointBound, ?_⟩
  unfold CompactProofRootFormulaTermEndpointBoundedGraph
  refine
    ⟨
      coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
      coordinates.inputBoundarySize, ?_, coordinates.root.start, ?_,
      coordinates.root.finish, ?_, coordinates.root.tag, ?_,
      coordinates.root.gammaFinish, ?_, coordinates.root.gammaCount, ?_,
      coordinates.root.gammaBoundary, ?_, coordinates.root.firstFinish, ?_,
      coordinates.root.firstCount, ?_, coordinates.root.secondFinish, ?_,
      coordinates.root.secondCount, ?_, coordinates.root.witnessFinish, ?_,
      coordinates.root.witnessCount, ?_, coordinates.root.suffixCount, ?_,
      coordinates.rootSize.gammaBoundarySize, ?_, coordinates.finalStart, ?_,
      coordinates.finalFinish, ?_, coordinates.sequent.inputBoundary, ?_,
      coordinates.sequent.inputCount, ?_, coordinates.sequent.inputBoundarySize, ?_,
      coordinates.sequent.firstStart, ?_, coordinates.sequent.firstFinish, ?_,
      coordinates.sequent.firstBoundary, ?_, coordinates.sequent.firstCount, ?_,
      coordinates.sequent.firstBoundarySize, ?_, coordinates.sequent.suffixBoundary, ?_,
      coordinates.sequent.suffixCount, ?_, coordinates.sequent.valueBoundary, ?_,
      coordinates.sequent.valueCount, ?_, coordinates.sequent.valueBoundarySize, ?_,
      coordinates.sequent.finalBoundary, ?_, coordinates.sequent.finalCount, ?_,
      coordinates.sequent.finalBoundarySize, ?_, coordinates.sequent.traceTableWidth, ?_,
      coordinates.sequent.traceValueBound, ?_, coordinates.formula.inputBoundary, ?_,
      coordinates.formula.inputCount, ?_, coordinates.formula.inputBoundarySize, ?_,
      coordinates.formula.expectedBoundary, ?_, coordinates.formula.expectedCount, ?_,
      coordinates.formula.expectedBoundarySize, ?_, coordinates.formula.stateBoundary, ?_,
      coordinates.formula.stateCount, ?_, coordinates.formula.tableWidth, ?_,
      coordinates.formula.valueBound, ?_, coordinates.middleStart, ?_,
      coordinates.middleFinish, ?_, coordinates.term.inputBoundary, ?_,
      coordinates.term.inputCount, ?_, coordinates.term.inputBoundarySize, ?_,
      coordinates.term.expectedBoundary, ?_, coordinates.term.expectedCount, ?_,
      coordinates.term.expectedBoundarySize, ?_, coordinates.term.stateBoundary, ?_,
      coordinates.term.stateCount, ?_, coordinates.term.tableWidth, ?_,
      coordinates.term.valueBound, ?_,
      hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactProofRootFormulaTermEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish endpointBound : Nat}
    (hbounded : CompactProofRootFormulaTermEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish endpointBound) :
    ∃ input : List Nat,
    ∃ root :
        FoundationCompactNumericListedRootFieldsDecomposition.CompactNumericProofRoot,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactNumericListedDirectVerifierTaskLayout.CompactNumericVerifierTaskDirectLayout
        tokenTable width tokenCount rootStart rootFinish root ∧
      FoundationCompactNumericListedNodeFields.compactListedProofNodeFieldsParser
        input = some root := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

theorem exists_compactProofRootFormulaTermEndpointBoundedGraph_of_success_with_inputLayout
    {input : List Nat}
    {root :
      FoundationCompactNumericListedRootFieldsDecomposition.CompactNumericProofRoot}
    (hparser :
      FoundationCompactNumericListedNodeFields.compactListedProofNodeFieldsParser
        input = some root)
    (htag : root.1 = 6) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootFormulaTermEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound := by
  rcases exists_compactProofRootFormulaTermEndpointGraph_of_success_with_inputLayout
      hparser htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
      hinputLayout, hgraph⟩
  rcases CompactProofRootFormulaTermEndpointGraph.exists_bounded hgraph with
    ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, endpointBound,
    hinputLayout, hbounded⟩

theorem exists_compactProofRootFormulaTermEndpointBoundedGraph_of_success
    {input : List Nat}
    {root :
      FoundationCompactNumericListedRootFieldsDecomposition.CompactNumericProofRoot}
    (hparser :
      FoundationCompactNumericListedNodeFields.compactListedProofNodeFieldsParser
        input = some root)
    (htag : root.1 = 6) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish endpointBound,
      CompactProofRootFormulaTermEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish endpointBound := by
  rcases
      exists_compactProofRootFormulaTermEndpointBoundedGraph_of_success_with_inputLayout
        hparser htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, endpointBound,
      _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, endpointBound, hgraph⟩

#print axioms compactProofRootFormulaTermEndpointGraphDef_spec
#print axioms compactProofRootFormulaTermEndpointGraphDef_sigmaZero
#print axioms compactProofRootFormulaTermEndpointBoundedGraphDef_spec
#print axioms compactProofRootFormulaTermEndpointBoundedGraphDef_sigmaZero
#print axioms CompactProofRootFormulaTermEndpointBoundedGraph.exists_coordinates
#print axioms CompactProofRootFormulaTermEndpointGraph.exists_bounded
#print axioms CompactProofRootFormulaTermEndpointBoundedGraph.sound
#print axioms exists_compactProofRootFormulaTermEndpointBoundedGraph_of_success

end FoundationCompactNumericListedDirectProofRootFormulaTermBoundedFormula
