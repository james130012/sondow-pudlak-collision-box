import integration.FoundationCompactNumericListedDirectProofRootTwoFormulaEndpoint

/-!
# Bounded arithmetic formula for two-formula proof-root endpoints

The tag 3/4 endpoint is first exposed as one sixty-eight-column Delta-zero
graph. A later section bounds its fifty-nine local coordinates by one witness.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootTwoFormulaBoundedFormula

open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectSequentFormulaEndpointFormula
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula
open FoundationCompactNumericListedDirectProofRootTwoFormulaEndpoint

def compactProofRootTwoFormulaEndpointGraphDef : 𝚺₀.Semisentence 68 :=
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
    (taskTag = 3 ∨ taskTag = 4) ∧
    taskWitnessCount = 0 ∧
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
      middleStart middleFinish 1 0 0
      firstInputBoundary firstInputCount firstInputBoundarySize
      firstExpectedBoundary firstExpectedCount firstExpectedBoundarySize
      firstStateBoundary firstStateCount firstTableWidth firstValueBound ∧
    !(compactParserSyntaxExactEndpointGraphDef)
      tokenTable width tokenCount middleStart middleFinish
      taskWitnessFinish taskFinish 1 0 0
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
      taskFirstFinish taskSecondFinish taskSecondCount
      taskWitnessFinish taskFinish taskSuffixCount
      middleStart middleFinish secondInputCount”

def compactProofRootTwoFormulaEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootTwoFormulaEndpointCoordinates) :
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
    coordinates.firstFormula.inputBoundary,
    coordinates.firstFormula.inputCount,
    coordinates.firstFormula.inputBoundarySize,
    coordinates.firstFormula.expectedBoundary,
    coordinates.firstFormula.expectedCount,
    coordinates.firstFormula.expectedBoundarySize,
    coordinates.firstFormula.stateBoundary,
    coordinates.firstFormula.stateCount,
    coordinates.firstFormula.tableWidth,
    coordinates.firstFormula.valueBound,
    coordinates.middleStart, coordinates.middleFinish,
    coordinates.secondFormula.inputBoundary,
    coordinates.secondFormula.inputCount,
    coordinates.secondFormula.inputBoundarySize,
    coordinates.secondFormula.expectedBoundary,
    coordinates.secondFormula.expectedCount,
    coordinates.secondFormula.expectedBoundarySize,
    coordinates.secondFormula.stateBoundary,
    coordinates.secondFormula.stateCount,
    coordinates.secondFormula.tableWidth,
    coordinates.secondFormula.valueBound]

set_option maxRecDepth 4096 in
@[simp] theorem compactProofRootTwoFormulaEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootTwoFormulaEndpointCoordinates) :
    compactProofRootTwoFormulaEndpointGraphDef.val.Evalb
        (compactProofRootTwoFormulaEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish coordinates) ↔
      CompactProofRootTwoFormulaEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  let env := compactProofRootTwoFormulaEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish coordinates
  change compactProofRootTwoFormulaEndpointGraphDef.val.Evalb env ↔ _
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
      compactProofRootTwoFormulaEndpointEnvironment,
      compactSequentFormulaEndpointEnvironment]
  have hfirstEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2, #26, #27,
          #56, #57, ‘1’, ‘0’, ‘0’,
          #46, #47, #48, #49, #50, #51, #52, #53, #54, #55]) =
        compactParserSyntaxExactEndpointEnvironment
          tokenTable width tokenCount
          coordinates.finalStart coordinates.finalFinish
          coordinates.middleStart coordinates.middleFinish 1 0 0
          coordinates.firstFormula := by
    funext index
    fin_cases index <;> simp [env,
      compactProofRootTwoFormulaEndpointEnvironment,
      compactParserSyntaxExactEndpointEnvironment]
  have hsecondEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2, #56, #57,
          #22, #13, ‘1’, ‘0’, ‘0’,
          #58, #59, #60, #61, #62, #63, #64, #65, #66, #67]) =
        compactParserSyntaxExactEndpointEnvironment
          tokenTable width tokenCount
          coordinates.middleStart coordinates.middleFinish
          coordinates.root.witnessFinish coordinates.root.finish 1 0 0
          coordinates.secondFormula := by
    funext index
    fin_cases index <;> simp [env,
      compactProofRootTwoFormulaEndpointEnvironment,
      compactParserSyntaxExactEndpointEnvironment]
  have hfirstAppendEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2,
          #15, #18, #19, #56, #57, #50, #26, #27, #47]) =
        ![tokenTable, width, tokenCount,
          coordinates.root.gammaFinish, coordinates.root.firstFinish,
          coordinates.root.firstCount,
          coordinates.middleStart, coordinates.middleFinish,
          coordinates.firstFormula.expectedCount,
          coordinates.finalStart, coordinates.finalFinish,
          coordinates.firstFormula.inputCount] := by
    funext index
    fin_cases index <;> rfl
  have hsecondAppendEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 68), #1, #2,
          #18, #20, #21, #22, #13, #24, #56, #57, #59]) =
        ![tokenTable, width, tokenCount,
          coordinates.root.firstFinish, coordinates.root.secondFinish,
          coordinates.root.secondCount,
          coordinates.root.witnessFinish, coordinates.root.finish,
          coordinates.root.suffixCount,
          coordinates.middleStart, coordinates.middleFinish,
          coordinates.secondFormula.inputCount] := by
    funext index
    fin_cases index <;> rfl
  have hrootStartValue : env 12 = coordinates.root.start := rfl
  have hrootFinishValue : env 13 = coordinates.root.finish := rfl
  have hrootStartParameterValue : env 5 = rootStart := rfl
  have hrootFinishParameterValue : env 6 = rootFinish := rfl
  have hrootTagValue : env 14 = coordinates.root.tag := rfl
  have hwitnessCountValue : env 23 = coordinates.root.witnessCount := rfl
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
  simp [compactProofRootTwoFormulaEndpointGraphDef,
    CompactProofRootTwoFormulaEndpointGraph,
    hinputEnv, htaskEnv, hconsEnv, hsequentEnv, hfirstEnv, hsecondEnv,
    hfirstAppendEnv, hsecondAppendEnv,
    hrootStartValue, hrootFinishValue, hrootStartParameterValue,
    hrootFinishParameterValue, hrootTagValue, hwitnessCountValue,
    hrootCoordinatesOf, hrootSizeOf] <;> tauto

theorem compactProofRootTwoFormulaEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootTwoFormulaEndpointGraphDef.val := by
  simp [compactProofRootTwoFormulaEndpointGraphDef]


def compactProofRootTwoFormulaEndpointCoordinatesOfValues
    (
      inputBoundary inputCount inputBoundarySize
      taskStart taskFinish taskTag taskGammaFinish taskGammaCount taskGammaBoundary taskFirstFinish taskFirstCount taskSecondFinish taskSecondCount taskWitnessFinish taskWitnessCount taskSuffixCount taskGammaBoundarySize
      finalStart finalFinish
      sequentInputBoundary sequentInputCount sequentInputBoundarySize sequentFirstStart sequentFirstFinish sequentFirstBoundary sequentFirstCount sequentFirstBoundarySize sequentSuffixBoundary sequentSuffixCount sequentValueBoundary sequentValueCount sequentValueBoundarySize sequentFinalBoundary sequentFinalCount sequentFinalBoundarySize sequentTraceTableWidth sequentTraceValueBound
      firstInputBoundary firstInputCount firstInputBoundarySize firstExpectedBoundary firstExpectedCount firstExpectedBoundarySize firstStateBoundary firstStateCount firstTableWidth firstValueBound
      middleStart middleFinish
      secondInputBoundary secondInputCount secondInputBoundarySize secondExpectedBoundary secondExpectedCount secondExpectedBoundarySize secondStateBoundary secondStateCount secondTableWidth secondValueBound : Nat) :
    CompactProofRootTwoFormulaEndpointCoordinates :=
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
    firstFormula :=
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
    secondFormula :=
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

def CompactProofRootTwoFormulaEndpointBoundedGraph
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
    CompactProofRootTwoFormulaEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish
        (compactProofRootTwoFormulaEndpointCoordinatesOfValues
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

def compactProofRootTwoFormulaEndpointBoundedGraphDef :
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
      !(compactProofRootTwoFormulaEndpointGraphDef)
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
@[simp] theorem compactProofRootTwoFormulaEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish endpointBound : Nat) :
    compactProofRootTwoFormulaEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          rootStart, rootFinish, bodyStart, bodyFinish, endpointBound] ↔
      CompactProofRootTwoFormulaEndpointBoundedGraph
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
          Empty.elim) compactProofRootTwoFormulaEndpointGraphDef.val ↔
        CompactProofRootTwoFormulaEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish
            (compactProofRootTwoFormulaEndpointCoordinatesOfValues
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
          compactProofRootTwoFormulaEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              rootStart rootFinish bodyStart bodyFinish
              (compactProofRootTwoFormulaEndpointCoordinatesOfValues
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
    exact compactProofRootTwoFormulaEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish _
  simp [compactProofRootTwoFormulaEndpointBoundedGraphDef,
    CompactProofRootTwoFormulaEndpointBoundedGraph, hrow]

theorem compactProofRootTwoFormulaEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootTwoFormulaEndpointBoundedGraphDef.val := by
  simp [compactProofRootTwoFormulaEndpointBoundedGraphDef]

theorem CompactProofRootTwoFormulaEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish endpointBound : Nat}
    (hbounded : CompactProofRootTwoFormulaEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish endpointBound) :
    ∃ coordinates : CompactProofRootTwoFormulaEndpointCoordinates,
      CompactProofRootTwoFormulaEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  unfold CompactProofRootTwoFormulaEndpointBoundedGraph at hbounded
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
  exact ⟨compactProofRootTwoFormulaEndpointCoordinatesOfValues
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

theorem CompactProofRootTwoFormulaEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootTwoFormulaEndpointCoordinates}
    (hgraph : CompactProofRootTwoFormulaEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish coordinates) :
    ∃ endpointBound,
      CompactProofRootTwoFormulaEndpointBoundedGraph
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
    coordinates.firstFormula.inputBoundary +
    coordinates.firstFormula.inputCount +
    coordinates.firstFormula.inputBoundarySize +
    coordinates.firstFormula.expectedBoundary +
    coordinates.firstFormula.expectedCount +
    coordinates.firstFormula.expectedBoundarySize +
    coordinates.firstFormula.stateBoundary +
    coordinates.firstFormula.stateCount +
    coordinates.firstFormula.tableWidth +
    coordinates.firstFormula.valueBound +
    coordinates.middleStart +
    coordinates.middleFinish +
    coordinates.secondFormula.inputBoundary +
    coordinates.secondFormula.inputCount +
    coordinates.secondFormula.inputBoundarySize +
    coordinates.secondFormula.expectedBoundary +
    coordinates.secondFormula.expectedCount +
    coordinates.secondFormula.expectedBoundarySize +
    coordinates.secondFormula.stateBoundary +
    coordinates.secondFormula.stateCount +
    coordinates.secondFormula.tableWidth +
    coordinates.secondFormula.valueBound
  refine ⟨endpointBound, ?_⟩
  unfold CompactProofRootTwoFormulaEndpointBoundedGraph
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
      coordinates.sequent.traceValueBound, ?_, coordinates.firstFormula.inputBoundary, ?_,
      coordinates.firstFormula.inputCount, ?_, coordinates.firstFormula.inputBoundarySize, ?_,
      coordinates.firstFormula.expectedBoundary, ?_, coordinates.firstFormula.expectedCount, ?_,
      coordinates.firstFormula.expectedBoundarySize, ?_, coordinates.firstFormula.stateBoundary, ?_,
      coordinates.firstFormula.stateCount, ?_, coordinates.firstFormula.tableWidth, ?_,
      coordinates.firstFormula.valueBound, ?_, coordinates.middleStart, ?_,
      coordinates.middleFinish, ?_, coordinates.secondFormula.inputBoundary, ?_,
      coordinates.secondFormula.inputCount, ?_, coordinates.secondFormula.inputBoundarySize, ?_,
      coordinates.secondFormula.expectedBoundary, ?_, coordinates.secondFormula.expectedCount, ?_,
      coordinates.secondFormula.expectedBoundarySize, ?_, coordinates.secondFormula.stateBoundary, ?_,
      coordinates.secondFormula.stateCount, ?_, coordinates.secondFormula.tableWidth, ?_,
      coordinates.secondFormula.valueBound, ?_,
      hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactProofRootTwoFormulaEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish endpointBound : Nat}
    (hbounded : CompactProofRootTwoFormulaEndpointBoundedGraph
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

theorem exists_compactProofRootTwoFormulaEndpointBoundedGraph_of_success_with_inputLayout
    {input : List Nat}
    {root :
      FoundationCompactNumericListedRootFieldsDecomposition.CompactNumericProofRoot}
    (hparser :
      FoundationCompactNumericListedNodeFields.compactListedProofNodeFieldsParser
        input = some root)
    (htag : root.1 = 3 ∨ root.1 = 4) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootTwoFormulaEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound := by
  rcases exists_compactProofRootTwoFormulaEndpointGraph_of_success_with_inputLayout
      hparser htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
      hinputLayout, hgraph⟩
  rcases CompactProofRootTwoFormulaEndpointGraph.exists_bounded hgraph with
    ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, endpointBound,
    hinputLayout, hbounded⟩

theorem exists_compactProofRootTwoFormulaEndpointBoundedGraph_of_success
    {input : List Nat}
    {root :
      FoundationCompactNumericListedRootFieldsDecomposition.CompactNumericProofRoot}
    (hparser :
      FoundationCompactNumericListedNodeFields.compactListedProofNodeFieldsParser
        input = some root)
    (htag : root.1 = 3 ∨ root.1 = 4) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish endpointBound,
      CompactProofRootTwoFormulaEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish endpointBound := by
  rcases
      exists_compactProofRootTwoFormulaEndpointBoundedGraph_of_success_with_inputLayout
        hparser htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, endpointBound,
      _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, endpointBound, hgraph⟩

#print axioms compactProofRootTwoFormulaEndpointGraphDef_spec
#print axioms compactProofRootTwoFormulaEndpointGraphDef_sigmaZero
#print axioms compactProofRootTwoFormulaEndpointBoundedGraphDef_spec
#print axioms compactProofRootTwoFormulaEndpointBoundedGraphDef_sigmaZero
#print axioms CompactProofRootTwoFormulaEndpointBoundedGraph.exists_coordinates
#print axioms CompactProofRootTwoFormulaEndpointGraph.exists_bounded
#print axioms CompactProofRootTwoFormulaEndpointBoundedGraph.sound
#print axioms exists_compactProofRootTwoFormulaEndpointBoundedGraph_of_success

end FoundationCompactNumericListedDirectProofRootTwoFormulaBoundedFormula
