import integration.FoundationCompactNumericListedDirectProofRootClosedFormulaEndpoint

/-!
# Bounded formula for the closed-formula proof-root endpoint

The exact tag 1 endpoint is expressed as one fifty-seven-column Delta-zero
graph. Its forty-eight local coordinates are then bounded by one public
endpoint witness.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootClosedFormulaBoundedFormula

open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectSequentFormulaEndpointFormula
open FoundationCompactNumericListedDirectParserClosedEndpointFormula
open FoundationCompactNumericListedDirectProofRootOneFormulaEndpoint
open FoundationCompactNumericListedDirectProofRootClosedFormulaEndpoint

def compactProofRootClosedFormulaEndpointGraphDef : 𝚺₀.Semisentence 57 :=
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
      binderArity
      formulaInputBoundary formulaInputCount formulaInputBoundarySize
      formulaExpectedBoundary formulaExpectedCount formulaExpectedBoundarySize
      formulaStateBoundary formulaStateCount
      formulaTableWidth formulaValueBound.
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
    taskTag = 1 ∧
    binderArity = 0 ∧
    taskSecondCount = 0 ∧
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
    !(compactParserClosedEndpointGraphDef)
      tokenTable width tokenCount finalStart finalFinish
      taskWitnessFinish taskFinish binderArity
      formulaInputBoundary formulaInputCount formulaInputBoundarySize
      formulaExpectedBoundary formulaExpectedCount formulaExpectedBoundarySize
      formulaStateBoundary formulaStateCount formulaTableWidth formulaValueBound ∧
    !(compactAdditiveNatListAppendSlicesDef)
      tokenTable width tokenCount
      taskGammaFinish taskFirstFinish taskFirstCount
      taskWitnessFinish taskFinish taskSuffixCount
      finalStart finalFinish formulaInputCount”

def compactProofRootClosedFormulaEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootOneFormulaEndpointCoordinates) :
    Fin 57 → Nat :=
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
    coordinates.binderArity,
    coordinates.formula.inputBoundary, coordinates.formula.inputCount,
    coordinates.formula.inputBoundarySize,
    coordinates.formula.expectedBoundary, coordinates.formula.expectedCount,
    coordinates.formula.expectedBoundarySize,
    coordinates.formula.stateBoundary, coordinates.formula.stateCount,
    coordinates.formula.tableWidth, coordinates.formula.valueBound]

set_option maxRecDepth 4096 in
@[simp] theorem compactProofRootClosedFormulaEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootOneFormulaEndpointCoordinates) :
    compactProofRootClosedFormulaEndpointGraphDef.val.Evalb
        (compactProofRootClosedFormulaEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish coordinates) ↔
      CompactProofRootClosedFormulaEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  let env := compactProofRootClosedFormulaEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish coordinates
  change compactProofRootClosedFormulaEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 57), #1, #2, #3, #10, #4,
          #9, #11]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have htaskEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 57), #1, #2,
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
        ![(#0 : Semiterm ℒₒᵣ Empty 57), #1, #2,
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
        ![(#0 : Semiterm ℒₒᵣ Empty 57), #1, #2, #7, #8,
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
      compactProofRootClosedFormulaEndpointEnvironment,
      compactSequentFormulaEndpointEnvironment]
  have hformulaEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 57), #1, #2, #26, #27,
          #22, #13, #46,
          #47, #48, #49, #50, #51, #52, #53, #54, #55, #56]) =
        compactParserClosedEndpointEnvironment
          tokenTable width tokenCount
          coordinates.finalStart coordinates.finalFinish
          coordinates.root.witnessFinish coordinates.root.finish
          coordinates.binderArity coordinates.formula := by
    funext index
    fin_cases index <;> simp [env,
      compactProofRootClosedFormulaEndpointEnvironment,
      compactParserClosedEndpointEnvironment]
  have happendEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 57), #1, #2,
          #15, #18, #19, #22, #13, #24, #26, #27, #48]) =
        ![tokenTable, width, tokenCount,
          coordinates.root.gammaFinish, coordinates.root.firstFinish,
          coordinates.root.firstCount, coordinates.root.witnessFinish,
          coordinates.root.finish, coordinates.root.suffixCount,
          coordinates.finalStart, coordinates.finalFinish,
          coordinates.formula.inputCount] := by
    funext index
    fin_cases index <;> rfl
  have hrootStartValue : env 12 = coordinates.root.start := rfl
  have hrootFinishValue : env 13 = coordinates.root.finish := rfl
  have hrootStartParameterValue : env 5 = rootStart := rfl
  have hrootFinishParameterValue : env 6 = rootFinish := rfl
  have hrootTagValue : env 14 = coordinates.root.tag := rfl
  have hsecondCountValue : env 21 = coordinates.root.secondCount := rfl
  have hwitnessCountValue : env 23 = coordinates.root.witnessCount := rfl
  have hbinderValue : env 46 = coordinates.binderArity := rfl
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
  simp [compactProofRootClosedFormulaEndpointGraphDef,
    CompactProofRootClosedFormulaEndpointGraph,
    hinputEnv, htaskEnv, hconsEnv, hsequentEnv, hformulaEnv, happendEnv,
    hrootStartValue, hrootFinishValue, hrootStartParameterValue,
    hrootFinishParameterValue, hrootTagValue,
    hsecondCountValue, hwitnessCountValue, hbinderValue,
    hrootCoordinatesOf, hrootSizeOf]

theorem compactProofRootClosedFormulaEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootClosedFormulaEndpointGraphDef.val := by
  simp [compactProofRootClosedFormulaEndpointGraphDef]

def compactProofRootClosedFormulaEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
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
      binderArity
      formulaInputBoundary formulaInputCount formulaInputBoundarySize
      formulaExpectedBoundary formulaExpectedCount formulaExpectedBoundarySize
      formulaStateBoundary formulaStateCount
      formulaTableWidth formulaValueBound : Nat) :
    CompactProofRootOneFormulaEndpointCoordinates :=
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
    binderArity := binderArity
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
      { inputBoundary := formulaInputBoundary
        inputCount := formulaInputCount
        inputBoundarySize := formulaInputBoundarySize
        expectedBoundary := formulaExpectedBoundary
        expectedCount := formulaExpectedCount
        expectedBoundarySize := formulaExpectedBoundarySize
        stateBoundary := formulaStateBoundary
        stateCount := formulaStateCount
        tableWidth := formulaTableWidth
        valueBound := formulaValueBound } }

def CompactProofRootClosedFormulaEndpointBoundedGraph
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
  ∃ sequentInputBoundarySize,
      sequentInputBoundarySize ≤ endpointBound ∧
  ∃ sequentFirstStart, sequentFirstStart ≤ endpointBound ∧
  ∃ sequentFirstFinish, sequentFirstFinish ≤ endpointBound ∧
  ∃ sequentFirstBoundary, sequentFirstBoundary ≤ endpointBound ∧
  ∃ sequentFirstCount, sequentFirstCount ≤ endpointBound ∧
  ∃ sequentFirstBoundarySize,
      sequentFirstBoundarySize ≤ endpointBound ∧
  ∃ sequentSuffixBoundary, sequentSuffixBoundary ≤ endpointBound ∧
  ∃ sequentSuffixCount, sequentSuffixCount ≤ endpointBound ∧
  ∃ sequentValueBoundary, sequentValueBoundary ≤ endpointBound ∧
  ∃ sequentValueCount, sequentValueCount ≤ endpointBound ∧
  ∃ sequentValueBoundarySize,
      sequentValueBoundarySize ≤ endpointBound ∧
  ∃ sequentFinalBoundary, sequentFinalBoundary ≤ endpointBound ∧
  ∃ sequentFinalCount, sequentFinalCount ≤ endpointBound ∧
  ∃ sequentFinalBoundarySize,
      sequentFinalBoundarySize ≤ endpointBound ∧
  ∃ sequentTraceTableWidth, sequentTraceTableWidth ≤ endpointBound ∧
  ∃ sequentTraceValueBound, sequentTraceValueBound ≤ endpointBound ∧
  ∃ binderArity, binderArity ≤ endpointBound ∧
  ∃ formulaInputBoundary, formulaInputBoundary ≤ endpointBound ∧
  ∃ formulaInputCount, formulaInputCount ≤ endpointBound ∧
  ∃ formulaInputBoundarySize,
      formulaInputBoundarySize ≤ endpointBound ∧
  ∃ formulaExpectedBoundary, formulaExpectedBoundary ≤ endpointBound ∧
  ∃ formulaExpectedCount, formulaExpectedCount ≤ endpointBound ∧
  ∃ formulaExpectedBoundarySize,
      formulaExpectedBoundarySize ≤ endpointBound ∧
  ∃ formulaStateBoundary, formulaStateBoundary ≤ endpointBound ∧
  ∃ formulaStateCount, formulaStateCount ≤ endpointBound ∧
  ∃ formulaTableWidth, formulaTableWidth ≤ endpointBound ∧
  ∃ formulaValueBound, formulaValueBound ≤ endpointBound ∧
    CompactProofRootClosedFormulaEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish
        (compactProofRootClosedFormulaEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          taskStart taskFinish taskTag taskGammaFinish taskGammaCount
          taskGammaBoundary taskFirstFinish taskFirstCount
          taskSecondFinish taskSecondCount taskWitnessFinish taskWitnessCount
          taskSuffixCount taskGammaBoundarySize finalStart finalFinish
          sequentInputBoundary sequentInputCount sequentInputBoundarySize
          sequentFirstStart sequentFirstFinish sequentFirstBoundary
          sequentFirstCount sequentFirstBoundarySize
          sequentSuffixBoundary sequentSuffixCount
          sequentValueBoundary sequentValueCount sequentValueBoundarySize
          sequentFinalBoundary sequentFinalCount sequentFinalBoundarySize
          sequentTraceTableWidth sequentTraceValueBound binderArity
          formulaInputBoundary formulaInputCount formulaInputBoundarySize
          formulaExpectedBoundary formulaExpectedCount
          formulaExpectedBoundarySize formulaStateBoundary formulaStateCount
          formulaTableWidth formulaValueBound)

def compactProofRootClosedFormulaEndpointBoundedGraphDef :
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
    ∃ binderArity <⁺ endpointBound,
    ∃ formulaInputBoundary <⁺ endpointBound,
    ∃ formulaInputCount <⁺ endpointBound,
    ∃ formulaInputBoundarySize <⁺ endpointBound,
    ∃ formulaExpectedBoundary <⁺ endpointBound,
    ∃ formulaExpectedCount <⁺ endpointBound,
    ∃ formulaExpectedBoundarySize <⁺ endpointBound,
    ∃ formulaStateBoundary <⁺ endpointBound,
    ∃ formulaStateCount <⁺ endpointBound,
    ∃ formulaTableWidth <⁺ endpointBound,
    ∃ formulaValueBound <⁺ endpointBound,
      !(compactProofRootClosedFormulaEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish
        inputBoundary inputCount inputBoundarySize
        taskStart taskFinish taskTag taskGammaFinish taskGammaCount
        taskGammaBoundary taskFirstFinish taskFirstCount
        taskSecondFinish taskSecondCount taskWitnessFinish taskWitnessCount
        taskSuffixCount taskGammaBoundarySize finalStart finalFinish
        sequentInputBoundary sequentInputCount sequentInputBoundarySize
        sequentFirstStart sequentFirstFinish sequentFirstBoundary
        sequentFirstCount sequentFirstBoundarySize
        sequentSuffixBoundary sequentSuffixCount
        sequentValueBoundary sequentValueCount sequentValueBoundarySize
        sequentFinalBoundary sequentFinalCount sequentFinalBoundarySize
        sequentTraceTableWidth sequentTraceValueBound binderArity
        formulaInputBoundary formulaInputCount formulaInputBoundarySize
        formulaExpectedBoundary formulaExpectedCount
        formulaExpectedBoundarySize formulaStateBoundary formulaStateCount
        formulaTableWidth formulaValueBound”

set_option maxRecDepth 16384 in
@[simp] theorem compactProofRootClosedFormulaEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish endpointBound : Nat) :
    compactProofRootClosedFormulaEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          rootStart, rootFinish, bodyStart, bodyFinish, endpointBound] ↔
      CompactProofRootClosedFormulaEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish endpointBound := by
  have hrow
      (formulaValueBound formulaTableWidth
        formulaStateCount formulaStateBoundary
        formulaExpectedBoundarySize formulaExpectedCount
        formulaExpectedBoundary formulaInputBoundarySize
        formulaInputCount formulaInputBoundary binderArity
        sequentTraceValueBound sequentTraceTableWidth
        sequentFinalBoundarySize sequentFinalCount sequentFinalBoundary
        sequentValueBoundarySize sequentValueCount sequentValueBoundary
        sequentSuffixCount sequentSuffixBoundary
        sequentFirstBoundarySize sequentFirstCount sequentFirstBoundary
        sequentFirstFinish sequentFirstStart
        sequentInputBoundarySize sequentInputCount sequentInputBoundary
        finalFinish finalStart taskGammaBoundarySize taskSuffixCount
        taskWitnessCount taskWitnessFinish taskSecondCount taskSecondFinish
        taskFirstCount taskFirstFinish taskGammaBoundary taskGammaCount
        taskGammaFinish taskTag taskFinish taskStart
        inputBoundarySize inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![formulaValueBound, formulaTableWidth,
                formulaStateCount, formulaStateBoundary,
                formulaExpectedBoundarySize, formulaExpectedCount,
                formulaExpectedBoundary, formulaInputBoundarySize,
                formulaInputCount, formulaInputBoundary, binderArity,
                sequentTraceValueBound, sequentTraceTableWidth,
                sequentFinalBoundarySize, sequentFinalCount,
                sequentFinalBoundary, sequentValueBoundarySize,
                sequentValueCount, sequentValueBoundary,
                sequentSuffixCount, sequentSuffixBoundary,
                sequentFirstBoundarySize, sequentFirstCount,
                sequentFirstBoundary, sequentFirstFinish,
                sequentFirstStart, sequentInputBoundarySize,
                sequentInputCount, sequentInputBoundary,
                finalFinish, finalStart, taskGammaBoundarySize,
                taskSuffixCount, taskWitnessCount, taskWitnessFinish,
                taskSecondCount, taskSecondFinish, taskFirstCount,
                taskFirstFinish, taskGammaBoundary, taskGammaCount,
                taskGammaFinish, taskTag, taskFinish, taskStart,
                inputBoundarySize, inputCount, inputBoundary,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                rootStart, rootFinish, bodyStart, bodyFinish, endpointBound]
              Empty.elim ∘
            ![(#48 : Semiterm ℒₒᵣ Empty 58), #49, #50, #51, #52,
              #53, #54, #55, #56,
              #47, #46, #45, #44, #43, #42, #41, #40, #39, #38,
              #37, #36, #35, #34, #33, #32, #31, #30, #29, #28,
              #27, #26, #25, #24, #23, #22, #21, #20, #19, #18,
              #17, #16, #15, #14, #13, #12, #11, #10, #9, #8,
              #7, #6, #5, #4, #3, #2, #1, #0])
          Empty.elim) compactProofRootClosedFormulaEndpointGraphDef.val ↔
        CompactProofRootClosedFormulaEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish
            (compactProofRootClosedFormulaEndpointCoordinatesOfValues
              inputBoundary inputCount inputBoundarySize
              taskStart taskFinish taskTag taskGammaFinish taskGammaCount
              taskGammaBoundary taskFirstFinish taskFirstCount
              taskSecondFinish taskSecondCount
              taskWitnessFinish taskWitnessCount
              taskSuffixCount taskGammaBoundarySize finalStart finalFinish
              sequentInputBoundary sequentInputCount sequentInputBoundarySize
              sequentFirstStart sequentFirstFinish sequentFirstBoundary
              sequentFirstCount sequentFirstBoundarySize
              sequentSuffixBoundary sequentSuffixCount
              sequentValueBoundary sequentValueCount sequentValueBoundarySize
              sequentFinalBoundary sequentFinalCount sequentFinalBoundarySize
              sequentTraceTableWidth sequentTraceValueBound binderArity
              formulaInputBoundary formulaInputCount formulaInputBoundarySize
              formulaExpectedBoundary formulaExpectedCount
              formulaExpectedBoundarySize formulaStateBoundary
              formulaStateCount formulaTableWidth formulaValueBound) := by
    have henv :
        (Semiterm.val
            ![formulaValueBound, formulaTableWidth,
              formulaStateCount, formulaStateBoundary,
              formulaExpectedBoundarySize, formulaExpectedCount,
              formulaExpectedBoundary, formulaInputBoundarySize,
              formulaInputCount, formulaInputBoundary, binderArity,
              sequentTraceValueBound, sequentTraceTableWidth,
              sequentFinalBoundarySize, sequentFinalCount,
              sequentFinalBoundary, sequentValueBoundarySize,
              sequentValueCount, sequentValueBoundary,
              sequentSuffixCount, sequentSuffixBoundary,
              sequentFirstBoundarySize, sequentFirstCount,
              sequentFirstBoundary, sequentFirstFinish,
              sequentFirstStart, sequentInputBoundarySize,
              sequentInputCount, sequentInputBoundary,
              finalFinish, finalStart, taskGammaBoundarySize,
              taskSuffixCount, taskWitnessCount, taskWitnessFinish,
              taskSecondCount, taskSecondFinish, taskFirstCount,
              taskFirstFinish, taskGammaBoundary, taskGammaCount,
              taskGammaFinish, taskTag, taskFinish, taskStart,
              inputBoundarySize, inputCount, inputBoundary,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              rootStart, rootFinish, bodyStart, bodyFinish, endpointBound]
            Empty.elim ∘
          ![(#48 : Semiterm ℒₒᵣ Empty 58), #49, #50, #51, #52,
            #53, #54, #55, #56,
            #47, #46, #45, #44, #43, #42, #41, #40, #39, #38,
            #37, #36, #35, #34, #33, #32, #31, #30, #29, #28,
            #27, #26, #25, #24, #23, #22, #21, #20, #19, #18,
            #17, #16, #15, #14, #13, #12, #11, #10, #9, #8,
            #7, #6, #5, #4, #3, #2, #1, #0]) =
          compactProofRootClosedFormulaEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              rootStart rootFinish bodyStart bodyFinish
              (compactProofRootClosedFormulaEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                taskStart taskFinish taskTag taskGammaFinish taskGammaCount
                taskGammaBoundary taskFirstFinish taskFirstCount
                taskSecondFinish taskSecondCount
                taskWitnessFinish taskWitnessCount
                taskSuffixCount taskGammaBoundarySize finalStart finalFinish
                sequentInputBoundary sequentInputCount
                sequentInputBoundarySize sequentFirstStart
                sequentFirstFinish sequentFirstBoundary
                sequentFirstCount sequentFirstBoundarySize
                sequentSuffixBoundary sequentSuffixCount
                sequentValueBoundary sequentValueCount
                sequentValueBoundarySize sequentFinalBoundary
                sequentFinalCount sequentFinalBoundarySize
                sequentTraceTableWidth sequentTraceValueBound binderArity
                formulaInputBoundary formulaInputCount
                formulaInputBoundarySize formulaExpectedBoundary
                formulaExpectedCount formulaExpectedBoundarySize
                formulaStateBoundary formulaStateCount
                formulaTableWidth formulaValueBound) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactProofRootClosedFormulaEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish _
  simp [compactProofRootClosedFormulaEndpointBoundedGraphDef,
    CompactProofRootClosedFormulaEndpointBoundedGraph, hrow]

theorem compactProofRootClosedFormulaEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootClosedFormulaEndpointBoundedGraphDef.val := by
  simp [compactProofRootClosedFormulaEndpointBoundedGraphDef]

theorem CompactProofRootClosedFormulaEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish endpointBound : Nat}
    (hbounded : CompactProofRootClosedFormulaEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish endpointBound) :
    ∃ coordinates : CompactProofRootOneFormulaEndpointCoordinates,
      CompactProofRootClosedFormulaEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  unfold CompactProofRootClosedFormulaEndpointBoundedGraph at hbounded
  rcases hbounded with
    ⟨inputBoundary, _hinputBoundary,
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
      binderArity, _hbinderArity,
      formulaInputBoundary, _hformulaInputBoundary,
      formulaInputCount, _hformulaInputCount,
      formulaInputBoundarySize, _hformulaInputBoundarySize,
      formulaExpectedBoundary, _hformulaExpectedBoundary,
      formulaExpectedCount, _hformulaExpectedCount,
      formulaExpectedBoundarySize, _hformulaExpectedBoundarySize,
      formulaStateBoundary, _hformulaStateBoundary,
      formulaStateCount, _hformulaStateCount,
      formulaTableWidth, _hformulaTableWidth,
      formulaValueBound, _hformulaValueBound, hgraph⟩
  exact ⟨compactProofRootClosedFormulaEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    taskStart taskFinish taskTag taskGammaFinish taskGammaCount
    taskGammaBoundary taskFirstFinish taskFirstCount
    taskSecondFinish taskSecondCount taskWitnessFinish taskWitnessCount
    taskSuffixCount taskGammaBoundarySize finalStart finalFinish
    sequentInputBoundary sequentInputCount sequentInputBoundarySize
    sequentFirstStart sequentFirstFinish sequentFirstBoundary
    sequentFirstCount sequentFirstBoundarySize
    sequentSuffixBoundary sequentSuffixCount
    sequentValueBoundary sequentValueCount sequentValueBoundarySize
    sequentFinalBoundary sequentFinalCount sequentFinalBoundarySize
    sequentTraceTableWidth sequentTraceValueBound binderArity
    formulaInputBoundary formulaInputCount formulaInputBoundarySize
    formulaExpectedBoundary formulaExpectedCount formulaExpectedBoundarySize
    formulaStateBoundary formulaStateCount formulaTableWidth formulaValueBound,
    hgraph⟩

theorem CompactProofRootClosedFormulaEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootOneFormulaEndpointCoordinates}
    (hgraph : CompactProofRootClosedFormulaEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish coordinates) :
    ∃ endpointBound,
      CompactProofRootClosedFormulaEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.root.start +
    coordinates.root.finish + coordinates.root.tag +
    coordinates.root.gammaFinish + coordinates.root.gammaCount +
    coordinates.root.gammaBoundary + coordinates.root.firstFinish +
    coordinates.root.firstCount + coordinates.root.secondFinish +
    coordinates.root.secondCount + coordinates.root.witnessFinish +
    coordinates.root.witnessCount + coordinates.root.suffixCount +
    coordinates.rootSize.gammaBoundarySize + coordinates.finalStart +
    coordinates.finalFinish + coordinates.sequent.inputBoundary +
    coordinates.sequent.inputCount +
    coordinates.sequent.inputBoundarySize + coordinates.sequent.firstStart +
    coordinates.sequent.firstFinish + coordinates.sequent.firstBoundary +
    coordinates.sequent.firstCount +
    coordinates.sequent.firstBoundarySize +
    coordinates.sequent.suffixBoundary + coordinates.sequent.suffixCount +
    coordinates.sequent.valueBoundary + coordinates.sequent.valueCount +
    coordinates.sequent.valueBoundarySize +
    coordinates.sequent.finalBoundary + coordinates.sequent.finalCount +
    coordinates.sequent.finalBoundarySize +
    coordinates.sequent.traceTableWidth +
    coordinates.sequent.traceValueBound + coordinates.binderArity +
    coordinates.formula.inputBoundary + coordinates.formula.inputCount +
    coordinates.formula.inputBoundarySize +
    coordinates.formula.expectedBoundary + coordinates.formula.expectedCount +
    coordinates.formula.expectedBoundarySize +
    coordinates.formula.stateBoundary + coordinates.formula.stateCount +
    coordinates.formula.tableWidth + coordinates.formula.valueBound
  refine ⟨endpointBound, ?_⟩
  unfold CompactProofRootClosedFormulaEndpointBoundedGraph
  refine
    ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
      coordinates.inputBoundarySize, ?_, coordinates.root.start, ?_,
      coordinates.root.finish, ?_, coordinates.root.tag, ?_,
      coordinates.root.gammaFinish, ?_, coordinates.root.gammaCount, ?_,
      coordinates.root.gammaBoundary, ?_, coordinates.root.firstFinish, ?_,
      coordinates.root.firstCount, ?_, coordinates.root.secondFinish, ?_,
      coordinates.root.secondCount, ?_, coordinates.root.witnessFinish, ?_,
      coordinates.root.witnessCount, ?_, coordinates.root.suffixCount, ?_,
      coordinates.rootSize.gammaBoundarySize, ?_,
      coordinates.finalStart, ?_, coordinates.finalFinish, ?_,
      coordinates.sequent.inputBoundary, ?_,
      coordinates.sequent.inputCount, ?_,
      coordinates.sequent.inputBoundarySize, ?_,
      coordinates.sequent.firstStart, ?_,
      coordinates.sequent.firstFinish, ?_,
      coordinates.sequent.firstBoundary, ?_,
      coordinates.sequent.firstCount, ?_,
      coordinates.sequent.firstBoundarySize, ?_,
      coordinates.sequent.suffixBoundary, ?_,
      coordinates.sequent.suffixCount, ?_,
      coordinates.sequent.valueBoundary, ?_,
      coordinates.sequent.valueCount, ?_,
      coordinates.sequent.valueBoundarySize, ?_,
      coordinates.sequent.finalBoundary, ?_,
      coordinates.sequent.finalCount, ?_,
      coordinates.sequent.finalBoundarySize, ?_,
      coordinates.sequent.traceTableWidth, ?_,
      coordinates.sequent.traceValueBound, ?_,
      coordinates.binderArity, ?_,
      coordinates.formula.inputBoundary, ?_,
      coordinates.formula.inputCount, ?_,
      coordinates.formula.inputBoundarySize, ?_,
      coordinates.formula.expectedBoundary, ?_,
      coordinates.formula.expectedCount, ?_,
      coordinates.formula.expectedBoundarySize, ?_,
      coordinates.formula.stateBoundary, ?_,
      coordinates.formula.stateCount, ?_,
      coordinates.formula.tableWidth, ?_,
      coordinates.formula.valueBound, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactProofRootClosedFormulaEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish endpointBound : Nat}
    (hbounded : CompactProofRootClosedFormulaEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish endpointBound) :
    ∃ input : List Nat,
    ∃ root : FoundationCompactNumericListedRootFieldsDecomposition.CompactNumericProofRoot,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactNumericListedDirectVerifierTaskLayout.CompactNumericVerifierTaskDirectLayout
        tokenTable width tokenCount rootStart rootFinish root ∧
      FoundationCompactNumericListedNodeFields.compactListedProofNodeFieldsParser
        input = some root := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

theorem exists_compactProofRootClosedFormulaEndpointBoundedGraph_of_success_with_inputLayout
    {input : List Nat}
    {root : FoundationCompactNumericListedRootFieldsDecomposition.CompactNumericProofRoot}
    (hparser :
      FoundationCompactNumericListedNodeFields.compactListedProofNodeFieldsParser
        input = some root)
    (htag : root.1 = 1) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootClosedFormulaEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound := by
  rcases exists_compactProofRootClosedFormulaEndpointGraph_of_success_with_inputLayout
      hparser htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
      hinputLayout, hgraph⟩
  rcases CompactProofRootClosedFormulaEndpointGraph.exists_bounded hgraph with
    ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, endpointBound,
    hinputLayout, hbounded⟩

theorem exists_compactProofRootClosedFormulaEndpointBoundedGraph_of_success
    {input : List Nat}
    {root : FoundationCompactNumericListedRootFieldsDecomposition.CompactNumericProofRoot}
    (hparser :
      FoundationCompactNumericListedNodeFields.compactListedProofNodeFieldsParser
        input = some root)
    (htag : root.1 = 1) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish endpointBound,
      CompactProofRootClosedFormulaEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish endpointBound := by
  rcases
      exists_compactProofRootClosedFormulaEndpointBoundedGraph_of_success_with_inputLayout
        hparser htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, endpointBound,
      _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, endpointBound, hgraph⟩

#print axioms compactProofRootClosedFormulaEndpointGraphDef_spec
#print axioms compactProofRootClosedFormulaEndpointGraphDef_sigmaZero
#print axioms compactProofRootClosedFormulaEndpointBoundedGraphDef_spec
#print axioms compactProofRootClosedFormulaEndpointBoundedGraphDef_sigmaZero
#print axioms CompactProofRootClosedFormulaEndpointBoundedGraph.exists_coordinates
#print axioms CompactProofRootClosedFormulaEndpointGraph.exists_bounded
#print axioms CompactProofRootClosedFormulaEndpointBoundedGraph.sound
#print axioms exists_compactProofRootClosedFormulaEndpointBoundedGraph_of_success

end FoundationCompactNumericListedDirectProofRootClosedFormulaBoundedFormula
