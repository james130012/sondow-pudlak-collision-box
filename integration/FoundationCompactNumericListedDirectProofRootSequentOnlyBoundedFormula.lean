import integration.FoundationCompactNumericListedDirectProofRootSequentOnlyEndpoint

/-!
# Bounded formula for sequent-only proof-root endpoints

All thirty-seven local coordinates of the tags 2, 7, and 8 endpoint graph are
bounded by one public witness.  This is the form embedded by the complete
verifier-step formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootSequentOnlyBoundedFormula

open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectProofRootSequentOnlyEndpoint

def compactProofRootSequentOnlyEndpointCoordinatesOfValues
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
      sequentTraceTableWidth sequentTraceValueBound : Nat) :
    CompactProofRootSequentOnlyEndpointCoordinates :=
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
        traceValueBound := sequentTraceValueBound } }

def CompactProofRootSequentOnlyEndpointBoundedGraph
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
    CompactProofRootSequentOnlyEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish
        (compactProofRootSequentOnlyEndpointCoordinatesOfValues
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
          sequentTraceTableWidth sequentTraceValueBound)

def compactProofRootSequentOnlyEndpointBoundedGraphDef :
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
      !(compactProofRootSequentOnlyEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish
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
        sequentTraceTableWidth sequentTraceValueBound”

set_option maxRecDepth 8192 in
@[simp] theorem compactProofRootSequentOnlyEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish endpointBound : Nat) :
    compactProofRootSequentOnlyEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          rootStart, rootFinish, bodyStart, bodyFinish, endpointBound] ↔
      CompactProofRootSequentOnlyEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish endpointBound := by
  have hrow
      (sequentTraceValueBound sequentTraceTableWidth
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
              ![sequentTraceValueBound, sequentTraceTableWidth,
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
            ![(#37 : Semiterm ℒₒᵣ Empty 47), #38, #39, #40, #41,
              #42, #43, #44, #45,
              #36, #35, #34,
              #33, #32, #31, #30, #29, #28, #27, #26, #25, #24,
              #23, #22, #21, #20,
              #19, #18,
              #17, #16, #15, #14, #13, #12, #11, #10,
              #9, #8, #7, #6, #5, #4, #3, #2, #1, #0])
          Empty.elim) compactProofRootSequentOnlyEndpointGraphDef.val ↔
        CompactProofRootSequentOnlyEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish
            (compactProofRootSequentOnlyEndpointCoordinatesOfValues
              inputBoundary inputCount inputBoundarySize
              taskStart taskFinish taskTag taskGammaFinish taskGammaCount
              taskGammaBoundary taskFirstFinish taskFirstCount
              taskSecondFinish taskSecondCount taskWitnessFinish
              taskWitnessCount taskSuffixCount taskGammaBoundarySize
              finalStart finalFinish
              sequentInputBoundary sequentInputCount
              sequentInputBoundarySize sequentFirstStart
              sequentFirstFinish sequentFirstBoundary sequentFirstCount
              sequentFirstBoundarySize sequentSuffixBoundary
              sequentSuffixCount sequentValueBoundary sequentValueCount
              sequentValueBoundarySize sequentFinalBoundary
              sequentFinalCount sequentFinalBoundarySize
              sequentTraceTableWidth sequentTraceValueBound) := by
    have henv :
        (Semiterm.val
            ![sequentTraceValueBound, sequentTraceTableWidth,
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
          ![(#37 : Semiterm ℒₒᵣ Empty 47), #38, #39, #40, #41,
            #42, #43, #44, #45,
            #36, #35, #34,
            #33, #32, #31, #30, #29, #28, #27, #26, #25, #24,
            #23, #22, #21, #20,
            #19, #18,
            #17, #16, #15, #14, #13, #12, #11, #10,
            #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]) =
          compactProofRootSequentOnlyEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              rootStart rootFinish bodyStart bodyFinish
              (compactProofRootSequentOnlyEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                taskStart taskFinish taskTag taskGammaFinish taskGammaCount
                taskGammaBoundary taskFirstFinish taskFirstCount
                taskSecondFinish taskSecondCount taskWitnessFinish
                taskWitnessCount taskSuffixCount taskGammaBoundarySize
                finalStart finalFinish
                sequentInputBoundary sequentInputCount
                sequentInputBoundarySize sequentFirstStart
                sequentFirstFinish sequentFirstBoundary sequentFirstCount
                sequentFirstBoundarySize sequentSuffixBoundary
                sequentSuffixCount sequentValueBoundary sequentValueCount
                sequentValueBoundarySize sequentFinalBoundary
                sequentFinalCount sequentFinalBoundarySize
                sequentTraceTableWidth sequentTraceValueBound) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactProofRootSequentOnlyEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish _
  simp [compactProofRootSequentOnlyEndpointBoundedGraphDef,
    CompactProofRootSequentOnlyEndpointBoundedGraph, hrow]

theorem compactProofRootSequentOnlyEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootSequentOnlyEndpointBoundedGraphDef.val := by
  simp [compactProofRootSequentOnlyEndpointBoundedGraphDef]

theorem CompactProofRootSequentOnlyEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish endpointBound : Nat}
    (hbounded : CompactProofRootSequentOnlyEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish endpointBound) :
    ∃ coordinates : CompactProofRootSequentOnlyEndpointCoordinates,
      CompactProofRootSequentOnlyEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  unfold CompactProofRootSequentOnlyEndpointBoundedGraph at hbounded
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
      sequentTraceValueBound, _hsequentTraceValueBound, hgraph⟩
  exact ⟨compactProofRootSequentOnlyEndpointCoordinatesOfValues
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
    sequentTraceTableWidth sequentTraceValueBound, hgraph⟩

theorem CompactProofRootSequentOnlyEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootSequentOnlyEndpointCoordinates}
    (hgraph : CompactProofRootSequentOnlyEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish coordinates) :
    ∃ endpointBound,
      CompactProofRootSequentOnlyEndpointBoundedGraph
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
    coordinates.sequent.traceValueBound
  refine ⟨endpointBound, ?_⟩
  unfold CompactProofRootSequentOnlyEndpointBoundedGraph
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
      coordinates.sequent.traceValueBound, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactProofRootSequentOnlyEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish endpointBound : Nat}
    (hbounded : CompactProofRootSequentOnlyEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish endpointBound) :
    ∃ input : List Nat,
    ∃ root : CompactNumericProofRoot,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactNumericListedDirectVerifierTaskLayout.CompactNumericVerifierTaskDirectLayout
        tokenTable width tokenCount rootStart rootFinish root ∧
      FoundationCompactNumericListedNodeFields.compactListedProofNodeFieldsParser
        input = some root := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

theorem exists_compactProofRootSequentOnlyEndpointBoundedGraph_of_success_with_inputLayout
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser :
      FoundationCompactNumericListedNodeFields.compactListedProofNodeFieldsParser
        input = some root)
    (htag : root.1 = 2 ∨ root.1 = 7 ∨ root.1 = 8) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootSequentOnlyEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound := by
  rcases exists_compactProofRootSequentOnlyEndpointGraph_of_success_with_inputLayout
      hparser htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
      hinputLayout, hgraph⟩
  rcases CompactProofRootSequentOnlyEndpointGraph.exists_bounded hgraph with
    ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, endpointBound,
    hinputLayout, hbounded⟩

theorem exists_compactProofRootSequentOnlyEndpointBoundedGraph_of_success
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser :
      FoundationCompactNumericListedNodeFields.compactListedProofNodeFieldsParser
        input = some root)
    (htag : root.1 = 2 ∨ root.1 = 7 ∨ root.1 = 8) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish endpointBound,
      CompactProofRootSequentOnlyEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish endpointBound := by
  rcases
      exists_compactProofRootSequentOnlyEndpointBoundedGraph_of_success_with_inputLayout
        hparser htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, endpointBound,
      _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, endpointBound, hgraph⟩

#print axioms compactProofRootSequentOnlyEndpointBoundedGraphDef_spec
#print axioms compactProofRootSequentOnlyEndpointBoundedGraphDef_sigmaZero
#print axioms CompactProofRootSequentOnlyEndpointBoundedGraph.exists_coordinates
#print axioms CompactProofRootSequentOnlyEndpointGraph.exists_bounded
#print axioms CompactProofRootSequentOnlyEndpointBoundedGraph.sound
#print axioms exists_compactProofRootSequentOnlyEndpointBoundedGraph_of_success

end FoundationCompactNumericListedDirectProofRootSequentOnlyBoundedFormula
