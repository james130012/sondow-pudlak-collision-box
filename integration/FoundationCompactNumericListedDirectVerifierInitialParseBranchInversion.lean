import integration.FoundationCompactNumericListedDirectVerifierStepEnvironmentSurjectivity
import integration.FoundationCompactNumericListedDirectVerifierStateRealization
import integration.FoundationCompactNumericListedDirectVerifierStateCrossTableEquality

/-!
# Initial parse-branch inversion for a verifier step

The task-head coordinates in columns 45--58 are fixed by the satisfying
environment itself.  At an initial verifier state, the non-parse step branches
are impossible, and those fixed coordinates therefore describe the unique
initial parse task without selecting coordinates from an existential package.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierInitialParseBranchInversion

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierStateRealization
open FoundationCompactNumericListedDirectVerifierStateCrossTableEquality
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectVerifierStepEnvironmentSurjectivity

def compactNumericVerifierInitialTaskCoordinatesFromEnvironment
    (env : Fin 429 -> Nat) : CompactNumericVerifierTaskRowCoordinates where
  start := env 45
  finish := env 46
  tag := env 47
  gammaFinish := env 48
  gammaCount := env 49
  gammaBoundary := env 50
  firstFinish := env 51
  firstCount := env 52
  secondFinish := env 53
  secondCount := env 54
  witnessFinish := env 55
  witnessCount := env 56
  suffixCount := env 57

def compactNumericVerifierInitialTaskSizeWitnessFromEnvironment
    (env : Fin 429 -> Nat) : CompactNumericVerifierTaskSizeWitness where
  gammaBoundarySize := env 58

@[simp] theorem
    compactNumericVerifierParseStateGraphParameters_initialTaskCoordinates
    (env : Fin 429 -> Nat) :
    (compactNumericVerifierParseStateGraphParametersFromEnvironment env).arguments.taskCoordinates =
      compactNumericVerifierInitialTaskCoordinatesFromEnvironment env := by
  rfl

@[simp] theorem
    compactNumericVerifierParseStateGraphParameters_initialTaskSizeWitness
    (env : Fin 429 -> Nat) :
    (compactNumericVerifierParseStateGraphParametersFromEnvironment env).arguments.taskSizeWitness =
      compactNumericVerifierInitialTaskSizeWitnessFromEnvironment env := by
  rfl

private theorem compactNumericParseTask_shape_of_boundedHead
    {tokenTable width tokenCount taskBoundary valueBound : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hhead : CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount taskBoundary valueBound
      coordinates sizeWitness)
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        taskBoundary [compactNumericParseTask]) :
    coordinates.tag = 10 ∧
      coordinates.gammaCount = 0 ∧
      coordinates.firstCount = 0 ∧
      coordinates.secondCount = 0 ∧
      coordinates.witnessCount = 0 ∧
      coordinates.suffixCount = 0 := by
  rcases hhead.realize_actualHeadWithFields (by simp) hrows with
    ⟨task, htask, htaskTag, _htaskLayout,
      _hgammaRows, hgammaLength,
      _hfirstLayout, hfirstLength,
      _hsecondLayout, hsecondLength,
      _hwitnessLayout, hwitnessLength,
      _hsuffixLayout, hsuffixLength⟩
  have htaskParse : task = compactNumericParseTask := by
    simpa using htask
  subst task
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [compactNumericParseTask,
      compactNumericEmptyNodeFields] using htaskTag.symm
  · simpa [compactNumericParseTask,
      compactNumericEmptyNodeFields] using hgammaLength.symm
  · simpa [compactNumericParseTask,
      compactNumericEmptyNodeFields] using hfirstLength.symm
  · simpa [compactNumericParseTask,
      compactNumericEmptyNodeFields] using hsecondLength.symm
  · simpa [compactNumericParseTask,
      compactNumericEmptyNodeFields] using hwitnessLength.symm
  · simpa [compactNumericParseTask,
      compactNumericEmptyNodeFields] using hsuffixLength.symm

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
theorem compactNumericVerifierInitialParseBranchInversion
    (env : Fin 429 -> Nat)
    {proofTokens certificateTokens : List Nat}
    (hformula : compactNumericVerifierStepGraphDef.val.Evalb env)
    (hcurrent : CompactNumericVerifierStateDirectLayout
      (env 0) (env 1) (env 2) (env 3) (env 4)
      (compactNumericVerifierInitialState proofTokens certificateTokens)) :
    let coordinates :=
      compactNumericVerifierInitialTaskCoordinatesFromEnvironment env
    let sizeWitness :=
      compactNumericVerifierInitialTaskSizeWitnessFromEnvironment env
    CompactNumericVerifierTaskBoundedHead
        (env 0) (env 1) (env 2) (env 11) (env 21)
        coordinates sizeWitness ∧
      coordinates.tag = 10 ∧
      coordinates.gammaCount = 0 ∧
      coordinates.firstCount = 0 ∧
      coordinates.secondCount = 0 ∧
      coordinates.witnessCount = 0 ∧
      coordinates.suffixCount = 0 := by
  let currentCoordinates := compactNumericVerifierStepCurrentCoordinates env
  let currentSizeWitness := compactNumericVerifierStepCurrentSizeWitness env
  have hcore : CompactNumericVerifierStateCoreGraph
      (env 0) (env 1) (env 2)
      currentCoordinates currentSizeWitness :=
    compactNumericVerifierStepGraphDef_evalb_currentCore env hformula
  rcases
      FoundationCompactNumericListedDirectVerifierStateRealization.CompactNumericVerifierStateCoreGraph.realizeDirectLayout
        hcore with
    ⟨decodedProof, decodedCertificate, tasks, values, status,
      _hproofLength, _hcertificateLength, htasksLength, _hvaluesLength,
      hdecodedLayout, _hproofLayout, _hcertificateLayout,
      _htaskListLayout, htaskRows,
      _hvalueListLayout, _hvalueRows, hstatusCase⟩
  have hcoordinateFields :=
    compactNumericVerifierStepCurrentCoordinates_fields env
  change
    currentCoordinates.start = env 3 ∧
      currentCoordinates.finish = env 4 ∧
      currentCoordinates.proofFinish = env 5 ∧
      currentCoordinates.proofCount = env 6 ∧
      currentCoordinates.certificateFinish = env 7 ∧
      currentCoordinates.certificateCount = env 8 ∧
      currentCoordinates.tasksFinish = env 9 ∧
      currentCoordinates.taskCount = env 10 ∧
      currentCoordinates.taskBoundary = env 11 ∧
      currentCoordinates.valuesFinish = env 12 ∧
      currentCoordinates.valueCount = env 13 ∧
      currentCoordinates.valueBoundary = env 14 ∧
      currentCoordinates.statusTag = env 15 ∧
      currentCoordinates.statusPayloadStart = env 16 ∧
      currentCoordinates.statusBool = env 17 at hcoordinateFields
  rcases hcoordinateFields with
    ⟨hstart, hfinish, _hproofFinish, _hproofCount,
      _hcertificateFinish, _hcertificateCount,
      _htasksFinish, _htaskCount, htaskBoundary,
      _hvaluesFinish, _hvalueCount, _hvalueBoundary,
      _hstatusTag, _hstatusPayloadStart, _hstatusBool⟩
  have hsizeFields :=
    compactNumericVerifierStepCurrentSizeWitness_fields env
  change
    currentSizeWitness.taskBoundarySize = env 18 ∧
      currentSizeWitness.valueBoundarySize = env 19 ∧
      currentSizeWitness.taskTableWidth = env 20 ∧
      currentSizeWitness.taskValueBound = env 21 ∧
      currentSizeWitness.valueTableWidth = env 22 ∧
      currentSizeWitness.valueValueBound = env 23 at hsizeFields
  rcases hsizeFields with
    ⟨_hTaskBoundarySize, _hValueBoundarySize, _hTaskTableWidth,
      htaskValueBound, _hValueTableWidth, _hValueValueBound⟩
  have hdecodedLayout' : CompactNumericVerifierStateDirectLayout
      (env 0) (env 1) (env 2) (env 3) (env 4)
      (((decodedProof, decodedCertificate), (tasks, values)), status) := by
    simpa only [hstart, hfinish] using hdecodedLayout
  rcases
      FoundationCompactNumericListedDirectVerifierStateCrossTableEquality.CompactNumericVerifierStateDirectLayout.toSliceCarries
        hcurrent with
    ⟨_hcurrentFinish, hcurrentBound, _hcurrentEntries⟩
  have hslices : CompactFixedWidthTokenSlicesEq
      (env 0) (env 1) (env 2)
      (env 3) (env 4) (env 3) (env 4) :=
    CompactFixedWidthTokenSlicesEq.refl (by omega) hcurrentBound
  have hstateEq :
      (((decodedProof, decodedCertificate), (tasks, values)), status) =
        compactNumericVerifierInitialState proofTokens certificateTokens :=
    CompactFixedWidthTokenSlicesEq.verifierStateValue_eq
      hslices hcurrent hdecodedLayout'
  have htasksEq : tasks = [compactNumericParseTask] :=
    congrArg (fun state : CompactNumericVerifierState => state.1.2.1) hstateEq
  have hstatusEq : status = none :=
    congrArg (fun state : CompactNumericVerifierState => state.2) hstateEq
  have htaskCountOne : currentCoordinates.taskCount = 1 := by
    rw [← htasksLength, htasksEq]
    rfl
  have hstatusZero : currentCoordinates.statusTag = 0 := by
    rcases hstatusCase with hnone | hsome
    · exact hnone.2
    · rcases hsome with ⟨result, hsome, _htag, _hbool⟩
      rw [hstatusEq] at hsome
      simp at hsome
  have htaskRows' : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout
      (env 0) (env 1) (env 2) (env 11)
      [compactNumericParseTask] := by
    simpa only [htaskBoundary, htasksEq] using htaskRows
  let parameters :=
    compactNumericVerifierParseStateGraphParametersFromEnvironment env
  have hgraph : parameters.arguments.Graph
      parameters.stateTable parameters.stateWidth parameters.stateTokenCount
      parameters.currentCoordinates parameters.nextCoordinates
      parameters.currentSizeWitness parameters.nextSizeWitness :=
    compactNumericVerifierStepGraphDef_evalb_graph env hformula
  have normalizeHead :
      CompactNumericVerifierTaskBoundedHead
          parameters.stateTable parameters.stateWidth
          parameters.stateTokenCount
          parameters.currentCoordinates.taskBoundary
          parameters.currentSizeWitness.taskValueBound
          parameters.arguments.taskCoordinates
          parameters.arguments.taskSizeWitness ->
        CompactNumericVerifierTaskBoundedHead
          (env 0) (env 1) (env 2) (env 11) (env 21)
          (compactNumericVerifierInitialTaskCoordinatesFromEnvironment env)
          (compactNumericVerifierInitialTaskSizeWitnessFromEnvironment env) := by
    intro hhead
    change CompactNumericVerifierTaskBoundedHead
      (env 0) (env 1) (env 2)
      currentCoordinates.taskBoundary currentSizeWitness.taskValueBound
      (compactNumericVerifierParseStateGraphParametersFromEnvironment env).arguments.taskCoordinates
      (compactNumericVerifierParseStateGraphParametersFromEnvironment env).arguments.taskSizeWitness at hhead
    simpa only [htaskBoundary, htaskValueBound,
      compactNumericVerifierParseStateGraphParameters_initialTaskCoordinates,
      compactNumericVerifierParseStateGraphParameters_initialTaskSizeWitness]
      using hhead
  unfold CompactNumericVerifierStepArguments.Graph at hgraph
  rcases hgraph with hhalted | hfinish | hparse | hcombine
  · have hhaltedStatus := hhalted.2.2.1
    change currentCoordinates.statusTag = 1 at hhaltedStatus
    omega
  · have hfinishTaskCount := hfinish.2.2.2.1
    change currentCoordinates.taskCount = 0 at hfinishTaskCount
    omega
  · rcases hparse with hfailure | hsuccess
    · have hhead := normalizeHead hfailure.2.2.1
      exact ⟨hhead,
        compactNumericParseTask_shape_of_boundedHead hhead htaskRows'⟩
    · have hhead := normalizeHead hsuccess.2.2.1
      exact ⟨hhead,
        compactNumericParseTask_shape_of_boundedHead hhead htaskRows'⟩
  · have hhead := normalizeHead hcombine.2.2.1
    have hshape :=
      compactNumericParseTask_shape_of_boundedHead hhead htaskRows'
    have htagNe := hcombine.2.2.2.1.2.2.1
    change
      (compactNumericVerifierParseStateGraphParametersFromEnvironment env).arguments.taskCoordinates.tag ≠
        10 at htagNe
    simpa only [
      compactNumericVerifierParseStateGraphParameters_initialTaskCoordinates]
      using htagNe hshape.1

#print axioms compactNumericVerifierInitialParseBranchInversion

end FoundationCompactNumericListedDirectVerifierInitialParseBranchInversion
