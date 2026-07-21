import integration.FoundationCompactNumericListedDirectVerifierCombineActiveCountBounds
import integration.FoundationCompactNumericListedDirectVerifierCombinePublicBounds
import integration.FoundationCompactNumericListedDirectVerifierAcceptedStateTableControlBounds

/-!
# Public combine rows retaining active numerical loop controls

This module constructs one canonical formula witness and keeps both kinds of
quantitative evidence on that same witness: pointwise binary-size bounds for
all 429 coordinates and numerical bounds for loops used by the selected
combine branch.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineActiveCountPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierCombineBranchRows
open FoundationCompactNumericListedDirectVerifierCombineRuleWitnessBounds
open FoundationCompactNumericListedDirectVerifierCombineCanonicalGraph
open FoundationCompactNumericListedDirectVerifierCombinePublicBounds
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierAcceptedStateTableControlBounds
open FoundationCompactNumericListedDirectVerifierCombineActiveCountBounds

set_option maxRecDepth 5000 in
set_option maxHeartbeats 12000000 in
theorem
    exists_compactNumericVerifierPublicCombineStepFormulaWitness_with_fixed_sizeBound_and_countControls
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source : List CompactNumericChildResult)
    (htaskNe : task.1 ≠ 10) :
    exists target nextStatus,
      compactNumericCombineState task
          ((proofTokens, certificateTokens), (tasks, source)) =
        (((proofTokens, certificateTokens), (tasks, target)), nextStatus) /\
      let currentState : CompactNumericVerifierState :=
        (((proofTokens, certificateTokens), (task :: tasks, source)), none)
      let nextState : CompactNumericVerifierState :=
        (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
      let currentTokens := compactAdditiveEncode currentState
      let nextTokens := compactAdditiveEncode nextState
      let backTokens :=
        compactNumericVerifierPublicCombineAuxiliaryTokens task source
      let tokens := currentTokens ++ nextTokens ++ backTokens
      let width := (compactBinaryNatPayloadBits tokens).length
      exists witness : CompactNumericVerifierStepFormulaWitness
          (compactFixedWidthTableCode width tokens) width tokens.length
          0 currentTokens.length currentTokens.length
          (currentTokens.length + nextTokens.length),
        CompactNumericVerifierCombineEnvironmentCountControls
            witness.environment /\
          forall coordinate : Fin 429,
            Nat.size (witness.environment coordinate) <=
              compactNumericVerifierPublicCombineStepCoordinateSizeBound
                (compactNumericVerifierPublicCombineTokenWeightBound
                  (compactAdditiveValueWeight currentState)
                  (compactAdditiveValueWeight nextState)) := by
  rcases
      CompactNumericVerifierCanonicalPublicCombineBoundedStateGraph.exists_of_public_step
        proofTokens certificateTokens task tasks source htaskNe with
    ⟨target, nextStatus, ruleCoordinateBound,
      htransition, hcanonical, hruleEnvelope⟩
  refine ⟨target, nextStatus, htransition, ?_⟩
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let backTokens :=
    compactNumericVerifierPublicCombineAuxiliaryTokens task source
  let tokens := currentTokens ++ nextTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenWeightBound :=
    compactNumericVerifierPublicCombineTokenWeightBound
      (compactAdditiveValueWeight currentState)
      (compactAdditiveValueWeight nextState)
  have htokenCount : tokens.length <= tokenWeightBound := by
    simpa only [tokens, currentTokens, nextTokens, backTokens,
      currentState, nextState, tokenWeightBound] using
      compactNumericVerifierPublicCombineTokens_length_le
        proofTokens certificateTokens task tasks source target nextStatus
  have hwidth : width <= 2 * tokenWeightBound := by
    simpa only [width, tokens, currentTokens, nextTokens, backTokens,
      currentState, nextState, tokenWeightBound] using
      compactNumericVerifierPublicCombineWidth_le
        proofTokens certificateTokens task tasks source target nextStatus
  have henvelope :
      compactNumericVerifierCanonicalCombineRuleCoordinateEnvelope
          proofTokens certificateTokens task tasks source target nextStatus
            backTokens <=
        compactNumericVerifierPublicCombineRuleCoordinateBound
          tokenWeightBound := by
    simpa only [backTokens, currentState, nextState, tokenWeightBound] using
      compactNumericVerifierCanonicalCombineRuleCoordinateEnvelope_le_public
        proofTokens certificateTokens task tasks source target nextStatus
  have hrulePublic :
      ruleCoordinateBound <=
        compactNumericVerifierPublicCombineRuleCoordinateBound
          tokenWeightBound :=
    hruleEnvelope.trans henvelope
  have hcoordinateBound :
      compactNumericVerifierCanonicalCombineStepCoordinateSizeBound
          width tokens.length ruleCoordinateBound <=
        compactNumericVerifierPublicCombineStepCoordinateSizeBound
          tokenWeightBound :=
    compactNumericVerifierCanonicalCombineStepCoordinateSizeBound_le_public
      hwidth htokenCount hrulePublic
  dsimp only [CompactNumericVerifierCanonicalCombineBoundedGraph] at hcanonical
  rcases hcanonical with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, ruleWitness,
      _hcurrentStart, _hcurrentFinish, _hnextStart, _hnextFinish,
      hcurrentPackage, hnextPackage, hcombine, hrule⟩
  let arguments := CompactNumericVerifierStepArguments.ofCombine
    taskCoordinates taskSizeWitness ruleWitness
  have hgraph : arguments.Graph
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness := by
    dsimp only [CompactNumericVerifierStepArguments.Graph, arguments,
      CompactNumericVerifierStepArguments.ofCombine]
    refine Or.inr (Or.inr (Or.inr ?_))
    simpa only [
      FoundationCompactNumericListedDirectVerifierStepFormula.compactNumericVerifierStepCombineRuleWitness,
      compactNumericVerifierCombineRuleWitnessOf] using hcombine
  let witness := arguments.toFormulaWitness
    hcurrentPackage.1 hcurrentPackage.2.1
    hnextPackage.1 hnextPackage.2.1 hgraph
  have hcontrols : CompactNumericVerifierCombineEnvironmentCountControls
      witness.environment := by
    change CompactNumericVerifierCombineEnvironmentCountControls
      (arguments.environment (compactFixedWidthTableCode width tokens)
        width tokens.length currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness)
    exact CompactNumericVerifierCombineStateGraph.environmentCountControls
      hcombine
  have hstateBounds :=
    CompactNumericVerifierStateCanonicalCorePackage.coordinateSizeBounds
      hcurrentPackage
  let stateBound :=
    compactNumericVerifierStateCoreCoordinateSizeBound width tokens.length
  let commonBound := stateBound + ruleCoordinateBound
  have hstateValueBound : Nat.size currentSizeWitness.taskValueBound <=
      stateBound := by
    simpa only [stateBound, width, tokens, currentTokens, nextTokens,
      currentState, nextState] using hstateBounds.taskValueBound
  have hvalueBound : Nat.size currentSizeWitness.taskValueBound <=
      commonBound := hstateValueBound.trans (by
        dsimp only [commonBound, stateBound]
        omega)
  have hruleCommon : forall coordinate : Fin 34,
      Nat.size (compactNumericVerifierCombineRuleWitnessEnvironment
        ruleWitness coordinate) <= commonBound := by
    intro coordinate
    exact (hrule coordinate).trans (by
      dsimp only [commonBound, stateBound]
      omega)
  have hconstant :
      compactNumericVerifierStepArgumentsEnvironmentConstant arguments <=
        384 * commonBound :=
    compactNumericVerifierStepArgumentsEnvironmentConstant_ofCombine_le
      taskCoordinates taskSizeWitness ruleWitness
      hcombine.2.2.1 hvalueBound hruleCommon
  have htotal :
      compactNumericVerifierStepArgumentsCoordinateSizeBound
          arguments width tokens.length <=
        compactNumericVerifierCanonicalCombineStepCoordinateSizeBound
          width tokens.length ruleCoordinateBound := by
    dsimp only [compactNumericVerifierStepArgumentsCoordinateSizeBound,
      compactNumericVerifierCanonicalCombineStepCoordinateSizeBound,
      stateBound, commonBound]
    exact Nat.add_le_add_left hconstant _
  refine ⟨witness, hcontrols, ?_⟩
  intro coordinate
  have hraw : Nat.size (witness.environment coordinate) <=
      compactNumericVerifierStepArgumentsCoordinateSizeBound
        arguments width tokens.length := by
    change Nat.size (arguments.environment
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      coordinate) <=
        compactNumericVerifierStepArgumentsCoordinateSizeBound arguments
          width tokens.length
    exact compactNumericVerifierStepEnvironment_size_le arguments
      (canonicalStateTable_size_le_coordinateSizeBound tokens width)
      (CompactNumericVerifierStateCanonicalCorePackage.coordinateSizeBounds
        hcurrentPackage)
      (CompactNumericVerifierStateCanonicalCorePackage.coordinateSizeBounds
        hnextPackage)
      coordinate
  simpa only [currentState, nextState, currentTokens, nextTokens,
    backTokens, tokens, width, tokenWeightBound] using
    (hraw.trans htotal).trans hcoordinateBound

set_option maxRecDepth 5000 in
set_option maxHeartbeats 12000000 in
theorem
    exists_compactNumericVerifierPublicCombineCheckedStepRow_with_controlBounds_and_countControls_of_transition
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool)
    (htaskNe : task.1 ≠ 10)
    (htransition : compactNumericCombineState task
      ((proofTokens, certificateTokens), (tasks, source)) =
        (((proofTokens, certificateTokens), (tasks, target)), nextStatus))
    {rowWeight : Nat}
    (hcurrent : compactNumericVerifierStateWeight
      ((((proofTokens, certificateTokens), (task :: tasks, source)), none)) <=
        rowWeight)
    (hnext : compactNumericVerifierStateWeight
      ((((proofTokens, certificateTokens), (tasks, target)), nextStatus)) <=
        rowWeight) :
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (task :: tasks, source)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
    let coordinateBound :=
      compactNumericVerifierPublicCombineStepCoordinateSizeBound
        (compactNumericVerifierPublicCombineTokenWeightBound
          (compactAdditiveValueWeight currentState)
          (compactAdditiveValueWeight nextState))
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = currentState /\
        row.nextState = nextState /\
        CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight /\
        (forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <= coordinateBound) /\
        CompactNumericVerifierCombineEnvironmentCountControls
          row.environment := by
  dsimp only
  rcases
      exists_compactNumericVerifierPublicCombineStepFormulaWitness_with_fixed_sizeBound_and_countControls
        proofTokens certificateTokens task tasks source htaskNe with
    ⟨actualTarget, actualStatus, hactualTransition,
      witness, hcontrols, hcoordinates⟩
  have hstateEquality :
      (((proofTokens, certificateTokens), (tasks, actualTarget)),
          actualStatus) =
        (((proofTokens, certificateTokens), (tasks, target)), nextStatus) :=
    hactualTransition.symm.trans htransition
  have htargetStatus : actualTarget = target /\ actualStatus = nextStatus := by
    simpa only [Prod.mk.injEq, true_and, and_true] using hstateEquality
  rcases htargetStatus with ⟨rfl, rfl⟩
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, actualTarget)), actualStatus)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let backTokens :=
    compactNumericVerifierPublicCombineAuxiliaryTokens task source
  let tokens := currentTokens ++ nextTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let stateTable := compactFixedWidthTableCode width tokens
  have hpairRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState backTokens
  have hpair :
      CompactNumericVerifierStateDirectLayout stateTable width tokens.length
          0 currentTokens.length currentState /\
        CompactNumericVerifierStateDirectLayout stateTable width tokens.length
          currentTokens.length (currentTokens.length + nextTokens.length)
            nextState := by
    simpa only [stateTable, width, tokens, currentTokens, nextTokens,
      backTokens] using hpairRaw
  rcases hpair with ⟨hcurrentLayout, hnextLayout⟩
  let row := CompactNumericVerifierStepFormulaWitness.toCheckedStepRow witness
    currentState nextState hcurrentLayout hnextLayout
  refine ⟨row, rfl, rfl, ?_, ?_, ?_⟩
  · refine
      CompactNumericVerifierAcceptedStateTableControlBounds.of_canonicalCombine
        row proofTokens certificateTokens task tasks source actualTarget
          actualStatus rowWeight
          (by simpa only [compactNumericVerifierStateWeight] using hcurrent)
          (by simpa only [compactNumericVerifierStateWeight] using hnext)
          ?_ ?_
    · simpa only [row,
        CompactNumericVerifierStepFormulaWitness.toCheckedStepRow_environment,
        width, tokens, currentTokens, nextTokens, backTokens, currentState,
        nextState] using witness.stateWidth_eq
    · simpa only [row,
        CompactNumericVerifierStepFormulaWitness.toCheckedStepRow_environment,
        tokens, currentTokens, nextTokens, backTokens, currentState,
        nextState] using witness.stateTokenCount_eq
  · intro coordinate
    simpa only [row,
      CompactNumericVerifierStepFormulaWitness.toCheckedStepRow_environment]
      using hcoordinates coordinate
  · simpa only [row,
      CompactNumericVerifierStepFormulaWitness.toCheckedStepRow_environment]
      using hcontrols

#print axioms
  exists_compactNumericVerifierPublicCombineStepFormulaWitness_with_fixed_sizeBound_and_countControls
#print axioms
  exists_compactNumericVerifierPublicCombineCheckedStepRow_with_controlBounds_and_countControls_of_transition

end FoundationCompactNumericListedDirectVerifierCombineActiveCountPublicBounds
