import integration.FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsPublicBounds

/-!
# Global coordinate budgets for non-parse checked rows

The fixed halted, finish, and combine row bounds are monotone in the two
endpoint-state weights.  Hence one public row-weight bound controls all three
non-parse branches without retaining local auxiliary-token parameters.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsGlobalBound

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectVerifierCombinePublicBounds
open FoundationCompactNumericListedDirectVerifierSimpleStepPublicBounds
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsPublicBounds

theorem compactNumericVerifierSimpleStepCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericVerifierSimpleStepCoordinateSizeBound left <=
      compactNumericVerifierSimpleStepCoordinateSizeBound right := by
  unfold compactNumericVerifierSimpleStepCoordinateSizeBound
  exact compactNumericVerifierStepUnusedCoordinateSizeBound_mono
    (Nat.mul_le_mul_left 2 h) h

theorem compactNumericVerifierPublicCombineRuleCoordinateBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericVerifierPublicCombineRuleCoordinateBound left <=
      compactNumericVerifierPublicCombineRuleCoordinateBound right := by
  have hsimple :=
    compactNumericVerifierSimpleCombineRuleCoordinateSizeBound_mono h
  have hwidth : 2 * left <= 2 * right := Nat.mul_le_mul_left 2 h
  have hallShift :=
    compactNumericAllShiftCombineRuleCoordinateSizeBound_mono hwidth h
  have hexsCut :=
    compactNumericExsCutCombineRuleCoordinateSizeBound_mono hwidth h
  unfold compactNumericVerifierPublicCombineRuleCoordinateBound
  omega

theorem compactNumericVerifierPublicCombineStepCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericVerifierPublicCombineStepCoordinateSizeBound left <=
      compactNumericVerifierPublicCombineStepCoordinateSizeBound right := by
  exact compactNumericVerifierCanonicalCombineStepCoordinateSizeBound_mono
    (Nat.mul_le_mul_left 2 h) h
    (compactNumericVerifierPublicCombineRuleCoordinateBound_mono h)

def compactNumericVerifierSimpleGlobalCoordinateSizeBound
    (rowWeight : Nat) : Nat :=
  compactNumericVerifierSimpleStepCoordinateSizeBound
    (compactNumericVerifierStatePairTokenWeightBound rowWeight rowWeight)

def compactNumericVerifierCombineGlobalCoordinateSizeBound
    (rowWeight : Nat) : Nat :=
  compactNumericVerifierPublicCombineStepCoordinateSizeBound
    (compactNumericVerifierPublicCombineTokenWeightBound rowWeight rowWeight)

def compactNumericVerifierNonParseGlobalCoordinateSizeBound
    (rowWeight : Nat) : Nat :=
  compactNumericVerifierSimpleGlobalCoordinateSizeBound rowWeight +
    compactNumericVerifierCombineGlobalCoordinateSizeBound rowWeight

theorem compactNumericVerifierSimpleLocalCoordinateSizeBound_le_global
    {currentState nextState : CompactNumericVerifierState}
    {rowWeight : Nat}
    (hcurrent : compactNumericVerifierStateWeight currentState <= rowWeight)
    (hnext : compactNumericVerifierStateWeight nextState <= rowWeight) :
    compactNumericVerifierSimpleStepCoordinateSizeBound
        (compactNumericVerifierStatePairTokenWeightBound
          (compactAdditiveValueWeight currentState)
          (compactAdditiveValueWeight nextState)) <=
      compactNumericVerifierSimpleGlobalCoordinateSizeBound rowWeight := by
  have hcurrent' : compactAdditiveValueWeight currentState <= rowWeight := by
    simpa [compactNumericVerifierStateWeight] using hcurrent
  have hnext' : compactAdditiveValueWeight nextState <= rowWeight := by
    simpa [compactNumericVerifierStateWeight] using hnext
  unfold compactNumericVerifierSimpleGlobalCoordinateSizeBound
  exact compactNumericVerifierSimpleStepCoordinateSizeBound_mono
    (compactNumericVerifierStatePairTokenWeightBound_mono hcurrent' hnext')

theorem compactNumericVerifierCombineLocalCoordinateSizeBound_le_global
    {currentState nextState : CompactNumericVerifierState}
    {rowWeight : Nat}
    (hcurrent : compactNumericVerifierStateWeight currentState <= rowWeight)
    (hnext : compactNumericVerifierStateWeight nextState <= rowWeight) :
    compactNumericVerifierPublicCombineStepCoordinateSizeBound
        (compactNumericVerifierPublicCombineTokenWeightBound
          (compactAdditiveValueWeight currentState)
          (compactAdditiveValueWeight nextState)) <=
      compactNumericVerifierCombineGlobalCoordinateSizeBound rowWeight := by
  have hcurrent' : compactAdditiveValueWeight currentState <= rowWeight := by
    simpa [compactNumericVerifierStateWeight] using hcurrent
  have hnext' : compactAdditiveValueWeight nextState <= rowWeight := by
    simpa [compactNumericVerifierStateWeight] using hnext
  unfold compactNumericVerifierCombineGlobalCoordinateSizeBound
  exact compactNumericVerifierPublicCombineStepCoordinateSizeBound_mono
    (compactNumericVerifierPublicCombineTokenWeightBound_mono
      hcurrent' hnext')

theorem compactNumericVerifierSimpleGlobal_le_nonParseGlobal
    (rowWeight : Nat) :
    compactNumericVerifierSimpleGlobalCoordinateSizeBound rowWeight <=
      compactNumericVerifierNonParseGlobalCoordinateSizeBound rowWeight := by
  unfold compactNumericVerifierNonParseGlobalCoordinateSizeBound
  omega

theorem compactNumericVerifierCombineGlobal_le_nonParseGlobal
    (rowWeight : Nat) :
    compactNumericVerifierCombineGlobalCoordinateSizeBound rowWeight <=
      compactNumericVerifierNonParseGlobalCoordinateSizeBound rowWeight := by
  unfold compactNumericVerifierNonParseGlobalCoordinateSizeBound
  omega

theorem
    exists_compactNumericVerifierHaltedCheckedStepRow_with_globalBound
    (proofTokens certificateTokens : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (result : Bool)
    {rowWeight : Nat}
    (hstate : compactNumericVerifierStateWeight
      ((((proofTokens, certificateTokens), (tasks, values)), some result)) <=
        rowWeight) :
    let state : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (tasks, values)), some result)
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = state /\
        row.nextState = state /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierNonParseGlobalCoordinateSizeBound
              rowWeight := by
  dsimp only
  rcases
      exists_compactNumericVerifierHaltedCheckedStepRow_with_fixed_sizeBound
        proofTokens certificateTokens tasks values result with
    ⟨row, hcurrent, hnext, hcoordinates⟩
  refine ⟨row, hcurrent, hnext, ?_⟩
  intro coordinate
  exact (hcoordinates coordinate).trans
    ((compactNumericVerifierSimpleLocalCoordinateSizeBound_le_global
        hstate hstate).trans
      (compactNumericVerifierSimpleGlobal_le_nonParseGlobal rowWeight))

theorem
    exists_compactNumericVerifierFinishCheckedStepRow_with_globalBound
    (proofTokens certificateTokens : List Nat)
    (values : List CompactNumericChildResult)
    {rowWeight : Nat}
    (hcurrent : compactNumericVerifierStateWeight
      ((((proofTokens, certificateTokens), ([], values)), none)) <= rowWeight)
    (hnext : compactNumericVerifierStateWeight
      (compactNumericFinishState
        ((proofTokens, certificateTokens), ([], values))) <= rowWeight) :
    let payload : CompactNumericRunningPayload :=
      ((proofTokens, certificateTokens), ([], values))
    let currentState : CompactNumericVerifierState := (payload, none)
    let nextState := compactNumericFinishState payload
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = currentState /\
        row.nextState = nextState /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierNonParseGlobalCoordinateSizeBound
              rowWeight := by
  dsimp only
  rcases
      exists_compactNumericVerifierFinishCheckedStepRow_with_fixed_sizeBound
        proofTokens certificateTokens values with
    ⟨row, hrowCurrent, hrowNext, hcoordinates⟩
  refine ⟨row, hrowCurrent, hrowNext, ?_⟩
  intro coordinate
  exact (hcoordinates coordinate).trans
    ((compactNumericVerifierSimpleLocalCoordinateSizeBound_le_global
        hcurrent hnext).trans
      (compactNumericVerifierSimpleGlobal_le_nonParseGlobal rowWeight))

theorem
    exists_compactNumericVerifierPublicCombineCheckedStepRow_with_globalBound
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source : List CompactNumericChildResult)
    (htaskNe : task.1 ≠ 10)
    {rowWeight : Nat}
    (hcurrent : compactNumericVerifierStateWeight
      ((((proofTokens, certificateTokens), (task :: tasks, source)), none)) <=
        rowWeight)
    (hnext : forall target nextStatus,
      compactNumericCombineState task
          ((proofTokens, certificateTokens), (tasks, source)) =
        (((proofTokens, certificateTokens), (tasks, target)), nextStatus) ->
      compactNumericVerifierStateWeight
          (((proofTokens, certificateTokens), (tasks, target)), nextStatus) <=
        rowWeight) :
    exists target nextStatus,
      compactNumericCombineState task
          ((proofTokens, certificateTokens), (tasks, source)) =
        (((proofTokens, certificateTokens), (tasks, target)), nextStatus) /\
      let currentState : CompactNumericVerifierState :=
        (((proofTokens, certificateTokens), (task :: tasks, source)), none)
      let nextState : CompactNumericVerifierState :=
        (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <=
              compactNumericVerifierNonParseGlobalCoordinateSizeBound
                rowWeight := by
  rcases
      exists_compactNumericVerifierPublicCombineCheckedStepRow_with_fixed_sizeBound
        proofTokens certificateTokens task tasks source htaskNe with
    ⟨target, nextStatus, htransition, hlocal⟩
  refine ⟨target, nextStatus, htransition, ?_⟩
  dsimp only at hlocal ⊢
  rcases hlocal with
    ⟨row, hrowCurrent, hrowNext, hcoordinates⟩
  refine ⟨row, hrowCurrent, hrowNext, ?_⟩
  intro coordinate
  exact (hcoordinates coordinate).trans
    ((compactNumericVerifierCombineLocalCoordinateSizeBound_le_global
        hcurrent (hnext target nextStatus htransition)).trans
      (compactNumericVerifierCombineGlobal_le_nonParseGlobal rowWeight))

theorem
    exists_compactNumericVerifierPublicCombineCheckedStepRow_with_globalBound_of_transition
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
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = currentState /\
        row.nextState = nextState /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <=
            compactNumericVerifierNonParseGlobalCoordinateSizeBound
              rowWeight := by
  rcases
      exists_compactNumericVerifierPublicCombineCheckedStepRow_with_fixed_sizeBound
        proofTokens certificateTokens task tasks source htaskNe with
    ⟨actualTarget, actualStatus, hactualTransition, hlocal⟩
  have hstateEquality :
      (((proofTokens, certificateTokens), (tasks, actualTarget)),
          actualStatus) =
        (((proofTokens, certificateTokens), (tasks, target)), nextStatus) :=
    hactualTransition.symm.trans htransition
  have htargetStatus :
      actualTarget = target /\ actualStatus = nextStatus := by
    simpa only [Prod.mk.injEq, true_and, and_true] using hstateEquality
  rcases htargetStatus with ⟨rfl, rfl⟩
  dsimp only at hlocal ⊢
  rcases hlocal with
    ⟨row, hrowCurrent, hrowNext, hcoordinates⟩
  refine ⟨row, hrowCurrent, hrowNext, ?_⟩
  intro coordinate
  exact (hcoordinates coordinate).trans
    ((compactNumericVerifierCombineLocalCoordinateSizeBound_le_global
        hcurrent hnext).trans
      (compactNumericVerifierCombineGlobal_le_nonParseGlobal rowWeight))

#print axioms compactNumericVerifierSimpleLocalCoordinateSizeBound_le_global
#print axioms compactNumericVerifierCombineLocalCoordinateSizeBound_le_global
#print axioms
  exists_compactNumericVerifierHaltedCheckedStepRow_with_globalBound
#print axioms
  exists_compactNumericVerifierFinishCheckedStepRow_with_globalBound
#print axioms
  exists_compactNumericVerifierPublicCombineCheckedStepRow_with_globalBound
#print axioms
  exists_compactNumericVerifierPublicCombineCheckedStepRow_with_globalBound_of_transition

end FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsGlobalBound
