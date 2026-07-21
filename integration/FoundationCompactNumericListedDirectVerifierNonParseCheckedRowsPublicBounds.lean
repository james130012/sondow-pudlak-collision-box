import integration.FoundationCompactNumericListedDirectVerifierSimpleStepPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
import integration.FoundationCompactNumericListedDirectVerifierCheckedStepRow

/-!
# Publicly bounded checked rows for non-parse verifier steps

The halted, finish, and combine fixed-bound witnesses are packaged as actual
checked rows.  Their existing public coordinate bounds are retained exactly.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectVerifierSimpleStepPublicBounds
open FoundationCompactNumericListedDirectVerifierCombinePublicBounds
open FoundationCompactNumericListedDirectVerifierCheckedStepRow

theorem
    exists_compactNumericVerifierHaltedCheckedStepRow_with_fixed_sizeBound
    (proofTokens certificateTokens : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (result : Bool) :
    let state : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (tasks, values)), some result)
    let coordinateBound :=
      compactNumericVerifierSimpleStepCoordinateSizeBound
        (compactNumericVerifierStatePairTokenWeightBound
          (compactAdditiveValueWeight state)
          (compactAdditiveValueWeight state))
    ∃ row : CompactNumericVerifierCheckedStepRow,
      row.currentState = state ∧
        row.nextState = state ∧
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <= coordinateBound := by
  let state : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, values)), some result)
  let stateTokens := compactAdditiveEncode state
  let tokens := stateTokens ++ stateTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let stateTable := compactFixedWidthTableCode width tokens
  let coordinateBound :=
    compactNumericVerifierSimpleStepCoordinateSizeBound
      (compactNumericVerifierStatePairTokenWeightBound
        (compactAdditiveValueWeight state)
        (compactAdditiveValueWeight state))
  rcases
      exists_compactNumericVerifierHaltedStepFormulaWitness_with_fixed_sizeBound
        proofTokens certificateTokens tasks values result with
    ⟨witness, hwitness⟩
  have hpairRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    state state []
  have hpair :
      CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length 0 stateTokens.length state ∧
        CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length stateTokens.length
            (stateTokens.length + stateTokens.length) state := by
    simpa only [stateTable, width, tokens, stateTokens, List.append_nil] using
      hpairRaw
  rcases hpair with ⟨hcurrentLayout, hnextLayout⟩
  let row : CompactNumericVerifierCheckedStepRow :=
    { environment := witness.environment
      currentState := state
      nextState := state
      currentLayout := by
        simpa only [witness.stateTable_eq, witness.stateWidth_eq,
          witness.stateTokenCount_eq, witness.currentStart_eq,
          witness.currentFinish_eq] using hcurrentLayout
      nextLayout := by
        simpa only [witness.stateTable_eq, witness.stateWidth_eq,
          witness.stateTokenCount_eq, witness.nextStart_eq,
          witness.nextFinish_eq] using hnextLayout
      formula := witness.formula }
  exact ⟨row, rfl, rfl, fun coordinate => hwitness coordinate⟩

theorem
    exists_compactNumericVerifierFinishCheckedStepRow_with_fixed_sizeBound
    (proofTokens certificateTokens : List Nat)
    (values : List CompactNumericChildResult) :
    let payload : CompactNumericRunningPayload :=
      ((proofTokens, certificateTokens), ([], values))
    let currentState : CompactNumericVerifierState := (payload, none)
    let nextState := compactNumericFinishState payload
    let coordinateBound :=
      compactNumericVerifierSimpleStepCoordinateSizeBound
        (compactNumericVerifierStatePairTokenWeightBound
          (compactAdditiveValueWeight currentState)
          (compactAdditiveValueWeight nextState))
    ∃ row : CompactNumericVerifierCheckedStepRow,
      row.currentState = currentState ∧
        row.nextState = nextState ∧
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <= coordinateBound := by
  let payload : CompactNumericRunningPayload :=
    ((proofTokens, certificateTokens), ([], values))
  let currentState : CompactNumericVerifierState := (payload, none)
  let nextState := compactNumericFinishState payload
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let stateTable := compactFixedWidthTableCode width tokens
  let coordinateBound :=
    compactNumericVerifierSimpleStepCoordinateSizeBound
      (compactNumericVerifierStatePairTokenWeightBound
        (compactAdditiveValueWeight currentState)
        (compactAdditiveValueWeight nextState))
  rcases
      exists_compactNumericVerifierFinishStepFormulaWitness_with_fixed_sizeBound
        proofTokens certificateTokens values with
    ⟨witness, hwitness⟩
  have hpairRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState []
  have hpair :
      CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length 0 currentTokens.length currentState ∧
        CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length currentTokens.length
            (currentTokens.length + nextTokens.length) nextState := by
    simpa only [stateTable, width, tokens, currentTokens, nextTokens,
      List.append_nil] using hpairRaw
  rcases hpair with ⟨hcurrentLayout, hnextLayout⟩
  let row : CompactNumericVerifierCheckedStepRow :=
    { environment := witness.environment
      currentState := currentState
      nextState := nextState
      currentLayout := by
        simpa only [witness.stateTable_eq, witness.stateWidth_eq,
          witness.stateTokenCount_eq, witness.currentStart_eq,
          witness.currentFinish_eq] using hcurrentLayout
      nextLayout := by
        simpa only [witness.stateTable_eq, witness.stateWidth_eq,
          witness.stateTokenCount_eq, witness.nextStart_eq,
          witness.nextFinish_eq] using hnextLayout
      formula := witness.formula }
  exact ⟨row, rfl, rfl, fun coordinate => hwitness coordinate⟩

theorem
    exists_compactNumericVerifierPublicCombineCheckedStepRow_with_fixed_sizeBound
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source : List CompactNumericChildResult)
    (htaskNe : task.1 ≠ 10) :
    ∃ target nextStatus,
      compactNumericCombineState task
          ((proofTokens, certificateTokens), (tasks, source)) =
        (((proofTokens, certificateTokens), (tasks, target)), nextStatus) ∧
      let currentState : CompactNumericVerifierState :=
        (((proofTokens, certificateTokens), (task :: tasks, source)), none)
      let nextState : CompactNumericVerifierState :=
        (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
      let coordinateBound :=
        compactNumericVerifierPublicCombineStepCoordinateSizeBound
          (compactNumericVerifierPublicCombineTokenWeightBound
            (compactAdditiveValueWeight currentState)
            (compactAdditiveValueWeight nextState))
      ∃ row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState ∧
          row.nextState = nextState ∧
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound := by
  rcases
      exists_compactNumericVerifierPublicCombineStepFormulaWitness_with_fixed_sizeBound
        proofTokens certificateTokens task tasks source htaskNe with
    ⟨target, nextStatus, htransition, witness, hwitness⟩
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
  let stateTable := compactFixedWidthTableCode width tokens
  let coordinateBound :=
    compactNumericVerifierPublicCombineStepCoordinateSizeBound
      (compactNumericVerifierPublicCombineTokenWeightBound
        (compactAdditiveValueWeight currentState)
        (compactAdditiveValueWeight nextState))
  have hpairRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState backTokens
  have hpair :
      CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length 0 currentTokens.length currentState ∧
        CompactNumericVerifierStateDirectLayout
          stateTable width tokens.length currentTokens.length
            (currentTokens.length + nextTokens.length) nextState := by
    simpa only [stateTable, width, tokens, currentTokens, nextTokens,
      backTokens] using hpairRaw
  rcases hpair with ⟨hcurrentLayout, hnextLayout⟩
  let row : CompactNumericVerifierCheckedStepRow :=
    { environment := witness.environment
      currentState := currentState
      nextState := nextState
      currentLayout := by
        simpa only [witness.stateTable_eq, witness.stateWidth_eq,
          witness.stateTokenCount_eq, witness.currentStart_eq,
          witness.currentFinish_eq] using hcurrentLayout
      nextLayout := by
        simpa only [witness.stateTable_eq, witness.stateWidth_eq,
          witness.stateTokenCount_eq, witness.nextStart_eq,
          witness.nextFinish_eq] using hnextLayout
      formula := witness.formula }
  exact ⟨row, rfl, rfl, fun coordinate => hwitness coordinate⟩

#print axioms
  exists_compactNumericVerifierHaltedCheckedStepRow_with_fixed_sizeBound
#print axioms
  exists_compactNumericVerifierFinishCheckedStepRow_with_fixed_sizeBound
#print axioms
  exists_compactNumericVerifierPublicCombineCheckedStepRow_with_fixed_sizeBound

end FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsPublicBounds
