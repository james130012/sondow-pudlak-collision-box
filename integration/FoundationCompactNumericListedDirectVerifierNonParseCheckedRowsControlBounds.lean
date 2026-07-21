import integration.FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsPublicBounds

/-!
# Numeric control bounds for canonical non-parse checked rows

The existing global row bounds control the binary size of all 429 coordinates.
This module additionally retains numeric bounds for coordinates 1 and 2,
because they are used as universal-loop controls by the direct predicate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsControlBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectVerifierSimpleStepPublicBounds
open FoundationCompactNumericListedDirectVerifierCheckedStepRow

structure CompactNumericVerifierCheckedRowControlBounds
    (row : CompactNumericVerifierCheckedStepRow) (pairWeightBound : Nat) : Prop where
  stateWidth_le : row.environment 1 <= 2 * pairWeightBound
  stateTokenCount_le : row.environment 2 <= pairWeightBound

theorem
    exists_compactNumericVerifierHaltedCheckedStepRow_with_controlBounds
    (proofTokens certificateTokens : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (result : Bool) :
    let state : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (tasks, values)), some result)
    let pairWeightBound := compactNumericVerifierStatePairTokenWeightBound
      (compactAdditiveValueWeight state) (compactAdditiveValueWeight state)
    let coordinateBound :=
      compactNumericVerifierSimpleStepCoordinateSizeBound pairWeightBound
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = state /\
        row.nextState = state /\
        CompactNumericVerifierCheckedRowControlBounds row pairWeightBound /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <= coordinateBound := by
  let state : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, values)), some result)
  let stateTokens := compactAdditiveEncode state
  let tokens := stateTokens ++ stateTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let pairWeightBound := compactNumericVerifierStatePairTokenWeightBound
    (compactAdditiveValueWeight state) (compactAdditiveValueWeight state)
  let coordinateBound :=
    compactNumericVerifierSimpleStepCoordinateSizeBound pairWeightBound
  have htoken : tokens.length <= pairWeightBound := by
    simpa only [tokens, stateTokens, state, pairWeightBound] using
      compactNumericVerifierStatePairTokens_length_le state state
  have hwidth : width <= 2 * pairWeightBound := by
    simpa only [width, tokens, stateTokens, state, pairWeightBound] using
      compactNumericVerifierStatePairWidth_le state state
  rcases exists_compactNumericVerifierHaltedStepFormulaWitness_with_fixed_sizeBound
      proofTokens certificateTokens tasks values result with
    ⟨witness, hwitness⟩
  have hpairRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    state state []
  have hpair :
      CompactNumericVerifierStateDirectLayout
          (compactFixedWidthTableCode width tokens) width tokens.length
          0 stateTokens.length state /\
        CompactNumericVerifierStateDirectLayout
          (compactFixedWidthTableCode width tokens) width tokens.length
          stateTokens.length (stateTokens.length + stateTokens.length) state := by
    simpa only [width, tokens, stateTokens, List.append_nil] using hpairRaw
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
  refine ⟨row, rfl, rfl, ?_, fun coordinate => hwitness coordinate⟩
  refine
    { stateWidth_le := ?_
      stateTokenCount_le := ?_ }
  · simpa only [row, witness.stateWidth_eq] using hwidth
  · simpa only [row, witness.stateTokenCount_eq] using htoken

theorem
    exists_compactNumericVerifierFinishCheckedStepRow_with_controlBounds
    (proofTokens certificateTokens : List Nat)
    (values : List CompactNumericChildResult) :
    let payload : CompactNumericRunningPayload :=
      ((proofTokens, certificateTokens), ([], values))
    let currentState : CompactNumericVerifierState := (payload, none)
    let nextState := compactNumericFinishState payload
    let pairWeightBound := compactNumericVerifierStatePairTokenWeightBound
      (compactAdditiveValueWeight currentState)
      (compactAdditiveValueWeight nextState)
    let coordinateBound :=
      compactNumericVerifierSimpleStepCoordinateSizeBound pairWeightBound
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = currentState /\
        row.nextState = nextState /\
        CompactNumericVerifierCheckedRowControlBounds row pairWeightBound /\
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
  let pairWeightBound := compactNumericVerifierStatePairTokenWeightBound
    (compactAdditiveValueWeight currentState)
    (compactAdditiveValueWeight nextState)
  let coordinateBound :=
    compactNumericVerifierSimpleStepCoordinateSizeBound pairWeightBound
  have htoken : tokens.length <= pairWeightBound := by
    simpa only [tokens, currentTokens, nextTokens, currentState, nextState,
      pairWeightBound] using
      compactNumericVerifierStatePairTokens_length_le currentState nextState
  have hwidth : width <= 2 * pairWeightBound := by
    simpa only [width, tokens, currentTokens, nextTokens, currentState,
      nextState, pairWeightBound] using
      compactNumericVerifierStatePairWidth_le currentState nextState
  rcases exists_compactNumericVerifierFinishStepFormulaWitness_with_fixed_sizeBound
      proofTokens certificateTokens values with ⟨witness, hwitness⟩
  have hpairRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState []
  have hpair :
      CompactNumericVerifierStateDirectLayout
          (compactFixedWidthTableCode width tokens) width tokens.length
          0 currentTokens.length currentState /\
        CompactNumericVerifierStateDirectLayout
          (compactFixedWidthTableCode width tokens) width tokens.length
          currentTokens.length (currentTokens.length + nextTokens.length)
          nextState := by
    simpa only [width, tokens, currentTokens, nextTokens, List.append_nil] using
      hpairRaw
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
  refine ⟨row, rfl, rfl, ?_, fun coordinate => hwitness coordinate⟩
  refine
    { stateWidth_le := ?_
      stateTokenCount_le := ?_ }
  · simpa only [row, witness.stateWidth_eq] using hwidth
  · simpa only [row, witness.stateTokenCount_eq] using htoken

#print axioms
  exists_compactNumericVerifierHaltedCheckedStepRow_with_controlBounds
#print axioms
  exists_compactNumericVerifierFinishCheckedStepRow_with_controlBounds

end FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsControlBounds
