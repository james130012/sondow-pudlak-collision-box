import integration.FoundationCompactNumericListedDirectVerifierCombinePublicBounds

/-!
# Public coordinate bounds for no-auxiliary verifier steps

Halted and finish steps serialize only their current and next verifier states.
This file removes the exact token width and token count from their 429-column
coordinate bounds.  The resulting budget depends only on the two endpoint
state weights.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierSimpleStepPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
open FoundationCompactNumericListedDirectVerifierCombinePublicBounds

def compactNumericVerifierStatePairTokenWeightBound
    (currentWeight nextWeight : Nat) : Nat :=
  currentWeight + nextWeight

theorem compactNumericVerifierStatePairTokenWeightBound_mono
    {currentLeft currentRight nextLeft nextRight : Nat}
    (hcurrent : currentLeft ≤ currentRight)
    (hnext : nextLeft ≤ nextRight) :
    compactNumericVerifierStatePairTokenWeightBound
        currentLeft nextLeft ≤
      compactNumericVerifierStatePairTokenWeightBound
        currentRight nextRight := by
  unfold compactNumericVerifierStatePairTokenWeightBound
  omega

theorem compactNumericVerifierStatePairTokens_weight_le
    (currentState nextState : CompactNumericVerifierState) :
    compactAdditiveTokenWeight
        (compactAdditiveEncode currentState ++
          compactAdditiveEncode nextState) ≤
      compactNumericVerifierStatePairTokenWeightBound
        (compactAdditiveValueWeight currentState)
        (compactAdditiveValueWeight nextState) := by
  rw [compactAdditiveTokenWeight_append]
  rfl

theorem compactNumericVerifierStatePairTokens_length_le
    (currentState nextState : CompactNumericVerifierState) :
    (compactAdditiveEncode currentState ++
        compactAdditiveEncode nextState).length ≤
      compactNumericVerifierStatePairTokenWeightBound
        (compactAdditiveValueWeight currentState)
        (compactAdditiveValueWeight nextState) := by
  exact
    (compactAdditiveTokenList_length_le_weight _).trans
      (compactNumericVerifierStatePairTokens_weight_le
        currentState nextState)

theorem compactNumericVerifierStatePairWidth_le
    (currentState nextState : CompactNumericVerifierState) :
    (compactBinaryNatPayloadBits
      (compactAdditiveEncode currentState ++
        compactAdditiveEncode nextState)).length ≤
      2 * compactNumericVerifierStatePairTokenWeightBound
        (compactAdditiveValueWeight currentState)
        (compactAdditiveValueWeight nextState) := by
  change compactAdditiveTokenBitLength _ ≤ _
  rw [compactAdditiveTokenBitLength_eq_two_mul_weight]
  exact Nat.mul_le_mul_left 2
    (compactNumericVerifierStatePairTokens_weight_le
      currentState nextState)

theorem compactNumericVerifierStepUnusedCoordinateSizeBound_mono
    {widthLeft widthRight tokenLeft tokenRight : Nat}
    (hwidth : widthLeft ≤ widthRight)
    (htoken : tokenLeft ≤ tokenRight) :
    compactNumericVerifierStepUnusedCoordinateSizeBound
        widthLeft tokenLeft ≤
      compactNumericVerifierStepUnusedCoordinateSizeBound
        widthRight tokenRight := by
  have hstate :=
    compactNumericVerifierStateCoreCoordinateSizeBound_mono hwidth htoken
  unfold compactNumericVerifierStepUnusedCoordinateSizeBound
    compactNumericVerifierStepArgumentsCoordinateSizeBound
  omega

def compactNumericVerifierSimpleStepCoordinateSizeBound
    (pairWeightBound : Nat) : Nat :=
  compactNumericVerifierStepUnusedCoordinateSizeBound
    (2 * pairWeightBound) pairWeightBound

theorem compactNumericVerifierStepUnusedCoordinateSizeBound_le_public
    {width tokenCount pairWeightBound : Nat}
    (hwidth : width ≤ 2 * pairWeightBound)
    (htoken : tokenCount ≤ pairWeightBound) :
    compactNumericVerifierStepUnusedCoordinateSizeBound width tokenCount ≤
      compactNumericVerifierSimpleStepCoordinateSizeBound
        pairWeightBound := by
  exact compactNumericVerifierStepUnusedCoordinateSizeBound_mono
    hwidth htoken

theorem
    exists_compactNumericVerifierHaltedStepFormulaWitness_with_fixed_sizeBound
    (proofTokens certificateTokens : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (result : Bool) :
    let state : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (tasks, values)), some result)
    let stateTokens := compactAdditiveEncode state
    let tokens := stateTokens ++ stateTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    ∃ witness : CompactNumericVerifierStepFormulaWitness
        (compactFixedWidthTableCode width tokens) width tokens.length
        0 stateTokens.length stateTokens.length
        (stateTokens.length + stateTokens.length),
      ∀ coordinate : Fin 429,
        Nat.size (witness.environment coordinate) ≤
          compactNumericVerifierSimpleStepCoordinateSizeBound
            (compactNumericVerifierStatePairTokenWeightBound
              (compactAdditiveValueWeight state)
              (compactAdditiveValueWeight state)) := by
  let state : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, values)), some result)
  let stateTokens := compactAdditiveEncode state
  let tokens := stateTokens ++ stateTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let pairWeightBound :=
    compactNumericVerifierStatePairTokenWeightBound
      (compactAdditiveValueWeight state)
      (compactAdditiveValueWeight state)
  have htoken : tokens.length ≤ pairWeightBound := by
    simpa only [tokens, stateTokens, state, pairWeightBound] using
      compactNumericVerifierStatePairTokens_length_le state state
  have hwidth : width ≤ 2 * pairWeightBound := by
    simpa only [width, tokens, stateTokens, state, pairWeightBound] using
      compactNumericVerifierStatePairWidth_le state state
  have hbound :=
    compactNumericVerifierStepUnusedCoordinateSizeBound_le_public
      hwidth htoken
  have hstep :=
    exists_compactNumericVerifierHaltedStepFormulaWitness_with_sizeBound
      proofTokens certificateTokens tasks values result
  dsimp only at hstep
  rcases hstep with ⟨witness, hwitness⟩
  refine ⟨witness, ?_⟩
  intro coordinate
  simpa only [state, stateTokens, tokens, width, pairWeightBound] using
    (hwitness coordinate).trans hbound

theorem
    exists_compactNumericVerifierFinishStepFormulaWitness_with_fixed_sizeBound
    (proofTokens certificateTokens : List Nat)
    (values : List CompactNumericChildResult) :
    let payload : CompactNumericRunningPayload :=
      ((proofTokens, certificateTokens), ([], values))
    let currentState : CompactNumericVerifierState := (payload, none)
    let nextState := compactNumericFinishState payload
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let tokens := currentTokens ++ nextTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    ∃ witness : CompactNumericVerifierStepFormulaWitness
        (compactFixedWidthTableCode width tokens) width tokens.length
        0 currentTokens.length currentTokens.length
        (currentTokens.length + nextTokens.length),
      ∀ coordinate : Fin 429,
        Nat.size (witness.environment coordinate) ≤
          compactNumericVerifierSimpleStepCoordinateSizeBound
            (compactNumericVerifierStatePairTokenWeightBound
              (compactAdditiveValueWeight currentState)
              (compactAdditiveValueWeight nextState)) := by
  let payload : CompactNumericRunningPayload :=
    ((proofTokens, certificateTokens), ([], values))
  let currentState : CompactNumericVerifierState := (payload, none)
  let nextState := compactNumericFinishState payload
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let pairWeightBound :=
    compactNumericVerifierStatePairTokenWeightBound
      (compactAdditiveValueWeight currentState)
      (compactAdditiveValueWeight nextState)
  have htoken : tokens.length ≤ pairWeightBound := by
    simpa only [tokens, currentTokens, nextTokens, currentState, nextState,
      pairWeightBound] using
      compactNumericVerifierStatePairTokens_length_le
        currentState nextState
  have hwidth : width ≤ 2 * pairWeightBound := by
    simpa only [width, tokens, currentTokens, nextTokens, currentState,
      nextState, pairWeightBound] using
      compactNumericVerifierStatePairWidth_le currentState nextState
  have hbound :=
    compactNumericVerifierStepUnusedCoordinateSizeBound_le_public
      hwidth htoken
  have hstep :=
    exists_compactNumericVerifierFinishStepFormulaWitness_with_sizeBound
      proofTokens certificateTokens values
  dsimp only at hstep
  rcases hstep with ⟨witness, hwitness⟩
  refine ⟨witness, ?_⟩
  intro coordinate
  simpa only [payload, currentState, nextState, currentTokens, nextTokens,
    tokens, width, pairWeightBound] using
    (hwitness coordinate).trans hbound

#print axioms
  exists_compactNumericVerifierHaltedStepFormulaWitness_with_fixed_sizeBound
#print axioms
  exists_compactNumericVerifierFinishStepFormulaWitness_with_fixed_sizeBound

end FoundationCompactNumericListedDirectVerifierSimpleStepPublicBounds
