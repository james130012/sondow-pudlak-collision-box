import integration.FoundationCompactNumericListedDirectVerifierAcceptedTerminalRowsControlBounds
import integration.FoundationCompactNumericListedDirectVerifierCombinePublicBounds

/-!
# Common numeric controls for accepted verifier state tables

The common budget covers both an ordinary canonical pair of verifier states and
the larger canonical combine table carrying its explicit auxiliary suffix.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedStateTableControlBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierSimpleStepPublicBounds
open FoundationCompactNumericListedDirectVerifierCombinePublicBounds

def compactNumericVerifierAcceptedStateTokenCountBound
    (rowWeight : Nat) : Nat :=
  compactNumericVerifierPublicCombineTokenWeightBound rowWeight rowWeight

def compactNumericVerifierAcceptedStateWidthBound
    (rowWeight : Nat) : Nat :=
  2 * compactNumericVerifierAcceptedStateTokenCountBound rowWeight

structure CompactNumericVerifierAcceptedStateTableControlBounds
    (row : CompactNumericVerifierCheckedStepRow) (rowWeight : Nat) : Prop where
  stateWidth_le : row.environment 1 <=
    compactNumericVerifierAcceptedStateWidthBound rowWeight
  stateTokenCount_le : row.environment 2 <=
    compactNumericVerifierAcceptedStateTokenCountBound rowWeight

theorem compactNumericVerifierStatePairWeight_le_acceptedStateTokenCountBound
    {currentWeight nextWeight rowWeight : Nat}
    (hcurrent : currentWeight <= rowWeight)
    (hnext : nextWeight <= rowWeight) :
    compactNumericVerifierStatePairTokenWeightBound currentWeight nextWeight <=
      compactNumericVerifierAcceptedStateTokenCountBound rowWeight := by
  unfold compactNumericVerifierStatePairTokenWeightBound
    compactNumericVerifierAcceptedStateTokenCountBound
    compactNumericVerifierPublicCombineTokenWeightBound
  omega

theorem compactNumericVerifierPublicCombineTokenWeightBound_le_accepted
    {currentWeight nextWeight rowWeight : Nat}
    (hcurrent : currentWeight <= rowWeight)
    (hnext : nextWeight <= rowWeight) :
    compactNumericVerifierPublicCombineTokenWeightBound
        currentWeight nextWeight <=
      compactNumericVerifierAcceptedStateTokenCountBound rowWeight := by
  exact compactNumericVerifierPublicCombineTokenWeightBound_mono
    hcurrent hnext

theorem
    CompactNumericVerifierAcceptedStateTableControlBounds.of_canonicalStatePair
    (row : CompactNumericVerifierCheckedStepRow)
    (currentState nextState : CompactNumericVerifierState)
    (rowWeight : Nat)
    (hcurrent : compactAdditiveValueWeight currentState <= rowWeight)
    (hnext : compactAdditiveValueWeight nextState <= rowWeight)
    (hwidth : row.environment 1 =
      (compactBinaryNatPayloadBits
        (compactAdditiveEncode currentState ++
          compactAdditiveEncode nextState)).length)
    (htokenCount : row.environment 2 =
      (compactAdditiveEncode currentState ++
        compactAdditiveEncode nextState).length) :
    CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight := by
  have hpair :=
    compactNumericVerifierStatePairWeight_le_acceptedStateTokenCountBound
      hcurrent hnext
  constructor
  · rw [hwidth]
    exact (compactNumericVerifierStatePairWidth_le
      currentState nextState).trans (by
        unfold compactNumericVerifierAcceptedStateWidthBound
        exact Nat.mul_le_mul_left 2 hpair)
  · rw [htokenCount]
    exact (compactNumericVerifierStatePairTokens_length_le
      currentState nextState).trans hpair

theorem
    CompactNumericVerifierAcceptedStateTableControlBounds.of_canonicalCombine
    (row : CompactNumericVerifierCheckedStepRow)
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool)
    (rowWeight : Nat)
    (hcurrent : compactAdditiveValueWeight
      ((((proofTokens, certificateTokens), (task :: tasks, source)), none) :
        CompactNumericVerifierState) <= rowWeight)
    (hnext : compactAdditiveValueWeight
      ((((proofTokens, certificateTokens), (tasks, target)), nextStatus) :
        CompactNumericVerifierState) <= rowWeight)
    (hwidth : row.environment 1 =
      (compactBinaryNatPayloadBits
        (compactAdditiveEncode
            ((((proofTokens, certificateTokens),
              (task :: tasks, source)), none) :
              CompactNumericVerifierState) ++
          compactAdditiveEncode
            ((((proofTokens, certificateTokens),
              (tasks, target)), nextStatus) :
              CompactNumericVerifierState) ++
          compactNumericVerifierPublicCombineAuxiliaryTokens
            task source)).length)
    (htokenCount : row.environment 2 =
      (compactAdditiveEncode
          ((((proofTokens, certificateTokens),
            (task :: tasks, source)), none) :
            CompactNumericVerifierState) ++
        compactAdditiveEncode
          ((((proofTokens, certificateTokens),
            (tasks, target)), nextStatus) :
            CompactNumericVerifierState) ++
        compactNumericVerifierPublicCombineAuxiliaryTokens task source).length) :
    CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight := by
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
  have hbudget :=
    compactNumericVerifierPublicCombineTokenWeightBound_le_accepted
      hcurrent hnext
  constructor
  · rw [hwidth]
    exact (compactNumericVerifierPublicCombineWidth_le
      proofTokens certificateTokens task tasks source target nextStatus).trans
        (by
          unfold compactNumericVerifierAcceptedStateWidthBound
          exact Nat.mul_le_mul_left 2 hbudget)
  · rw [htokenCount]
    exact (compactNumericVerifierPublicCombineTokens_length_le
      proofTokens certificateTokens task tasks source target nextStatus).trans
        hbudget

/-- Turn a formula witness over the exact canonical pair table into a checked
row while retaining numeric controls for the two table-loop coordinates. -/
theorem exists_checkedStepRow_of_canonicalStatePairFormulaWitness_with_controls
    (currentState nextState : CompactNumericVerifierState)
    (rowWeight coordinateBound : Nat)
    (hcurrent : compactAdditiveValueWeight currentState <= rowWeight)
    (hnext : compactAdditiveValueWeight nextState <= rowWeight) :
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let tokens := currentTokens ++ nextTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let stateTable := compactFixedWidthTableCode width tokens
    forall witness : CompactNumericVerifierStepFormulaWitness
        stateTable width tokens.length 0 currentTokens.length
          currentTokens.length (currentTokens.length + nextTokens.length),
      (forall coordinate : Fin 429,
        Nat.size (witness.environment coordinate) <= coordinateBound) ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound := by
  dsimp only
  intro witness hcoordinates
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let stateTable := compactFixedWidthTableCode width tokens
  have hpairRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState []
  have hpair :
      CompactNumericVerifierStateDirectLayout stateTable width tokens.length
          0 currentTokens.length currentState /\
        CompactNumericVerifierStateDirectLayout stateTable width tokens.length
          currentTokens.length (currentTokens.length + nextTokens.length)
            nextState := by
    simpa only [stateTable, width, tokens, currentTokens, nextTokens,
      List.append_nil] using hpairRaw
  rcases hpair with ⟨hcurrentLayout, hnextLayout⟩
  let row :=
    CompactNumericVerifierStepFormulaWitness.toCheckedStepRow witness
      currentState nextState hcurrentLayout hnextLayout
  refine ⟨row, rfl, rfl, ?_, ?_⟩
  · refine
      CompactNumericVerifierAcceptedStateTableControlBounds.of_canonicalStatePair
        row currentState nextState rowWeight hcurrent hnext ?_ ?_
    · simpa only [row,
        CompactNumericVerifierStepFormulaWitness.toCheckedStepRow_environment,
        width, tokens, currentTokens, nextTokens] using witness.stateWidth_eq
    · simpa only [row,
        CompactNumericVerifierStepFormulaWitness.toCheckedStepRow_environment,
        tokens, currentTokens, nextTokens] using witness.stateTokenCount_eq
  · intro coordinate
    simpa only [row,
      CompactNumericVerifierStepFormulaWitness.toCheckedStepRow_environment]
      using hcoordinates coordinate

/-- The canonical-pair row constructor preserves any proof-level property of
the exact formula environment.  This is used by quantitative branch compilers
to retain numeric loop controls in addition to coordinate bit-size bounds. -/
theorem
    exists_checkedStepRow_of_canonicalStatePairFormulaWitness_with_controls_and_property
    (currentState nextState : CompactNumericVerifierState)
    (rowWeight coordinateBound : Nat)
    (property : (Fin 429 -> Nat) -> Prop)
    (hcurrent : compactAdditiveValueWeight currentState <= rowWeight)
    (hnext : compactAdditiveValueWeight nextState <= rowWeight) :
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let tokens := currentTokens ++ nextTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let stateTable := compactFixedWidthTableCode width tokens
    forall witness : CompactNumericVerifierStepFormulaWitness
        stateTable width tokens.length 0 currentTokens.length
          currentTokens.length (currentTokens.length + nextTokens.length),
      (forall coordinate : Fin 429,
        Nat.size (witness.environment coordinate) <= coordinateBound) ->
      property witness.environment ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight /\
          (forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound) /\
          property row.environment := by
  dsimp only
  intro witness hcoordinates hproperty
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let stateTable := compactFixedWidthTableCode width tokens
  have hpairRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState []
  have hpair :
      CompactNumericVerifierStateDirectLayout stateTable width tokens.length
          0 currentTokens.length currentState /\
        CompactNumericVerifierStateDirectLayout stateTable width tokens.length
          currentTokens.length (currentTokens.length + nextTokens.length)
            nextState := by
    simpa only [stateTable, width, tokens, currentTokens, nextTokens,
      List.append_nil] using hpairRaw
  rcases hpair with ⟨hcurrentLayout, hnextLayout⟩
  let row :=
    CompactNumericVerifierStepFormulaWitness.toCheckedStepRow witness
      currentState nextState hcurrentLayout hnextLayout
  refine ⟨row, rfl, rfl, ?_, ?_, ?_⟩
  · refine
      CompactNumericVerifierAcceptedStateTableControlBounds.of_canonicalStatePair
        row currentState nextState rowWeight hcurrent hnext ?_ ?_
    · simpa only [row,
        CompactNumericVerifierStepFormulaWitness.toCheckedStepRow_environment,
        width, tokens, currentTokens, nextTokens] using witness.stateWidth_eq
    · simpa only [row,
        CompactNumericVerifierStepFormulaWitness.toCheckedStepRow_environment,
        tokens, currentTokens, nextTokens] using witness.stateTokenCount_eq
  · intro coordinate
    simpa only [row,
      CompactNumericVerifierStepFormulaWitness.toCheckedStepRow_environment]
      using hcoordinates coordinate
  · simpa only [row,
      CompactNumericVerifierStepFormulaWitness.toCheckedStepRow_environment]
      using hproperty

/-- The analogous constructor for canonical combine rows, whose state table
contains the explicit branch-checking suffix after the two state encodings. -/
theorem exists_checkedStepRow_of_canonicalCombineFormulaWitness_with_controls
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool)
    (rowWeight coordinateBound : Nat)
    (hcurrent : compactAdditiveValueWeight
      ((((proofTokens, certificateTokens), (task :: tasks, source)), none) :
        CompactNumericVerifierState) <= rowWeight)
    (hnext : compactAdditiveValueWeight
      ((((proofTokens, certificateTokens), (tasks, target)), nextStatus) :
        CompactNumericVerifierState) <= rowWeight) :
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
    forall witness : CompactNumericVerifierStepFormulaWitness
        stateTable width tokens.length 0 currentTokens.length
          currentTokens.length (currentTokens.length + nextTokens.length),
      (forall coordinate : Fin 429,
        Nat.size (witness.environment coordinate) <= coordinateBound) ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound := by
  dsimp only
  intro witness hcoordinates
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
  let row :=
    CompactNumericVerifierStepFormulaWitness.toCheckedStepRow witness
      currentState nextState hcurrentLayout hnextLayout
  refine ⟨row, rfl, rfl, ?_, ?_⟩
  · refine
      CompactNumericVerifierAcceptedStateTableControlBounds.of_canonicalCombine
        row proofTokens certificateTokens task tasks source target nextStatus
          rowWeight hcurrent hnext ?_ ?_
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

#print axioms
  compactNumericVerifierStatePairWeight_le_acceptedStateTokenCountBound
#print axioms
  CompactNumericVerifierAcceptedStateTableControlBounds.of_canonicalStatePair
#print axioms
  CompactNumericVerifierAcceptedStateTableControlBounds.of_canonicalCombine
#print axioms
  exists_checkedStepRow_of_canonicalStatePairFormulaWitness_with_controls
#print axioms
  exists_checkedStepRow_of_canonicalStatePairFormulaWitness_with_controls_and_property
#print axioms
  exists_checkedStepRow_of_canonicalCombineFormulaWitness_with_controls

end FoundationCompactNumericListedDirectVerifierAcceptedStateTableControlBounds
