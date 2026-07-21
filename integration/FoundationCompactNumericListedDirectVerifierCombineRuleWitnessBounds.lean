import integration.FoundationCompactNumericListedDirectVerifierCombineBranchRows

/-!
# Canonical combine-rule witnesses and their quantitative coordinates

The branch disjunction does not constrain coordinates unused by the selected
rule.  These named constructors make the canonical zero padding explicit, so
later size proofs do not rely on an opaque existential witness.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineRuleWitnessBounds

open FoundationCompactNumericListedDirectVerifierCombineBranchRows

def compactNumericVerifierCombineRuleWitnessEnvironment
    (witness : CompactNumericVerifierCombineRuleWitness) : Fin 34 -> Nat :=
  ![witness.rightGammaCount, witness.rightGammaBoundary,
    witness.rightBoolValue, witness.leftGammaCount,
    witness.leftGammaBoundary, witness.leftBoolValue,
    witness.formulaBoundary, witness.formulaBoundarySize,
    witness.transformedStart, witness.transformedFinish,
    witness.transformedBoundary, witness.transformedCount,
    witness.transformedBoundarySize, witness.transformStateBoundary,
    witness.transformStateCount, witness.freedStart, witness.freedFinish,
    witness.freedBoundary, witness.freedCount, witness.freedBoundarySize,
    witness.freeStateBoundary, witness.freeStateCount,
    witness.shiftCandidateBoundary, witness.shiftSuccessTable,
    witness.shiftedBoundary, witness.shiftedCount, witness.emptyStart,
    witness.emptyFinish, witness.emptyBoundary, witness.emptyBoundarySize,
    witness.shiftWitnessBound, witness.freeTableWidth,
    witness.freeValueBound, witness.resultBoolValue]

def compactNumericVerifierCombineRuleWitnessHeadEnvironment
    (witness : CompactNumericVerifierCombineRuleWitness) : Fin 22 -> Nat :=
  fun coordinate =>
    compactNumericVerifierCombineRuleWitnessEnvironment witness
      ⟨coordinate.val, by omega⟩

def compactNumericVerifierCombineRuleWitnessTailEnvironment
    (witness : CompactNumericVerifierCombineRuleWitness) : Fin 12 -> Nat :=
  fun coordinate =>
    compactNumericVerifierCombineRuleWitnessEnvironment witness
      ⟨coordinate.val + 22, by omega⟩

def compactNumericVerifierSimpleCombineRuleWitness
    (rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      resultBoolValue : Nat) : CompactNumericVerifierCombineRuleWitness :=
  { rightGammaCount := rightGammaCount
    rightGammaBoundary := rightGammaBoundary
    rightBoolValue := rightBoolValue
    leftGammaCount := leftGammaCount
    leftGammaBoundary := leftGammaBoundary
    leftBoolValue := leftBoolValue
    formulaBoundary := 0
    formulaBoundarySize := 0
    transformedStart := 0
    transformedFinish := 0
    transformedBoundary := 0
    transformedCount := 0
    transformedBoundarySize := 0
    transformStateBoundary := 0
    transformStateCount := 0
    freedStart := 0
    freedFinish := 0
    freedBoundary := 0
    freedCount := 0
    freedBoundarySize := 0
    freeStateBoundary := 0
    freeStateCount := 0
    shiftCandidateBoundary := 0
    shiftSuccessTable := 0
    shiftedBoundary := 0
    shiftedCount := 0
    emptyStart := 0
    emptyFinish := 0
    emptyBoundary := 0
    emptyBoundarySize := 0
    shiftWitnessBound := 0
    freeTableWidth := 0
    freeValueBound := 0
    resultBoolValue := resultBoolValue }

def compactNumericVerifierAllShiftCombineRuleWitness
    (premiseGammaCount premiseGammaBoundary premiseBoolValue
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      resultBoolValue : Nat) : CompactNumericVerifierCombineRuleWitness :=
  { rightGammaCount := premiseGammaCount
    rightGammaBoundary := premiseGammaBoundary
    rightBoolValue := premiseBoolValue
    leftGammaCount := 0
    leftGammaBoundary := 0
    leftBoolValue := 0
    formulaBoundary := formulaBoundary
    formulaBoundarySize := formulaBoundarySize
    transformedStart := 0
    transformedFinish := 0
    transformedBoundary := 0
    transformedCount := 0
    transformedBoundarySize := 0
    transformStateBoundary := 0
    transformStateCount := 0
    freedStart := freedStart
    freedFinish := freedFinish
    freedBoundary := freedBoundary
    freedCount := freedCount
    freedBoundarySize := freedBoundarySize
    freeStateBoundary := freeStateBoundary
    freeStateCount := freeStateCount
    shiftCandidateBoundary := shiftCandidateBoundary
    shiftSuccessTable := shiftSuccessTable
    shiftedBoundary := shiftedBoundary
    shiftedCount := shiftedCount
    emptyStart := emptyStart
    emptyFinish := emptyFinish
    emptyBoundary := emptyBoundary
    emptyBoundarySize := emptyBoundarySize
    shiftWitnessBound := shiftWitnessBound
    freeTableWidth := freeTableWidth
    freeValueBound := freeValueBound
    resultBoolValue := resultBoolValue }

def compactNumericVerifierExsCutCombineRuleWitness
    (rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      resultBoolValue : Nat) : CompactNumericVerifierCombineRuleWitness :=
  { rightGammaCount := rightGammaCount
    rightGammaBoundary := rightGammaBoundary
    rightBoolValue := rightBoolValue
    leftGammaCount := leftGammaCount
    leftGammaBoundary := leftGammaBoundary
    leftBoolValue := leftBoolValue
    formulaBoundary := formulaBoundary
    formulaBoundarySize := formulaBoundarySize
    transformedStart := transformedStart
    transformedFinish := transformedFinish
    transformedBoundary := transformedBoundary
    transformedCount := transformedCount
    transformedBoundarySize := transformedBoundarySize
    transformStateBoundary := transformStateBoundary
    transformStateCount := transformStateCount
    freedStart := 0
    freedFinish := 0
    freedBoundary := 0
    freedCount := 0
    freedBoundarySize := 0
    freeStateBoundary := 0
    freeStateCount := 0
    shiftCandidateBoundary := 0
    shiftSuccessTable := 0
    shiftedBoundary := 0
    shiftedCount := 0
    emptyStart := emptyStart
    emptyFinish := emptyFinish
    emptyBoundary := emptyBoundary
    emptyBoundarySize := emptyBoundarySize
    shiftWitnessBound := 0
    freeTableWidth := transformTableWidth
    freeValueBound := transformValueBound
    resultBoolValue := resultBoolValue }

def compactNumericVerifierFailureCombineRuleWitness :
    CompactNumericVerifierCombineRuleWitness :=
  compactNumericVerifierSimpleCombineRuleWitness 0 0 0 0 0 0 0

def compactNumericVerifierSimpleCombineRuleWitnessBitBudget
    (rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      resultBoolValue : Nat) : Nat :=
  [Nat.size rightGammaCount, Nat.size rightGammaBoundary,
    Nat.size rightBoolValue, Nat.size leftGammaCount,
    Nat.size leftGammaBoundary, Nat.size leftBoolValue,
    Nat.size resultBoolValue].sum

def compactNumericVerifierSimpleCombineRuleCoordinateSizeBound
    (tokenCount : Nat) : Nat :=
  (tokenCount + 1) * tokenCount + tokenCount + 2

def compactNumericVerifierAllShiftCombineRuleWitnessBitBudget
    (premiseGammaCount premiseGammaBoundary premiseBoolValue
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      resultBoolValue : Nat) : Nat :=
  [Nat.size premiseGammaCount, Nat.size premiseGammaBoundary,
    Nat.size premiseBoolValue, Nat.size formulaBoundary,
    Nat.size formulaBoundarySize, Nat.size freedStart,
    Nat.size freedFinish, Nat.size freedBoundary, Nat.size freedCount,
    Nat.size freedBoundarySize, Nat.size freeStateBoundary,
    Nat.size freeStateCount, Nat.size shiftCandidateBoundary,
    Nat.size shiftSuccessTable, Nat.size shiftedBoundary,
    Nat.size shiftedCount, Nat.size emptyStart, Nat.size emptyFinish,
    Nat.size emptyBoundary, Nat.size emptyBoundarySize,
    Nat.size shiftWitnessBound, Nat.size freeTableWidth,
    Nat.size freeValueBound, Nat.size resultBoolValue].sum

def compactNumericVerifierExsCutCombineRuleWitnessBitBudget
    (rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      resultBoolValue : Nat) : Nat :=
  [Nat.size rightGammaCount, Nat.size rightGammaBoundary,
    Nat.size rightBoolValue, Nat.size leftGammaCount,
    Nat.size leftGammaBoundary, Nat.size leftBoolValue,
    Nat.size formulaBoundary, Nat.size formulaBoundarySize,
    Nat.size transformedStart, Nat.size transformedFinish,
    Nat.size transformedBoundary, Nat.size transformedCount,
    Nat.size transformedBoundarySize, Nat.size transformStateBoundary,
    Nat.size transformStateCount, Nat.size emptyStart, Nat.size emptyFinish,
    Nat.size emptyBoundary, Nat.size emptyBoundarySize,
    Nat.size transformTableWidth, Nat.size transformValueBound,
    Nat.size resultBoolValue].sum

structure CompactNumericVerifierAllShiftCombineRuleFieldSizeBounds
    (premiseGammaCount premiseGammaBoundary premiseBoolValue
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      resultBoolValue bound : Nat) : Prop where
  premiseGammaCount : Nat.size premiseGammaCount ≤ bound
  premiseGammaBoundary : Nat.size premiseGammaBoundary ≤ bound
  premiseBoolValue : Nat.size premiseBoolValue ≤ bound
  formulaBoundary : Nat.size formulaBoundary ≤ bound
  formulaBoundarySize : Nat.size formulaBoundarySize ≤ bound
  freedStart : Nat.size freedStart ≤ bound
  freedFinish : Nat.size freedFinish ≤ bound
  freedBoundary : Nat.size freedBoundary ≤ bound
  freedCount : Nat.size freedCount ≤ bound
  freedBoundarySize : Nat.size freedBoundarySize ≤ bound
  freeStateBoundary : Nat.size freeStateBoundary ≤ bound
  freeStateCount : Nat.size freeStateCount ≤ bound
  shiftCandidateBoundary : Nat.size shiftCandidateBoundary ≤ bound
  shiftSuccessTable : Nat.size shiftSuccessTable ≤ bound
  shiftedBoundary : Nat.size shiftedBoundary ≤ bound
  shiftedCount : Nat.size shiftedCount ≤ bound
  emptyStart : Nat.size emptyStart ≤ bound
  emptyFinish : Nat.size emptyFinish ≤ bound
  emptyBoundary : Nat.size emptyBoundary ≤ bound
  emptyBoundarySize : Nat.size emptyBoundarySize ≤ bound
  shiftWitnessBound : Nat.size shiftWitnessBound ≤ bound
  freeTableWidth : Nat.size freeTableWidth ≤ bound
  freeValueBound : Nat.size freeValueBound ≤ bound
  resultBoolValue : Nat.size resultBoolValue ≤ bound

structure CompactNumericVerifierExsCutCombineRuleFieldSizeBounds
    (rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      resultBoolValue bound : Nat) : Prop where
  rightGammaCount : Nat.size rightGammaCount ≤ bound
  rightGammaBoundary : Nat.size rightGammaBoundary ≤ bound
  rightBoolValue : Nat.size rightBoolValue ≤ bound
  leftGammaCount : Nat.size leftGammaCount ≤ bound
  leftGammaBoundary : Nat.size leftGammaBoundary ≤ bound
  leftBoolValue : Nat.size leftBoolValue ≤ bound
  formulaBoundary : Nat.size formulaBoundary ≤ bound
  formulaBoundarySize : Nat.size formulaBoundarySize ≤ bound
  transformedStart : Nat.size transformedStart ≤ bound
  transformedFinish : Nat.size transformedFinish ≤ bound
  transformedBoundary : Nat.size transformedBoundary ≤ bound
  transformedCount : Nat.size transformedCount ≤ bound
  transformedBoundarySize : Nat.size transformedBoundarySize ≤ bound
  transformStateBoundary : Nat.size transformStateBoundary ≤ bound
  transformStateCount : Nat.size transformStateCount ≤ bound
  emptyStart : Nat.size emptyStart ≤ bound
  emptyFinish : Nat.size emptyFinish ≤ bound
  emptyBoundary : Nat.size emptyBoundary ≤ bound
  emptyBoundarySize : Nat.size emptyBoundarySize ≤ bound
  transformTableWidth : Nat.size transformTableWidth ≤ bound
  transformValueBound : Nat.size transformValueBound ≤ bound
  resultBoolValue : Nat.size resultBoolValue ≤ bound

theorem CompactNumericVerifierAllShiftCombineRuleFieldSizeBounds.coordinate
    {premiseGammaCount premiseGammaBoundary premiseBoolValue
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      resultBoolValue bound : Nat}
    (hbounds : CompactNumericVerifierAllShiftCombineRuleFieldSizeBounds
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      resultBoolValue bound)
    (coordinate : Fin 34) :
    Nat.size (compactNumericVerifierCombineRuleWitnessEnvironment
      (compactNumericVerifierAllShiftCombineRuleWitness
        premiseGammaCount premiseGammaBoundary premiseBoolValue
        formulaBoundary formulaBoundarySize
        freedStart freedFinish freedBoundary freedCount freedBoundarySize
        freeStateBoundary freeStateCount
        shiftCandidateBoundary shiftSuccessTable shiftedBoundary shiftedCount
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        shiftWitnessBound freeTableWidth freeValueBound resultBoolValue)
      coordinate) ≤ bound := by
  rcases hbounds with
    ⟨hpremiseGammaCount, hpremiseGammaBoundary, hpremiseBoolValue,
      hformulaBoundary, hformulaBoundarySize,
      hfreedStart, hfreedFinish, hfreedBoundary, hfreedCount,
      hfreedBoundarySize, hfreeStateBoundary, hfreeStateCount,
      hshiftCandidateBoundary, hshiftSuccessTable,
      hshiftedBoundary, hshiftedCount,
      hemptyStart, hemptyFinish, hemptyBoundary, hemptyBoundarySize,
      hshiftWitnessBound, hfreeTableWidth, hfreeValueBound,
      hresultBoolValue⟩
  fin_cases coordinate <;>
    simp [compactNumericVerifierCombineRuleWitnessEnvironment,
      compactNumericVerifierAllShiftCombineRuleWitness] <;>
    assumption

theorem CompactNumericVerifierExsCutCombineRuleFieldSizeBounds.coordinate
    {rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      resultBoolValue bound : Nat}
    (hbounds : CompactNumericVerifierExsCutCombineRuleFieldSizeBounds
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound resultBoolValue bound)
    (coordinate : Fin 34) :
    Nat.size (compactNumericVerifierCombineRuleWitnessEnvironment
      (compactNumericVerifierExsCutCombineRuleWitness
        rightGammaCount rightGammaBoundary rightBoolValue
        leftGammaCount leftGammaBoundary leftBoolValue
        formulaBoundary formulaBoundarySize
        transformedStart transformedFinish transformedBoundary
        transformedCount transformedBoundarySize
        transformStateBoundary transformStateCount
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        transformTableWidth transformValueBound resultBoolValue)
      coordinate) ≤ bound := by
  rcases hbounds with
    ⟨hrightGammaCount, hrightGammaBoundary, hrightBoolValue,
      hleftGammaCount, hleftGammaBoundary, hleftBoolValue,
      hformulaBoundary, hformulaBoundarySize,
      htransformedStart, htransformedFinish, htransformedBoundary,
      htransformedCount, htransformedBoundarySize,
      htransformStateBoundary, htransformStateCount,
      hemptyStart, hemptyFinish, hemptyBoundary, hemptyBoundarySize,
      htransformTableWidth, htransformValueBound, hresultBoolValue⟩
  fin_cases coordinate <;>
    simp [compactNumericVerifierCombineRuleWitnessEnvironment,
      compactNumericVerifierExsCutCombineRuleWitness] <;>
    assumption

theorem compactNumericVerifierSimpleCombineRuleWitness_size_le_budget
    (rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      resultBoolValue : Nat) (coordinate : Fin 34) :
    Nat.size (compactNumericVerifierCombineRuleWitnessEnvironment
      (compactNumericVerifierSimpleCombineRuleWitness
        rightGammaCount rightGammaBoundary rightBoolValue
        leftGammaCount leftGammaBoundary leftBoolValue resultBoolValue)
      coordinate) <=
    compactNumericVerifierSimpleCombineRuleWitnessBitBudget
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue resultBoolValue := by
  fin_cases coordinate <;>
    simp [compactNumericVerifierCombineRuleWitnessEnvironment,
      compactNumericVerifierSimpleCombineRuleWitness,
      compactNumericVerifierSimpleCombineRuleWitnessBitBudget] <;>
    omega

theorem compactNumericVerifierSimpleCombineRuleWitness_size_le
    {tokenCount rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      resultBoolValue : Nat}
    (hrightGammaCount : Nat.size rightGammaCount <= tokenCount)
    (hrightGammaBoundary : Nat.size rightGammaBoundary <=
      (tokenCount + 1) * tokenCount)
    (hrightBoolValue : Nat.size rightBoolValue <= 1)
    (hleftGammaCount : Nat.size leftGammaCount <= tokenCount)
    (hleftGammaBoundary : Nat.size leftGammaBoundary <=
      (tokenCount + 1) * tokenCount)
    (hleftBoolValue : Nat.size leftBoolValue <= 1)
    (hresultBoolValue : Nat.size resultBoolValue <= 1)
    (coordinate : Fin 34) :
    Nat.size (compactNumericVerifierCombineRuleWitnessEnvironment
      (compactNumericVerifierSimpleCombineRuleWitness
        rightGammaCount rightGammaBoundary rightBoolValue
        leftGammaCount leftGammaBoundary leftBoolValue resultBoolValue)
      coordinate) <=
      compactNumericVerifierSimpleCombineRuleCoordinateSizeBound
        tokenCount := by
  fin_cases coordinate <;>
    simp [compactNumericVerifierCombineRuleWitnessEnvironment,
      compactNumericVerifierSimpleCombineRuleWitness,
      compactNumericVerifierSimpleCombineRuleCoordinateSizeBound] <;>
    omega

theorem compactNumericVerifierAllShiftCombineRuleWitness_size_le_budget
    (premiseGammaCount premiseGammaBoundary premiseBoolValue
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      resultBoolValue : Nat) (coordinate : Fin 34) :
    Nat.size (compactNumericVerifierCombineRuleWitnessEnvironment
      (compactNumericVerifierAllShiftCombineRuleWitness
        premiseGammaCount premiseGammaBoundary premiseBoolValue
        formulaBoundary formulaBoundarySize
        freedStart freedFinish freedBoundary freedCount freedBoundarySize
        freeStateBoundary freeStateCount
        shiftCandidateBoundary shiftSuccessTable shiftedBoundary shiftedCount
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        shiftWitnessBound freeTableWidth freeValueBound resultBoolValue)
      coordinate) <=
    compactNumericVerifierAllShiftCombineRuleWitnessBitBudget
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound resultBoolValue := by
  fin_cases coordinate <;>
    simp [compactNumericVerifierCombineRuleWitnessEnvironment,
      compactNumericVerifierAllShiftCombineRuleWitness,
      compactNumericVerifierAllShiftCombineRuleWitnessBitBudget] <;>
    omega

theorem compactNumericVerifierExsCutCombineRuleWitness_size_le_budget
    (rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      resultBoolValue : Nat) (coordinate : Fin 34) :
    Nat.size (compactNumericVerifierCombineRuleWitnessEnvironment
      (compactNumericVerifierExsCutCombineRuleWitness
        rightGammaCount rightGammaBoundary rightBoolValue
        leftGammaCount leftGammaBoundary leftBoolValue
        formulaBoundary formulaBoundarySize
        transformedStart transformedFinish transformedBoundary
        transformedCount transformedBoundarySize
        transformStateBoundary transformStateCount
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        transformTableWidth transformValueBound resultBoolValue)
      coordinate) <=
    compactNumericVerifierExsCutCombineRuleWitnessBitBudget
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound resultBoolValue := by
  fin_cases coordinate <;>
    simp [compactNumericVerifierCombineRuleWitnessEnvironment,
      compactNumericVerifierExsCutCombineRuleWitness,
      compactNumericVerifierExsCutCombineRuleWitnessBitBudget] <;>
    omega

theorem compactNumericVerifierFailureCombineRuleWitness_size_le
    (bound : Nat) (coordinate : Fin 34) :
    Nat.size (compactNumericVerifierCombineRuleWitnessEnvironment
      compactNumericVerifierFailureCombineRuleWitness coordinate) <= bound := by
  fin_cases coordinate <;>
    simp [compactNumericVerifierCombineRuleWitnessEnvironment,
      compactNumericVerifierFailureCombineRuleWitness,
      compactNumericVerifierSimpleCombineRuleWitness]

#print axioms compactNumericVerifierFailureCombineRuleWitness_size_le
#print axioms
  compactNumericVerifierSimpleCombineRuleWitness_size_le_budget
#print axioms compactNumericVerifierSimpleCombineRuleWitness_size_le
#print axioms
  compactNumericVerifierAllShiftCombineRuleWitness_size_le_budget
#print axioms
  compactNumericVerifierExsCutCombineRuleWitness_size_le_budget

end FoundationCompactNumericListedDirectVerifierCombineRuleWitnessBounds
