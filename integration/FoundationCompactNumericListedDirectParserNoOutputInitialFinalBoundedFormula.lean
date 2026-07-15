import integration.FoundationCompactNumericListedDirectParserNoOutputInitialFinalFormula

/-!
# Bounded witness closure for parser no-output endpoints

All twenty coordinates of the exact initial/no-output-final relation are
quantified below one explicit value bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserNoOutputInitialFinalBoundedFormula

open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserNoOutputInitialFinalFormula

def compactParserNoOutputInitialFinalWitnessOfValues
    (initialStart initialFinish initialTokensFinish initialTasksFinish
      initialTokensBoundary initialTokensCount
      initialTasksBoundary initialTasksCount
      initialTokensBoundarySize initialTasksBoundarySize
      finalStart finalFinish finalTokensFinish finalTasksFinish
      finalTokensBoundary finalTokensCount finalTasksBoundary finalTasksCount
      finalTokensBoundarySize finalTasksBoundarySize : Nat) :
    CompactParserNoOutputInitialFinalWitnessCoordinates :=
  { initialCoordinates :=
      compactUnifiedParserStateRowCoordinatesOf
        initialStart initialFinish initialTokensFinish initialTasksFinish
        initialTokensBoundary initialTokensCount
        initialTasksBoundary initialTasksCount
    initialSizeWitness :=
      { tokensBoundarySize := initialTokensBoundarySize
        tasksBoundarySize := initialTasksBoundarySize }
    finalCoordinates :=
      compactUnifiedParserStateRowCoordinatesOf
        finalStart finalFinish finalTokensFinish finalTasksFinish
        finalTokensBoundary finalTokensCount finalTasksBoundary finalTasksCount
    finalSizeWitness :=
      { tokensBoundarySize := finalTokensBoundarySize
        tasksBoundarySize := finalTasksBoundarySize } }

def compactParserNoOutputInitialFinalWitnessValues
    (witness : CompactParserNoOutputInitialFinalWitnessCoordinates) :
    List Nat :=
  [witness.initialCoordinates.start,
    witness.initialCoordinates.finish,
    witness.initialCoordinates.tokensFinish,
    witness.initialCoordinates.tasksFinish,
    witness.initialCoordinates.tokensBoundary,
    witness.initialCoordinates.tokensCount,
    witness.initialCoordinates.tasksBoundary,
    witness.initialCoordinates.tasksCount,
    witness.initialSizeWitness.tokensBoundarySize,
    witness.initialSizeWitness.tasksBoundarySize,
    witness.finalCoordinates.start,
    witness.finalCoordinates.finish,
    witness.finalCoordinates.tokensFinish,
    witness.finalCoordinates.tasksFinish,
    witness.finalCoordinates.tokensBoundary,
    witness.finalCoordinates.tokensCount,
    witness.finalCoordinates.tasksBoundary,
    witness.finalCoordinates.tasksCount,
    witness.finalSizeWitness.tokensBoundarySize,
    witness.finalSizeWitness.tasksBoundarySize]

def compactParserNoOutputInitialFinalWitnessDynamicWidth
    (witness : CompactParserNoOutputInitialFinalWitnessCoordinates) : Nat :=
  ((compactParserNoOutputInitialFinalWitnessValues witness).map Nat.size).sum

theorem compactParserNoOutputInitialFinalWitnessValue_size_le_dynamic
    (witness : CompactParserNoOutputInitialFinalWitnessCoordinates)
    {value : Nat}
    (hvalue : value ∈ compactParserNoOutputInitialFinalWitnessValues witness) :
    Nat.size value ≤
      compactParserNoOutputInitialFinalWitnessDynamicWidth witness := by
  have hsize : Nat.size value ∈
      (compactParserNoOutputInitialFinalWitnessValues witness).map Nat.size :=
    List.mem_map.mpr ⟨value, hvalue, rfl⟩
  simpa [compactParserNoOutputInitialFinalWitnessDynamicWidth] using
    List.single_le_sum (by simp) _ hsize

def CompactParserNoOutputInitialFinalBounded
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      valueBound : Nat) : Prop :=
  ∃ initialStart, initialStart ≤ valueBound ∧
  ∃ initialFinish, initialFinish ≤ valueBound ∧
  ∃ initialTokensFinish, initialTokensFinish ≤ valueBound ∧
  ∃ initialTasksFinish, initialTasksFinish ≤ valueBound ∧
  ∃ initialTokensBoundary, initialTokensBoundary ≤ valueBound ∧
  ∃ initialTokensCount, initialTokensCount ≤ valueBound ∧
  ∃ initialTasksBoundary, initialTasksBoundary ≤ valueBound ∧
  ∃ initialTasksCount, initialTasksCount ≤ valueBound ∧
  ∃ initialTokensBoundarySize, initialTokensBoundarySize ≤ valueBound ∧
  ∃ initialTasksBoundarySize, initialTasksBoundarySize ≤ valueBound ∧
  ∃ finalStart, finalStart ≤ valueBound ∧
  ∃ finalFinish, finalFinish ≤ valueBound ∧
  ∃ finalTokensFinish, finalTokensFinish ≤ valueBound ∧
  ∃ finalTasksFinish, finalTasksFinish ≤ valueBound ∧
  ∃ finalTokensBoundary, finalTokensBoundary ≤ valueBound ∧
  ∃ finalTokensCount, finalTokensCount ≤ valueBound ∧
  ∃ finalTasksBoundary, finalTasksBoundary ≤ valueBound ∧
  ∃ finalTasksCount, finalTasksCount ≤ valueBound ∧
  ∃ finalTokensBoundarySize, finalTokensBoundarySize ≤ valueBound ∧
  ∃ finalTasksBoundarySize, finalTasksBoundarySize ≤ valueBound ∧
    CompactUnifiedParserNoOutputInitialFinalRows
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      (compactParserNoOutputInitialFinalWitnessOfValues
        initialStart initialFinish initialTokensFinish initialTasksFinish
        initialTokensBoundary initialTokensCount
        initialTasksBoundary initialTasksCount
        initialTokensBoundarySize initialTasksBoundarySize
        finalStart finalFinish finalTokensFinish finalTasksFinish
        finalTokensBoundary finalTokensCount finalTasksBoundary finalTasksCount
        finalTokensBoundarySize finalTasksBoundarySize)

def compactParserNoOutputInitialFinalBoundedDef :
    𝚺₀.Semisentence 12 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      valueBound.
    ∃ initialStart <⁺ valueBound,
    ∃ initialFinish <⁺ valueBound,
    ∃ initialTokensFinish <⁺ valueBound,
    ∃ initialTasksFinish <⁺ valueBound,
    ∃ initialTokensBoundary <⁺ valueBound,
    ∃ initialTokensCount <⁺ valueBound,
    ∃ initialTasksBoundary <⁺ valueBound,
    ∃ initialTasksCount <⁺ valueBound,
    ∃ initialTokensBoundarySize <⁺ valueBound,
    ∃ initialTasksBoundarySize <⁺ valueBound,
    ∃ finalStart <⁺ valueBound,
    ∃ finalFinish <⁺ valueBound,
    ∃ finalTokensFinish <⁺ valueBound,
    ∃ finalTasksFinish <⁺ valueBound,
    ∃ finalTokensBoundary <⁺ valueBound,
    ∃ finalTokensCount <⁺ valueBound,
    ∃ finalTasksBoundary <⁺ valueBound,
    ∃ finalTasksCount <⁺ valueBound,
    ∃ finalTokensBoundarySize <⁺ valueBound,
    ∃ finalTasksBoundarySize <⁺ valueBound,
      !(compactUnifiedParserNoOutputInitialFinalRowsDef)
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
        initialStart initialFinish initialTokensFinish initialTasksFinish
        initialTokensBoundary initialTokensCount
        initialTasksBoundary initialTasksCount
        initialTokensBoundarySize initialTasksBoundarySize
        finalStart finalFinish finalTokensFinish finalTasksFinish
        finalTokensBoundary finalTokensCount finalTasksBoundary finalTasksCount
        finalTokensBoundarySize finalTasksBoundarySize”

set_option maxRecDepth 4096 in
@[simp] theorem compactParserNoOutputInitialFinalBoundedDef_spec
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      valueBound : Nat) :
    compactParserNoOutputInitialFinalBoundedDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
          inputBoundary, inputCount, taskKind, taskBinderArity,
          taskRepeatCount, valueBound] ↔
      CompactParserNoOutputInitialFinalBounded
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
        valueBound := by
  have hrelation
      (finalTasksBoundarySize finalTokensBoundarySize
        finalTasksCount finalTasksBoundary finalTokensCount finalTokensBoundary
        finalTasksFinish finalTokensFinish finalFinish finalStart
        initialTasksBoundarySize initialTokensBoundarySize
        initialTasksCount initialTasksBoundary initialTokensCount
        initialTokensBoundary initialTasksFinish initialTokensFinish
        initialFinish initialStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![finalTasksBoundarySize, finalTokensBoundarySize,
                finalTasksCount, finalTasksBoundary, finalTokensCount,
                finalTokensBoundary, finalTasksFinish, finalTokensFinish,
                finalFinish, finalStart,
                initialTasksBoundarySize, initialTokensBoundarySize,
                initialTasksCount, initialTasksBoundary, initialTokensCount,
                initialTokensBoundary, initialTasksFinish, initialTokensFinish,
                initialFinish, initialStart,
                tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
                inputBoundary, inputCount, taskKind, taskBinderArity,
                taskRepeatCount, valueBound]
              Empty.elim ∘
            ![(#20 : Semiterm ℒₒᵣ Empty 32), #21, #22, #23, #24, #25,
              #26, #27, #28, #29, #30,
              #19, #18, #17, #16, #15, #14, #13, #12, #11, #10,
              #9, #8, #7, #6, #5, #4, #3, #2, #1, #0])
          Empty.elim)
        compactUnifiedParserNoOutputInitialFinalRowsDef.val ↔
      CompactUnifiedParserNoOutputInitialFinalRows
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
        (compactParserNoOutputInitialFinalWitnessOfValues
          initialStart initialFinish initialTokensFinish initialTasksFinish
          initialTokensBoundary initialTokensCount
          initialTasksBoundary initialTasksCount
          initialTokensBoundarySize initialTasksBoundarySize
          finalStart finalFinish finalTokensFinish finalTasksFinish
          finalTokensBoundary finalTokensCount
          finalTasksBoundary finalTasksCount
          finalTokensBoundarySize finalTasksBoundarySize) := by
    have henv :
        (Semiterm.val
            ![finalTasksBoundarySize, finalTokensBoundarySize,
              finalTasksCount, finalTasksBoundary, finalTokensCount,
              finalTokensBoundary, finalTasksFinish, finalTokensFinish,
              finalFinish, finalStart,
              initialTasksBoundarySize, initialTokensBoundarySize,
              initialTasksCount, initialTasksBoundary, initialTokensCount,
              initialTokensBoundary, initialTasksFinish, initialTokensFinish,
              initialFinish, initialStart,
              tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
              inputBoundary, inputCount, taskKind, taskBinderArity,
              taskRepeatCount, valueBound]
            Empty.elim ∘
          ![(#20 : Semiterm ℒₒᵣ Empty 32), #21, #22, #23, #24, #25,
            #26, #27, #28, #29, #30,
            #19, #18, #17, #16, #15, #14, #13, #12, #11, #10,
            #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]) =
          compactUnifiedParserNoOutputInitialFinalRowsEnvironment
            tokenTable width tokenCount stateBoundary stateCount fuel
            inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
            (compactParserNoOutputInitialFinalWitnessOfValues
              initialStart initialFinish initialTokensFinish initialTasksFinish
              initialTokensBoundary initialTokensCount
              initialTasksBoundary initialTasksCount
              initialTokensBoundarySize initialTasksBoundarySize
              finalStart finalFinish finalTokensFinish finalTasksFinish
              finalTokensBoundary finalTokensCount
              finalTasksBoundary finalTasksCount
              finalTokensBoundarySize finalTasksBoundarySize) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactUnifiedParserNoOutputInitialFinalRowsDef_spec
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount _
  simp [compactParserNoOutputInitialFinalBoundedDef,
    CompactParserNoOutputInitialFinalBounded, hrelation]

theorem compactParserNoOutputInitialFinalBoundedDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserNoOutputInitialFinalBoundedDef.val := by
  simp [compactParserNoOutputInitialFinalBoundedDef]

theorem CompactParserNoOutputInitialFinalBounded.exists_witness
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      valueBound : Nat}
    (hbounded : CompactParserNoOutputInitialFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      valueBound) :
    ∃ witness,
      CompactUnifiedParserNoOutputInitialFinalRows
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
        witness := by
  rcases hbounded with
    ⟨initialStart, _, initialFinish, _, initialTokensFinish, _,
      initialTasksFinish, _, initialTokensBoundary, _, initialTokensCount, _,
      initialTasksBoundary, _, initialTasksCount, _,
      initialTokensBoundarySize, _, initialTasksBoundarySize, _,
      finalStart, _, finalFinish, _, finalTokensFinish, _, finalTasksFinish, _,
      finalTokensBoundary, _, finalTokensCount, _, finalTasksBoundary, _,
      finalTasksCount, _, finalTokensBoundarySize, _, finalTasksBoundarySize, _,
      hrelation⟩
  exact ⟨compactParserNoOutputInitialFinalWitnessOfValues
    initialStart initialFinish initialTokensFinish initialTasksFinish
    initialTokensBoundary initialTokensCount
    initialTasksBoundary initialTasksCount
    initialTokensBoundarySize initialTasksBoundarySize
    finalStart finalFinish finalTokensFinish finalTasksFinish
    finalTokensBoundary finalTokensCount finalTasksBoundary finalTasksCount
    finalTokensBoundarySize finalTasksBoundarySize, hrelation⟩

theorem CompactParserNoOutputInitialFinalBounded.of_witness
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth : Nat}
    {witness : CompactParserNoOutputInitialFinalWitnessCoordinates}
    (hwidth :
      compactParserNoOutputInitialFinalWitnessDynamicWidth witness ≤
        tableWidth)
    (hrelation : CompactUnifiedParserNoOutputInitialFinalRows
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      witness) :
    CompactParserNoOutputInitialFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      (2 ^ tableWidth) := by
  have hall (value : Nat)
      (hvalue : value ∈
        compactParserNoOutputInitialFinalWitnessValues witness) :
      value ≤ 2 ^ tableWidth :=
    (Nat.size_le.mp
      ((compactParserNoOutputInitialFinalWitnessValue_size_le_dynamic
        witness hvalue).trans hwidth)).le
  unfold CompactParserNoOutputInitialFinalBounded
  refine ⟨
    witness.initialCoordinates.start, ?_,
    witness.initialCoordinates.finish, ?_,
    witness.initialCoordinates.tokensFinish, ?_,
    witness.initialCoordinates.tasksFinish, ?_,
    witness.initialCoordinates.tokensBoundary, ?_,
    witness.initialCoordinates.tokensCount, ?_,
    witness.initialCoordinates.tasksBoundary, ?_,
    witness.initialCoordinates.tasksCount, ?_,
    witness.initialSizeWitness.tokensBoundarySize, ?_,
    witness.initialSizeWitness.tasksBoundarySize, ?_,
    witness.finalCoordinates.start, ?_,
    witness.finalCoordinates.finish, ?_,
    witness.finalCoordinates.tokensFinish, ?_,
    witness.finalCoordinates.tasksFinish, ?_,
    witness.finalCoordinates.tokensBoundary, ?_,
    witness.finalCoordinates.tokensCount, ?_,
    witness.finalCoordinates.tasksBoundary, ?_,
    witness.finalCoordinates.tasksCount, ?_,
    witness.finalSizeWitness.tokensBoundarySize, ?_,
    witness.finalSizeWitness.tasksBoundarySize, ?_, ?_⟩
  all_goals
    first
    | apply hall
      simp [compactParserNoOutputInitialFinalWitnessValues]
    | simpa [compactParserNoOutputInitialFinalWitnessOfValues,
        compactUnifiedParserStateRowCoordinatesOf] using hrelation

#print axioms compactParserNoOutputInitialFinalBoundedDef_spec
#print axioms compactParserNoOutputInitialFinalBoundedDef_sigmaZero
#print axioms compactParserNoOutputInitialFinalWitnessValue_size_le_dynamic
#print axioms CompactParserNoOutputInitialFinalBounded.exists_witness
#print axioms CompactParserNoOutputInitialFinalBounded.of_witness

end FoundationCompactNumericListedDirectParserNoOutputInitialFinalBoundedFormula
