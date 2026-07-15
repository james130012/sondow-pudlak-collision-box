import integration.FoundationCompactNumericListedDirectParserInitialFinalFormula

/-!
# Bounded witness closure for parser endpoints

All twenty-three coordinates used by the exact parser initial/final relation
are quantified below one explicit value bound.  The predicate remains a
handwritten Delta-zero arithmetic formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula

open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserInitialFinalFormula

def compactParserInitialFinalWitnessOfValues
    (initialStart initialFinish initialTokensFinish initialTasksFinish
      initialTokensBoundary initialTokensCount
      initialTasksBoundary initialTasksCount
      initialTokensBoundarySize initialTasksBoundarySize
      finalStart finalFinish finalTokensFinish finalTasksFinish
      finalTokensBoundary finalTokensCount finalTasksBoundary finalTasksCount
      finalTokensBoundarySize finalTasksBoundarySize
      outputStart outputBoundary outputBoundarySize : Nat) :
    CompactParserInitialFinalWitnessCoordinates :=
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
        tasksBoundarySize := finalTasksBoundarySize }
    outputStart := outputStart
    outputBoundary := outputBoundary
    outputBoundarySize := outputBoundarySize }

def compactParserInitialFinalWitnessValues
    (witness : CompactParserInitialFinalWitnessCoordinates) : List Nat :=
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
    witness.finalSizeWitness.tasksBoundarySize,
    witness.outputStart, witness.outputBoundary, witness.outputBoundarySize]

def compactParserInitialFinalWitnessDynamicWidth
    (witness : CompactParserInitialFinalWitnessCoordinates) : Nat :=
  ((compactParserInitialFinalWitnessValues witness).map Nat.size).sum

theorem compactParserInitialFinalWitnessValue_size_le_dynamic
    (witness : CompactParserInitialFinalWitnessCoordinates)
    {value : Nat}
    (hvalue : value ∈ compactParserInitialFinalWitnessValues witness) :
    Nat.size value ≤ compactParserInitialFinalWitnessDynamicWidth witness := by
  have hsize : Nat.size value ∈
      (compactParserInitialFinalWitnessValues witness).map Nat.size :=
    List.mem_map.mpr ⟨value, hvalue, rfl⟩
  simpa [compactParserInitialFinalWitnessDynamicWidth] using
    List.single_le_sum (by simp) _ hsize

def CompactParserInitialFinalBounded
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat) : Prop :=
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
  ∃ outputStart, outputStart ≤ valueBound ∧
  ∃ outputBoundary, outputBoundary ≤ valueBound ∧
  ∃ outputBoundarySize, outputBoundarySize ≤ valueBound ∧
    CompactUnifiedParserInitialFinalRows
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount
      (compactParserInitialFinalWitnessOfValues
        initialStart initialFinish initialTokensFinish initialTasksFinish
        initialTokensBoundary initialTokensCount
        initialTasksBoundary initialTasksCount
        initialTokensBoundarySize initialTasksBoundarySize
        finalStart finalFinish finalTokensFinish finalTasksFinish
        finalTokensBoundary finalTokensCount finalTasksBoundary finalTasksCount
        finalTokensBoundarySize finalTasksBoundarySize
        outputStart outputBoundary outputBoundarySize)

def compactParserInitialFinalBoundedDef :
    𝚺₀.Semisentence 14 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound.
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
    ∃ outputStart <⁺ valueBound,
    ∃ outputBoundary <⁺ valueBound,
    ∃ outputBoundarySize <⁺ valueBound,
      !(compactUnifiedParserInitialFinalRowsDef)
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedBoundary expectedCount
        taskKind taskBinderArity taskRepeatCount
        initialStart initialFinish initialTokensFinish initialTasksFinish
        initialTokensBoundary initialTokensCount
        initialTasksBoundary initialTasksCount
        initialTokensBoundarySize initialTasksBoundarySize
        finalStart finalFinish finalTokensFinish finalTasksFinish
        finalTokensBoundary finalTokensCount finalTasksBoundary finalTasksCount
        finalTokensBoundarySize finalTasksBoundarySize
        outputStart outputBoundary outputBoundarySize”

set_option maxRecDepth 4096 in
@[simp] theorem compactParserInitialFinalBoundedDef_spec
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat) :
    compactParserInitialFinalBoundedDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
          inputBoundary, inputCount, expectedBoundary, expectedCount,
          taskKind, taskBinderArity, taskRepeatCount, valueBound] ↔
      CompactParserInitialFinalBounded
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedBoundary expectedCount
        taskKind taskBinderArity taskRepeatCount valueBound := by
  have hrelation
      (outputBoundarySize outputBoundary outputStart
        finalTasksBoundarySize finalTokensBoundarySize
        finalTasksCount finalTasksBoundary finalTokensCount finalTokensBoundary
        finalTasksFinish finalTokensFinish finalFinish finalStart
        initialTasksBoundarySize initialTokensBoundarySize
        initialTasksCount initialTasksBoundary initialTokensCount
        initialTokensBoundary initialTasksFinish initialTokensFinish
        initialFinish initialStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![outputBoundarySize, outputBoundary, outputStart,
                finalTasksBoundarySize, finalTokensBoundarySize,
                finalTasksCount, finalTasksBoundary, finalTokensCount,
                finalTokensBoundary, finalTasksFinish, finalTokensFinish,
                finalFinish, finalStart,
                initialTasksBoundarySize, initialTokensBoundarySize,
                initialTasksCount, initialTasksBoundary, initialTokensCount,
                initialTokensBoundary, initialTasksFinish, initialTokensFinish,
                initialFinish, initialStart,
                tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
                inputBoundary, inputCount, expectedBoundary, expectedCount,
                taskKind, taskBinderArity, taskRepeatCount, valueBound]
              Empty.elim ∘
            ![(#23 : Semiterm ℒₒᵣ Empty 37), #24, #25, #26, #27, #28,
              #29, #30, #31, #32, #33, #34, #35,
              #22, #21, #20, #19, #18, #17, #16, #15, #14, #13,
              #12, #11, #10, #9, #8, #7, #6, #5, #4, #3,
              #2, #1, #0])
          Empty.elim)
        compactUnifiedParserInitialFinalRowsDef.val ↔
      CompactUnifiedParserInitialFinalRows
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedBoundary expectedCount
        taskKind taskBinderArity taskRepeatCount
        (compactParserInitialFinalWitnessOfValues
          initialStart initialFinish initialTokensFinish initialTasksFinish
          initialTokensBoundary initialTokensCount
          initialTasksBoundary initialTasksCount
          initialTokensBoundarySize initialTasksBoundarySize
          finalStart finalFinish finalTokensFinish finalTasksFinish
          finalTokensBoundary finalTokensCount finalTasksBoundary finalTasksCount
          finalTokensBoundarySize finalTasksBoundarySize
          outputStart outputBoundary outputBoundarySize) := by
    have henv :
        (Semiterm.val
            ![outputBoundarySize, outputBoundary, outputStart,
              finalTasksBoundarySize, finalTokensBoundarySize,
              finalTasksCount, finalTasksBoundary, finalTokensCount,
              finalTokensBoundary, finalTasksFinish, finalTokensFinish,
              finalFinish, finalStart,
              initialTasksBoundarySize, initialTokensBoundarySize,
              initialTasksCount, initialTasksBoundary, initialTokensCount,
              initialTokensBoundary, initialTasksFinish, initialTokensFinish,
              initialFinish, initialStart,
              tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
              inputBoundary, inputCount, expectedBoundary, expectedCount,
              taskKind, taskBinderArity, taskRepeatCount, valueBound]
            Empty.elim ∘
          ![(#23 : Semiterm ℒₒᵣ Empty 37), #24, #25, #26, #27, #28,
            #29, #30, #31, #32, #33, #34, #35,
            #22, #21, #20, #19, #18, #17, #16, #15, #14, #13,
            #12, #11, #10, #9, #8, #7, #6, #5, #4, #3,
            #2, #1, #0]) =
          compactUnifiedParserInitialFinalRowsEnvironment
            tokenTable width tokenCount stateBoundary stateCount fuel
            inputBoundary inputCount expectedBoundary expectedCount
            taskKind taskBinderArity taskRepeatCount
            (compactParserInitialFinalWitnessOfValues
              initialStart initialFinish initialTokensFinish initialTasksFinish
              initialTokensBoundary initialTokensCount
              initialTasksBoundary initialTasksCount
              initialTokensBoundarySize initialTasksBoundarySize
              finalStart finalFinish finalTokensFinish finalTasksFinish
              finalTokensBoundary finalTokensCount
              finalTasksBoundary finalTasksCount
              finalTokensBoundarySize finalTasksBoundarySize
              outputStart outputBoundary outputBoundarySize) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactUnifiedParserInitialFinalRowsDef_spec
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount _
  simp [compactParserInitialFinalBoundedDef,
    CompactParserInitialFinalBounded, hrelation]

theorem compactParserInitialFinalBoundedDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserInitialFinalBoundedDef.val := by
  simp [compactParserInitialFinalBoundedDef]

theorem CompactParserInitialFinalBounded.exists_witness
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat}
    (hbounded : CompactParserInitialFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound) :
    ∃ witness,
      CompactUnifiedParserInitialFinalRows
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedBoundary expectedCount
        taskKind taskBinderArity taskRepeatCount witness := by
  rcases hbounded with
    ⟨initialStart, _, initialFinish, _, initialTokensFinish, _,
      initialTasksFinish, _, initialTokensBoundary, _, initialTokensCount, _,
      initialTasksBoundary, _, initialTasksCount, _,
      initialTokensBoundarySize, _, initialTasksBoundarySize, _,
      finalStart, _, finalFinish, _, finalTokensFinish, _, finalTasksFinish, _,
      finalTokensBoundary, _, finalTokensCount, _, finalTasksBoundary, _,
      finalTasksCount, _, finalTokensBoundarySize, _, finalTasksBoundarySize, _,
      outputStart, _, outputBoundary, _, outputBoundarySize, _, hrelation⟩
  exact ⟨compactParserInitialFinalWitnessOfValues
    initialStart initialFinish initialTokensFinish initialTasksFinish
    initialTokensBoundary initialTokensCount
    initialTasksBoundary initialTasksCount
    initialTokensBoundarySize initialTasksBoundarySize
    finalStart finalFinish finalTokensFinish finalTasksFinish
    finalTokensBoundary finalTokensCount finalTasksBoundary finalTasksCount
    finalTokensBoundarySize finalTasksBoundarySize
    outputStart outputBoundary outputBoundarySize, hrelation⟩

theorem CompactParserInitialFinalBounded.of_witness
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount tableWidth : Nat}
    {witness : CompactParserInitialFinalWitnessCoordinates}
    (hwidth : compactParserInitialFinalWitnessDynamicWidth witness ≤ tableWidth)
    (hrelation : CompactUnifiedParserInitialFinalRows
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount witness) :
    CompactParserInitialFinalBounded
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount (2 ^ tableWidth) := by
  have hall (value : Nat)
      (hvalue : value ∈ compactParserInitialFinalWitnessValues witness) :
      value ≤ 2 ^ tableWidth :=
    (Nat.size_le.mp
      ((compactParserInitialFinalWitnessValue_size_le_dynamic
        witness hvalue).trans hwidth)).le
  unfold CompactParserInitialFinalBounded
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
    witness.finalSizeWitness.tasksBoundarySize, ?_,
    witness.outputStart, ?_, witness.outputBoundary, ?_,
    witness.outputBoundarySize, ?_, ?_⟩
  all_goals
    first
    | apply hall
      simp [compactParserInitialFinalWitnessValues]
    | simpa [compactParserInitialFinalWitnessOfValues,
        compactUnifiedParserStateRowCoordinatesOf] using hrelation

#print axioms compactParserInitialFinalBoundedDef_spec
#print axioms compactParserInitialFinalBoundedDef_sigmaZero
#print axioms compactParserInitialFinalWitnessValue_size_le_dynamic
#print axioms CompactParserInitialFinalBounded.exists_witness
#print axioms CompactParserInitialFinalBounded.of_witness

end FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula
