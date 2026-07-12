import integration.FoundationCompactNumericListedDirectParserInitialFormula
import integration.FoundationCompactNumericListedDirectParserFinalFormula

/-!
# Combined bounded formula for parser initial and final rows

The formula selects row zero and row `fuel` from one parser-state boundary
table, fixes the canonical trace length, checks the exact initial state, and
checks the completed final output against a supplied natural-token list.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserInitialFinalFormula

open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserInitialFormula
open FoundationCompactNumericListedDirectParserFinalFormula

structure CompactParserInitialFinalWitnessCoordinates where
  initialCoordinates : CompactUnifiedParserStateRowCoordinates
  initialSizeWitness : CompactUnifiedParserStateCoreSizeWitness
  finalCoordinates : CompactUnifiedParserStateRowCoordinates
  finalSizeWitness : CompactUnifiedParserStateCoreSizeWitness
  outputStart : Nat
  outputBoundary : Nat
  outputBoundarySize : Nat

def CompactUnifiedParserInitialFinalRows
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) : Prop :=
  stateCount = fuel + 1 ∧
    CompactUnifiedParserStateAtRows
      tokenTable width tokenCount stateBoundary stateCount 0
        witness.initialCoordinates witness.initialSizeWitness ∧
    CompactUnifiedParserInitialStateRows
      tokenTable width tokenCount witness.initialCoordinates
        inputBoundary inputCount taskKind taskBinderArity taskRepeatCount ∧
    CompactUnifiedParserStateAtRows
      tokenTable width tokenCount stateBoundary stateCount fuel
        witness.finalCoordinates witness.finalSizeWitness ∧
    CompactUnifiedParserFinalStateRows
      tokenTable width tokenCount witness.finalCoordinates
        expectedBoundary expectedCount witness.outputStart
        witness.outputBoundary witness.outputBoundarySize

def compactUnifiedParserInitialFinalRowsDef : 𝚺₀.Semisentence 36 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount
      initialStart initialFinish initialTokensFinish initialTasksFinish
      initialTokensBoundary initialTokensCount
      initialTasksBoundary initialTasksCount
      initialTokensBoundarySize initialTasksBoundarySize
      finalStart finalFinish finalTokensFinish finalTasksFinish
      finalTokensBoundary finalTokensCount finalTasksBoundary finalTasksCount
      finalTokensBoundarySize finalTasksBoundarySize
      outputStart outputBoundary outputBoundarySize.
    stateCount = fuel + 1 ∧
    !(compactUnifiedParserStateAtRowsDef)
      tokenTable width tokenCount stateBoundary stateCount 0
      initialStart initialFinish initialTokensFinish initialTasksFinish
      initialTokensBoundary initialTokensCount
      initialTasksBoundary initialTasksCount
      initialTokensBoundarySize initialTasksBoundarySize ∧
    !(compactUnifiedParserInitialStateRowsDef)
      tokenTable width tokenCount
      initialStart initialFinish initialTokensFinish initialTasksFinish
      initialTokensBoundary initialTokensCount
      initialTasksBoundary initialTasksCount
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount ∧
    !(compactUnifiedParserStateAtRowsDef)
      tokenTable width tokenCount stateBoundary stateCount fuel
      finalStart finalFinish finalTokensFinish finalTasksFinish
      finalTokensBoundary finalTokensCount finalTasksBoundary finalTasksCount
      finalTokensBoundarySize finalTasksBoundarySize ∧
    !(compactUnifiedParserFinalStateRowsDef)
      tokenTable width tokenCount
      finalStart finalFinish finalTokensFinish finalTasksFinish
      finalTokensBoundary finalTokensCount finalTasksBoundary finalTasksCount
      expectedBoundary expectedCount
      outputStart outputBoundary outputBoundarySize”

def compactUnifiedParserInitialFinalRowsEnvironment
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) : Fin 36 → Nat :=
  ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
    inputBoundary, inputCount, expectedBoundary, expectedCount,
    taskKind, taskBinderArity, taskRepeatCount,
    witness.initialCoordinates.start,
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

@[simp] theorem compactUnifiedParserInitialFinalRowsDef_spec
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    compactUnifiedParserInitialFinalRowsDef.val.Evalb
        (compactUnifiedParserInitialFinalRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedBoundary expectedCount
          taskKind taskBinderArity taskRepeatCount witness) ↔
      CompactUnifiedParserInitialFinalRows
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedBoundary expectedCount
        taskKind taskBinderArity taskRepeatCount witness := by
  let env := compactUnifiedParserInitialFinalRowsEnvironment
    tokenTable width tokenCount stateBoundary stateCount fuel
    inputBoundary inputCount expectedBoundary expectedCount
    taskKind taskBinderArity taskRepeatCount witness
  change compactUnifiedParserInitialFinalRowsDef.val.Evalb env ↔ _
  have hinitialAtEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 36), #1, #2, #3, #4,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 36),
          #13, #14, #15, #16, #17, #18, #19, #20, #21, #22]) =
        compactUnifiedParserStateAtRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount 0
            witness.initialCoordinates witness.initialSizeWitness := by
    funext index
    fin_cases index <;> rfl
  have hinitialEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 36), #1, #2,
          #13, #14, #15, #16, #17, #18, #19, #20,
          #6, #7, #10, #11, #12]) =
        compactUnifiedParserInitialStateRowsEnvironment
          tokenTable width tokenCount witness.initialCoordinates
            inputBoundary inputCount
            taskKind taskBinderArity taskRepeatCount := by
    funext index
    fin_cases index <;> rfl
  have hfinalAtEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 36), #1, #2, #3, #4, #5,
          #23, #24, #25, #26, #27, #28, #29, #30, #31, #32]) =
        compactUnifiedParserStateAtRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount fuel
            witness.finalCoordinates witness.finalSizeWitness := by
    funext index
    fin_cases index <;> rfl
  have hfinalEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 36), #1, #2,
          #23, #24, #25, #26, #27, #28, #29, #30,
          #8, #9, #33, #34, #35]) =
        compactUnifiedParserFinalStateRowsEnvironment
          tokenTable width tokenCount witness.finalCoordinates
            expectedBoundary expectedCount witness.outputStart
            witness.outputBoundary witness.outputBoundarySize := by
    funext index
    fin_cases index <;> rfl
  have hstateCountValue : env 4 = stateCount := rfl
  have hfuelValue : env 5 = fuel := rfl
  simp [compactUnifiedParserInitialFinalRowsDef,
    CompactUnifiedParserInitialFinalRows,
    hinitialAtEnv, hinitialEnv, hfinalAtEnv, hfinalEnv,
    hstateCountValue, hfuelValue]

theorem compactUnifiedParserInitialFinalRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserInitialFinalRowsDef.val := by
  simp [compactUnifiedParserInitialFinalRowsDef]

theorem exists_compactUnifiedParserInitialFinalRows_iff
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary expectedBoundary taskKind taskBinderArity taskRepeatCount :
      Nat}
    {states : List CompactUnifiedParserState}
    {input expected : List Nat}
    (hcount : states.length = stateCount)
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpected : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedBoundary expected) :
    (∃ witness,
        CompactUnifiedParserInitialFinalRows
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary input.length expectedBoundary expected.length
          taskKind taskBinderArity taskRepeatCount witness) ↔
      states.length = fuel + 1 ∧
        states.getI 0 =
          (input, [(taskKind, taskBinderArity, taskRepeatCount)], none) ∧
        (states.getI fuel).2.2 = some (some expected) := by
  constructor
  · rintro ⟨witness, hstateCount, hinitialAt, hinitial,
      hfinalAt, hfinal⟩
    have hinitialFixed :=
      CompactUnifiedParserStateAtRows.fixedLayout_of_rows
        hcount hrows hinitialAt
    have hfinalFixed :=
      CompactUnifiedParserStateAtRows.fixedLayout_of_rows
        hcount hrows hfinalAt
    have hinitialState :=
      (compactUnifiedParserInitialStateRows_iff
        hinput hinitialFixed).mp hinitial
    have hfinalState :=
      (exists_compactUnifiedParserFinalStateRows_iff
        hexpected hfinalFixed).mp
          ⟨witness.outputStart, witness.outputBoundary,
            witness.outputBoundarySize, hfinal⟩
    exact ⟨hcount.trans hstateCount, hinitialState, hfinalState⟩
  · rintro ⟨hlength, hinitialState, hfinalState⟩
    have hstateCount : stateCount = fuel + 1 := hcount.symm.trans hlength
    have hzero : 0 < states.length := by omega
    have hfinalIndex : fuel < states.length := by omega
    rcases exists_compactUnifiedParserStateAtRows_with_fixed_layout
        hrows hzero with
      ⟨initialCoordinates, initialSizeWitness,
        hinitialAtTyped, hinitialFixed⟩
    rcases exists_compactUnifiedParserStateAtRows_with_fixed_layout
        hrows hfinalIndex with
      ⟨finalCoordinates, finalSizeWitness, hfinalAtTyped, hfinalFixed⟩
    have hinitial :=
      (compactUnifiedParserInitialStateRows_iff
        hinput hinitialFixed).mpr hinitialState
    rcases (exists_compactUnifiedParserFinalStateRows_iff
        hexpected hfinalFixed).mpr hfinalState with
      ⟨outputStart, outputBoundary, outputBoundarySize, hfinal⟩
    let witness : CompactParserInitialFinalWitnessCoordinates :=
      { initialCoordinates := initialCoordinates
        initialSizeWitness := initialSizeWitness
        finalCoordinates := finalCoordinates
        finalSizeWitness := finalSizeWitness
        outputStart := outputStart
        outputBoundary := outputBoundary
        outputBoundarySize := outputBoundarySize }
    refine ⟨witness, hstateCount, ?_, hinitial, ?_, hfinal⟩
    · simpa only [hcount] using hinitialAtTyped
    · simpa only [hcount] using hfinalAtTyped

theorem exists_compactUnifiedParserInitialFinalFormula_iff
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary expectedBoundary taskKind taskBinderArity taskRepeatCount :
      Nat}
    {states : List CompactUnifiedParserState}
    {input expected : List Nat}
    (hcount : states.length = stateCount)
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpected : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedBoundary expected) :
    (∃ witness,
        compactUnifiedParserInitialFinalRowsDef.val.Evalb
          (compactUnifiedParserInitialFinalRowsEnvironment
            tokenTable width tokenCount stateBoundary stateCount fuel
            inputBoundary input.length expectedBoundary expected.length
            taskKind taskBinderArity taskRepeatCount witness)) ↔
      states.length = fuel + 1 ∧
        states.getI 0 =
          (input, [(taskKind, taskBinderArity, taskRepeatCount)], none) ∧
        (states.getI fuel).2.2 = some (some expected) := by
  simp only [compactUnifiedParserInitialFinalRowsDef_spec]
  exact exists_compactUnifiedParserInitialFinalRows_iff
    hcount hrows hinput hexpected

#print axioms compactUnifiedParserInitialFinalRowsDef_spec
#print axioms compactUnifiedParserInitialFinalRowsDef_sigmaZero
#print axioms exists_compactUnifiedParserInitialFinalRows_iff
#print axioms exists_compactUnifiedParserInitialFinalFormula_iff

end FoundationCompactNumericListedDirectParserInitialFinalFormula
