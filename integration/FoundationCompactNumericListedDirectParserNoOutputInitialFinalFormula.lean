import integration.FoundationCompactNumericListedDirectParserInitialFormula

/-!
# Exact initial and no-output final rows for the syntax parser

The final parser output is `none` in exactly two encoded status cases: the
machine is still running, or it has explicitly failed.  This endpoint formula
records that disjunction directly instead of assuming an unproved halting
property of the public fuel bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserNoOutputInitialFinalFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserInitialFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases

structure CompactParserNoOutputInitialFinalWitnessCoordinates where
  initialCoordinates : CompactUnifiedParserStateRowCoordinates
  initialSizeWitness : CompactUnifiedParserStateCoreSizeWitness
  finalCoordinates : CompactUnifiedParserStateRowCoordinates
  finalSizeWitness : CompactUnifiedParserStateCoreSizeWitness

def CompactUnifiedParserNoOutputInitialFinalRows
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (witness : CompactParserNoOutputInitialFinalWitnessCoordinates) : Prop :=
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
    (CompactBinaryNatRunningStatusSlice
        tokenTable width tokenCount
          witness.finalCoordinates.tasksFinish
          witness.finalCoordinates.finish ∨
      CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount
          witness.finalCoordinates.tasksFinish
          witness.finalCoordinates.finish)

def compactUnifiedParserNoOutputInitialFinalRowsDef :
    𝚺₀.Semisentence 31 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      initialStart initialFinish initialTokensFinish initialTasksFinish
      initialTokensBoundary initialTokensCount
      initialTasksBoundary initialTasksCount
      initialTokensBoundarySize initialTasksBoundarySize
      finalStart finalFinish finalTokensFinish finalTasksFinish
      finalTokensBoundary finalTokensCount
      finalTasksBoundary finalTasksCount
      finalTokensBoundarySize finalTasksBoundarySize.
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
      finalTokensBoundary finalTokensCount
      finalTasksBoundary finalTasksCount
      finalTokensBoundarySize finalTasksBoundarySize ∧
    (!(compactBinaryNatRunningStatusSliceDef)
        tokenTable width tokenCount finalTasksFinish finalFinish ∨
      !(compactBinaryNatFailedStatusSliceDef)
        tokenTable width tokenCount finalTasksFinish finalFinish)”

def compactUnifiedParserNoOutputInitialFinalRowsEnvironment
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (witness : CompactParserNoOutputInitialFinalWitnessCoordinates) :
    Fin 31 → Nat :=
  ![tokenTable, width, tokenCount, stateBoundary, stateCount, fuel,
    inputBoundary, inputCount, taskKind, taskBinderArity, taskRepeatCount,
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
    witness.finalSizeWitness.tasksBoundarySize]

@[simp] theorem compactUnifiedParserNoOutputInitialFinalRowsDef_spec
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (witness : CompactParserNoOutputInitialFinalWitnessCoordinates) :
    compactUnifiedParserNoOutputInitialFinalRowsDef.val.Evalb
        (compactUnifiedParserNoOutputInitialFinalRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
          witness) ↔
      CompactUnifiedParserNoOutputInitialFinalRows
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
        witness := by
  let env := compactUnifiedParserNoOutputInitialFinalRowsEnvironment
    tokenTable width tokenCount stateBoundary stateCount fuel
    inputBoundary inputCount taskKind taskBinderArity taskRepeatCount witness
  change compactUnifiedParserNoOutputInitialFinalRowsDef.val.Evalb env ↔ _
  have hinitialAtEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #3, #4,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 31),
          #11, #12, #13, #14, #15, #16, #17, #18, #19, #20]) =
        compactUnifiedParserStateAtRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount 0
            witness.initialCoordinates witness.initialSizeWitness := by
    funext index
    fin_cases index <;> rfl
  have hinitialEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2,
          #11, #12, #13, #14, #15, #16, #17, #18,
          #6, #7, #8, #9, #10]) =
        compactUnifiedParserInitialStateRowsEnvironment
          tokenTable width tokenCount witness.initialCoordinates
            inputBoundary inputCount
            taskKind taskBinderArity taskRepeatCount := by
    funext index
    fin_cases index <;> rfl
  have hfinalAtEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #3, #4, #5,
          #21, #22, #23, #24, #25, #26, #27, #28, #29, #30]) =
        compactUnifiedParserStateAtRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount fuel
            witness.finalCoordinates witness.finalSizeWitness := by
    funext index
    fin_cases index <;> rfl
  have hstatusEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 31), #1, #2, #24, #22]) =
        ![tokenTable, width, tokenCount,
          witness.finalCoordinates.tasksFinish,
          witness.finalCoordinates.finish] := by
    funext index
    fin_cases index <;> rfl
  have hstateCountValue : env 4 = stateCount := rfl
  have hfuelValue : env 5 = fuel := rfl
  simp [compactUnifiedParserNoOutputInitialFinalRowsDef,
    CompactUnifiedParserNoOutputInitialFinalRows,
    hinitialAtEnv, hinitialEnv, hfinalAtEnv, hstatusEnv,
    hstateCountValue, hfuelValue]

theorem compactUnifiedParserNoOutputInitialFinalRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserNoOutputInitialFinalRowsDef.val := by
  simp [compactUnifiedParserNoOutputInitialFinalRowsDef]

theorem compactSyntaxParserStateOutput_eq_none_iff
    (state : CompactUnifiedParserState) :
    compactSyntaxParserStateOutput state = none ↔
      state.2.2 = none ∨ state.2.2 = some none := by
  rcases state with ⟨tokens, tasks, status⟩
  cases status with
  | none => simp [compactSyntaxParserStateOutput]
  | some result =>
      cases result <;> simp [compactSyntaxParserStateOutput]

theorem exists_compactUnifiedParserNoOutputInitialFinalRows_iff
    {tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      taskKind taskBinderArity taskRepeatCount : Nat}
    {states : List CompactUnifiedParserState}
    {input : List Nat}
    (hcount : states.length = stateCount)
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input) :
    (∃ witness,
        CompactUnifiedParserNoOutputInitialFinalRows
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary input.length
          taskKind taskBinderArity taskRepeatCount witness) ↔
      states.length = fuel + 1 ∧
        states.getI 0 =
          (input, [(taskKind, taskBinderArity, taskRepeatCount)], none) ∧
        compactSyntaxParserStateOutput (states.getI fuel) = none := by
  constructor
  · rintro ⟨witness, hstateCount, hinitialAt, hinitial,
      hfinalAt, hfinalNoOutput⟩
    have hinitialFixed :=
      CompactUnifiedParserStateAtRows.fixedLayout_of_rows
        hcount hrows hinitialAt
    have hfinalFixed :=
      CompactUnifiedParserStateAtRows.fixedLayout_of_rows
        hcount hrows hfinalAt
    have hinitialState :=
      (compactUnifiedParserInitialStateRows_iff
        hinput hinitialFixed).mp hinitial
    have hfinalStatus :
        (states.getI fuel).2.2 = none ∨
          (states.getI fuel).2.2 = some none := by
      rcases hfinalNoOutput with hrunning | hfailed
      · exact Or.inl
          ((CompactBinaryNatStreamStatusDirectLayout.running_iff
            hfinalFixed.statusLayout).mp hrunning)
      · exact Or.inr
          ((CompactBinaryNatStreamStatusDirectLayout.failed_iff
            hfinalFixed.statusLayout).mp hfailed)
    exact ⟨hcount.trans hstateCount, hinitialState,
      (compactSyntaxParserStateOutput_eq_none_iff _).mpr hfinalStatus⟩
  · rintro ⟨hlength, hinitialState, hfinalNoOutput⟩
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
    have hfinalStatus :=
      (compactSyntaxParserStateOutput_eq_none_iff _).mp hfinalNoOutput
    have hfinalRows :
        CompactBinaryNatRunningStatusSlice
            tokenTable width tokenCount
              finalCoordinates.tasksFinish finalCoordinates.finish ∨
          CompactBinaryNatFailedStatusSlice
            tokenTable width tokenCount
              finalCoordinates.tasksFinish finalCoordinates.finish := by
      rcases hfinalStatus with hrunning | hfailed
      · exact Or.inl
          ((CompactBinaryNatStreamStatusDirectLayout.running_iff
            hfinalFixed.statusLayout).mpr hrunning)
      · exact Or.inr
          ((CompactBinaryNatStreamStatusDirectLayout.failed_iff
            hfinalFixed.statusLayout).mpr hfailed)
    let witness : CompactParserNoOutputInitialFinalWitnessCoordinates :=
      { initialCoordinates := initialCoordinates
        initialSizeWitness := initialSizeWitness
        finalCoordinates := finalCoordinates
        finalSizeWitness := finalSizeWitness }
    refine ⟨witness, hstateCount, ?_, hinitial, ?_, hfinalRows⟩
    · simpa only [hcount] using hinitialAtTyped
    · simpa only [hcount] using hfinalAtTyped

theorem exists_compactUnifiedParserNoOutputInitialFinalFormula_iff
    {tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      taskKind taskBinderArity taskRepeatCount : Nat}
    {states : List CompactUnifiedParserState}
    {input : List Nat}
    (hcount : states.length = stateCount)
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input) :
    (∃ witness,
        compactUnifiedParserNoOutputInitialFinalRowsDef.val.Evalb
          (compactUnifiedParserNoOutputInitialFinalRowsEnvironment
            tokenTable width tokenCount stateBoundary stateCount fuel
            inputBoundary input.length
            taskKind taskBinderArity taskRepeatCount witness)) ↔
      states.length = fuel + 1 ∧
        states.getI 0 =
          (input, [(taskKind, taskBinderArity, taskRepeatCount)], none) ∧
        compactSyntaxParserStateOutput (states.getI fuel) = none := by
  simp only [compactUnifiedParserNoOutputInitialFinalRowsDef_spec]
  exact exists_compactUnifiedParserNoOutputInitialFinalRows_iff
    hcount hrows hinput

#print axioms compactUnifiedParserNoOutputInitialFinalRowsDef_spec
#print axioms compactUnifiedParserNoOutputInitialFinalRowsDef_sigmaZero
#print axioms compactSyntaxParserStateOutput_eq_none_iff
#print axioms exists_compactUnifiedParserNoOutputInitialFinalRows_iff
#print axioms exists_compactUnifiedParserNoOutputInitialFinalFormula_iff

end FoundationCompactNumericListedDirectParserNoOutputInitialFinalFormula
