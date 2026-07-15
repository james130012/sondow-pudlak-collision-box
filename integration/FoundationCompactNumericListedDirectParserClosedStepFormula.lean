import integration.FoundationCompactNumericListedDirectParserClosedSuccessStepFormula

/-!
# Exact bounded step formula for the closed-formula parser

The closed parser agrees with the ordinary syntax parser on every safe state.
Its only extra transition is a running term task with at least two tokens and
free-variable tag `1`; that transition preserves the token stream, pops the
task, and enters the failed status.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserClosedStepFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactClosedFormulaTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserClosedSuccessBridge
open FoundationCompactNumericListedDirectParserClosedSuccessStepFormula

def CompactUnifiedParserClosedFreeVariableFailureRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) : Prop :=
  CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount current.tasksFinish current.finish ∧
    CompactAdditiveSyntaxTaskListUnconsRowsWithSize
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
        witness.term.tailBoundary witness.term.tailCount
        witness.term.tailBoundarySize 0 witness.slot0 0 ∧
    2 ≤ current.tokensCount ∧
    CompactAdditiveNatListAtRows
      tokenTable width tokenCount current.tokensBoundary
        current.tokensCount 0 1 ∧
    CompactUnifiedParserSyntaxTermFailureRows
      tokenTable width tokenCount current next
        witness.term.tailBoundary witness.term.tailCount

def compactUnifiedParserClosedFreeVariableFailureRowsDef :
    𝚺₀.Semisentence 26 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot0 slot1 slot2 slot3 slot4 slot5 slot6.
    !(compactBinaryNatRunningStatusSliceDef)
      tokenTable width tokenCount currentTasksFinish currentFinish ∧
    !(compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef)
      tokenTable width tokenCount currentTasksBoundary currentTasksCount
      slot1 slot2 slot3 0 slot0 0 ∧
    2 ≤ currentTokensCount ∧
    !(compactAdditiveNatListAtRowsDef)
      tokenTable width tokenCount currentTokensBoundary currentTokensCount
      0 1 ∧
    !(compactUnifiedParserSyntaxTermFailureRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot1 slot2”

@[simp] theorem compactUnifiedParserClosedFreeVariableFailureRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) :
    compactUnifiedParserClosedFreeVariableFailureRowsDef.val.Evalb
        (compactUnifiedParserSyntaxStepFormulaEnvironment
          tokenTable width tokenCount current next witness) ↔
      CompactUnifiedParserClosedFreeVariableFailureRows
        tokenTable width tokenCount current next witness := by
  let env := compactUnifiedParserSyntaxStepFormulaEnvironment
    tokenTable width tokenCount current next witness
  change compactUnifiedParserClosedFreeVariableFailureRowsDef.val.Evalb env ↔ _
  have hrunningEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #6, #4]) =
        ![tokenTable, width, tokenCount, current.tasksFinish,
          current.finish] := by
    funext index
    fin_cases index <;> rfl
  have hunconsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #9, #10,
          #20, #21, #22, ‘0’, #19, ‘0’]) =
        compactAdditiveSyntaxTaskListUnconsRowsWithSizeEnvironment
          tokenTable width tokenCount current.tasksBoundary
            current.tasksCount witness.term.tailBoundary
            witness.term.tailCount witness.term.tailBoundarySize
            0 witness.slot0 0 := by
    funext index
    fin_cases index <;> rfl
  have hatEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #7, #8,
          ‘0’, ‘1’]) =
        compactAdditiveNatListAtRowsEnvironment
          tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 0 1 := by
    funext index
    fin_cases index <;> rfl
  have hfailureEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2,
          #3, #4, #5, #6, #7, #8, #9, #10,
          #11, #12, #13, #14, #15, #16, #17, #18, #20, #21]) =
        compactUnifiedParserSyntaxTermFailureEnvironment
          tokenTable width tokenCount current next
            witness.term.tailBoundary witness.term.tailCount := by
    funext index
    fin_cases index <;> rfl
  have hcurrentCount : env 8 = current.tokensCount := rfl
  simp [compactUnifiedParserClosedFreeVariableFailureRowsDef,
    CompactUnifiedParserClosedFreeVariableFailureRows,
    hrunningEnv, hunconsEnv, hatEnv, hfailureEnv, hcurrentCount] <;> tauto

theorem compactUnifiedParserClosedFreeVariableFailureRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserClosedFreeVariableFailureRowsDef.val := by
  simp [compactUnifiedParserClosedFreeVariableFailureRowsDef]

def CompactUnifiedParserClosedStepRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) : Prop :=
  CompactUnifiedParserClosedSuccessStepRows
      tokenTable width tokenCount current next witness ∨
    CompactUnifiedParserClosedFreeVariableFailureRows
      tokenTable width tokenCount current next witness

def compactUnifiedParserClosedStepRowsDef :
    𝚺₀.Semisentence 26 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot0 slot1 slot2 slot3 slot4 slot5 slot6.
    !(compactUnifiedParserClosedSuccessStepRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot0 slot1 slot2 slot3 slot4 slot5 slot6 ∨
    !(compactUnifiedParserClosedFreeVariableFailureRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot0 slot1 slot2 slot3 slot4 slot5 slot6”

@[simp] theorem compactUnifiedParserClosedStepRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) :
    compactUnifiedParserClosedStepRowsDef.val.Evalb
        (compactUnifiedParserSyntaxStepFormulaEnvironment
          tokenTable width tokenCount current next witness) ↔
      CompactUnifiedParserClosedStepRows
        tokenTable width tokenCount current next witness := by
  let env := compactUnifiedParserSyntaxStepFormulaEnvironment
    tokenTable width tokenCount current next witness
  change compactUnifiedParserClosedStepRowsDef.val.Evalb env ↔ _
  have hidentity :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #3, #4, #5, #6, #7,
          #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
          #19, #20, #21, #22, #23, #24, #25]) = env := by
    funext index
    fin_cases index <;> rfl
  have hsuccessSpec :
      compactUnifiedParserClosedSuccessStepRowsDef.val.Evalb env ↔
        CompactUnifiedParserClosedSuccessStepRows
          tokenTable width tokenCount current next witness := by
    simpa [env] using compactUnifiedParserClosedSuccessStepRowsDef_spec
      tokenTable width tokenCount current next witness
  have hfailureSpec :
      compactUnifiedParserClosedFreeVariableFailureRowsDef.val.Evalb env ↔
        CompactUnifiedParserClosedFreeVariableFailureRows
          tokenTable width tokenCount current next witness := by
    simpa [env] using compactUnifiedParserClosedFreeVariableFailureRowsDef_spec
      tokenTable width tokenCount current next witness
  simp [compactUnifiedParserClosedStepRowsDef,
    CompactUnifiedParserClosedStepRows, hidentity, hsuccessSpec, hfailureSpec]

theorem compactUnifiedParserClosedStepRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserClosedStepRowsDef.val := by
  simp [compactUnifiedParserClosedStepRowsDef]

theorem compactUnifiedParserClosedFreeVariableFailureRows_sound
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    {witness : CompactUnifiedParserSyntaxStepWitnessCoordinates}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hrows : CompactUnifiedParserClosedFreeVariableFailureRows
      tokenTable width tokenCount currentCoordinates nextCoordinates witness) :
    next = compactClosedSyntaxParserStep current := by
  rcases hrows with
    ⟨hcurrentRunning, huncons, hlengthRows, htagRows, hfailureRows⟩
  have hcurrentStatus : current.2.2 = none :=
    (CompactBinaryNatStreamStatusDirectLayout.running_iff
      hcurrent.statusLayout).mp hcurrentRunning
  rcases huncons.realizes hcurrent.tasksCount_eq hcurrent.tasksRows with
    ⟨tail, htailRows, htailCount, hcurrentTasks⟩
  have hlength : 2 ≤ current.1.length := by
    simpa only [hcurrent.tokensCount_eq] using hlengthRows
  have htagAt :=
    (compactAdditiveNatListAtRows_iff_getI
      hcurrent.tokensRows 0 1).mp (by
        simpa only [hcurrent.tokensCount_eq] using htagRows)
  have htag : compactTokenAt 0 current.1 = 1 :=
    (compactTokenAt_eq_getI 0 current.1).trans htagAt.2
  have hfailure :=
    (compactUnifiedParserSyntaxTermFailureRows_iff
      hcurrent hnext htailRows htailCount).mp hfailureRows
  rcases current with ⟨tokens, tasks, status⟩
  simp only at hcurrentStatus hcurrentTasks hlength htag hfailure ⊢
  subst status
  subst tasks
  simpa [compactClosedSyntaxParserStep, compactClosedSyntaxRunningStep,
    compactClosedSyntaxTaskTokenStep, compactClosedTermTokenStep,
    hlength, htag] using hfailure

theorem compactUnifiedParserClosedFreeVariableFailureRows_complete
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hwell : CompactSyntaxTaskStackFieldsWellFormed current.2.1)
    (hunsafe : ¬ CompactClosedSyntaxStepSafe current)
    (hstep : next = compactClosedSyntaxParserStep current) :
    ∃ witness, CompactUnifiedParserClosedFreeVariableFailureRows
      tokenTable width tokenCount currentCoordinates nextCoordinates witness := by
  have hcurrentStatus : current.2.2 = none := by
    by_contra hstatus
    apply hunsafe
    intro hnone
    exact (hstatus hnone).elim
  have hproblem : ∃ binderArity repeatCount tail,
      current.2.1 = (0, binderArity, repeatCount) :: tail ∧
      ¬ (current.1.length ≤ 1 ∨ compactTokenAt 0 current.1 ≠ 1) := by
    by_contra hnone
    apply hunsafe
    intro _status binderArity repeatCount tail htasks
    by_contra hbad
    exact hnone ⟨binderArity, repeatCount, tail, htasks, hbad⟩
  rcases hproblem with
    ⟨binderArity, repeatCount, tail, hcurrentTasks, hbad⟩
  have hlength : 2 ≤ current.1.length := by
    by_contra hlength
    apply hbad
    exact Or.inl (by omega)
  have htag : compactTokenAt 0 current.1 = 1 := by
    by_contra htag
    exact hbad (Or.inr htag)
  have hheadWell : CompactSyntaxTaskFieldsWellFormed
      (0, binderArity, repeatCount) :=
    hwell _ (by rw [hcurrentTasks]; simp)
  have hrepeatCount : repeatCount = 0 := hheadWell.1 rfl
  subst repeatCount
  rcases
      (exists_compactAdditiveSyntaxTaskListUnconsRowsWithSize_iff
        hcurrent.tasksRows 0 binderArity 0).mpr
          ⟨tail, hcurrentTasks⟩ with
    ⟨tailBoundary, tailCount, tailBoundarySize, huncons⟩
  have hunconsCoordinates : CompactAdditiveSyntaxTaskListUnconsRowsWithSize
      tokenTable width tokenCount currentCoordinates.tasksBoundary
        currentCoordinates.tasksCount tailBoundary tailCount tailBoundarySize
        0 binderArity 0 := by
    simpa only [hcurrent.tasksCount_eq] using huncons
  rcases hunconsCoordinates.realizes
      hcurrent.tasksCount_eq hcurrent.tasksRows with
    ⟨realizedTail, hrealizedTailRows, hrealizedTailCount,
      hrealizedTasks⟩
  have hrealizedTailEq : realizedTail = tail :=
    (List.cons.inj (hrealizedTasks.symm.trans hcurrentTasks)).2
  have htailRows : CompactAdditiveStructuredListElementRowLayouts
      FoundationCompactNumericListedDirectSyntaxTaskLayout.CompactSyntaxTaskDirectLayout
      tokenTable width tokenCount tailBoundary tail := by
    simpa only [hrealizedTailEq] using hrealizedTailRows
  have htailCount : tail.length = tailCount := by
    simpa only [hrealizedTailEq] using hrealizedTailCount
  have hcurrentRunning : CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount currentCoordinates.tasksFinish
        currentCoordinates.finish :=
    (CompactBinaryNatStreamStatusDirectLayout.running_iff
      hcurrent.statusLayout).mpr hcurrentStatus
  have htagRows : CompactAdditiveNatListAtRows
      tokenTable width tokenCount currentCoordinates.tokensBoundary
        currentCoordinates.tokensCount 0 1 := by
    have htagRowsLength : CompactAdditiveNatListAtRows
        tokenTable width tokenCount currentCoordinates.tokensBoundary
          current.1.length 0 1 :=
      (compactAdditiveNatListAtRows_iff_getI
        hcurrent.tokensRows 0 1).mpr
          ⟨by omega,
            (compactTokenAt_eq_getI 0 current.1).symm.trans htag⟩
    simpa only [hcurrent.tokensCount_eq] using htagRowsLength
  have hfailureState : next = compactSyntaxFailure current.1 tail := by
    rcases current with ⟨tokens, tasks, status⟩
    simp only at hcurrentStatus hcurrentTasks hlength htag hstep ⊢
    subst status
    subst tasks
    simpa [compactClosedSyntaxParserStep, compactClosedSyntaxRunningStep,
      compactClosedSyntaxTaskTokenStep, compactClosedTermTokenStep,
      hlength, htag] using hstep
  have hfailureRows :=
    (compactUnifiedParserSyntaxTermFailureRows_iff
      hcurrent hnext htailRows htailCount).mpr hfailureState
  let termWitness : CompactSyntaxTermTaskWitnessCoordinates :=
    { tailBoundary := tailBoundary
      tailCount := tailCount
      tailBoundarySize := tailBoundarySize
      tag := 1
      argument := 0
      functionCode := 0 }
  let witness :=
    CompactUnifiedParserSyntaxStepWitnessCoordinates.ofTerm
      binderArity termWitness
  refine ⟨witness, hcurrentRunning, ?_, ?_, ?_, ?_⟩
  · simpa only [witness, termWitness,
      CompactUnifiedParserSyntaxStepWitnessCoordinates.term_ofTerm,
      CompactUnifiedParserSyntaxStepWitnessCoordinates.slot0_ofTerm] using
        hunconsCoordinates
  · simpa only [hcurrent.tokensCount_eq] using hlength
  · exact htagRows
  · simpa only [witness, termWitness,
      CompactUnifiedParserSyntaxStepWitnessCoordinates.term_ofTerm] using
        hfailureRows

theorem compactUnifiedParserClosedStepRows_sound
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hrows : ∃ witness, CompactUnifiedParserClosedStepRows
      tokenTable width tokenCount currentCoordinates nextCoordinates witness) :
    next = compactClosedSyntaxParserStep current := by
  rcases hrows with ⟨witness, hsafe | hfree⟩
  · exact compactUnifiedParserClosedSuccessStepRows_sound
      hcurrent hnext hsafe
  · exact compactUnifiedParserClosedFreeVariableFailureRows_sound
      hcurrent hnext hfree

theorem compactUnifiedParserClosedStepRows_complete
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hwell : CompactSyntaxTaskStackFieldsWellFormed current.2.1)
    (hstep : next = compactClosedSyntaxParserStep current) :
    ∃ witness, CompactUnifiedParserClosedStepRows
      tokenTable width tokenCount currentCoordinates nextCoordinates witness := by
  by_cases hsafe : CompactClosedSyntaxStepSafe current
  · rcases compactUnifiedParserClosedSuccessStepRows_complete
      hcurrent hnext hwell hsafe hstep with ⟨witness, hrows⟩
    exact ⟨witness, Or.inl hrows⟩
  · rcases compactUnifiedParserClosedFreeVariableFailureRows_complete
      hcurrent hnext hwell hsafe hstep with ⟨witness, hrows⟩
    exact ⟨witness, Or.inr hrows⟩

theorem compactClosedSyntaxParserStep_preserves_task_fields_well_formed
    (state : CompactUnifiedParserState)
    (hwell : CompactSyntaxTaskStackFieldsWellFormed state.2.1) :
    CompactSyntaxTaskStackFieldsWellFormed
      (compactClosedSyntaxParserStep state).2.1 := by
  by_cases hsafe : CompactClosedSyntaxStepSafe state
  · rw [compactClosedSyntaxParserStep_eq_compactSyntaxParserStep_of_safe
      state hsafe]
    exact
      FoundationCompactNumericListedDirectFormulaTransformTraceInstallation.compactSyntaxParserStep_preserves_task_fields_well_formed
        state hwell
  · have hstatus : state.2.2 = none := by
      by_contra hstatus
      apply hsafe
      intro hnone
      exact (hstatus hnone).elim
    have hproblem : ∃ binderArity repeatCount tail,
        state.2.1 = (0, binderArity, repeatCount) :: tail ∧
          ¬ (state.1.length ≤ 1 ∨ compactTokenAt 0 state.1 ≠ 1) := by
      by_contra hnone
      apply hsafe
      intro _status binderArity repeatCount tail htasks
      by_contra hbad
      exact hnone ⟨binderArity, repeatCount, tail, htasks, hbad⟩
    rcases hproblem with
      ⟨binderArity, repeatCount, tail, htasks, hbad⟩
    have hlength : 2 ≤ state.1.length := by
      by_contra hlength
      exact hbad (Or.inl (by omega))
    have htag : compactTokenAt 0 state.1 = 1 := by
      by_contra htag
      exact hbad (Or.inr htag)
    have htail : CompactSyntaxTaskStackFieldsWellFormed tail := by
      intro task htask
      exact hwell task (by rw [htasks]; simp [htask])
    rcases state with ⟨tokens, tasks, status⟩
    simp only at hstatus htasks hlength htag htail ⊢
    subst status
    subst tasks
    simpa [compactClosedSyntaxParserStep, compactClosedSyntaxRunningStep,
      compactClosedSyntaxTaskTokenStep, compactClosedTermTokenStep,
      compactSyntaxFailure, hlength, htag] using htail

theorem exists_compactUnifiedParserClosedStepFormula_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hwell : CompactSyntaxTaskStackFieldsWellFormed current.2.1) :
    (∃ witness,
        compactUnifiedParserClosedStepRowsDef.val.Evalb
          (compactUnifiedParserSyntaxStepFormulaEnvironment
            tokenTable width tokenCount currentCoordinates nextCoordinates
              witness)) ↔
      next = compactClosedSyntaxParserStep current := by
  simp only [compactUnifiedParserClosedStepRowsDef_spec]
  exact ⟨compactUnifiedParserClosedStepRows_sound hcurrent hnext,
    compactUnifiedParserClosedStepRows_complete hcurrent hnext hwell⟩

#print axioms compactUnifiedParserClosedFreeVariableFailureRowsDef_spec
#print axioms compactUnifiedParserClosedFreeVariableFailureRowsDef_sigmaZero
#print axioms compactUnifiedParserClosedStepRowsDef_spec
#print axioms compactUnifiedParserClosedStepRowsDef_sigmaZero
#print axioms compactUnifiedParserClosedFreeVariableFailureRows_sound
#print axioms compactUnifiedParserClosedFreeVariableFailureRows_complete
#print axioms compactUnifiedParserClosedStepRows_sound
#print axioms compactUnifiedParserClosedStepRows_complete
#print axioms compactClosedSyntaxParserStep_preserves_task_fields_well_formed
#print axioms exists_compactUnifiedParserClosedStepFormula_iff

end FoundationCompactNumericListedDirectParserClosedStepFormula
