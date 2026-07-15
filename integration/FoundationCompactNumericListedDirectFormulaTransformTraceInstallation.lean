import integration.FoundationCompactNumericListedDirectFormulaTransformStepFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformStateAtRows

/-!
# Installation of the shared formula-transform graph into finite traces

The executable syntax parser preserves the task-field invariant required by
the complete direct step graph.  Consequently every row of a canonical local
formula-transform trace satisfies the invariant, and every adjacent pair can
be interpreted by the same checked step relation.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformTraceInstallation

open FoundationCompactArithmeticSymbolCode
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepFormula

private theorem taskStackFieldsWellFormed_cons_term
    (binderArity : Nat) (tail : List CompactSyntaxTask)
    (htail : CompactSyntaxTaskStackFieldsWellFormed tail) :
    CompactSyntaxTaskStackFieldsWellFormed
      (compactTermTask binderArity :: tail) := by
  intro task htask
  simp only [List.mem_cons] at htask
  rcases htask with rfl | htask
  · simp [CompactSyntaxTaskFieldsWellFormed, compactTermTask]
  · exact htail task htask

private theorem taskStackFieldsWellFormed_cons_formula
    (binderArity : Nat) (tail : List CompactSyntaxTask)
    (htail : CompactSyntaxTaskStackFieldsWellFormed tail) :
    CompactSyntaxTaskStackFieldsWellFormed
      (compactFormulaTask binderArity :: tail) := by
  intro task htask
  simp only [List.mem_cons] at htask
  rcases htask with rfl | htask
  · simp [CompactSyntaxTaskFieldsWellFormed, compactFormulaTask]
  · exact htail task htask

private theorem taskStackFieldsWellFormed_cons_repeat
    (binderArity repeatCount : Nat) (tail : List CompactSyntaxTask)
    (htail : CompactSyntaxTaskStackFieldsWellFormed tail) :
    CompactSyntaxTaskStackFieldsWellFormed
      (compactRepeatTermTask binderArity repeatCount :: tail) := by
  intro task htask
  simp only [List.mem_cons] at htask
  rcases htask with rfl | htask
  · simp [CompactSyntaxTaskFieldsWellFormed, compactRepeatTermTask]
  · exact htail task htask

private theorem compactTermTokenStep_preserves_task_fields_well_formed
    (binderArity : Nat) (tokens : List Nat) (tail : List CompactSyntaxTask)
    (htail : CompactSyntaxTaskStackFieldsWellFormed tail) :
    CompactSyntaxTaskStackFieldsWellFormed
      (compactTermTokenStep (binderArity, tokens, tail)).2.1 := by
  by_cases hlengthTwo : 2 <= tokens.length
  · by_cases htagZero : compactTokenAt 0 tokens = 0
    · by_cases hbound : compactTokenAt 1 tokens < binderArity
      · simpa [compactTermTokenStep, hlengthTwo, htagZero, hbound,
          compactSyntaxContinue] using htail
      · simpa [compactTermTokenStep, hlengthTwo, htagZero, hbound,
          compactSyntaxFailure] using htail
    · by_cases htagOne : compactTokenAt 0 tokens = 1
      · simpa [compactTermTokenStep, hlengthTwo, htagZero, htagOne,
          compactSyntaxContinue] using htail
      · by_cases htagTwo : compactTokenAt 0 tokens = 2
        · by_cases hlengthThree : 3 <= tokens.length
          · by_cases hvalid : ArithmeticFuncCodeValid
                (compactTokenAt 1 tokens) (compactTokenAt 2 tokens)
            · have hpush := taskStackFieldsWellFormed_cons_repeat
                binderArity (compactTokenAt 1 tokens) tail htail
              simpa [compactTermTokenStep, hlengthTwo, htagZero, htagOne,
                htagTwo, hlengthThree, hvalid, compactSyntaxContinue] using
                hpush
            · simpa [compactTermTokenStep, hlengthTwo, htagZero, htagOne,
                htagTwo, hlengthThree, hvalid, compactSyntaxFailure] using
                htail
          · simpa [compactTermTokenStep, hlengthTwo, htagZero, htagOne,
              htagTwo, hlengthThree, compactSyntaxFailure] using htail
        · simpa [compactTermTokenStep, hlengthTwo, htagZero, htagOne,
            htagTwo, compactSyntaxFailure] using htail
  · simpa [compactTermTokenStep, hlengthTwo, compactSyntaxFailure] using
      htail

private theorem compactFormulaTokenStep_preserves_task_fields_well_formed
    (binderArity : Nat) (tokens : List Nat) (tail : List CompactSyntaxTask)
    (htail : CompactSyntaxTaskStackFieldsWellFormed tail) :
    CompactSyntaxTaskStackFieldsWellFormed
      (compactFormulaTokenStep (binderArity, tokens, tail)).2.1 := by
  by_cases hlengthOne : 1 <= tokens.length
  · by_cases htagZero : compactTokenAt 0 tokens = 0
    · by_cases hlengthThree : 3 <= tokens.length
      · by_cases hvalid : ArithmeticRelCodeValid
            (compactTokenAt 1 tokens) (compactTokenAt 2 tokens)
        · have hpush := taskStackFieldsWellFormed_cons_repeat
              binderArity (compactTokenAt 1 tokens) tail htail
          simpa [compactFormulaTokenStep, hlengthOne, htagZero,
            hlengthThree, hvalid, compactSyntaxContinue] using hpush
        · simpa [compactFormulaTokenStep, hlengthOne, htagZero,
            hlengthThree, hvalid, compactSyntaxFailure] using htail
      · simpa [compactFormulaTokenStep, hlengthOne, htagZero,
          hlengthThree, compactSyntaxFailure] using htail
    · by_cases htagOne : compactTokenAt 0 tokens = 1
      · by_cases hlengthThree : 3 <= tokens.length
        · by_cases hvalid : ArithmeticRelCodeValid
              (compactTokenAt 1 tokens) (compactTokenAt 2 tokens)
          · have hpush := taskStackFieldsWellFormed_cons_repeat
                binderArity (compactTokenAt 1 tokens) tail htail
            simpa [compactFormulaTokenStep, hlengthOne, htagZero, htagOne,
              hlengthThree, hvalid, compactSyntaxContinue] using hpush
          · simpa [compactFormulaTokenStep, hlengthOne, htagZero, htagOne,
              hlengthThree, hvalid, compactSyntaxFailure] using htail
        · simpa [compactFormulaTokenStep, hlengthOne, htagZero, htagOne,
            hlengthThree, compactSyntaxFailure] using htail
      · by_cases htagTwo : compactTokenAt 0 tokens = 2
        · simpa [compactFormulaTokenStep, hlengthOne, htagZero, htagOne,
            htagTwo, compactSyntaxContinue] using htail
        · by_cases htagThree : compactTokenAt 0 tokens = 3
          · simpa [compactFormulaTokenStep, hlengthOne, htagZero, htagOne,
              htagTwo, htagThree, compactSyntaxContinue] using htail
          · by_cases htagFour : compactTokenAt 0 tokens = 4
            · have hpush := taskStackFieldsWellFormed_cons_formula
                  binderArity tail htail
              have hpushTwo := taskStackFieldsWellFormed_cons_formula
                  binderArity _ hpush
              simpa [compactFormulaTokenStep, hlengthOne, htagZero, htagOne,
                htagTwo, htagThree, htagFour, compactSyntaxContinue] using
                  hpushTwo
            · by_cases htagFive : compactTokenAt 0 tokens = 5
              · have hpush := taskStackFieldsWellFormed_cons_formula
                    binderArity tail htail
                have hpushTwo := taskStackFieldsWellFormed_cons_formula
                    binderArity _ hpush
                simpa [compactFormulaTokenStep, hlengthOne, htagZero,
                  htagOne, htagTwo, htagThree, htagFour, htagFive,
                  compactSyntaxContinue] using hpushTwo
              · by_cases htagSix : compactTokenAt 0 tokens = 6
                · have hpush := taskStackFieldsWellFormed_cons_formula
                      (binderArity + 1) tail htail
                  simpa [compactFormulaTokenStep, hlengthOne, htagZero,
                    htagOne, htagTwo, htagThree, htagFour, htagFive,
                    htagSix, compactSyntaxContinue] using hpush
                · by_cases htagSeven : compactTokenAt 0 tokens = 7
                  · have hpush := taskStackFieldsWellFormed_cons_formula
                        (binderArity + 1) tail htail
                    simpa [compactFormulaTokenStep, hlengthOne, htagZero,
                      htagOne, htagTwo, htagThree, htagFour, htagFive,
                      htagSix, htagSeven, compactSyntaxContinue] using hpush
                  · simpa [compactFormulaTokenStep, hlengthOne, htagZero,
                      htagOne, htagTwo, htagThree, htagFour, htagFive,
                      htagSix, htagSeven, compactSyntaxFailure] using htail
  · simpa [compactFormulaTokenStep, hlengthOne, compactSyntaxFailure] using
      htail

private theorem compactRepeatTermTokenStep_preserves_task_fields_well_formed
    (binderArity repeatCount : Nat) (tokens : List Nat)
    (tail : List CompactSyntaxTask)
    (htail : CompactSyntaxTaskStackFieldsWellFormed tail) :
    CompactSyntaxTaskStackFieldsWellFormed
      (compactRepeatTermTokenStep
        ((2, binderArity, repeatCount), tokens, tail)).2.1 := by
  by_cases hzero : repeatCount = 0
  · simpa [compactRepeatTermTokenStep, hzero, compactSyntaxContinue] using
      htail
  · have hrepeat := taskStackFieldsWellFormed_cons_repeat
        binderArity (repeatCount - 1) tail htail
    have hterm := taskStackFieldsWellFormed_cons_term
        binderArity _ hrepeat
    simpa [compactRepeatTermTokenStep, hzero, compactSyntaxContinue] using
      hterm

private theorem compactSyntaxTaskTokenStep_preserves_task_fields_well_formed
    (task : CompactSyntaxTask) (tokens : List Nat)
    (tail : List CompactSyntaxTask)
    (htail : CompactSyntaxTaskStackFieldsWellFormed tail) :
    CompactSyntaxTaskStackFieldsWellFormed
      (compactSyntaxTaskTokenStep (task, tokens, tail)).2.1 := by
  rcases task with ⟨kind, binderArity, repeatCount⟩
  by_cases hzero : kind = 0
  · simpa [compactSyntaxTaskTokenStep, hzero] using
      compactTermTokenStep_preserves_task_fields_well_formed
        binderArity tokens tail htail
  · by_cases hone : kind = 1
    · simpa [compactSyntaxTaskTokenStep, hzero, hone] using
        compactFormulaTokenStep_preserves_task_fields_well_formed
          binderArity tokens tail htail
    · by_cases htwo : kind = 2
      · simpa [compactSyntaxTaskTokenStep, hzero, hone, htwo] using
          compactRepeatTermTokenStep_preserves_task_fields_well_formed
            binderArity repeatCount tokens tail htail
      · simpa [compactSyntaxTaskTokenStep, hzero, hone, htwo,
          compactSyntaxFailure] using htail

theorem compactSyntaxParserStep_preserves_task_fields_well_formed
    (state : CompactSyntaxParserState)
    (hwell : CompactSyntaxTaskStackFieldsWellFormed state.2.1) :
    CompactSyntaxTaskStackFieldsWellFormed
      (compactSyntaxParserStep state).2.1 := by
  rcases state with ⟨tokens, tasks, status⟩
  cases status with
  | some result =>
      simpa [compactSyntaxParserStep] using hwell
  | none =>
      cases tasks with
      | nil =>
          simp [compactSyntaxParserStep, compactSyntaxRunningStep,
            CompactSyntaxTaskStackFieldsWellFormed]
      | cons task tail =>
          have htail : CompactSyntaxTaskStackFieldsWellFormed tail := by
            intro nextTask hnextTask
            exact hwell nextTask (by simp [hnextTask])
          simpa [compactSyntaxParserStep, compactSyntaxRunningStep] using
            compactSyntaxTaskTokenStep_preserves_task_fields_well_formed
              task tokens tail htail

theorem compactFormulaTransformStep_preserves_task_fields_well_formed
    (control : CompactFormulaTransformControl)
    (state : CompactFormulaTransformState)
    (hwell : CompactSyntaxTaskStackFieldsWellFormed state.1.2.1) :
    CompactSyntaxTaskStackFieldsWellFormed
      (compactFormulaTransformStep control state).1.2.1 := by
  rcases control with ⟨mode, witness⟩
  have hparser :=
    compactSyntaxParserStep_preserves_task_fields_well_formed state.1 hwell
  rw [compactFormulaTransformStep_parser]
  exact hparser

theorem compactFormulaTransformStateAt_task_fields_well_formed
    (control : CompactFormulaTransformControl)
    (start : CompactFormulaTransformState)
    (hstart : CompactSyntaxTaskStackFieldsWellFormed start.1.2.1)
    (stepIndex : Nat) :
    CompactSyntaxTaskStackFieldsWellFormed
      (compactFormulaTransformStateAt control start stepIndex).1.2.1 := by
  induction stepIndex with
  | zero =>
      simpa [compactFormulaTransformStateAt] using hstart
  | succ stepIndex ih =>
      rw [compactFormulaTransformStateAt,
        Function.iterate_succ_apply']
      exact compactFormulaTransformStep_preserves_task_fields_well_formed
        control _ ih

theorem CompactFormulaTransformLocalTraceValid.getI_eq_stateAt
    {control : CompactFormulaTransformControl} {fuel : Nat}
    {start : CompactFormulaTransformState}
    {states : List CompactFormulaTransformState}
    (hvalid : CompactFormulaTransformLocalTraceValid
      control fuel start states)
    {stepIndex : Nat} (hstepIndex : stepIndex ≤ fuel) :
    states.getI stepIndex =
      compactFormulaTransformStateAt control start stepIndex := by
  have hstate := hvalid.stateAt hstepIndex
  unfold compactFormulaTransformTraceState? at hstate
  rw [List.getI_eq_getElem?_getD, hstate]
  rfl

theorem CompactFormulaTransformLocalTraceValid.getI_step
    {control : CompactFormulaTransformControl} {fuel : Nat}
    {start : CompactFormulaTransformState}
    {states : List CompactFormulaTransformState}
    (hvalid : CompactFormulaTransformLocalTraceValid
      control fuel start states)
    {stepIndex : Nat} (hstepIndex : stepIndex < fuel) :
    states.getI (stepIndex + 1) =
      compactFormulaTransformStep control (states.getI stepIndex) := by
  rw [CompactFormulaTransformLocalTraceValid.getI_eq_stateAt
      hvalid (by omega),
    CompactFormulaTransformLocalTraceValid.getI_eq_stateAt
      hvalid (Nat.le_of_lt hstepIndex)]
  simp [compactFormulaTransformStateAt,
    Function.iterate_succ_apply']

theorem CompactFormulaTransformLocalTraceValid.getI_task_fields_well_formed
    {control : CompactFormulaTransformControl} {fuel : Nat}
    {start : CompactFormulaTransformState}
    {states : List CompactFormulaTransformState}
    (hvalid : CompactFormulaTransformLocalTraceValid
      control fuel start states)
    (hstart : CompactSyntaxTaskStackFieldsWellFormed start.1.2.1)
    {stepIndex : Nat} (hstepIndex : stepIndex ≤ fuel) :
    CompactSyntaxTaskStackFieldsWellFormed
      (states.getI stepIndex).1.2.1 := by
  rw [CompactFormulaTransformLocalTraceValid.getI_eq_stateAt
    hvalid hstepIndex]
  exact compactFormulaTransformStateAt_task_fields_well_formed
    control start hstart stepIndex

@[simp] theorem compactFormulaTransformInitialState_task_fields_well_formed
    (binderArity : Nat) (tokens : List Nat) :
    CompactSyntaxTaskStackFieldsWellFormed
      (compactFormulaTransformInitialState binderArity tokens).1.2.1 := by
  simp [compactFormulaTransformInitialState,
    compactFormulaParserInitialState, compactFormulaTask,
    CompactSyntaxTaskStackFieldsWellFormed,
    CompactSyntaxTaskFieldsWellFormed]

/-- Every adjacent pair in the typed trace is exposed through two exact
state-table rows and the complete direct transform-step graph. -/
def CompactFormulaTransformStateListAdjacentStepRows
    (tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat)
    (states : List CompactFormulaTransformState) : Prop :=
  ∀ index < states.length - 1,
    ∃ currentCoordinates currentSize nextCoordinates nextSize
        stepWitness consumedCount mappedHead,
      CompactFormulaTransformStateAtRows
          tokenTable width tokenCount stateBoundary states.length index
            currentCoordinates currentSize ∧
        CompactFormulaTransformStateAtRows
          tokenTable width tokenCount stateBoundary states.length (index + 1)
            nextCoordinates nextSize ∧
        CompactFormulaTransformStepRows
          tokenTable width tokenCount currentCoordinates nextCoordinates
            mode stepWitness consumedCount mappedHead
              witnessStart witnessFinish witnessCount ∧
        CompactBinaryNatStreamStatusDirectLayout
          tokenTable width tokenCount currentCoordinates.parserTasksFinish
            currentCoordinates.parserFinish (states.getI index).1.2.2 ∧
        CompactBinaryNatStreamStatusDirectLayout
          tokenTable width tokenCount nextCoordinates.parserTasksFinish
            nextCoordinates.parserFinish (states.getI (index + 1)).1.2.2

theorem stateListAdjacentStepRows_of_localTrace
    {tokenTable width tokenCount stateBoundary fuel mode
      witnessStart witnessFinish witnessCount : Nat}
    {witness : List Nat} {start : CompactFormulaTransformState}
    {states : List CompactFormulaTransformState}
    (hrows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hwitnessCount : witnessCount = witness.length)
    (hvalid : CompactFormulaTransformLocalTraceValid
      (mode, witness) fuel start states)
    (hstart : CompactSyntaxTaskStackFieldsWellFormed start.1.2.1) :
    CompactFormulaTransformStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states := by
  intro index hindex
  have hstepIndex : index < fuel := by
    rw [hvalid.1] at hindex
    omega
  have hcurrentIndex : index < states.length := by
    rw [hvalid.1]
    omega
  have hnextIndex : index + 1 < states.length := by
    rw [hvalid.1]
    omega
  rcases exists_compactFormulaTransformStateAtRows_with_fixed_layout
      hrows hcurrentIndex with
    ⟨currentCoordinates, currentSize, hcurrentRows, hcurrentFixed⟩
  rcases exists_compactFormulaTransformStateAtRows_with_fixed_layout
      hrows hnextIndex with
    ⟨nextCoordinates, nextSize, hnextRows, hnextFixed⟩
  have hwell : CompactSyntaxTaskStackFieldsWellFormed
      (states.getI index).1.2.1 :=
    CompactFormulaTransformLocalTraceValid.getI_task_fields_well_formed
      hvalid hstart (Nat.le_of_lt hstepIndex)
  have hstep : states.getI (index + 1) =
      compactFormulaTransformStep (mode, witness) (states.getI index) :=
    CompactFormulaTransformLocalTraceValid.getI_step hvalid hstepIndex
  rcases (exists_compactFormulaTransformStepRows_iff_step
      hcurrentFixed hnextFixed hwitness hwitnessCount hwell).mpr hstep with
    ⟨stepWitness, consumedCount, mappedHead, hstepRows⟩
  exact ⟨currentCoordinates, currentSize,
    nextCoordinates, nextSize, stepWitness, consumedCount, mappedHead,
    hcurrentRows, hnextRows, hstepRows,
    hcurrentFixed.parserLayout.statusLayout,
    hnextFixed.parserLayout.statusLayout⟩

theorem stateListAdjacentStepRows_of_initialLocalTrace
    {tokenTable width tokenCount stateBoundary fuel mode
      witnessStart witnessFinish witnessCount binderArity : Nat}
    {witness tokens : List Nat}
    {states : List CompactFormulaTransformState}
    (hrows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hwitnessCount : witnessCount = witness.length)
    (hvalid : CompactFormulaTransformLocalTraceValid
      (mode, witness) fuel
        (compactFormulaTransformInitialState binderArity tokens) states) :
    CompactFormulaTransformStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states := by
  exact stateListAdjacentStepRows_of_localTrace
    hrows hwitness hwitnessCount hvalid
      (compactFormulaTransformInitialState_task_fields_well_formed
        binderArity tokens)

#print axioms compactSyntaxParserStep_preserves_task_fields_well_formed
#print axioms compactFormulaTransformStep_preserves_task_fields_well_formed
#print axioms compactFormulaTransformStateAt_task_fields_well_formed
#print axioms CompactFormulaTransformLocalTraceValid.getI_eq_stateAt
#print axioms CompactFormulaTransformLocalTraceValid.getI_step
#print axioms CompactFormulaTransformLocalTraceValid.getI_task_fields_well_formed
#print axioms compactFormulaTransformInitialState_task_fields_well_formed
#print axioms stateListAdjacentStepRows_of_localTrace
#print axioms stateListAdjacentStepRows_of_initialLocalTrace

end FoundationCompactNumericListedDirectFormulaTransformTraceInstallation
