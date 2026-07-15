import integration.FoundationCompactNumericListedDirectParserDoneFormula
import integration.FoundationCompactNumericListedDirectParserEmptyFormula
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFormula
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula
import integration.FoundationCompactNumericListedDirectParserSyntaxInvalidFormula
import integration.FoundationCompactNumericListedDirectParserStepCases

/-!
# One bounded formula for every ordinary syntax-parser step

Seven shared witness slots cover the finished, empty-stack, repeated-term,
term, formula, and invalid-kind branches.  Completeness is stated with the
explicit task-field invariant used by every canonical syntax-parser run.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxStepFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStepCases
open FoundationCompactNumericListedDirectParserDoneRows
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserEmptyRows
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula
open FoundationCompactNumericListedDirectParserSyntaxInvalidRows
open FoundationCompactNumericListedDirectParserSyntaxInvalidFormula

structure CompactUnifiedParserSyntaxStepWitnessCoordinates where
  slot0 : Nat
  slot1 : Nat
  slot2 : Nat
  slot3 : Nat
  slot4 : Nat
  slot5 : Nat
  slot6 : Nat

def CompactUnifiedParserSyntaxStepWitnessCoordinates.done
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) :
    CompactUnifiedParserDoneWitnessCoordinates :=
  compactUnifiedParserDoneWitnessCoordinatesOf
    witness.slot0 witness.slot1 witness.slot2 witness.slot3
    witness.slot4 witness.slot5 witness.slot6

def CompactUnifiedParserSyntaxStepWitnessCoordinates.empty
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) :
    CompactUnifiedParserEmptyWitnessCoordinates :=
  compactUnifiedParserEmptyWitnessCoordinatesOf
    witness.slot0 witness.slot1 witness.slot2

def CompactUnifiedParserSyntaxStepWitnessCoordinates.repeat
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) :
    CompactSyntaxRepeatTaskWitnessCoordinates :=
  compactSyntaxRepeatTaskWitnessCoordinatesOf
    witness.slot2 witness.slot3 witness.slot4 witness.slot5

def CompactUnifiedParserSyntaxStepWitnessCoordinates.term
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) :
    CompactSyntaxTermTaskWitnessCoordinates :=
  compactSyntaxTermTaskWitnessCoordinatesOf
    witness.slot1 witness.slot2 witness.slot3 witness.slot4
    witness.slot5 witness.slot6

def CompactUnifiedParserSyntaxStepWitnessCoordinates.formula
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) :
    CompactSyntaxFormulaTaskWitnessCoordinates :=
  compactSyntaxFormulaTaskWitnessCoordinatesOf
    witness.slot1 witness.slot2 witness.slot3 witness.slot4
    witness.slot5 witness.slot6

def CompactUnifiedParserSyntaxStepWitnessCoordinates.invalid
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) :
    CompactSyntaxInvalidTaskWitnessCoordinates :=
  compactSyntaxInvalidTaskWitnessCoordinatesOf
    witness.slot0 witness.slot1 witness.slot2 witness.slot3
    witness.slot4 witness.slot5

def CompactUnifiedParserSyntaxStepWitnessCoordinates.ofDone
    (witness : CompactUnifiedParserDoneWitnessCoordinates) :
    CompactUnifiedParserSyntaxStepWitnessCoordinates :=
  { slot0 := witness.sourceOutputStart
    slot1 := witness.sourceOutputBoundary
    slot2 := witness.sourceOutputBoundarySize
    slot3 := witness.targetOutputStart
    slot4 := witness.targetOutputBoundary
    slot5 := witness.targetOutputBoundarySize
    slot6 := witness.outputCount }

def CompactUnifiedParserSyntaxStepWitnessCoordinates.ofEmpty
    (witness : CompactUnifiedParserEmptyWitnessCoordinates) :
    CompactUnifiedParserSyntaxStepWitnessCoordinates :=
  { slot0 := witness.targetOutputStart
    slot1 := witness.targetOutputBoundary
    slot2 := witness.targetOutputBoundarySize
    slot3 := 0
    slot4 := 0
    slot5 := 0
    slot6 := 0 }

def CompactUnifiedParserSyntaxStepWitnessCoordinates.ofRepeat
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) :
    CompactUnifiedParserSyntaxStepWitnessCoordinates :=
  { slot0 := binderArity
    slot1 := repeatCount
    slot2 := witness.tailBoundary
    slot3 := witness.tailCount
    slot4 := witness.tailBoundarySize
    slot5 := witness.decrementedCount
    slot6 := 0 }

def CompactUnifiedParserSyntaxStepWitnessCoordinates.ofTerm
    (binderArity : Nat) (witness : CompactSyntaxTermTaskWitnessCoordinates) :
    CompactUnifiedParserSyntaxStepWitnessCoordinates :=
  { slot0 := binderArity
    slot1 := witness.tailBoundary
    slot2 := witness.tailCount
    slot3 := witness.tailBoundarySize
    slot4 := witness.tag
    slot5 := witness.argument
    slot6 := witness.functionCode }

def CompactUnifiedParserSyntaxStepWitnessCoordinates.ofFormula
    (binderArity : Nat) (witness : CompactSyntaxFormulaTaskWitnessCoordinates) :
    CompactUnifiedParserSyntaxStepWitnessCoordinates :=
  { slot0 := binderArity
    slot1 := witness.tailBoundary
    slot2 := witness.tailCount
    slot3 := witness.tailBoundarySize
    slot4 := witness.tag
    slot5 := witness.relationArity
    slot6 := witness.relationCode }

def CompactUnifiedParserSyntaxStepWitnessCoordinates.ofInvalid
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates) :
    CompactUnifiedParserSyntaxStepWitnessCoordinates :=
  { slot0 := witness.tailBoundary
    slot1 := witness.tailCount
    slot2 := witness.tailBoundarySize
    slot3 := witness.kind
    slot4 := witness.binderArity
    slot5 := witness.repeatCount
    slot6 := 0 }

@[simp] theorem CompactUnifiedParserSyntaxStepWitnessCoordinates.done_ofDone
    (witness : CompactUnifiedParserDoneWitnessCoordinates) :
    (CompactUnifiedParserSyntaxStepWitnessCoordinates.ofDone witness).done =
      witness := by
  cases witness
  rfl

@[simp] theorem CompactUnifiedParserSyntaxStepWitnessCoordinates.empty_ofEmpty
    (witness : CompactUnifiedParserEmptyWitnessCoordinates) :
    (CompactUnifiedParserSyntaxStepWitnessCoordinates.ofEmpty witness).empty =
      witness := by
  cases witness
  rfl

@[simp] theorem CompactUnifiedParserSyntaxStepWitnessCoordinates.repeat_ofRepeat
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) :
    (CompactUnifiedParserSyntaxStepWitnessCoordinates.ofRepeat
      binderArity repeatCount witness).repeat = witness := by
  cases witness
  rfl

@[simp] theorem CompactUnifiedParserSyntaxStepWitnessCoordinates.term_ofTerm
    (binderArity : Nat) (witness : CompactSyntaxTermTaskWitnessCoordinates) :
    (CompactUnifiedParserSyntaxStepWitnessCoordinates.ofTerm
      binderArity witness).term = witness := by
  cases witness
  rfl

@[simp] theorem CompactUnifiedParserSyntaxStepWitnessCoordinates.slot0_ofTerm
    (binderArity : Nat) (witness : CompactSyntaxTermTaskWitnessCoordinates) :
    (CompactUnifiedParserSyntaxStepWitnessCoordinates.ofTerm
      binderArity witness).slot0 = binderArity := rfl

@[simp] theorem CompactUnifiedParserSyntaxStepWitnessCoordinates.formula_ofFormula
    (binderArity : Nat) (witness : CompactSyntaxFormulaTaskWitnessCoordinates) :
    (CompactUnifiedParserSyntaxStepWitnessCoordinates.ofFormula
      binderArity witness).formula = witness := by
  cases witness
  rfl

@[simp] theorem CompactUnifiedParserSyntaxStepWitnessCoordinates.slot0_ofFormula
    (binderArity : Nat) (witness : CompactSyntaxFormulaTaskWitnessCoordinates) :
    (CompactUnifiedParserSyntaxStepWitnessCoordinates.ofFormula
      binderArity witness).slot0 = binderArity := rfl

@[simp] theorem CompactUnifiedParserSyntaxStepWitnessCoordinates.slot0_ofRepeat
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) :
    (CompactUnifiedParserSyntaxStepWitnessCoordinates.ofRepeat
      binderArity repeatCount witness).slot0 = binderArity := rfl

@[simp] theorem CompactUnifiedParserSyntaxStepWitnessCoordinates.slot1_ofRepeat
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) :
    (CompactUnifiedParserSyntaxStepWitnessCoordinates.ofRepeat
      binderArity repeatCount witness).slot1 = repeatCount := rfl

@[simp] theorem CompactUnifiedParserSyntaxStepWitnessCoordinates.invalid_ofInvalid
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates) :
    (CompactUnifiedParserSyntaxStepWitnessCoordinates.ofInvalid witness).invalid =
      witness := by
  cases witness
  rfl

def CompactUnifiedParserSyntaxStepRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) : Prop :=
  CompactUnifiedParserDoneGraphRows tokenTable width tokenCount current next
      witness.done ∨
    CompactUnifiedParserEmptyGraphRows tokenTable width tokenCount current next
      witness.empty ∨
    CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount current next
      witness.slot0 witness.slot1 witness.repeat ∨
    CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount current next
      witness.slot0 witness.term ∨
    CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount current next
      witness.slot0 witness.formula ∨
    CompactUnifiedParserSyntaxInvalidRows tokenTable width tokenCount current next
      witness.invalid

def compactUnifiedParserSyntaxStepRowsDef : 𝚺₀.Semisentence 26 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot0 slot1 slot2 slot3 slot4 slot5 slot6.
    !(compactUnifiedParserDoneGraphRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot0 slot1 slot2 slot3 slot4 slot5 slot6 ∨
    !(compactUnifiedParserEmptyGraphRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot0 slot1 slot2 ∨
    !(compactUnifiedParserSyntaxRepeatRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot0 slot1 slot2 slot3 slot4 slot5 ∨
    !(compactUnifiedParserSyntaxTermRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot0 slot1 slot2 slot3 slot4 slot5 slot6 ∨
    !(compactUnifiedParserSyntaxFormulaRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot0 slot1 slot2 slot3 slot4 slot5 slot6 ∨
    !(compactUnifiedParserSyntaxInvalidRowsDef)
      tokenTable width tokenCount
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      slot0 slot1 slot2 slot3 slot4 slot5”

def compactUnifiedParserSyntaxStepFormulaEnvironment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) : Fin 26 → Nat :=
  ![tokenTable, width, tokenCount,
    current.start, current.finish, current.tokensFinish, current.tasksFinish,
    current.tokensBoundary, current.tokensCount,
    current.tasksBoundary, current.tasksCount,
    next.start, next.finish, next.tokensFinish, next.tasksFinish,
    next.tokensBoundary, next.tokensCount, next.tasksBoundary, next.tasksCount,
    witness.slot0, witness.slot1, witness.slot2, witness.slot3,
    witness.slot4, witness.slot5, witness.slot6]

@[simp] theorem compactUnifiedParserSyntaxStepRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) :
    compactUnifiedParserSyntaxStepRowsDef.val.Evalb
        (compactUnifiedParserSyntaxStepFormulaEnvironment
          tokenTable width tokenCount current next witness) ↔
      CompactUnifiedParserSyntaxStepRows
        tokenTable width tokenCount current next witness := by
  let env := compactUnifiedParserSyntaxStepFormulaEnvironment
    tokenTable width tokenCount current next witness
  change compactUnifiedParserSyntaxStepRowsDef.val.Evalb env ↔ _
  have hdoneEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #3, #4, #5, #6, #7,
          #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
          #19, #20, #21, #22, #23, #24, #25]) =
        compactUnifiedParserDoneFormulaEnvironmentOf
          tokenTable width tokenCount current next witness.done := by
    funext index
    fin_cases index <;> rfl
  have hemptyEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #3, #4, #5, #6, #7,
          #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
          #19, #20, #21]) =
        compactUnifiedParserEmptyFormulaEnvironmentOf
          tokenTable width tokenCount current next witness.empty := by
    funext index
    fin_cases index <;> rfl
  have hrepeatEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #3, #4, #5, #6, #7,
          #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
          #19, #20, #21, #22, #23, #24]) =
        compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf
          tokenTable width tokenCount current next witness.slot0 witness.slot1
            witness.repeat := by
    funext index
    fin_cases index <;> rfl
  have htermEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #3, #4, #5, #6, #7,
          #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
          #19, #20, #21, #22, #23, #24, #25]) =
        compactUnifiedParserSyntaxTermFormulaEnvironment
          tokenTable width tokenCount current next witness.slot0 witness.term := by
    funext index
    fin_cases index <;> rfl
  have hformulaEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #3, #4, #5, #6, #7,
          #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
          #19, #20, #21, #22, #23, #24, #25]) =
        compactUnifiedParserSyntaxFormulaTaskEnvironment
          tokenTable width tokenCount current next witness.slot0
            witness.formula := by
    funext index
    fin_cases index <;> rfl
  have hinvalidEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #3, #4, #5, #6, #7,
          #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
          #19, #20, #21, #22, #23, #24]) =
        compactUnifiedParserSyntaxInvalidFormulaEnvironment
          tokenTable width tokenCount current next witness.invalid := by
    funext index
    fin_cases index <;> rfl
  have hidentityEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #3, #4, #5, #6, #7,
          #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
          #19, #20, #21, #22, #23, #24, #25]) = env := by
    funext index
    fin_cases index <;> rfl
  have hdoneIdentity : env =
      compactUnifiedParserDoneFormulaEnvironmentOf
        tokenTable width tokenCount current next witness.done := by
    funext index
    fin_cases index <;> rfl
  have htermIdentity : env =
      compactUnifiedParserSyntaxTermFormulaEnvironment
        tokenTable width tokenCount current next witness.slot0 witness.term := by
    funext index
    fin_cases index <;> rfl
  have hformulaIdentity : env =
      compactUnifiedParserSyntaxFormulaTaskEnvironment
        tokenTable width tokenCount current next witness.slot0 witness.formula := by
    funext index
    fin_cases index <;> rfl
  have hdoneSpec : compactUnifiedParserDoneGraphRowsDef.val.Evalb env ↔
      CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
        current next witness.done := by
    rw [hdoneIdentity]
    exact compactUnifiedParserDoneGraphRowsDef_environmentOf_iff
      tokenTable width tokenCount current next witness.done
  have hemptySpec : compactUnifiedParserEmptyGraphRowsDef.val.Evalb
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #3, #4, #5, #6, #7,
            #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
            #19, #20, #21]) ↔
      CompactUnifiedParserEmptyGraphRows tokenTable width tokenCount
        current next witness.empty := by
    rw [hemptyEnv]
    exact compactUnifiedParserEmptyGraphRowsDef_environmentOf_iff
      tokenTable width tokenCount current next witness.empty
  have hrepeatSpec : compactUnifiedParserSyntaxRepeatRowsDef.val.Evalb
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #3, #4, #5, #6, #7,
            #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
            #19, #20, #21, #22, #23, #24]) ↔
      CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount
        current next witness.slot0 witness.slot1 witness.repeat := by
    rw [hrepeatEnv]
    exact compactUnifiedParserSyntaxRepeatRowsDef_environmentOf_iff
      tokenTable width tokenCount current next witness.slot0 witness.slot1
        witness.repeat
  have htermSpec : compactUnifiedParserSyntaxTermRowsDef.val.Evalb env ↔
      CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
        current next witness.slot0 witness.term := by
    rw [htermIdentity]
    exact compactUnifiedParserSyntaxTermRowsDef_spec
      tokenTable width tokenCount current next witness.slot0 witness.term
  have hformulaSpec : compactUnifiedParserSyntaxFormulaRowsDef.val.Evalb env ↔
      CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
        current next witness.slot0 witness.formula := by
    rw [hformulaIdentity]
    exact compactUnifiedParserSyntaxFormulaRowsDef_spec
      tokenTable width tokenCount current next witness.slot0 witness.formula
  have hinvalidSpec : compactUnifiedParserSyntaxInvalidRowsDef.val.Evalb
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #3, #4, #5, #6, #7,
            #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
            #19, #20, #21, #22, #23, #24]) ↔
      CompactUnifiedParserSyntaxInvalidRows tokenTable width tokenCount
        current next witness.invalid := by
    rw [hinvalidEnv]
    exact compactUnifiedParserSyntaxInvalidRowsDef_spec
      tokenTable width tokenCount current next witness.invalid
  simpa [compactUnifiedParserSyntaxStepRowsDef,
    CompactUnifiedParserSyntaxStepRows,
    hidentityEnv, hdoneSpec, hemptySpec, hrepeatSpec,
    htermSpec, hformulaSpec, hinvalidSpec]

theorem compactUnifiedParserSyntaxStepRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserSyntaxStepRowsDef.val := by
  simp [compactUnifiedParserSyntaxStepRowsDef]

def CompactSyntaxTaskFieldsWellFormed (task : CompactSyntaxTask) : Prop :=
  (task.1 = 0 → task.2.2 = 0) ∧
    (task.1 = 1 → task.2.2 = 0)

def CompactSyntaxTaskStackFieldsWellFormed
    (tasks : List CompactSyntaxTask) : Prop :=
  ∀ task ∈ tasks, CompactSyntaxTaskFieldsWellFormed task

theorem compactUnifiedParserSyntaxStepRows_sound
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hrows : ∃ witness, CompactUnifiedParserSyntaxStepRows
      tokenTable width tokenCount currentCoordinates nextCoordinates witness) :
    next = compactSyntaxParserStep current := by
  rcases hrows with ⟨witness, hdone | hempty | hrepeat | hterm | hformula | hinvalid⟩
  · rcases (exists_compactUnifiedParserDoneGraphRows_iff hcurrent hnext).mp
      ⟨witness.done, hdone⟩ with ⟨result, hstatus, rfl⟩
    simp [compactSyntaxParserStep, hstatus]
  · rcases (exists_compactUnifiedParserEmptyGraphRows_iff hcurrent hnext).mp
      ⟨witness.empty, hempty⟩ with ⟨hstatus, htasks, hstate⟩
    rcases current with ⟨tokens, tasks, status⟩
    simp only at hstatus htasks hstate ⊢
    subst status
    subst tasks
    simpa [compactSyntaxParserStep, compactSyntaxRunningStep] using hstate
  · rcases (compactUnifiedParserSyntaxRepeatRows_iff hcurrent hnext).mp
      ⟨witness.repeat, hrepeat⟩ with ⟨hstatus, tail, htasks, hstate⟩
    rcases current with ⟨tokens, tasks, status⟩
    simp only at hstatus htasks hstate ⊢
    subst status
    subst tasks
    simpa [compactSyntaxParserStep, compactSyntaxRunningStep,
      compactSyntaxTaskTokenStep] using hstate
  · rcases (compactUnifiedParserSyntaxTermRows_iff hcurrent hnext).mp
      ⟨witness.term, hterm⟩ with ⟨hstatus, tail, htasks, hstate⟩
    rcases current with ⟨tokens, tasks, status⟩
    simp only at hstatus htasks hstate ⊢
    subst status
    subst tasks
    simpa [compactSyntaxParserStep, compactSyntaxRunningStep,
      compactSyntaxTaskTokenStep] using hstate
  · rcases (compactUnifiedParserSyntaxFormulaRows_iff hcurrent hnext).mp
      ⟨witness.formula, hformula⟩ with ⟨hstatus, tail, htasks, hstate⟩
    rcases current with ⟨tokens, tasks, status⟩
    simp only at hstatus htasks hstate ⊢
    subst status
    subst tasks
    simpa [compactSyntaxParserStep, compactSyntaxRunningStep,
      compactSyntaxTaskTokenStep] using hstate
  · rcases (compactUnifiedParserSyntaxInvalidRows_iff hcurrent hnext).mp
      ⟨witness.invalid, hinvalid⟩ with
        ⟨hstatus, kind, binderArity, repeatCount, tail,
          htasks, hzero, hone, htwo, hstate⟩
    rcases current with ⟨tokens, tasks, status⟩
    simp only at hstatus htasks hstate ⊢
    subst status
    subst tasks
    simpa [compactSyntaxParserStep, compactSyntaxRunningStep,
      compactSyntaxTaskTokenStep, hzero, hone, htwo] using hstate

theorem compactUnifiedParserSyntaxStepRows_complete
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hwell : CompactSyntaxTaskStackFieldsWellFormed current.2.1)
    (hstep : next = compactSyntaxParserStep current) :
    ∃ witness, CompactUnifiedParserSyntaxStepRows
      tokenTable width tokenCount currentCoordinates nextCoordinates witness := by
  have hcases := (compactSyntaxParserStep_cases_iff current next).mpr hstep
  rcases hcases with hdone | hempty | htask
  · have hdoneCase : CompactUnifiedParserStepDoneCase current next := by
      rcases hstatus : current.2.2 with _ | result
      · simp [hstatus] at hdone
      · exact ⟨result, hstatus, hdone.2⟩
    rcases (exists_compactUnifiedParserDoneGraphRows_iff hcurrent hnext).mpr
      hdoneCase with ⟨doneWitness, hdoneRows⟩
    exact ⟨CompactUnifiedParserSyntaxStepWitnessCoordinates.ofDone doneWitness,
      Or.inl (by simpa using hdoneRows)⟩
  · rcases (exists_compactUnifiedParserEmptyGraphRows_iff hcurrent hnext).mpr
      hempty with ⟨emptyWitness, hemptyRows⟩
    exact ⟨CompactUnifiedParserSyntaxStepWitnessCoordinates.ofEmpty emptyWitness,
      Or.inr (Or.inl (by simpa using hemptyRows))⟩
  · rcases htask with ⟨hstatus, task, tail, htasks, htaskStep⟩
    rcases task with ⟨kind, binderArity, repeatCount⟩
    have hheadWell :
        CompactSyntaxTaskFieldsWellFormed (kind, binderArity, repeatCount) :=
      hwell _ (by rw [htasks]; simp)
    by_cases hzero : kind = 0
    · have hrepeatZero : repeatCount = 0 := hheadWell.1 hzero
      have hcase : CompactSyntaxParserTermTaskCase binderArity current next := by
        refine ⟨hstatus, tail, ?_, ?_⟩
        · simpa [hzero, hrepeatZero] using htasks
        · simpa [compactSyntaxTaskTokenStep, hzero] using htaskStep
      rcases (compactUnifiedParserSyntaxTermRows_iff hcurrent hnext).mpr hcase with
        ⟨termWitness, htermRows⟩
      exact ⟨CompactUnifiedParserSyntaxStepWitnessCoordinates.ofTerm
          binderArity termWitness,
        Or.inr (Or.inr (Or.inr (Or.inl (by
          simpa only [CompactUnifiedParserSyntaxStepWitnessCoordinates.slot0_ofTerm,
            CompactUnifiedParserSyntaxStepWitnessCoordinates.term_ofTerm] using
              htermRows))))⟩
    · by_cases hone : kind = 1
      · have hrepeatZero : repeatCount = 0 := hheadWell.2 hone
        have hcase : CompactSyntaxParserFormulaTaskCase binderArity current next := by
          refine ⟨hstatus, tail, ?_, ?_⟩
          · simpa [hone, hrepeatZero] using htasks
          · simpa [compactSyntaxTaskTokenStep, hzero, hone] using htaskStep
        rcases (compactUnifiedParserSyntaxFormulaRows_iff hcurrent hnext).mpr hcase with
          ⟨formulaWitness, hformulaRows⟩
        exact ⟨CompactUnifiedParserSyntaxStepWitnessCoordinates.ofFormula
            binderArity formulaWitness,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            (by
              simpa only [CompactUnifiedParserSyntaxStepWitnessCoordinates.slot0_ofFormula,
                CompactUnifiedParserSyntaxStepWitnessCoordinates.formula_ofFormula]
                  using hformulaRows)))))⟩
      · by_cases htwo : kind = 2
        · have hcase : CompactSyntaxParserRepeatTaskCase
              binderArity repeatCount current next := by
            refine ⟨hstatus, tail, ?_, ?_⟩
            · simpa [htwo] using htasks
            · simpa [compactSyntaxTaskTokenStep, hzero, hone, htwo] using htaskStep
          rcases (compactUnifiedParserSyntaxRepeatRows_iff hcurrent hnext).mpr hcase with
            ⟨repeatWitness, hrepeatRows⟩
          exact ⟨CompactUnifiedParserSyntaxStepWitnessCoordinates.ofRepeat
              binderArity repeatCount repeatWitness,
            Or.inr (Or.inr (Or.inl (by
              simpa only [CompactUnifiedParserSyntaxStepWitnessCoordinates.slot0_ofRepeat,
                CompactUnifiedParserSyntaxStepWitnessCoordinates.slot1_ofRepeat,
                CompactUnifiedParserSyntaxStepWitnessCoordinates.repeat_ofRepeat]
                  using hrepeatRows)))⟩
        · have hcase : CompactSyntaxParserInvalidTaskCase current next := by
            refine ⟨hstatus, kind, binderArity, repeatCount, tail,
              htasks, hzero, hone, htwo, ?_⟩
            simpa [compactSyntaxTaskTokenStep, hzero, hone, htwo] using htaskStep
          rcases (compactUnifiedParserSyntaxInvalidRows_iff hcurrent hnext).mpr hcase with
            ⟨invalidWitness, hinvalidRows⟩
          exact ⟨CompactUnifiedParserSyntaxStepWitnessCoordinates.ofInvalid
              invalidWitness,
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (by simpa using hinvalidRows)))))⟩

theorem exists_compactUnifiedParserSyntaxStepFormula_iff
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
        compactUnifiedParserSyntaxStepRowsDef.val.Evalb
          (compactUnifiedParserSyntaxStepFormulaEnvironment
            tokenTable width tokenCount currentCoordinates nextCoordinates
              witness)) ↔
      next = compactSyntaxParserStep current := by
  simp only [compactUnifiedParserSyntaxStepRowsDef_spec]
  exact ⟨compactUnifiedParserSyntaxStepRows_sound hcurrent hnext,
    compactUnifiedParserSyntaxStepRows_complete hcurrent hnext hwell⟩

#print axioms compactUnifiedParserSyntaxStepRowsDef_spec
#print axioms compactUnifiedParserSyntaxStepRowsDef_sigmaZero
#print axioms compactUnifiedParserSyntaxStepRows_sound
#print axioms compactUnifiedParserSyntaxStepRows_complete
#print axioms exists_compactUnifiedParserSyntaxStepFormula_iff

end FoundationCompactNumericListedDirectParserSyntaxStepFormula
