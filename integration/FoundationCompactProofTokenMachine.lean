import integration.FoundationCompactSyntaxTokenMachine
import integration.FoundationCompactListedProofDecoder

/-!
# Numeric token machine for compact listed proof trees

This layer consumes only lists of natural-number tokens.  Arithmetic terms and
formulas are delegated to the already checked syntax token machine; proof-tree
and sequent structure is scheduled by an explicit bounded task stack.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationCompactProofTokenMachine

open FoundationCompactSyntaxTokenMachine
open FoundationCompactListedProofDecoder

abbrev CompactProofParserTask := Nat × Nat × Nat

abbrev CompactProofParserState :=
  List Nat × List CompactProofParserTask ×
    Option (Option (List Nat))

def compactProofTask : CompactProofParserTask :=
  (3, 0, 0)

def compactProofFormulaTask (binderArity : Nat) :
    CompactProofParserTask :=
  (4, binderArity, 0)

def compactProofTermTask (binderArity : Nat) :
    CompactProofParserTask :=
  (5, binderArity, 0)

def compactProofRepeatFormulaTask (count : Nat) :
    CompactProofParserTask :=
  (6, 0, count)

def compactProofSequentTask : CompactProofParserTask :=
  (7, 0, 0)

def compactSequentListTokens
    (Gamma : List LO.FirstOrder.ArithmeticProposition) : List Nat :=
  Gamma.length :: Gamma.flatMap compactArithmeticFormulaTokens

def compactListedProofTokens :
    ListedCheckedPAProofTree -> List Nat
  | .closed Gamma formula =>
      0 :: compactSequentListTokens Gamma ++
        compactArithmeticFormulaTokens formula
  | .axm Gamma sentence =>
      1 :: compactSequentListTokens Gamma ++
        compactArithmeticFormulaTokens
          (Rewriting.emb sentence :
            LO.FirstOrder.ArithmeticProposition)
  | .verum Gamma =>
      2 :: compactSequentListTokens Gamma
  | .and Gamma leftFormula rightFormula left right =>
      3 :: compactSequentListTokens Gamma ++
        compactArithmeticFormulaTokens leftFormula ++
        compactArithmeticFormulaTokens rightFormula ++
        compactListedProofTokens left ++ compactListedProofTokens right
  | .or Gamma leftFormula rightFormula premise =>
      4 :: compactSequentListTokens Gamma ++
        compactArithmeticFormulaTokens leftFormula ++
        compactArithmeticFormulaTokens rightFormula ++
        compactListedProofTokens premise
  | .all Gamma formula premise =>
      5 :: compactSequentListTokens Gamma ++
        compactArithmeticFormulaTokens formula ++
        compactListedProofTokens premise
  | .exs Gamma formula witness premise =>
      6 :: compactSequentListTokens Gamma ++
        compactArithmeticFormulaTokens formula ++
        compactArithmeticTermTokens witness ++
        compactListedProofTokens premise
  | .wk Gamma premise =>
      7 :: compactSequentListTokens Gamma ++
        compactListedProofTokens premise
  | .shift Gamma premise =>
      8 :: compactSequentListTokens Gamma ++
        compactListedProofTokens premise
  | .cut Gamma formula left right =>
      9 :: compactSequentListTokens Gamma ++
        compactArithmeticFormulaTokens formula ++
        compactListedProofTokens left ++ compactListedProofTokens right

def compactProofSequentTaskSteps
    (Gamma : List LO.FirstOrder.ArithmeticProposition) : Nat :=
  2 + 2 * Gamma.length

def compactListedProofTaskSteps :
    ListedCheckedPAProofTree -> Nat
  | .closed Gamma _ =>
      1 + compactProofSequentTaskSteps Gamma + 1
  | .axm Gamma _ =>
      1 + compactProofSequentTaskSteps Gamma + 1
  | .verum Gamma =>
      1 + compactProofSequentTaskSteps Gamma
  | .and Gamma _ _ left right =>
      1 + compactProofSequentTaskSteps Gamma + 1 + 1 +
        compactListedProofTaskSteps left +
        compactListedProofTaskSteps right
  | .or Gamma _ _ premise =>
      1 + compactProofSequentTaskSteps Gamma + 1 + 1 +
        compactListedProofTaskSteps premise
  | .all Gamma _ premise =>
      1 + compactProofSequentTaskSteps Gamma + 1 +
        compactListedProofTaskSteps premise
  | .exs Gamma _ _ premise =>
      1 + compactProofSequentTaskSteps Gamma + 1 + 1 +
        compactListedProofTaskSteps premise
  | .wk Gamma premise =>
      1 + compactProofSequentTaskSteps Gamma +
        compactListedProofTaskSteps premise
  | .shift Gamma premise =>
      1 + compactProofSequentTaskSteps Gamma +
        compactListedProofTaskSteps premise
  | .cut Gamma _ left right =>
      1 + compactProofSequentTaskSteps Gamma + 1 +
        compactListedProofTaskSteps left +
        compactListedProofTaskSteps right

def compactProofFormulaTokenStep
    (input : Nat × List Nat × List CompactProofParserTask) :
    CompactProofParserState :=
  let binderArity := input.1
  let tokens := input.2.1
  let tasks := input.2.2
  match compactFormulaTokenParser binderArity tokens with
  | none => compactSyntaxFailure tokens tasks
  | some suffix => compactSyntaxContinue suffix tasks

def compactProofTermTokenStep
    (input : Nat × List Nat × List CompactProofParserTask) :
    CompactProofParserState :=
  let binderArity := input.1
  let tokens := input.2.1
  let tasks := input.2.2
  match compactTermTokenParser binderArity tokens with
  | none => compactSyntaxFailure tokens tasks
  | some suffix => compactSyntaxContinue suffix tasks

def compactProofRepeatFormulaTokenStep
    (input : CompactProofParserTask × List Nat ×
      List CompactProofParserTask) : CompactProofParserState :=
  let count := input.1.2.2
  let tokens := input.2.1
  let tasks := input.2.2
  if count = 0 then
    compactSyntaxContinue tokens tasks
  else
    compactSyntaxContinue tokens
      (compactProofFormulaTask 0 ::
        compactProofRepeatFormulaTask (count - 1) :: tasks)

def compactProofSequentTokenStep
    (tokens : List Nat) (tasks : List CompactProofParserTask) :
    CompactProofParserState :=
  match tokens with
  | [] => compactSyntaxFailure tokens tasks
  | count :: suffix =>
      compactSyntaxContinue suffix
        (compactProofRepeatFormulaTask count :: tasks)

def compactProofNodeTokenStep
    (tokens : List Nat) (tasks : List CompactProofParserTask) :
    CompactProofParserState :=
  match tokens with
  | [] => compactSyntaxFailure tokens tasks
  | tag :: suffix =>
      if tag = 0 then
        compactSyntaxContinue suffix
          (compactProofSequentTask :: compactProofFormulaTask 0 :: tasks)
      else if tag = 1 then
        compactSyntaxContinue suffix
          (compactProofSequentTask :: compactProofFormulaTask 0 :: tasks)
      else if tag = 2 then
        compactSyntaxContinue suffix (compactProofSequentTask :: tasks)
      else if tag = 3 then
        compactSyntaxContinue suffix
          (compactProofSequentTask :: compactProofFormulaTask 0 ::
            compactProofFormulaTask 0 :: compactProofTask ::
            compactProofTask :: tasks)
      else if tag = 4 then
        compactSyntaxContinue suffix
          (compactProofSequentTask :: compactProofFormulaTask 0 ::
            compactProofFormulaTask 0 :: compactProofTask :: tasks)
      else if tag = 5 then
        compactSyntaxContinue suffix
          (compactProofSequentTask :: compactProofFormulaTask 1 ::
            compactProofTask :: tasks)
      else if tag = 6 then
        compactSyntaxContinue suffix
          (compactProofSequentTask :: compactProofFormulaTask 1 ::
            compactProofTermTask 0 :: compactProofTask :: tasks)
      else if tag = 7 then
        compactSyntaxContinue suffix
          (compactProofSequentTask :: compactProofTask :: tasks)
      else if tag = 8 then
        compactSyntaxContinue suffix
          (compactProofSequentTask :: compactProofTask :: tasks)
      else if tag = 9 then
        compactSyntaxContinue suffix
          (compactProofSequentTask :: compactProofFormulaTask 0 ::
            compactProofTask :: compactProofTask :: tasks)
      else compactSyntaxFailure tokens tasks

def compactProofParserTaskTokenStep
    (input : CompactProofParserTask × List Nat ×
      List CompactProofParserTask) : CompactProofParserState :=
  let task := input.1
  let kind := task.1
  let binderArity := task.2.1
  let tokens := input.2.1
  let tasks := input.2.2
  if kind = 3 then
    compactProofNodeTokenStep tokens tasks
  else if kind = 4 then
    compactProofFormulaTokenStep (binderArity, tokens, tasks)
  else if kind = 5 then
    compactProofTermTokenStep (binderArity, tokens, tasks)
  else if kind = 6 then
    compactProofRepeatFormulaTokenStep input
  else if kind = 7 then
    compactProofSequentTokenStep tokens tasks
  else compactSyntaxFailure tokens tasks

def compactProofParserRunningStep
    (state : CompactProofParserState) : CompactProofParserState :=
  match state.2.1 with
  | [] => (state.1, [], some (some state.1))
  | task :: tasks =>
      compactProofParserTaskTokenStep (task, state.1, tasks)

def compactProofParserStep
    (state : CompactProofParserState) : CompactProofParserState :=
  if state.2.2.isSome then state else compactProofParserRunningStep state

def compactProofParserFuelBound (tokens : List Nat) : Nat :=
  32 * (tokens.length + 1) * (tokens.length + 1) + 16

def compactProofParserInitialState
    (tokens : List Nat) : CompactProofParserState :=
  (tokens, [compactProofTask], none)

def compactProofTokenParserRun
    (tokens : List Nat) : CompactProofParserState :=
  (compactProofParserStep^[compactProofParserFuelBound tokens])
    (compactProofParserInitialState tokens)

def compactProofTokenParser
    (tokens : List Nat) : Option (List Nat) :=
  compactSyntaxParserStateOutput (compactProofTokenParserRun tokens)

@[simp] theorem compactProofParserStep_formula
    (binderArity : Nat) (tokens : List Nat)
    (tasks : List CompactProofParserTask) :
    compactProofParserStep
        (tokens, compactProofFormulaTask binderArity :: tasks, none) =
      compactProofFormulaTokenStep (binderArity, tokens, tasks) := by
  simp [compactProofParserStep, compactProofParserRunningStep,
    compactProofParserTaskTokenStep, compactProofFormulaTask]

@[simp] theorem compactProofParserStep_term
    (binderArity : Nat) (tokens : List Nat)
    (tasks : List CompactProofParserTask) :
    compactProofParserStep
        (tokens, compactProofTermTask binderArity :: tasks, none) =
      compactProofTermTokenStep (binderArity, tokens, tasks) := by
  simp [compactProofParserStep, compactProofParserRunningStep,
    compactProofParserTaskTokenStep, compactProofTermTask]

@[simp] theorem compactProofParserStep_proof
    (tokens : List Nat) (tasks : List CompactProofParserTask) :
    compactProofParserStep
        (tokens, compactProofTask :: tasks, none) =
      compactProofNodeTokenStep tokens tasks := by
  simp [compactProofParserStep, compactProofParserRunningStep,
    compactProofParserTaskTokenStep, compactProofTask]

@[simp] theorem compactProofParserStep_formula_canonical
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix : List Nat) (tasks : List CompactProofParserTask) :
    compactProofParserStep
        (compactArithmeticFormulaTokens formula ++ suffix,
          compactProofFormulaTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
  simp [compactProofFormulaTokenStep,
    compactFormulaTokenParser_canonical_append, compactSyntaxContinue]

@[simp] theorem compactProofParserStep_term_canonical
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix : List Nat) (tasks : List CompactProofParserTask) :
    compactProofParserStep
        (compactArithmeticTermTokens term ++ suffix,
          compactProofTermTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
  simp [compactProofTermTokenStep,
    compactTermTokenParser_canonical_append, compactSyntaxContinue]

theorem compactProofParser_iterate_one_formula_canonical
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix : List Nat) (tasks : List CompactProofParserTask) :
    (compactProofParserStep^[1])
        (compactArithmeticFormulaTokens formula ++ suffix,
          compactProofFormulaTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
  simpa only [Function.iterate_one] using
    (compactProofParserStep_formula_canonical formula suffix tasks)

theorem compactProofParser_iterate_one_term_canonical
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix : List Nat) (tasks : List CompactProofParserTask) :
    (compactProofParserStep^[1])
        (compactArithmeticTermTokens term ++ suffix,
          compactProofTermTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
  simpa only [Function.iterate_one] using
    (compactProofParserStep_term_canonical term suffix tasks)

@[simp] theorem compactProofParserStep_repeat_zero
    (tokens : List Nat) (tasks : List CompactProofParserTask) :
    compactProofParserStep
        (tokens, compactProofRepeatFormulaTask 0 :: tasks, none) =
      (tokens, tasks, none) := by
  simp [compactProofParserStep, compactProofParserRunningStep,
    compactProofParserTaskTokenStep,
    compactProofRepeatFormulaTokenStep,
    compactProofRepeatFormulaTask, compactSyntaxContinue]

@[simp] theorem compactProofParserStep_repeat_succ
    (count : Nat) (tokens : List Nat)
    (tasks : List CompactProofParserTask) :
    compactProofParserStep
        (tokens, compactProofRepeatFormulaTask (count + 1) :: tasks, none) =
      (tokens,
        compactProofFormulaTask 0 ::
          compactProofRepeatFormulaTask count :: tasks,
        none) := by
  simp [compactProofParserStep, compactProofParserRunningStep,
    compactProofParserTaskTokenStep,
    compactProofRepeatFormulaTokenStep,
    compactProofRepeatFormulaTask, compactSyntaxContinue]

@[simp] theorem compactProofParserStep_sequent
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (suffix : List Nat) (tasks : List CompactProofParserTask) :
    compactProofParserStep
        (compactSequentListTokens Gamma ++ suffix,
          compactProofSequentTask :: tasks, none) =
      (Gamma.flatMap compactArithmeticFormulaTokens ++ suffix,
        compactProofRepeatFormulaTask Gamma.length :: tasks, none) := by
  simp [compactSequentListTokens, compactProofParserStep,
    compactProofParserRunningStep, compactProofParserTaskTokenStep,
    compactProofSequentTokenStep, compactProofSequentTask,
    compactSyntaxContinue]

theorem compactProofParser_iterate_trans
    {start middle finish : CompactProofParserState}
    {firstSteps secondSteps : Nat}
    (hfirst : (compactProofParserStep^[firstSteps]) start = middle)
    (hsecond : (compactProofParserStep^[secondSteps]) middle = finish) :
    (compactProofParserStep^[firstSteps + secondSteps]) start = finish := by
  rw [Nat.add_comm, Function.iterate_add_apply, hfirst, hsecond]

theorem compactProofFormulaList_execute
    (formulas : List LO.FirstOrder.ArithmeticProposition)
    (suffix : List Nat) (tasks : List CompactProofParserTask) :
    (compactProofParserStep^[1 + 2 * formulas.length])
        (formulas.flatMap compactArithmeticFormulaTokens ++ suffix,
          compactProofRepeatFormulaTask formulas.length :: tasks, none) =
      (suffix, tasks, none) := by
  induction formulas with
  | nil =>
      simp [Function.iterate_one]
  | cons formula formulas ih =>
      have hone :
          (compactProofParserStep^[1])
              ((formula :: formulas).flatMap
                    compactArithmeticFormulaTokens ++ suffix,
                compactProofRepeatFormulaTask
                  (formula :: formulas).length :: tasks,
                none) =
            (compactArithmeticFormulaTokens formula ++
                (formulas.flatMap compactArithmeticFormulaTokens ++ suffix),
              compactProofFormulaTask 0 ::
                compactProofRepeatFormulaTask formulas.length :: tasks,
              none) := by
        simp [Function.iterate_one, List.append_assoc]
      have hformula :
          (compactProofParserStep^[1])
              (compactArithmeticFormulaTokens formula ++
                  (formulas.flatMap compactArithmeticFormulaTokens ++ suffix),
                compactProofFormulaTask 0 ::
                  compactProofRepeatFormulaTask formulas.length :: tasks,
                none) =
            (formulas.flatMap compactArithmeticFormulaTokens ++ suffix,
              compactProofRepeatFormulaTask formulas.length :: tasks,
              none) := by
        simpa only [Function.iterate_one] using
          (compactProofParserStep_formula_canonical formula
            (formulas.flatMap compactArithmeticFormulaTokens ++ suffix)
            (compactProofRepeatFormulaTask formulas.length :: tasks))
      have hfirst := compactProofParser_iterate_trans hone hformula
      have hall := compactProofParser_iterate_trans hfirst ih
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall

theorem compactProofSequentTask_execute
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (suffix : List Nat) (tasks : List CompactProofParserTask) :
    (compactProofParserStep^[2 + 2 * Gamma.length])
        (compactSequentListTokens Gamma ++ suffix,
          compactProofSequentTask :: tasks, none) =
      (suffix, tasks, none) := by
  have hfirst :
      (compactProofParserStep^[1])
          (compactSequentListTokens Gamma ++ suffix,
            compactProofSequentTask :: tasks, none) =
        (Gamma.flatMap compactArithmeticFormulaTokens ++ suffix,
          compactProofRepeatFormulaTask Gamma.length :: tasks, none) := by
    simp [Function.iterate_one]
  have hformulas := compactProofFormulaList_execute Gamma suffix tasks
  have hrun := compactProofParser_iterate_trans hfirst hformulas
  have hsteps :
      1 + (1 + 2 * Gamma.length) = 2 + 2 * Gamma.length := by
    omega
  rw [← hsteps]
  exact hrun

theorem compactListedProofTask_execute
    (tree : ListedCheckedPAProofTree)
    (suffix : List Nat) (tasks : List CompactProofParserTask) :
    (compactProofParserStep^[compactListedProofTaskSteps tree])
        (compactListedProofTokens tree ++ suffix,
          compactProofTask :: tasks, none) =
      (suffix, tasks, none) := by
  induction tree generalizing suffix tasks with
  | closed Gamma formula =>
      have hnode :
          (compactProofParserStep^[1])
              (compactListedProofTokens (.closed Gamma formula) ++ suffix,
                compactProofTask :: tasks, none) =
            (compactSequentListTokens Gamma ++
                (compactArithmeticFormulaTokens formula ++ suffix),
              compactProofSequentTask ::
                compactProofFormulaTask 0 :: tasks,
              none) := by
        simp [Function.iterate_one, compactListedProofTokens,
          compactProofNodeTokenStep, compactSyntaxContinue,
          List.append_assoc]
      have hsequent := compactProofSequentTask_execute Gamma
        (compactArithmeticFormulaTokens formula ++ suffix)
        (compactProofFormulaTask 0 :: tasks)
      have hformula :
          (compactProofParserStep^[1])
              (compactArithmeticFormulaTokens formula ++ suffix,
                compactProofFormulaTask 0 :: tasks, none) =
            (suffix, tasks, none) := by
        simpa only [Function.iterate_one] using
          (compactProofParserStep_formula_canonical formula suffix tasks)
      have hfirst := compactProofParser_iterate_trans hnode hsequent
      have hrun := compactProofParser_iterate_trans hfirst hformula
      simpa [compactListedProofTaskSteps,
        compactProofSequentTaskSteps, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hrun
  | axm Gamma sentence =>
      let formula : LO.FirstOrder.ArithmeticProposition :=
        Rewriting.emb sentence
      have hnode :
          (compactProofParserStep^[1])
              (compactListedProofTokens (.axm Gamma sentence) ++ suffix,
                compactProofTask :: tasks, none) =
            (compactSequentListTokens Gamma ++
                (compactArithmeticFormulaTokens formula ++ suffix),
              compactProofSequentTask ::
                compactProofFormulaTask 0 :: tasks,
              none) := by
        simp [Function.iterate_one, compactListedProofTokens,
          compactProofNodeTokenStep, compactSyntaxContinue,
          formula, List.append_assoc]
      have hsequent := compactProofSequentTask_execute Gamma
        (compactArithmeticFormulaTokens formula ++ suffix)
        (compactProofFormulaTask 0 :: tasks)
      have hformula :
          (compactProofParserStep^[1])
              (compactArithmeticFormulaTokens formula ++ suffix,
                compactProofFormulaTask 0 :: tasks, none) =
            (suffix, tasks, none) := by
        simpa only [Function.iterate_one] using
          (compactProofParserStep_formula_canonical formula suffix tasks)
      have hfirst := compactProofParser_iterate_trans hnode hsequent
      have hrun := compactProofParser_iterate_trans hfirst hformula
      simpa [compactListedProofTaskSteps,
        compactProofSequentTaskSteps, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hrun
  | verum Gamma =>
      have hnode :
          (compactProofParserStep^[1])
              (compactListedProofTokens (.verum Gamma) ++ suffix,
                compactProofTask :: tasks, none) =
            (compactSequentListTokens Gamma ++ suffix,
              compactProofSequentTask :: tasks, none) := by
        simp [Function.iterate_one, compactListedProofTokens,
          compactProofNodeTokenStep, compactSyntaxContinue,
          List.append_assoc]
      have hsequent := compactProofSequentTask_execute Gamma suffix tasks
      have hrun := compactProofParser_iterate_trans hnode hsequent
      simpa [compactListedProofTaskSteps,
        compactProofSequentTaskSteps, Nat.add_assoc] using hrun
  | and Gamma leftFormula rightFormula left right ihLeft ihRight =>
      have hnode :
          (compactProofParserStep^[1])
              (compactListedProofTokens
                    (.and Gamma leftFormula rightFormula left right) ++ suffix,
                compactProofTask :: tasks, none) =
            (compactSequentListTokens Gamma ++
                (compactArithmeticFormulaTokens leftFormula ++
                  (compactArithmeticFormulaTokens rightFormula ++
                    (compactListedProofTokens left ++
                      (compactListedProofTokens right ++ suffix)))),
              compactProofSequentTask :: compactProofFormulaTask 0 ::
                compactProofFormulaTask 0 :: compactProofTask ::
                compactProofTask :: tasks,
              none) := by
        simp [Function.iterate_one, compactListedProofTokens,
          compactProofNodeTokenStep, compactSyntaxContinue,
          List.append_assoc]
      have hsequent := compactProofSequentTask_execute Gamma
        (compactArithmeticFormulaTokens leftFormula ++
          (compactArithmeticFormulaTokens rightFormula ++
            (compactListedProofTokens left ++
              (compactListedProofTokens right ++ suffix))))
        (compactProofFormulaTask 0 :: compactProofFormulaTask 0 ::
          compactProofTask :: compactProofTask :: tasks)
      have hleftFormula :
          (compactProofParserStep^[1])
              (compactArithmeticFormulaTokens leftFormula ++
                  (compactArithmeticFormulaTokens rightFormula ++
                    (compactListedProofTokens left ++
                      (compactListedProofTokens right ++ suffix))),
                compactProofFormulaTask 0 ::
                  compactProofFormulaTask 0 :: compactProofTask ::
                  compactProofTask :: tasks,
                none) =
            (compactArithmeticFormulaTokens rightFormula ++
                (compactListedProofTokens left ++
                  (compactListedProofTokens right ++ suffix)),
              compactProofFormulaTask 0 :: compactProofTask ::
                compactProofTask :: tasks,
              none) := by
        simpa only [Function.iterate_one] using
          (compactProofParserStep_formula_canonical leftFormula
            (compactArithmeticFormulaTokens rightFormula ++
              (compactListedProofTokens left ++
                (compactListedProofTokens right ++ suffix)))
            (compactProofFormulaTask 0 :: compactProofTask ::
              compactProofTask :: tasks))
      have hrightFormula :
          (compactProofParserStep^[1])
              (compactArithmeticFormulaTokens rightFormula ++
                  (compactListedProofTokens left ++
                    (compactListedProofTokens right ++ suffix)),
                compactProofFormulaTask 0 :: compactProofTask ::
                  compactProofTask :: tasks,
                none) =
            (compactListedProofTokens left ++
                (compactListedProofTokens right ++ suffix),
              compactProofTask :: compactProofTask :: tasks, none) := by
        simpa only [Function.iterate_one] using
          (compactProofParserStep_formula_canonical rightFormula
            (compactListedProofTokens left ++
              (compactListedProofTokens right ++ suffix))
            (compactProofTask :: compactProofTask :: tasks))
      have hleft := ihLeft
        (compactListedProofTokens right ++ suffix)
        (compactProofTask :: tasks)
      have hright := ihRight suffix tasks
      have hrun1 := compactProofParser_iterate_trans hnode hsequent
      have hrun2 := compactProofParser_iterate_trans hrun1 hleftFormula
      have hrun3 := compactProofParser_iterate_trans hrun2 hrightFormula
      have hrun4 := compactProofParser_iterate_trans hrun3 hleft
      have hrun := compactProofParser_iterate_trans hrun4 hright
      simpa [compactListedProofTaskSteps,
        compactProofSequentTaskSteps, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, List.append_assoc] using hrun
  | or Gamma leftFormula rightFormula premise ih =>
      have hnode :
          (compactProofParserStep^[1])
              (compactListedProofTokens
                    (.or Gamma leftFormula rightFormula premise) ++ suffix,
                compactProofTask :: tasks, none) =
            (compactSequentListTokens Gamma ++
                (compactArithmeticFormulaTokens leftFormula ++
                  (compactArithmeticFormulaTokens rightFormula ++
                    (compactListedProofTokens premise ++ suffix))),
              compactProofSequentTask :: compactProofFormulaTask 0 ::
                compactProofFormulaTask 0 :: compactProofTask :: tasks,
              none) := by
        simp [Function.iterate_one, compactListedProofTokens,
          compactProofNodeTokenStep, compactSyntaxContinue,
          List.append_assoc]
      have hsequent := compactProofSequentTask_execute Gamma
        (compactArithmeticFormulaTokens leftFormula ++
          (compactArithmeticFormulaTokens rightFormula ++
            (compactListedProofTokens premise ++ suffix)))
        (compactProofFormulaTask 0 :: compactProofFormulaTask 0 ::
          compactProofTask :: tasks)
      have hleftFormula :=
        compactProofParser_iterate_one_formula_canonical
        leftFormula
        (compactArithmeticFormulaTokens rightFormula ++
          (compactListedProofTokens premise ++ suffix))
        (compactProofFormulaTask 0 :: compactProofTask :: tasks)
      have hrightFormula :=
        compactProofParser_iterate_one_formula_canonical
        rightFormula (compactListedProofTokens premise ++ suffix)
        (compactProofTask :: tasks)
      have hpremise := ih suffix tasks
      have hrun1 := compactProofParser_iterate_trans hnode hsequent
      have hrun2 := compactProofParser_iterate_trans hrun1 hleftFormula
      have hrun3 := compactProofParser_iterate_trans hrun2 hrightFormula
      have hrun := compactProofParser_iterate_trans hrun3 hpremise
      simpa [compactListedProofTaskSteps,
        compactProofSequentTaskSteps, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, List.append_assoc] using hrun
  | all Gamma formula premise ih =>
      have hnode :
          (compactProofParserStep^[1])
              (compactListedProofTokens (.all Gamma formula premise) ++ suffix,
                compactProofTask :: tasks, none) =
            (compactSequentListTokens Gamma ++
                (compactArithmeticFormulaTokens formula ++
                  (compactListedProofTokens premise ++ suffix)),
              compactProofSequentTask :: compactProofFormulaTask 1 ::
                compactProofTask :: tasks,
              none) := by
        simp [Function.iterate_one, compactListedProofTokens,
          compactProofNodeTokenStep, compactSyntaxContinue,
          List.append_assoc]
      have hsequent := compactProofSequentTask_execute Gamma
        (compactArithmeticFormulaTokens formula ++
          (compactListedProofTokens premise ++ suffix))
        (compactProofFormulaTask 1 :: compactProofTask :: tasks)
      have hformula :=
        compactProofParser_iterate_one_formula_canonical formula
        (compactListedProofTokens premise ++ suffix)
        (compactProofTask :: tasks)
      have hpremise := ih suffix tasks
      have hrun1 := compactProofParser_iterate_trans hnode hsequent
      have hrun2 := compactProofParser_iterate_trans hrun1 hformula
      have hrun := compactProofParser_iterate_trans hrun2 hpremise
      simpa [compactListedProofTaskSteps,
        compactProofSequentTaskSteps, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, List.append_assoc] using hrun
  | exs Gamma formula witness premise ih =>
      have hnode :
          (compactProofParserStep^[1])
              (compactListedProofTokens
                    (.exs Gamma formula witness premise) ++ suffix,
                compactProofTask :: tasks, none) =
            (compactSequentListTokens Gamma ++
                (compactArithmeticFormulaTokens formula ++
                  (compactArithmeticTermTokens witness ++
                    (compactListedProofTokens premise ++ suffix))),
              compactProofSequentTask :: compactProofFormulaTask 1 ::
                compactProofTermTask 0 :: compactProofTask :: tasks,
              none) := by
        simp [Function.iterate_one, compactListedProofTokens,
          compactProofNodeTokenStep, compactSyntaxContinue,
          List.append_assoc]
      have hsequent := compactProofSequentTask_execute Gamma
        (compactArithmeticFormulaTokens formula ++
          (compactArithmeticTermTokens witness ++
            (compactListedProofTokens premise ++ suffix)))
        (compactProofFormulaTask 1 :: compactProofTermTask 0 ::
          compactProofTask :: tasks)
      have hformula :=
        compactProofParser_iterate_one_formula_canonical formula
        (compactArithmeticTermTokens witness ++
          (compactListedProofTokens premise ++ suffix))
        (compactProofTermTask 0 :: compactProofTask :: tasks)
      have hwitness := compactProofParser_iterate_one_term_canonical witness
        (compactListedProofTokens premise ++ suffix)
        (compactProofTask :: tasks)
      have hpremise := ih suffix tasks
      have hrun1 := compactProofParser_iterate_trans hnode hsequent
      have hrun2 := compactProofParser_iterate_trans hrun1 hformula
      have hrun3 := compactProofParser_iterate_trans hrun2 hwitness
      have hrun := compactProofParser_iterate_trans hrun3 hpremise
      simpa [compactListedProofTaskSteps,
        compactProofSequentTaskSteps, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, List.append_assoc] using hrun
  | wk Gamma premise ih =>
      have hnode :
          (compactProofParserStep^[1])
              (compactListedProofTokens (.wk Gamma premise) ++ suffix,
                compactProofTask :: tasks, none) =
            (compactSequentListTokens Gamma ++
                (compactListedProofTokens premise ++ suffix),
              compactProofSequentTask :: compactProofTask :: tasks,
              none) := by
        simp [Function.iterate_one, compactListedProofTokens,
          compactProofNodeTokenStep, compactSyntaxContinue,
          List.append_assoc]
      have hsequent := compactProofSequentTask_execute Gamma
        (compactListedProofTokens premise ++ suffix)
        (compactProofTask :: tasks)
      have hpremise := ih suffix tasks
      have hrun1 := compactProofParser_iterate_trans hnode hsequent
      have hrun := compactProofParser_iterate_trans hrun1 hpremise
      simpa [compactListedProofTaskSteps,
        compactProofSequentTaskSteps, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, List.append_assoc] using hrun
  | shift Gamma premise ih =>
      have hnode :
          (compactProofParserStep^[1])
              (compactListedProofTokens (.shift Gamma premise) ++ suffix,
                compactProofTask :: tasks, none) =
            (compactSequentListTokens Gamma ++
                (compactListedProofTokens premise ++ suffix),
              compactProofSequentTask :: compactProofTask :: tasks,
              none) := by
        simp [Function.iterate_one, compactListedProofTokens,
          compactProofNodeTokenStep, compactSyntaxContinue,
          List.append_assoc]
      have hsequent := compactProofSequentTask_execute Gamma
        (compactListedProofTokens premise ++ suffix)
        (compactProofTask :: tasks)
      have hpremise := ih suffix tasks
      have hrun1 := compactProofParser_iterate_trans hnode hsequent
      have hrun := compactProofParser_iterate_trans hrun1 hpremise
      simpa [compactListedProofTaskSteps,
        compactProofSequentTaskSteps, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, List.append_assoc] using hrun
  | cut Gamma formula left right ihLeft ihRight =>
      have hnode :
          (compactProofParserStep^[1])
              (compactListedProofTokens (.cut Gamma formula left right) ++ suffix,
                compactProofTask :: tasks, none) =
            (compactSequentListTokens Gamma ++
                (compactArithmeticFormulaTokens formula ++
                  (compactListedProofTokens left ++
                    (compactListedProofTokens right ++ suffix))),
              compactProofSequentTask :: compactProofFormulaTask 0 ::
                compactProofTask :: compactProofTask :: tasks,
              none) := by
        simp [Function.iterate_one, compactListedProofTokens,
          compactProofNodeTokenStep, compactSyntaxContinue,
          List.append_assoc]
      have hsequent := compactProofSequentTask_execute Gamma
        (compactArithmeticFormulaTokens formula ++
          (compactListedProofTokens left ++
            (compactListedProofTokens right ++ suffix)))
        (compactProofFormulaTask 0 :: compactProofTask ::
          compactProofTask :: tasks)
      have hformula :=
        compactProofParser_iterate_one_formula_canonical formula
        (compactListedProofTokens left ++
          (compactListedProofTokens right ++ suffix))
        (compactProofTask :: compactProofTask :: tasks)
      have hleft := ihLeft (compactListedProofTokens right ++ suffix)
        (compactProofTask :: tasks)
      have hright := ihRight suffix tasks
      have hrun1 := compactProofParser_iterate_trans hnode hsequent
      have hrun2 := compactProofParser_iterate_trans hrun1 hformula
      have hrun3 := compactProofParser_iterate_trans hrun2 hleft
      have hrun := compactProofParser_iterate_trans hrun3 hright
      simpa [compactListedProofTaskSteps,
        compactProofSequentTaskSteps, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, List.append_assoc] using hrun

theorem compactArithmeticTermTokens_length_pos
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) :
    0 < (compactArithmeticTermTokens term).length := by
  cases term <;>
    simp [compactArithmeticTermTokens]

theorem compactArithmeticFormulaTokens_length_pos
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) :
    0 < (compactArithmeticFormulaTokens formula).length := by
  cases formula <;>
    simp [compactArithmeticFormulaTokens]

theorem formulaList_length_le_flatMap_tokenLength
    (formulas : List LO.FirstOrder.ArithmeticProposition) :
    formulas.length <=
      (formulas.flatMap compactArithmeticFormulaTokens).length := by
  induction formulas with
  | nil => simp
  | cons formula formulas ih =>
      have hformula := compactArithmeticFormulaTokens_length_pos formula
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      omega

theorem compactProofSequentTaskSteps_le_two_mul_tokenLength
    (Gamma : List LO.FirstOrder.ArithmeticProposition) :
    compactProofSequentTaskSteps Gamma <=
      2 * (compactSequentListTokens Gamma).length := by
  have hformulas := formulaList_length_le_flatMap_tokenLength Gamma
  simp only [compactProofSequentTaskSteps, compactSequentListTokens,
    List.length_cons]
  omega

theorem compactListedProofTaskSteps_le_two_mul_tokenLength
    (tree : ListedCheckedPAProofTree) :
    compactListedProofTaskSteps tree <=
      2 * (compactListedProofTokens tree).length := by
  induction tree with
  | closed Gamma formula =>
      have hsequent :=
        compactProofSequentTaskSteps_le_two_mul_tokenLength Gamma
      have hformula := compactArithmeticFormulaTokens_length_pos formula
      simp only [compactListedProofTaskSteps, compactListedProofTokens,
        List.length_cons, List.length_append]
      omega
  | axm Gamma sentence =>
      have hsequent :=
        compactProofSequentTaskSteps_le_two_mul_tokenLength Gamma
      have hformula := compactArithmeticFormulaTokens_length_pos
        (Rewriting.emb sentence : LO.FirstOrder.ArithmeticProposition)
      simp only [compactListedProofTaskSteps, compactListedProofTokens,
        List.length_cons, List.length_append]
      omega
  | verum Gamma =>
      have hsequent :=
        compactProofSequentTaskSteps_le_two_mul_tokenLength Gamma
      simp only [compactListedProofTaskSteps, compactListedProofTokens,
        List.length_cons]
      omega
  | and Gamma leftFormula rightFormula left right ihLeft ihRight =>
      have hsequent :=
        compactProofSequentTaskSteps_le_two_mul_tokenLength Gamma
      have hleftFormula :=
        compactArithmeticFormulaTokens_length_pos leftFormula
      have hrightFormula :=
        compactArithmeticFormulaTokens_length_pos rightFormula
      simp only [compactListedProofTaskSteps, compactListedProofTokens,
        List.length_cons, List.length_append]
      omega
  | or Gamma leftFormula rightFormula premise ih =>
      have hsequent :=
        compactProofSequentTaskSteps_le_two_mul_tokenLength Gamma
      have hleftFormula :=
        compactArithmeticFormulaTokens_length_pos leftFormula
      have hrightFormula :=
        compactArithmeticFormulaTokens_length_pos rightFormula
      simp only [compactListedProofTaskSteps, compactListedProofTokens,
        List.length_cons, List.length_append]
      omega
  | all Gamma formula premise ih =>
      have hsequent :=
        compactProofSequentTaskSteps_le_two_mul_tokenLength Gamma
      have hformula := compactArithmeticFormulaTokens_length_pos formula
      simp only [compactListedProofTaskSteps, compactListedProofTokens,
        List.length_cons, List.length_append]
      omega
  | exs Gamma formula witness premise ih =>
      have hsequent :=
        compactProofSequentTaskSteps_le_two_mul_tokenLength Gamma
      have hformula := compactArithmeticFormulaTokens_length_pos formula
      have hwitness := compactArithmeticTermTokens_length_pos witness
      simp only [compactListedProofTaskSteps, compactListedProofTokens,
        List.length_cons, List.length_append]
      omega
  | wk Gamma premise ih =>
      have hsequent :=
        compactProofSequentTaskSteps_le_two_mul_tokenLength Gamma
      simp only [compactListedProofTaskSteps, compactListedProofTokens,
        List.length_cons, List.length_append]
      omega
  | shift Gamma premise ih =>
      have hsequent :=
        compactProofSequentTaskSteps_le_two_mul_tokenLength Gamma
      simp only [compactListedProofTaskSteps, compactListedProofTokens,
        List.length_cons, List.length_append]
      omega
  | cut Gamma formula left right ihLeft ihRight =>
      have hsequent :=
        compactProofSequentTaskSteps_le_two_mul_tokenLength Gamma
      have hformula := compactArithmeticFormulaTokens_length_pos formula
      simp only [compactListedProofTaskSteps, compactListedProofTokens,
        List.length_cons, List.length_append]
      omega

theorem compactProofParserFuelBound_two_mul_length_add_one
    (tokens : List Nat) :
    2 * tokens.length + 1 <= compactProofParserFuelBound tokens := by
  simp only [compactProofParserFuelBound]
  nlinarith

@[simp] theorem compactProofParserStep_empty
    (tokens : List Nat) :
    compactProofParserStep (tokens, [], none) =
      (tokens, [], some (some tokens)) := by
  simp [compactProofParserStep, compactProofParserRunningStep]

theorem compactProofParserStep_done
    (tokens : List Nat) (tasks : List CompactProofParserTask)
    (result : Option (List Nat)) :
    compactProofParserStep (tokens, tasks, some result) =
      (tokens, tasks, some result) := by
  simp [compactProofParserStep]

theorem compactProofParserStep_iterate_done
    (fuel : Nat) (tokens : List Nat)
    (tasks : List CompactProofParserTask)
    (result : Option (List Nat)) :
    (compactProofParserStep^[fuel]) (tokens, tasks, some result) =
      (tokens, tasks, some result) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply, compactProofParserStep_done, ih]

theorem compactProofTokenParser_canonical_append
    (tree : ListedCheckedPAProofTree) (suffix : List Nat) :
    compactProofTokenParser (compactListedProofTokens tree ++ suffix) =
      some suffix := by
  let tokens := compactListedProofTokens tree ++ suffix
  let used := compactListedProofTaskSteps tree + 1
  have htask := compactListedProofTask_execute tree suffix []
  have hfinish :
      (compactProofParserStep^[used])
          (tokens, [compactProofTask], none) =
        (suffix, [], some (some suffix)) := by
    apply compactProofParser_iterate_trans htask
    simp [Function.iterate_one]
  have hsteps := compactListedProofTaskSteps_le_two_mul_tokenLength tree
  have hprefixLength :
      (compactListedProofTokens tree).length <= tokens.length := by
    simp [tokens]
  have hfuel :=
    compactProofParserFuelBound_two_mul_length_add_one tokens
  have hused : used <= compactProofParserFuelBound tokens := by
    omega
  obtain ⟨extra, hfuelEq⟩ := exists_add_of_le hused
  have hrun :
      (compactProofParserStep^[compactProofParserFuelBound tokens])
          (tokens, [compactProofTask], none) =
        (suffix, [], some (some suffix)) := by
    rw [hfuelEq]
    exact compactProofParser_iterate_trans hfinish
      (compactProofParserStep_iterate_done extra suffix [] (some suffix))
  simp [compactProofTokenParser, compactProofTokenParserRun,
    compactProofParserInitialState, compactSyntaxParserStateOutput,
    tokens, hrun]

theorem compactProofFormulaTask_primrec :
    Primrec compactProofFormulaTask := by
  exact
    (Primrec.pair (Primrec.const 4)
      (Primrec.pair Primrec.id (Primrec.const 0))).of_eq
      fun binderArity => by rfl

theorem compactProofTermTask_primrec :
    Primrec compactProofTermTask := by
  exact
    (Primrec.pair (Primrec.const 5)
      (Primrec.pair Primrec.id (Primrec.const 0))).of_eq
      fun binderArity => by rfl

theorem compactProofRepeatFormulaTask_primrec :
    Primrec compactProofRepeatFormulaTask := by
  exact
    (Primrec.pair (Primrec.const 6)
      (Primrec.pair (Primrec.const 0) Primrec.id)).of_eq
      fun count => by rfl

theorem compactProofFormulaTokenStep_primrec :
    Primrec compactProofFormulaTokenStep := by
  have harity : Primrec
      (fun input : Nat × List Nat × List CompactProofParserTask =>
        input.1) :=
    Primrec.fst
  have htokens : Primrec
      (fun input : Nat × List Nat × List CompactProofParserTask =>
        input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have htasks : Primrec
      (fun input : Nat × List Nat × List CompactProofParserTask =>
        input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hparse : Primrec
      (fun input : Nat × List Nat × List CompactProofParserTask =>
        compactFormulaTokenParser input.1 input.2.1) :=
    compactFormulaTokenParser_primrec.comp harity htokens
  have hfailure : Primrec
      (fun input : Nat × List Nat × List CompactProofParserTask =>
        compactSyntaxFailure input.2.1 input.2.2) :=
    compactSyntaxFailure_primrec.comp htokens htasks
  have hsuccess : Primrec₂
      (fun (input : Nat × List Nat × List CompactProofParserTask)
          (suffix : List Nat) =>
        compactSyntaxContinue suffix input.2.2) :=
    compactSyntaxContinue_primrec.comp₂ Primrec₂.right
      ((htasks.comp Primrec.fst).to₂)
  exact
    (Primrec.option_casesOn hparse hfailure hsuccess).of_eq
      fun input => by
        cases hresult : compactFormulaTokenParser input.1 input.2.1 <;>
          simp [compactProofFormulaTokenStep, hresult]

theorem compactProofTermTokenStep_primrec :
    Primrec compactProofTermTokenStep := by
  have harity : Primrec
      (fun input : Nat × List Nat × List CompactProofParserTask =>
        input.1) :=
    Primrec.fst
  have htokens : Primrec
      (fun input : Nat × List Nat × List CompactProofParserTask =>
        input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have htasks : Primrec
      (fun input : Nat × List Nat × List CompactProofParserTask =>
        input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hparse : Primrec
      (fun input : Nat × List Nat × List CompactProofParserTask =>
        compactTermTokenParser input.1 input.2.1) :=
    compactTermTokenParser_primrec.comp harity htokens
  have hfailure : Primrec
      (fun input : Nat × List Nat × List CompactProofParserTask =>
        compactSyntaxFailure input.2.1 input.2.2) :=
    compactSyntaxFailure_primrec.comp htokens htasks
  have hsuccess : Primrec₂
      (fun (input : Nat × List Nat × List CompactProofParserTask)
          (suffix : List Nat) =>
        compactSyntaxContinue suffix input.2.2) :=
    compactSyntaxContinue_primrec.comp₂ Primrec₂.right
      ((htasks.comp Primrec.fst).to₂)
  exact
    (Primrec.option_casesOn hparse hfailure hsuccess).of_eq
      fun input => by
        cases hresult : compactTermTokenParser input.1 input.2.1 <;>
          simp [compactProofTermTokenStep, hresult]

theorem compactProofRepeatFormulaTokenStep_primrec :
    Primrec compactProofRepeatFormulaTokenStep := by
  have htask : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask => input.1) :=
    Primrec.fst
  have hcount : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask => input.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp htask)
  have htokens : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have htasks : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hzero : PrimrecPred
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask => input.1.2.2 = 0) :=
    Primrec.eq.comp hcount (Primrec.const 0)
  have hdone : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask =>
        compactSyntaxContinue input.2.1 input.2.2) :=
    compactSyntaxContinue_primrec.comp htokens htasks
  have hpred : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask => input.1.2.2 - 1) :=
    Primrec.nat_sub.comp hcount (Primrec.const 1)
  have hrepeat : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask =>
        compactProofRepeatFormulaTask (input.1.2.2 - 1)) :=
    compactProofRepeatFormulaTask_primrec.comp hpred
  have hnewTasks : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask =>
        compactProofFormulaTask 0 ::
          compactProofRepeatFormulaTask (input.1.2.2 - 1) :: input.2.2) :=
    Primrec.list_cons.comp (Primrec.const (compactProofFormulaTask 0))
      (Primrec.list_cons.comp hrepeat htasks)
  have hnext : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask =>
        compactSyntaxContinue input.2.1
          (compactProofFormulaTask 0 ::
            compactProofRepeatFormulaTask (input.1.2.2 - 1) :: input.2.2)) :=
    compactSyntaxContinue_primrec.comp htokens hnewTasks
  exact
    (Primrec.ite hzero hdone hnext).of_eq fun input => by
      simp only [compactProofRepeatFormulaTokenStep]

theorem compactProofSequentTokenStep_primrec :
    Primrec₂ compactProofSequentTokenStep := by
  apply Primrec₂.mk
  have htokens : Primrec
      (fun input : List Nat × List CompactProofParserTask => input.1) :=
    Primrec.fst
  have htasks : Primrec
      (fun input : List Nat × List CompactProofParserTask => input.2) :=
    Primrec.snd
  have hempty : PrimrecPred
      (fun input : List Nat × List CompactProofParserTask =>
        input.1 = []) :=
    Primrec.eq.comp htokens (Primrec.const [])
  have hfailure : Primrec
      (fun input : List Nat × List CompactProofParserTask =>
        compactSyntaxFailure input.1 input.2) :=
    compactSyntaxFailure_primrec.comp htokens htasks
  have hheadOption : Primrec
      (fun input : List Nat × List CompactProofParserTask =>
        input.1.head?) :=
    Primrec.list_head?.comp htokens
  have hhead : Primrec
      (fun input : List Nat × List CompactProofParserTask =>
        input.1.head?.getD 0) :=
    Primrec.option_getD.comp hheadOption (Primrec.const 0)
  have htail : Primrec
      (fun input : List Nat × List CompactProofParserTask =>
        input.1.tail) :=
    Primrec.list_tail.comp htokens
  have hrepeat : Primrec
      (fun input : List Nat × List CompactProofParserTask =>
        compactProofRepeatFormulaTask (input.1.head?.getD 0)) :=
    compactProofRepeatFormulaTask_primrec.comp hhead
  have hnewTasks : Primrec
      (fun input : List Nat × List CompactProofParserTask =>
        compactProofRepeatFormulaTask (input.1.head?.getD 0) :: input.2) :=
    Primrec.list_cons.comp hrepeat htasks
  have hsuccess : Primrec
      (fun input : List Nat × List CompactProofParserTask =>
        compactSyntaxContinue input.1.tail
          (compactProofRepeatFormulaTask (input.1.head?.getD 0) :: input.2)) :=
    compactSyntaxContinue_primrec.comp htail hnewTasks
  exact
    (Primrec.ite hempty hfailure hsuccess).of_eq fun input => by
      cases input.1 <;>
        simp [compactProofSequentTokenStep]

theorem compactProofNodeTokenStep_primrec :
    Primrec₂ compactProofNodeTokenStep := by
  apply Primrec₂.mk
  have htokens : Primrec
      (fun input : List Nat × List CompactProofParserTask => input.1) :=
    Primrec.fst
  have htasks : Primrec
      (fun input : List Nat × List CompactProofParserTask => input.2) :=
    Primrec.snd
  have hempty : PrimrecPred
      (fun input : List Nat × List CompactProofParserTask =>
        input.1 = []) :=
    Primrec.eq.comp htokens (Primrec.const [])
  have hheadOption : Primrec
      (fun input : List Nat × List CompactProofParserTask =>
        input.1.head?) :=
    Primrec.list_head?.comp htokens
  have htag : Primrec
      (fun input : List Nat × List CompactProofParserTask =>
        input.1.head?.getD 0) :=
    Primrec.option_getD.comp hheadOption (Primrec.const 0)
  have htail : Primrec
      (fun input : List Nat × List CompactProofParserTask =>
        input.1.tail) :=
    Primrec.list_tail.comp htokens
  have hfailure : Primrec
      (fun input : List Nat × List CompactProofParserTask =>
        compactSyntaxFailure input.1 input.2) :=
    compactSyntaxFailure_primrec.comp htokens htasks
  have hprepend (taskPrefix : List CompactProofParserTask) : Primrec
      (fun input : List Nat × List CompactProofParserTask =>
        taskPrefix ++ input.2) := by
    induction taskPrefix with
    | nil => simpa using htasks
    | cons head tail ih =>
        exact Primrec.list_cons.comp (Primrec.const head) ih
  have hcontinue (taskPrefix : List CompactProofParserTask) : Primrec
      (fun input : List Nat × List CompactProofParserTask =>
        compactSyntaxContinue input.1.tail (taskPrefix ++ input.2)) :=
    compactSyntaxContinue_primrec.comp htail (hprepend taskPrefix)
  have htagEq (tag : Nat) : PrimrecPred
      (fun input : List Nat × List CompactProofParserTask =>
        input.1.head?.getD 0 = tag) :=
    Primrec.eq.comp htag (Primrec.const tag)
  have h0 := hcontinue
    [compactProofSequentTask, compactProofFormulaTask 0]
  have h1 := hcontinue
    [compactProofSequentTask, compactProofFormulaTask 0]
  have h2 := hcontinue [compactProofSequentTask]
  have h3 := hcontinue
    [compactProofSequentTask, compactProofFormulaTask 0,
      compactProofFormulaTask 0, compactProofTask, compactProofTask]
  have h4 := hcontinue
    [compactProofSequentTask, compactProofFormulaTask 0,
      compactProofFormulaTask 0, compactProofTask]
  have h5 := hcontinue
    [compactProofSequentTask, compactProofFormulaTask 1,
      compactProofTask]
  have h6 := hcontinue
    [compactProofSequentTask, compactProofFormulaTask 1,
      compactProofTermTask 0, compactProofTask]
  have h7 := hcontinue [compactProofSequentTask, compactProofTask]
  have h8 := hcontinue [compactProofSequentTask, compactProofTask]
  have h9 := hcontinue
    [compactProofSequentTask, compactProofFormulaTask 0,
      compactProofTask, compactProofTask]
  have hnonempty : Primrec
      (fun input : List Nat × List CompactProofParserTask =>
        if input.1.head?.getD 0 = 0 then
          compactSyntaxContinue input.1.tail
            ([compactProofSequentTask, compactProofFormulaTask 0] ++ input.2)
        else if input.1.head?.getD 0 = 1 then
          compactSyntaxContinue input.1.tail
            ([compactProofSequentTask, compactProofFormulaTask 0] ++ input.2)
        else if input.1.head?.getD 0 = 2 then
          compactSyntaxContinue input.1.tail
            ([compactProofSequentTask] ++ input.2)
        else if input.1.head?.getD 0 = 3 then
          compactSyntaxContinue input.1.tail
            ([compactProofSequentTask, compactProofFormulaTask 0,
              compactProofFormulaTask 0, compactProofTask,
              compactProofTask] ++ input.2)
        else if input.1.head?.getD 0 = 4 then
          compactSyntaxContinue input.1.tail
            ([compactProofSequentTask, compactProofFormulaTask 0,
              compactProofFormulaTask 0, compactProofTask] ++ input.2)
        else if input.1.head?.getD 0 = 5 then
          compactSyntaxContinue input.1.tail
            ([compactProofSequentTask, compactProofFormulaTask 1,
              compactProofTask] ++ input.2)
        else if input.1.head?.getD 0 = 6 then
          compactSyntaxContinue input.1.tail
            ([compactProofSequentTask, compactProofFormulaTask 1,
              compactProofTermTask 0, compactProofTask] ++ input.2)
        else if input.1.head?.getD 0 = 7 then
          compactSyntaxContinue input.1.tail
            ([compactProofSequentTask, compactProofTask] ++ input.2)
        else if input.1.head?.getD 0 = 8 then
          compactSyntaxContinue input.1.tail
            ([compactProofSequentTask, compactProofTask] ++ input.2)
        else if input.1.head?.getD 0 = 9 then
          compactSyntaxContinue input.1.tail
            ([compactProofSequentTask, compactProofFormulaTask 0,
              compactProofTask, compactProofTask] ++ input.2)
        else compactSyntaxFailure input.1 input.2) :=
    Primrec.ite (htagEq 0) h0
      (Primrec.ite (htagEq 1) h1
        (Primrec.ite (htagEq 2) h2
          (Primrec.ite (htagEq 3) h3
            (Primrec.ite (htagEq 4) h4
              (Primrec.ite (htagEq 5) h5
                (Primrec.ite (htagEq 6) h6
                  (Primrec.ite (htagEq 7) h7
                    (Primrec.ite (htagEq 8) h8
                      (Primrec.ite (htagEq 9) h9 hfailure)))))))))
  exact
    (Primrec.ite hempty hfailure hnonempty).of_eq fun input => by
      cases input.1 <;>
        simp [compactProofNodeTokenStep]

theorem compactProofParserTaskTokenStep_primrec :
    Primrec compactProofParserTaskTokenStep := by
  have htask : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask => input.1) :=
    Primrec.fst
  have hkind : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask => input.1.1) :=
    Primrec.fst.comp htask
  have harity : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask => input.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp htask)
  have htokens : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have htasks : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hkindEq (kind : Nat) : PrimrecPred
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask => input.1.1 = kind) :=
    Primrec.eq.comp hkind (Primrec.const kind)
  have hsyntaxInput : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask =>
        (input.1.2.1, input.2.1, input.2.2)) :=
    Primrec.pair harity (Primrec.pair htokens htasks)
  have hproof : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask =>
        compactProofNodeTokenStep input.2.1 input.2.2) :=
    compactProofNodeTokenStep_primrec.comp htokens htasks
  have hformula : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask =>
        compactProofFormulaTokenStep
          (input.1.2.1, input.2.1, input.2.2)) :=
    compactProofFormulaTokenStep_primrec.comp hsyntaxInput
  have hterm : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask =>
        compactProofTermTokenStep
          (input.1.2.1, input.2.1, input.2.2)) :=
    compactProofTermTokenStep_primrec.comp hsyntaxInput
  have hsequent : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask =>
        compactProofSequentTokenStep input.2.1 input.2.2) :=
    compactProofSequentTokenStep_primrec.comp htokens htasks
  have hfailure : Primrec
      (fun input : CompactProofParserTask × List Nat ×
          List CompactProofParserTask =>
        compactSyntaxFailure input.2.1 input.2.2) :=
    compactSyntaxFailure_primrec.comp htokens htasks
  exact
    (Primrec.ite (hkindEq 3) hproof
      (Primrec.ite (hkindEq 4) hformula
        (Primrec.ite (hkindEq 5) hterm
          (Primrec.ite (hkindEq 6)
            compactProofRepeatFormulaTokenStep_primrec
            (Primrec.ite (hkindEq 7) hsequent hfailure))))).of_eq
      fun input => by
        simp only [compactProofParserTaskTokenStep]

theorem compactProofParserRunningStep_primrec :
    Primrec compactProofParserRunningStep := by
  have htokens : Primrec
      (fun state : CompactProofParserState => state.1) :=
    Primrec.fst
  have htasks : Primrec
      (fun state : CompactProofParserState => state.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hempty : PrimrecPred
      (fun state : CompactProofParserState => state.2.1 = []) :=
    Primrec.eq.comp htasks (Primrec.const [])
  have hsuccessStatus : Primrec
      (fun state : CompactProofParserState => some (some state.1)) :=
    Primrec.option_some.comp (Primrec.option_some.comp htokens)
  have hsuccess : Primrec
      (fun state : CompactProofParserState =>
        (state.1, [], some (some state.1))) :=
    Primrec.pair htokens
      (Primrec.pair (Primrec.const ([] : List CompactProofParserTask))
        hsuccessStatus)
  have hheadOption : Primrec
      (fun state : CompactProofParserState => state.2.1.head?) :=
    Primrec.list_head?.comp htasks
  have hhead : Primrec
      (fun state : CompactProofParserState =>
        state.2.1.head?.getD compactProofTask) :=
    Primrec.option_getD.comp hheadOption (Primrec.const compactProofTask)
  have htail : Primrec
      (fun state : CompactProofParserState => state.2.1.tail) :=
    Primrec.list_tail.comp htasks
  have hinput : Primrec
      (fun state : CompactProofParserState =>
        (state.2.1.head?.getD compactProofTask,
          state.1, state.2.1.tail)) :=
    Primrec.pair hhead (Primrec.pair htokens htail)
  have hbranch : Primrec
      (fun state : CompactProofParserState =>
        compactProofParserTaskTokenStep
          (state.2.1.head?.getD compactProofTask,
            state.1, state.2.1.tail)) :=
    compactProofParserTaskTokenStep_primrec.comp hinput
  exact
    (Primrec.ite hempty hsuccess hbranch).of_eq fun state => by
      cases htasksValue : state.2.1 <;>
        simp [compactProofParserRunningStep, htasksValue]

theorem compactProofParserStep_primrec :
    Primrec compactProofParserStep := by
  have hstatus : Primrec
      (fun state : CompactProofParserState => state.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hdone : Primrec
      (fun state : CompactProofParserState => state.2.2.isSome) :=
    Primrec.option_isSome.comp hstatus
  exact
    (Primrec.cond hdone Primrec.id
      compactProofParserRunningStep_primrec).of_eq fun state => by
        cases hstatusValue : state.2.2 <;>
          simp [compactProofParserStep, hstatusValue]

theorem compactProofParserFuelBound_primrec :
    Primrec compactProofParserFuelBound := by
  have hsize : Primrec (fun tokens : List Nat => tokens.length + 1) :=
    Primrec.succ.comp Primrec.list_length
  have hsquare : Primrec
      (fun tokens : List Nat =>
        (tokens.length + 1) * (tokens.length + 1)) :=
    Primrec.nat_mul.comp hsize hsize
  have hscaled : Primrec
      (fun tokens : List Nat =>
        32 * ((tokens.length + 1) * (tokens.length + 1))) :=
    Primrec.nat_mul.comp (Primrec.const 32) hsquare
  exact
    (Primrec.nat_add.comp hscaled (Primrec.const 16)).of_eq
      fun tokens => by
        simp [compactProofParserFuelBound, Nat.mul_assoc]

theorem compactProofParserInitialState_primrec :
    Primrec compactProofParserInitialState := by
  exact
    (Primrec.pair Primrec.id
      (Primrec.pair
        (Primrec.const ([compactProofTask] : List CompactProofParserTask))
        (Primrec.const (none : Option (Option (List Nat)))))).of_eq
      fun tokens => by rfl

theorem compactProofTokenParserRun_primrec :
    Primrec compactProofTokenParserRun := by
  have hstep : Primrec₂
      (fun (_tokens : List Nat) (state : CompactProofParserState) =>
        compactProofParserStep state) :=
    (compactProofParserStep_primrec.comp Primrec.snd).to₂
  exact
    (Primrec.nat_iterate compactProofParserFuelBound_primrec
      compactProofParserInitialState_primrec hstep).of_eq
      fun tokens => by rfl

theorem compactProofTokenParser_primrec :
    Primrec compactProofTokenParser := by
  exact
    (compactSyntaxParserStateOutput_primrec.comp
      compactProofTokenParserRun_primrec).of_eq fun tokens => by rfl

#print axioms compactProofNodeTokenStep_primrec
#print axioms compactProofParserStep_primrec
#print axioms compactProofTokenParser_primrec
#print axioms compactListedProofTask_execute
#print axioms compactProofTokenParser_canonical_append

end FoundationCompactProofTokenMachine
