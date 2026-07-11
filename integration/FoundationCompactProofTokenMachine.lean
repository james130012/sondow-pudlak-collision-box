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

end FoundationCompactProofTokenMachine
