import integration.FoundationCompactArithmeticSymbolCode

/-!
# Numeric token machine for compact arithmetic syntax

The machine validates the same prefix grammar used by the typed compact
decoder, but its state contains only naturals and lists of naturals.  Function
arguments are scheduled through a repeat frame, so a huge arity token cannot
materialize a huge hidden task list in one transition.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationCompactSyntaxTokenMachine

open FoundationCompactArithmeticSymbolCode
open FoundationSuccinctFiniteConsistencyTarget

def compactArithmeticTermTokens {binderArity : Nat} :
    LO.FirstOrder.ArithmeticSemiterm Nat binderArity -> List Nat
  | #index => [0, index.val]
  | &freeIndex => [1, freeIndex]
  | Semiterm.func (arity := functionArity) functionSymbol arguments =>
      [2, functionArity, Encodable.encode functionSymbol] ++
        (List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten

def compactArithmeticFormulaTokens {binderArity : Nat} :
    LO.FirstOrder.ArithmeticSemiformula Nat binderArity -> List Nat
  | Semiformula.rel (arity := relationArity) relationSymbol arguments =>
      [0, relationArity, Encodable.encode relationSymbol] ++
        (List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten
  | Semiformula.nrel (arity := relationArity) relationSymbol arguments =>
      [1, relationArity, Encodable.encode relationSymbol] ++
        (List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten
  | ⊤ => [2]
  | ⊥ => [3]
  | left ⋏ right =>
      4 :: compactArithmeticFormulaTokens left ++
        compactArithmeticFormulaTokens right
  | left ⋎ right =>
      5 :: compactArithmeticFormulaTokens left ++
        compactArithmeticFormulaTokens right
  | ∀⁰ body => 6 :: compactArithmeticFormulaTokens body
  | ∃⁰ body => 7 :: compactArithmeticFormulaTokens body

def compactTermTaskSteps {binderArity : Nat} :
    LO.FirstOrder.ArithmeticSemiterm Nat binderArity -> Nat
  | #_ => 1
  | &_ => 1
  | Semiterm.func _ arguments =>
      2 + (List.ofFn fun index =>
        1 + compactTermTaskSteps (arguments index)).sum

def compactFormulaTaskSteps {binderArity : Nat} :
    LO.FirstOrder.ArithmeticSemiformula Nat binderArity -> Nat
  | Semiformula.rel _ arguments =>
      2 + (List.ofFn fun index =>
        1 + compactTermTaskSteps (arguments index)).sum
  | Semiformula.nrel _ arguments =>
      2 + (List.ofFn fun index =>
        1 + compactTermTaskSteps (arguments index)).sum
  | ⊤ => 1
  | ⊥ => 1
  | left ⋏ right =>
      1 + compactFormulaTaskSteps left + compactFormulaTaskSteps right
  | left ⋎ right =>
      1 + compactFormulaTaskSteps left + compactFormulaTaskSteps right
  | ∀⁰ body => 1 + compactFormulaTaskSteps body
  | ∃⁰ body => 1 + compactFormulaTaskSteps body

def compactTermListTokens {binderArity : Nat}
    (terms : List (LO.FirstOrder.ArithmeticSemiterm Nat binderArity)) :
    List Nat :=
  terms.flatMap compactArithmeticTermTokens

def compactTermListRepeatSteps {binderArity : Nat}
    (terms : List (LO.FirstOrder.ArithmeticSemiterm Nat binderArity)) : Nat :=
  1 + (terms.map fun term => 1 + compactTermTaskSteps term).sum

@[simp] theorem compactTermListTokens_ofFn
    {binderArity count : Nat}
    (terms : Fin count ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity) :
    compactTermListTokens (List.ofFn terms) =
      (List.ofFn fun index =>
        compactArithmeticTermTokens (terms index)).flatten := by
  simp [compactTermListTokens, List.ofFn_comp', List.flatMap]

theorem arithmeticFuncCodeValid_encode
    {arity : Nat}
    (functionSymbol : (ℒₒᵣ : LO.FirstOrder.Language).Func arity) :
    ArithmeticFuncCodeValid arity (Encodable.encode functionSymbol) := by
  apply (arithmeticFuncCodeValid_iff_decode₂_ne_none
    arity (Encodable.encode functionSymbol)).2
  simp

theorem arithmeticRelCodeValid_encode
    {arity : Nat}
    (relationSymbol : (ℒₒᵣ : LO.FirstOrder.Language).Rel arity) :
    ArithmeticRelCodeValid arity (Encodable.encode relationSymbol) := by
  apply (arithmeticRelCodeValid_iff_decode₂_ne_none
    arity (Encodable.encode relationSymbol)).2
  simp

/-- `(kind, binderArity, count)`: kind 0 is a term task, kind 1 is a
formula task, and kind 2 is a repeated-term frame. -/
abbrev CompactSyntaxTask := Nat × Nat × Nat

def compactTermTask (binderArity : Nat) : CompactSyntaxTask :=
  (0, binderArity, 0)

def compactFormulaTask (binderArity : Nat) : CompactSyntaxTask :=
  (1, binderArity, 0)

def compactRepeatTermTask
    (binderArity count : Nat) : CompactSyntaxTask :=
  (2, binderArity, count)

abbrev CompactSyntaxParserStatus := Option (Option (List Nat))

abbrev CompactSyntaxParserState :=
  List Nat × List CompactSyntaxTask × CompactSyntaxParserStatus

/-- Input to one term-task transition: binder arity, remaining tokens, and
the continuation task stack. -/
abbrev CompactTermBranchInput :=
  Nat × List Nat × List CompactSyntaxTask

abbrev CompactFormulaBranchInput :=
  Nat × List Nat × List CompactSyntaxTask

def compactTokenAt (index : Nat) (tokens : List Nat) : Nat :=
  tokens[index]?.getD 0

def compactSyntaxFailure
    (tokens : List Nat) (tasks : List CompactSyntaxTask) :
    CompactSyntaxParserState :=
  (tokens, tasks, some none)

def compactSyntaxContinue
    (tokens : List Nat) (tasks : List CompactSyntaxTask) :
    CompactSyntaxParserState :=
  (tokens, tasks, none)

def compactTermTokenStep
    (input : CompactTermBranchInput) : CompactSyntaxParserState :=
  let binderArity := input.1
  let tokens := input.2.1
  let tasks := input.2.2
  let tag := compactTokenAt 0 tokens
  let argument := compactTokenAt 1 tokens
  if 2 <= tokens.length then
    if tag = 0 then
      if argument < binderArity then
        compactSyntaxContinue (tokens.drop 2) tasks
      else
        compactSyntaxFailure tokens tasks
    else if tag = 1 then
      compactSyntaxContinue (tokens.drop 2) tasks
    else if tag = 2 then
      if 3 <= tokens.length then
        let functionArity := argument
        let functionCode := compactTokenAt 2 tokens
        if ArithmeticFuncCodeValid functionArity functionCode then
          compactSyntaxContinue (tokens.drop 3)
            (compactRepeatTermTask binderArity functionArity :: tasks)
        else
          compactSyntaxFailure tokens tasks
      else
        compactSyntaxFailure tokens tasks
    else
      compactSyntaxFailure tokens tasks
  else
    compactSyntaxFailure tokens tasks

def compactFormulaTokenStep
    (input : CompactFormulaBranchInput) : CompactSyntaxParserState :=
  let binderArity := input.1
  let tokens := input.2.1
  let tasks := input.2.2
  let tag := compactTokenAt 0 tokens
  if 1 <= tokens.length then
    if tag = 0 then
      if 3 <= tokens.length then
        let relationArity := compactTokenAt 1 tokens
        let relationCode := compactTokenAt 2 tokens
        if ArithmeticRelCodeValid relationArity relationCode then
          compactSyntaxContinue (tokens.drop 3)
            (compactRepeatTermTask binderArity relationArity :: tasks)
        else
          compactSyntaxFailure tokens tasks
      else
        compactSyntaxFailure tokens tasks
    else if tag = 1 then
      if 3 <= tokens.length then
        let relationArity := compactTokenAt 1 tokens
        let relationCode := compactTokenAt 2 tokens
        if ArithmeticRelCodeValid relationArity relationCode then
          compactSyntaxContinue (tokens.drop 3)
            (compactRepeatTermTask binderArity relationArity :: tasks)
        else
          compactSyntaxFailure tokens tasks
      else
        compactSyntaxFailure tokens tasks
    else if tag = 2 then
      compactSyntaxContinue (tokens.drop 1) tasks
    else if tag = 3 then
      compactSyntaxContinue (tokens.drop 1) tasks
    else if tag = 4 then
      compactSyntaxContinue (tokens.drop 1)
        (compactFormulaTask binderArity ::
          compactFormulaTask binderArity :: tasks)
    else if tag = 5 then
      compactSyntaxContinue (tokens.drop 1)
        (compactFormulaTask binderArity ::
          compactFormulaTask binderArity :: tasks)
    else if tag = 6 then
      compactSyntaxContinue (tokens.drop 1)
        (compactFormulaTask (binderArity + 1) :: tasks)
    else if tag = 7 then
      compactSyntaxContinue (tokens.drop 1)
        (compactFormulaTask (binderArity + 1) :: tasks)
    else
      compactSyntaxFailure tokens tasks
  else
    compactSyntaxFailure tokens tasks

@[simp] theorem compactTermTokenStep_bvar
    {binderArity : Nat} (index : Fin binderArity)
    (suffix : List Nat) (tasks : List CompactSyntaxTask) :
    compactTermTokenStep
        (binderArity,
          compactArithmeticTermTokens (#index) ++ suffix, tasks) =
      compactSyntaxContinue suffix tasks := by
  simp [compactArithmeticTermTokens, compactTermTokenStep,
    compactTokenAt, index.isLt]

@[simp] theorem compactTermTokenStep_fvar
    {binderArity : Nat} (freeIndex : Nat)
    (suffix : List Nat) (tasks : List CompactSyntaxTask) :
    compactTermTokenStep
        (binderArity,
          compactArithmeticTermTokens
            (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) ++
              suffix,
          tasks) =
      compactSyntaxContinue suffix tasks := by
  simp [compactArithmeticTermTokens, compactTermTokenStep,
    compactTokenAt]

@[simp] theorem compactTermTokenStep_func
    {binderArity functionArity : Nat}
    (functionSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Func functionArity)
    (arguments : Fin functionArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix : List Nat) (tasks : List CompactSyntaxTask) :
    compactTermTokenStep
        (binderArity,
          compactArithmeticTermTokens
              (Semiterm.func functionSymbol arguments) ++ suffix,
          tasks) =
      compactSyntaxContinue
        ((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix)
        (compactRepeatTermTask binderArity functionArity :: tasks) := by
  have hvalid : ArithmeticFuncCodeValid functionArity
      (Encodable.encode functionSymbol) :=
    arithmeticFuncCodeValid_encode functionSymbol
  simp [compactArithmeticTermTokens, compactTermTokenStep,
    compactTokenAt, hvalid]

@[simp] theorem compactFormulaTokenStep_rel
    {binderArity relationArity : Nat}
    (relationSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Rel relationArity)
    (arguments : Fin relationArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaTokenStep
        (binderArity,
          compactArithmeticFormulaTokens
              (Semiformula.rel relationSymbol arguments) ++ suffix,
          tasks) =
      compactSyntaxContinue
        ((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix)
        (compactRepeatTermTask binderArity relationArity :: tasks) := by
  have hvalid : ArithmeticRelCodeValid relationArity
      (Encodable.encode relationSymbol) :=
    arithmeticRelCodeValid_encode relationSymbol
  simp [compactArithmeticFormulaTokens, compactFormulaTokenStep,
    compactTokenAt, hvalid]

@[simp] theorem compactFormulaTokenStep_nrel
    {binderArity relationArity : Nat}
    (relationSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Rel relationArity)
    (arguments : Fin relationArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaTokenStep
        (binderArity,
          compactArithmeticFormulaTokens
              (Semiformula.nrel relationSymbol arguments) ++ suffix,
          tasks) =
      compactSyntaxContinue
        ((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix)
        (compactRepeatTermTask binderArity relationArity :: tasks) := by
  have hvalid : ArithmeticRelCodeValid relationArity
      (Encodable.encode relationSymbol) :=
    arithmeticRelCodeValid_encode relationSymbol
  simp [compactArithmeticFormulaTokens, compactFormulaTokenStep,
    compactTokenAt, hvalid]

@[simp] theorem compactFormulaTokenStep_verum
    {binderArity : Nat} (suffix : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaTokenStep
        (binderArity,
          compactArithmeticFormulaTokens (⊤ :
            LO.FirstOrder.ArithmeticSemiformula Nat binderArity) ++ suffix,
          tasks) =
      compactSyntaxContinue suffix tasks := by
  simp [compactArithmeticFormulaTokens, compactFormulaTokenStep,
    compactTokenAt]

@[simp] theorem compactFormulaTokenStep_falsum
    {binderArity : Nat} (suffix : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaTokenStep
        (binderArity,
          compactArithmeticFormulaTokens (⊥ :
            LO.FirstOrder.ArithmeticSemiformula Nat binderArity) ++ suffix,
          tasks) =
      compactSyntaxContinue suffix tasks := by
  simp [compactArithmeticFormulaTokens, compactFormulaTokenStep,
    compactTokenAt]

@[simp] theorem compactFormulaTokenStep_and
    {binderArity : Nat}
    (left right :
      LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaTokenStep
        (binderArity,
          compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
          tasks) =
      compactSyntaxContinue
        (compactArithmeticFormulaTokens left ++
          compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask binderArity ::
          compactFormulaTask binderArity :: tasks) := by
  simp [compactArithmeticFormulaTokens, compactFormulaTokenStep,
    compactTokenAt, List.append_assoc]

@[simp] theorem compactFormulaTokenStep_or
    {binderArity : Nat}
    (left right :
      LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaTokenStep
        (binderArity,
          compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
          tasks) =
      compactSyntaxContinue
        (compactArithmeticFormulaTokens left ++
          compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask binderArity ::
          compactFormulaTask binderArity :: tasks) := by
  simp [compactArithmeticFormulaTokens, compactFormulaTokenStep,
    compactTokenAt, List.append_assoc]

@[simp] theorem compactFormulaTokenStep_all
    {binderArity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (binderArity + 1))
    (suffix : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaTokenStep
        (binderArity,
          compactArithmeticFormulaTokens (∀⁰ body) ++ suffix, tasks) =
      compactSyntaxContinue
        (compactArithmeticFormulaTokens body ++ suffix)
        (compactFormulaTask (binderArity + 1) :: tasks) := by
  simp [compactArithmeticFormulaTokens, compactFormulaTokenStep,
    compactTokenAt]

@[simp] theorem compactFormulaTokenStep_exs
    {binderArity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (binderArity + 1))
    (suffix : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaTokenStep
        (binderArity,
          compactArithmeticFormulaTokens (∃⁰ body) ++ suffix, tasks) =
      compactSyntaxContinue
        (compactArithmeticFormulaTokens body ++ suffix)
        (compactFormulaTask (binderArity + 1) :: tasks) := by
  simp [compactArithmeticFormulaTokens, compactFormulaTokenStep,
    compactTokenAt]

theorem flatten_map_flatMap_eq_flatMap_flatten
    {alpha beta : Type*} (transform : alpha -> List beta)
    (values : List (List alpha)) :
    (values.map (List.flatMap transform)).flatten =
      values.flatten.flatMap transform := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp [ih, List.flatMap_append]

@[simp] theorem flatten_ofFn_flatMap_eq_flatMap_flatten
    {alpha beta : Type*} {count : Nat}
    (transform : alpha -> List beta) (values : Fin count -> List alpha) :
    (List.ofFn fun index => (values index).flatMap transform).flatten =
      (List.ofFn values).flatten.flatMap transform := by
  rw [List.ofFn_comp' values (List.flatMap transform)]
  exact flatten_map_flatMap_eq_flatMap_flatten transform (List.ofFn values)

theorem binaryTermCode_eq_tokenStream
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) :
    binaryTermCode term =
      (compactArithmeticTermTokens term).flatMap binaryNatCode := by
  induction term with
  | bvar index => simp [binaryTermCode, compactArithmeticTermTokens]
  | fvar freeIndex => simp [binaryTermCode, compactArithmeticTermTokens]
  | func functionSymbol arguments ih =>
      simp [binaryTermCode, compactArithmeticTermTokens,
        List.flatMap_append, ih]

theorem binaryFormulaCode_eq_tokenStream
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) :
    binaryFormulaCode formula =
      (compactArithmeticFormulaTokens formula).flatMap binaryNatCode := by
  induction formula with
  | rel relationSymbol arguments =>
      simp [binaryFormulaCode, compactArithmeticFormulaTokens,
        List.flatMap_append, binaryTermCode_eq_tokenStream]
  | nrel relationSymbol arguments =>
      simp [binaryFormulaCode, compactArithmeticFormulaTokens,
        List.flatMap_append, binaryTermCode_eq_tokenStream]
  | verum => simp [binaryFormulaCode, compactArithmeticFormulaTokens]
  | falsum => simp [binaryFormulaCode, compactArithmeticFormulaTokens]
  | and left right ihLeft ihRight =>
      simp [binaryFormulaCode, compactArithmeticFormulaTokens,
        List.flatMap_append, ihLeft, ihRight, List.append_assoc]
  | or left right ihLeft ihRight =>
      simp [binaryFormulaCode, compactArithmeticFormulaTokens,
        List.flatMap_append, ihLeft, ihRight, List.append_assoc]
  | all body ih =>
      simp [binaryFormulaCode, compactArithmeticFormulaTokens,
        List.flatMap_append, ih]
  | exs body ih =>
      simp [binaryFormulaCode, compactArithmeticFormulaTokens,
        List.flatMap_append, ih]

abbrev CompactTaskBranchInput :=
  CompactSyntaxTask × List Nat × List CompactSyntaxTask

def compactRepeatTermTokenStep
    (input : CompactTaskBranchInput) : CompactSyntaxParserState :=
  let binderArity := input.1.2.1
  let count := input.1.2.2
  let tokens := input.2.1
  let tasks := input.2.2
  if count = 0 then
    compactSyntaxContinue tokens tasks
  else
    compactSyntaxContinue tokens
      (compactTermTask binderArity ::
        compactRepeatTermTask binderArity (count - 1) :: tasks)

def compactSyntaxTaskTokenStep
    (input : CompactTaskBranchInput) : CompactSyntaxParserState :=
  let kind := input.1.1
  let binderArity := input.1.2.1
  let tokens := input.2.1
  let tasks := input.2.2
  if kind = 0 then
    compactTermTokenStep (binderArity, tokens, tasks)
  else if kind = 1 then
    compactFormulaTokenStep (binderArity, tokens, tasks)
  else if kind = 2 then
    compactRepeatTermTokenStep input
  else
    compactSyntaxFailure tokens tasks

def compactSyntaxRunningStep
    (state : CompactSyntaxParserState) : CompactSyntaxParserState :=
  match state.2.1 with
  | [] => (state.1, [], some (some state.1))
  | task :: tasks =>
      compactSyntaxTaskTokenStep (task, state.1, tasks)

def compactSyntaxParserStep
    (state : CompactSyntaxParserState) : CompactSyntaxParserState :=
  if state.2.2.isSome then state else compactSyntaxRunningStep state

def compactSyntaxRunFuelBound (tokens : List Nat) : Nat :=
  16 * (tokens.length + 1) * (tokens.length + 1) + 8

def compactTermParserInitialState
    (binderArity : Nat) (tokens : List Nat) :
    CompactSyntaxParserState :=
  (tokens, [compactTermTask binderArity], none)

def compactFormulaParserInitialState
    (binderArity : Nat) (tokens : List Nat) :
    CompactSyntaxParserState :=
  (tokens, [compactFormulaTask binderArity], none)

def compactTermTokenParserRun
    (binderArity : Nat) (tokens : List Nat) :
    CompactSyntaxParserState :=
  (compactSyntaxParserStep^[compactSyntaxRunFuelBound tokens])
    (compactTermParserInitialState binderArity tokens)

def compactFormulaTokenParserRun
    (binderArity : Nat) (tokens : List Nat) :
    CompactSyntaxParserState :=
  (compactSyntaxParserStep^[compactSyntaxRunFuelBound tokens])
    (compactFormulaParserInitialState binderArity tokens)

def compactSyntaxParserStateOutput
    (state : CompactSyntaxParserState) : Option (List Nat) :=
  state.2.2.getD none

def compactTermTokenParser
    (binderArity : Nat) (tokens : List Nat) : Option (List Nat) :=
  compactSyntaxParserStateOutput
    (compactTermTokenParserRun binderArity tokens)

def compactFormulaTokenParser
    (binderArity : Nat) (tokens : List Nat) : Option (List Nat) :=
  compactSyntaxParserStateOutput
    (compactFormulaTokenParserRun binderArity tokens)

@[simp] theorem compactSyntaxParserStep_term
    (binderArity : Nat) (tokens : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactSyntaxParserStep
        (tokens, compactTermTask binderArity :: tasks, none) =
      compactTermTokenStep (binderArity, tokens, tasks) := by
  simp [compactSyntaxParserStep, compactSyntaxRunningStep,
    compactSyntaxTaskTokenStep, compactTermTask]

@[simp] theorem compactSyntaxParserStep_formula
    (binderArity : Nat) (tokens : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactSyntaxParserStep
        (tokens, compactFormulaTask binderArity :: tasks, none) =
      compactFormulaTokenStep (binderArity, tokens, tasks) := by
  simp [compactSyntaxParserStep, compactSyntaxRunningStep,
    compactSyntaxTaskTokenStep, compactFormulaTask]

@[simp] theorem compactSyntaxParserStep_repeat_zero
    (binderArity : Nat) (tokens : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactSyntaxParserStep
        (tokens, compactRepeatTermTask binderArity 0 :: tasks, none) =
      compactSyntaxContinue tokens tasks := by
  simp [compactSyntaxParserStep, compactSyntaxRunningStep,
    compactSyntaxTaskTokenStep, compactRepeatTermTokenStep,
    compactRepeatTermTask]

@[simp] theorem compactSyntaxParserStep_repeat_succ
    (binderArity count : Nat) (tokens : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactSyntaxParserStep
        (tokens, compactRepeatTermTask binderArity (count + 1) :: tasks,
          none) =
      compactSyntaxContinue tokens
        (compactTermTask binderArity ::
          compactRepeatTermTask binderArity count :: tasks) := by
  simp [compactSyntaxParserStep, compactSyntaxRunningStep,
    compactSyntaxTaskTokenStep, compactRepeatTermTokenStep,
    compactRepeatTermTask]

theorem compactSyntaxParser_iterate_trans
    {start middle finish : CompactSyntaxParserState}
    {firstSteps secondSteps : Nat}
    (hfirst : (compactSyntaxParserStep^[firstSteps]) start = middle)
    (hsecond : (compactSyntaxParserStep^[secondSteps]) middle = finish) :
    (compactSyntaxParserStep^[firstSteps + secondSteps]) start = finish := by
  rw [Nat.add_comm, Function.iterate_add_apply, hfirst, hsecond]

theorem compactTermTask_execute
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix : List Nat) (tasks : List CompactSyntaxTask) :
    (compactSyntaxParserStep^[compactTermTaskSteps term])
        (compactArithmeticTermTokens term ++ suffix,
          compactTermTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
  induction term generalizing suffix tasks with
  | bvar index =>
      simp [compactTermTaskSteps, Function.iterate_one,
        compactSyntaxContinue]
  | fvar freeIndex =>
      simp [compactTermTaskSteps, Function.iterate_one,
        compactSyntaxContinue]
  | @func functionArity functionSymbol arguments ih =>
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat binderArity) :=
        List.ofFn arguments
      have hmembers : ∀ member ∈ terms,
          ∀ (memberSuffix : List Nat)
            (memberTasks : List CompactSyntaxTask),
          (compactSyntaxParserStep^[compactTermTaskSteps member])
              (compactArithmeticTermTokens member ++ memberSuffix,
                compactTermTask binderArity :: memberTasks, none) =
            (memberSuffix, memberTasks, none) := by
        intro member hmember memberSuffix memberTasks
        rw [List.mem_ofFn] at hmember
        rcases hmember with ⟨index, rfl⟩
        exact ih index memberSuffix memberTasks
      have hrepeat : ∀ (termList : List
          (LO.FirstOrder.ArithmeticSemiterm Nat binderArity)),
          (∀ member ∈ termList,
            ∀ (memberSuffix : List Nat)
              (memberTasks : List CompactSyntaxTask),
            (compactSyntaxParserStep^[compactTermTaskSteps member])
                (compactArithmeticTermTokens member ++ memberSuffix,
                  compactTermTask binderArity :: memberTasks, none) =
              (memberSuffix, memberTasks, none)) ->
          (compactSyntaxParserStep^[compactTermListRepeatSteps termList])
              (compactTermListTokens termList ++ suffix,
                compactRepeatTermTask binderArity termList.length :: tasks,
                none) =
            (suffix, tasks, none) := by
        intro termList
        induction termList with
        | nil =>
            intro _
            simp [compactTermListRepeatSteps, compactTermListTokens,
              Function.iterate_one, compactSyntaxContinue]
        | cons head tail ihTail =>
            intro hall
            have hhead := hall head (by simp)
            have htailMembers : ∀ member ∈ tail,
                ∀ (memberSuffix : List Nat)
                  (memberTasks : List CompactSyntaxTask),
                (compactSyntaxParserStep^[compactTermTaskSteps member])
                    (compactArithmeticTermTokens member ++ memberSuffix,
                      compactTermTask binderArity :: memberTasks, none) =
                  (memberSuffix, memberTasks, none) := by
              intro member hmember
              exact hall member (by simp [hmember])
            have hone :
                (compactSyntaxParserStep^[1])
                    (compactTermListTokens (head :: tail) ++ suffix,
                      compactRepeatTermTask binderArity
                        (head :: tail).length :: tasks,
                      none) =
                  (compactArithmeticTermTokens head ++
                      (compactTermListTokens tail ++ suffix),
                    compactTermTask binderArity ::
                      compactRepeatTermTask binderArity tail.length :: tasks,
                    none) := by
              simp [compactTermListTokens, Function.iterate_one,
                List.append_assoc, compactSyntaxContinue]
            have hheadRun := hhead
              (compactTermListTokens tail ++ suffix)
              (compactRepeatTermTask binderArity tail.length :: tasks)
            have htailRun := ihTail htailMembers
            have hfirst := compactSyntaxParser_iterate_trans hone hheadRun
            have hallRun := compactSyntaxParser_iterate_trans hfirst htailRun
            simpa [compactTermListRepeatSteps, compactTermListTokens,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              List.append_assoc] using hallRun
      have hfirst :
          (compactSyntaxParserStep^[1])
              (compactArithmeticTermTokens
                    (Semiterm.func functionSymbol arguments) ++ suffix,
                compactTermTask binderArity :: tasks, none) =
            (compactTermListTokens terms ++ suffix,
              compactRepeatTermTask binderArity terms.length :: tasks,
              none) := by
        simp [Function.iterate_one, terms, compactTermListTokens,
          List.ofFn_comp', List.append_assoc, compactSyntaxContinue]
        exact (compactTermListTokens_ofFn arguments).symm
      have hrepeatRun := hrepeat terms hmembers
      have hrun := compactSyntaxParser_iterate_trans hfirst hrepeatRun
      have hsteps :
          compactTermTaskSteps
              (Semiterm.func functionSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactTermTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      exact hrun

theorem compactTermList_execute
    {binderArity : Nat}
    (terms : List
      (LO.FirstOrder.ArithmeticSemiterm Nat binderArity))
    (suffix : List Nat) (tasks : List CompactSyntaxTask) :
    (compactSyntaxParserStep^[compactTermListRepeatSteps terms])
        (compactTermListTokens terms ++ suffix,
          compactRepeatTermTask binderArity terms.length :: tasks, none) =
      (suffix, tasks, none) := by
  induction terms with
  | nil =>
      simp [compactTermListRepeatSteps, compactTermListTokens,
        Function.iterate_one, compactSyntaxContinue]
  | cons head tail ih =>
      have hone :
          (compactSyntaxParserStep^[1])
              (compactTermListTokens (head :: tail) ++ suffix,
                compactRepeatTermTask binderArity
                  (head :: tail).length :: tasks,
                none) =
            (compactArithmeticTermTokens head ++
                (compactTermListTokens tail ++ suffix),
              compactTermTask binderArity ::
                compactRepeatTermTask binderArity tail.length :: tasks,
              none) := by
        simp [compactTermListTokens, Function.iterate_one,
          List.append_assoc, compactSyntaxContinue]
      have hhead := compactTermTask_execute head
        (compactTermListTokens tail ++ suffix)
        (compactRepeatTermTask binderArity tail.length :: tasks)
      have hfirst := compactSyntaxParser_iterate_trans hone hhead
      have hall := compactSyntaxParser_iterate_trans hfirst ih
      simpa [compactTermListRepeatSteps, compactTermListTokens,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using hall

theorem compactFormulaTask_execute
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix : List Nat) (tasks : List CompactSyntaxTask) :
    (compactSyntaxParserStep^[compactFormulaTaskSteps formula])
        (compactArithmeticFormulaTokens formula ++ suffix,
          compactFormulaTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
  revert suffix tasks
  let P : (arity : Nat) ->
      LO.FirstOrder.ArithmeticSemiformula Nat arity -> Prop :=
    fun arity formula =>
      ∀ (suffix : List Nat) (tasks : List CompactSyntaxTask),
        (compactSyntaxParserStep^[compactFormulaTaskSteps formula])
            (compactArithmeticFormulaTokens formula ++ suffix,
              compactFormulaTask arity :: tasks, none) =
          (suffix, tasks, none)
  change P binderArity formula
  induction formula with
  | @rel formulaArity relationArity relationSymbol arguments =>
      intro suffix tasks
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat formulaArity) :=
        List.ofFn arguments
      have hfirst :
          (compactSyntaxParserStep^[1])
              (compactArithmeticFormulaTokens
                    (Semiformula.rel relationSymbol arguments) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none) =
            (compactTermListTokens terms ++ suffix,
              compactRepeatTermTask formulaArity terms.length :: tasks,
              none) := by
        simp [Function.iterate_one, terms, compactTermListTokens,
          List.ofFn_comp', List.append_assoc, compactSyntaxContinue]
        exact (compactTermListTokens_ofFn arguments).symm
      have hterms := compactTermList_execute terms suffix tasks
      have hrun := compactSyntaxParser_iterate_trans hfirst hterms
      have hsteps :
          compactFormulaTaskSteps
              (Semiformula.rel relationSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactFormulaTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      exact hrun
  | @nrel formulaArity relationArity relationSymbol arguments =>
      intro suffix tasks
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat formulaArity) :=
        List.ofFn arguments
      have hfirst :
          (compactSyntaxParserStep^[1])
              (compactArithmeticFormulaTokens
                    (Semiformula.nrel relationSymbol arguments) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none) =
            (compactTermListTokens terms ++ suffix,
              compactRepeatTermTask formulaArity terms.length :: tasks,
              none) := by
        simp [Function.iterate_one, terms, compactTermListTokens,
          List.ofFn_comp', List.append_assoc, compactSyntaxContinue]
        exact (compactTermListTokens_ofFn arguments).symm
      have hterms := compactTermList_execute terms suffix tasks
      have hrun := compactSyntaxParser_iterate_trans hfirst hterms
      have hsteps :
          compactFormulaTaskSteps
              (Semiformula.nrel relationSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactFormulaTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      exact hrun
  | @verum formulaArity =>
      intro suffix tasks
      simp only [compactFormulaTaskSteps, Function.iterate_one,
        compactSyntaxParserStep_formula]
      change compactFormulaTokenStep
          (formulaArity,
            compactArithmeticFormulaTokens
                (⊤ : LO.FirstOrder.ArithmeticSemiformula Nat formulaArity) ++
              suffix,
            tasks) =
        compactSyntaxContinue suffix tasks
      exact compactFormulaTokenStep_verum suffix tasks
  | @falsum formulaArity =>
      intro suffix tasks
      simp only [compactFormulaTaskSteps, Function.iterate_one,
        compactSyntaxParserStep_formula]
      change compactFormulaTokenStep
          (formulaArity,
            compactArithmeticFormulaTokens
                (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat formulaArity) ++
              suffix,
            tasks) =
        compactSyntaxContinue suffix tasks
      exact compactFormulaTokenStep_falsum suffix tasks
  | @and formulaArity left right ihLeft ihRight =>
      intro suffix tasks
      have hone :
          (compactSyntaxParserStep^[1])
              (compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none) =
            (compactArithmeticFormulaTokens left ++
                (compactArithmeticFormulaTokens right ++ suffix),
              compactFormulaTask formulaArity ::
                compactFormulaTask formulaArity :: tasks,
              none) := by
        simp [Function.iterate_one, List.append_assoc,
          compactSyntaxContinue]
      have hleft := ihLeft
        (compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask formulaArity :: tasks)
      have hright := ihRight suffix tasks
      have hfirst := compactSyntaxParser_iterate_trans hone hleft
      have hrun := compactSyntaxParser_iterate_trans hfirst hright
      change
        (compactSyntaxParserStep^[compactFormulaTaskSteps (left ⋏ right)])
            (compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none) =
          (suffix, tasks, none)
      simpa only [compactFormulaTaskSteps] using hrun
  | @or formulaArity left right ihLeft ihRight =>
      intro suffix tasks
      have hone :
          (compactSyntaxParserStep^[1])
              (compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none) =
            (compactArithmeticFormulaTokens left ++
                (compactArithmeticFormulaTokens right ++ suffix),
              compactFormulaTask formulaArity ::
                compactFormulaTask formulaArity :: tasks,
              none) := by
        simp [Function.iterate_one, List.append_assoc,
          compactSyntaxContinue]
      have hleft := ihLeft
        (compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask formulaArity :: tasks)
      have hright := ihRight suffix tasks
      have hfirst := compactSyntaxParser_iterate_trans hone hleft
      have hrun := compactSyntaxParser_iterate_trans hfirst hright
      change
        (compactSyntaxParserStep^[compactFormulaTaskSteps (left ⋎ right)])
            (compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none) =
          (suffix, tasks, none)
      simpa only [compactFormulaTaskSteps] using hrun
  | @all formulaArity body ih =>
      intro suffix tasks
      have hone :
          (compactSyntaxParserStep^[1])
              (compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none) =
            (compactArithmeticFormulaTokens body ++ suffix,
              compactFormulaTask (formulaArity + 1) :: tasks, none) := by
        simp [Function.iterate_one, compactSyntaxContinue]
      have hbody := ih suffix tasks
      have hrun := compactSyntaxParser_iterate_trans hone hbody
      change
        (compactSyntaxParserStep^[compactFormulaTaskSteps (∀⁰ body)])
            (compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none) =
          (suffix, tasks, none)
      simpa only [compactFormulaTaskSteps] using hrun
  | @exs formulaArity body ih =>
      intro suffix tasks
      have hone :
          (compactSyntaxParserStep^[1])
              (compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none) =
            (compactArithmeticFormulaTokens body ++ suffix,
              compactFormulaTask (formulaArity + 1) :: tasks, none) := by
        simp [Function.iterate_one, compactSyntaxContinue]
      have hbody := ih suffix tasks
      have hrun := compactSyntaxParser_iterate_trans hone hbody
      change
        (compactSyntaxParserStep^[compactFormulaTaskSteps (∃⁰ body)])
            (compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none) =
          (suffix, tasks, none)
      simpa only [compactFormulaTaskSteps] using hrun

theorem compactTermTaskSteps_add_one_le_tokenLength
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) :
    compactTermTaskSteps term + 1 <=
      (compactArithmeticTermTokens term).length := by
  induction term with
  | bvar index =>
      simp [compactTermTaskSteps, compactArithmeticTermTokens]
  | fvar freeIndex =>
      simp [compactTermTaskSteps, compactArithmeticTermTokens]
  | func functionSymbol arguments ih =>
      have hchildren :
          Finset.univ.sum
              (fun index => 1 + compactTermTaskSteps (arguments index)) <=
            Finset.univ.sum
              (fun index =>
                (compactArithmeticTermTokens (arguments index)).length) :=
        Finset.sum_le_sum fun index _ => by
          simpa [Nat.add_comm] using ih index
      have hstepSum := list_sum_ofFn_eq_finset_sum
        (fun index => 1 + compactTermTaskSteps (arguments index))
      have htokenSum := length_flatten_ofFn
        (fun index => compactArithmeticTermTokens (arguments index))
      simp only [compactTermTaskSteps, compactArithmeticTermTokens,
        List.length_append, List.length_cons, List.length_nil]
      rw [hstepSum, htokenSum]
      omega

theorem compactTermListRepeatSteps_le_tokenLength_add_one
    {binderArity : Nat}
    (terms : List
      (LO.FirstOrder.ArithmeticSemiterm Nat binderArity)) :
    compactTermListRepeatSteps terms <=
      (compactTermListTokens terms).length + 1 := by
  induction terms with
  | nil =>
      simp [compactTermListRepeatSteps, compactTermListTokens]
  | cons head tail ih =>
      have hhead := compactTermTaskSteps_add_one_le_tokenLength head
      simp only [compactTermListRepeatSteps, compactTermListTokens,
        List.map_cons, List.sum_cons, List.flatMap_cons,
        List.length_append]
      simp only [compactTermListRepeatSteps, compactTermListTokens] at ih
      omega

theorem compactFormulaTaskSteps_le_tokenLength
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) :
    compactFormulaTaskSteps formula <=
      (compactArithmeticFormulaTokens formula).length := by
  induction formula with
  | rel relationSymbol arguments =>
      have hchildren :
          Finset.univ.sum
              (fun index => 1 + compactTermTaskSteps (arguments index)) <=
            Finset.univ.sum
              (fun index =>
                (compactArithmeticTermTokens (arguments index)).length) :=
        Finset.sum_le_sum fun index _ =>
          by simpa [Nat.add_comm] using
            compactTermTaskSteps_add_one_le_tokenLength (arguments index)
      have hstepSum := list_sum_ofFn_eq_finset_sum
        (fun index => 1 + compactTermTaskSteps (arguments index))
      have htokenSum := length_flatten_ofFn
        (fun index => compactArithmeticTermTokens (arguments index))
      simp only [compactFormulaTaskSteps, compactArithmeticFormulaTokens,
        List.length_append, List.length_cons, List.length_nil]
      rw [hstepSum, htokenSum]
      omega
  | nrel relationSymbol arguments =>
      have hchildren :
          Finset.univ.sum
              (fun index => 1 + compactTermTaskSteps (arguments index)) <=
            Finset.univ.sum
              (fun index =>
                (compactArithmeticTermTokens (arguments index)).length) :=
        Finset.sum_le_sum fun index _ =>
          by simpa [Nat.add_comm] using
            compactTermTaskSteps_add_one_le_tokenLength (arguments index)
      have hstepSum := list_sum_ofFn_eq_finset_sum
        (fun index => 1 + compactTermTaskSteps (arguments index))
      have htokenSum := length_flatten_ofFn
        (fun index => compactArithmeticTermTokens (arguments index))
      simp only [compactFormulaTaskSteps, compactArithmeticFormulaTokens,
        List.length_append, List.length_cons, List.length_nil]
      rw [hstepSum, htokenSum]
      omega
  | verum =>
      simp [compactFormulaTaskSteps, compactArithmeticFormulaTokens]
  | falsum =>
      simp [compactFormulaTaskSteps, compactArithmeticFormulaTokens]
  | and left right ihLeft ihRight =>
      simp only [compactFormulaTaskSteps, compactArithmeticFormulaTokens,
        List.length_cons, List.length_append]
      omega
  | or left right ihLeft ihRight =>
      simp only [compactFormulaTaskSteps, compactArithmeticFormulaTokens,
        List.length_cons, List.length_append]
      omega
  | all body ih =>
      simp only [compactFormulaTaskSteps, compactArithmeticFormulaTokens,
        List.length_cons]
      omega
  | exs body ih =>
      simp only [compactFormulaTaskSteps, compactArithmeticFormulaTokens,
        List.length_cons]
      omega

theorem compactSyntaxRunFuelBound_length_add_one
    (tokens : List Nat) :
    tokens.length + 1 <= compactSyntaxRunFuelBound tokens := by
  simp only [compactSyntaxRunFuelBound]
  nlinarith

@[simp] theorem compactSyntaxParserStep_empty
    (tokens : List Nat) :
    compactSyntaxParserStep (tokens, [], none) =
      (tokens, [], some (some tokens)) := by
  simp [compactSyntaxParserStep, compactSyntaxRunningStep]

theorem compactSyntaxParserStep_done
    (tokens : List Nat) (tasks : List CompactSyntaxTask)
    (result : Option (List Nat)) :
    compactSyntaxParserStep (tokens, tasks, some result) =
      (tokens, tasks, some result) := by
  simp [compactSyntaxParserStep]

theorem compactSyntaxParserStep_iterate_done
    (fuel : Nat) (tokens : List Nat) (tasks : List CompactSyntaxTask)
    (result : Option (List Nat)) :
    (compactSyntaxParserStep^[fuel]) (tokens, tasks, some result) =
      (tokens, tasks, some result) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply,
        compactSyntaxParserStep_done, ih]

theorem compactTermTokenParser_canonical_append
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix : List Nat) :
    compactTermTokenParser binderArity
        (compactArithmeticTermTokens term ++ suffix) =
      some suffix := by
  let tokens := compactArithmeticTermTokens term ++ suffix
  let used := compactTermTaskSteps term + 1
  have htask := compactTermTask_execute term suffix []
  have hfinish :
      (compactSyntaxParserStep^[used])
          (tokens, [compactTermTask binderArity], none) =
        (suffix, [], some (some suffix)) := by
    apply compactSyntaxParser_iterate_trans htask
    simp [Function.iterate_one]
  have hterm := compactTermTaskSteps_add_one_le_tokenLength term
  have hinputLength :
      (compactArithmeticTermTokens term).length <= tokens.length := by
    simp [tokens]
  have hfuelLength := compactSyntaxRunFuelBound_length_add_one tokens
  have hused : used <= compactSyntaxRunFuelBound tokens := by
    omega
  obtain ⟨extra, hfuel⟩ := exists_add_of_le hused
  have hrun :
      (compactSyntaxParserStep^[compactSyntaxRunFuelBound tokens])
          (tokens, [compactTermTask binderArity], none) =
        (suffix, [], some (some suffix)) := by
    rw [hfuel]
    exact compactSyntaxParser_iterate_trans hfinish
      (compactSyntaxParserStep_iterate_done extra suffix [] (some suffix))
  simp [compactTermTokenParser, compactTermTokenParserRun,
    compactTermParserInitialState, compactSyntaxParserStateOutput,
    tokens, hrun]

theorem compactFormulaTokenParser_canonical_append
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix : List Nat) :
    compactFormulaTokenParser binderArity
        (compactArithmeticFormulaTokens formula ++ suffix) =
      some suffix := by
  let tokens := compactArithmeticFormulaTokens formula ++ suffix
  let used := compactFormulaTaskSteps formula + 1
  have htask := compactFormulaTask_execute formula suffix []
  have hfinish :
      (compactSyntaxParserStep^[used])
          (tokens, [compactFormulaTask binderArity], none) =
        (suffix, [], some (some suffix)) := by
    apply compactSyntaxParser_iterate_trans htask
    simp [Function.iterate_one]
  have hformula := compactFormulaTaskSteps_le_tokenLength formula
  have hinputLength :
      (compactArithmeticFormulaTokens formula).length <= tokens.length := by
    simp [tokens]
  have hfuelLength := compactSyntaxRunFuelBound_length_add_one tokens
  have hused : used <= compactSyntaxRunFuelBound tokens := by
    omega
  obtain ⟨extra, hfuel⟩ := exists_add_of_le hused
  have hrun :
      (compactSyntaxParserStep^[compactSyntaxRunFuelBound tokens])
          (tokens, [compactFormulaTask binderArity], none) =
        (suffix, [], some (some suffix)) := by
    rw [hfuel]
    exact compactSyntaxParser_iterate_trans hfinish
      (compactSyntaxParserStep_iterate_done extra suffix [] (some suffix))
  simp [compactFormulaTokenParser, compactFormulaTokenParserRun,
    compactFormulaParserInitialState, compactSyntaxParserStateOutput,
    tokens, hrun]

theorem compactTermTask_primrec : Primrec compactTermTask := by
  exact
    (Primrec.pair (Primrec.const 0)
      (Primrec.pair Primrec.id (Primrec.const 0))).of_eq
      fun binderArity => by rfl

theorem compactFormulaTask_primrec : Primrec compactFormulaTask := by
  exact
    (Primrec.pair (Primrec.const 1)
      (Primrec.pair Primrec.id (Primrec.const 0))).of_eq
      fun binderArity => by rfl

theorem compactRepeatTermTask_primrec :
    Primrec₂ compactRepeatTermTask := by
  exact
    (Primrec₂.pair.comp₂ (Primrec₂.const 2)
      (Primrec₂.pair.comp₂ Primrec₂.left Primrec₂.right)).of_eq
      fun binderArity count => by rfl

theorem compactTokenAt_primrec : Primrec₂ compactTokenAt := by
  have hget : Primrec₂
      (fun (index : Nat) (tokens : List Nat) => tokens[index]?) :=
    Primrec.list_getElem?.swap
  exact
    (Primrec.option_getD.comp₂ hget (Primrec₂.const 0)).of_eq
      fun index tokens => by rfl

theorem compactSyntaxFailure_primrec :
    Primrec₂ compactSyntaxFailure := by
  exact
    (Primrec₂.pair.comp₂ Primrec₂.left
      (Primrec₂.pair.comp₂ Primrec₂.right
        (Primrec₂.const (some none : CompactSyntaxParserStatus)))).of_eq
      fun tokens tasks => by rfl

theorem compactSyntaxContinue_primrec :
    Primrec₂ compactSyntaxContinue := by
  exact
    (Primrec₂.pair.comp₂ Primrec₂.left
      (Primrec₂.pair.comp₂ Primrec₂.right
        (Primrec₂.const (none : CompactSyntaxParserStatus)))).of_eq
      fun tokens tasks => by rfl

theorem compactTermTokenStep_primrec :
    Primrec compactTermTokenStep := by
  have harity : Primrec
      (fun input : CompactTermBranchInput => input.1) :=
    Primrec.fst
  have htokens : Primrec
      (fun input : CompactTermBranchInput => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have htasks : Primrec
      (fun input : CompactTermBranchInput => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hlength : Primrec
      (fun input : CompactTermBranchInput => input.2.1.length) :=
    Primrec.list_length.comp htokens
  have htag : Primrec
      (fun input : CompactTermBranchInput =>
        compactTokenAt 0 input.2.1) :=
    compactTokenAt_primrec.comp (Primrec.const 0) htokens
  have hargument : Primrec
      (fun input : CompactTermBranchInput =>
        compactTokenAt 1 input.2.1) :=
    compactTokenAt_primrec.comp (Primrec.const 1) htokens
  have hfunctionCode : Primrec
      (fun input : CompactTermBranchInput =>
        compactTokenAt 2 input.2.1) :=
    compactTokenAt_primrec.comp (Primrec.const 2) htokens
  have htwo : PrimrecPred
      (fun input : CompactTermBranchInput => 2 <= input.2.1.length) :=
    Primrec.nat_le.comp (Primrec.const 2) hlength
  have hthree : PrimrecPred
      (fun input : CompactTermBranchInput => 3 <= input.2.1.length) :=
    Primrec.nat_le.comp (Primrec.const 3) hlength
  have htagZero : PrimrecPred
      (fun input : CompactTermBranchInput =>
        compactTokenAt 0 input.2.1 = 0) :=
    Primrec.eq.comp htag (Primrec.const 0)
  have htagOne : PrimrecPred
      (fun input : CompactTermBranchInput =>
        compactTokenAt 0 input.2.1 = 1) :=
    Primrec.eq.comp htag (Primrec.const 1)
  have htagTwo : PrimrecPred
      (fun input : CompactTermBranchInput =>
        compactTokenAt 0 input.2.1 = 2) :=
    Primrec.eq.comp htag (Primrec.const 2)
  have hbvar : PrimrecPred
      (fun input : CompactTermBranchInput =>
        compactTokenAt 1 input.2.1 < input.1) :=
    Primrec.nat_lt.comp hargument harity
  have hfunction : PrimrecPred
      (fun input : CompactTermBranchInput =>
        ArithmeticFuncCodeValid
          (compactTokenAt 1 input.2.1)
          (compactTokenAt 2 input.2.1)) :=
    arithmeticFuncCodeValid_primrec.comp hargument hfunctionCode
  have hdropTwo : Primrec
      (fun input : CompactTermBranchInput => input.2.1.drop 2) :=
    Primrec.list_drop.comp (Primrec.const 2) htokens
  have hdropThree : Primrec
      (fun input : CompactTermBranchInput => input.2.1.drop 3) :=
    Primrec.list_drop.comp (Primrec.const 3) htokens
  have hfailure : Primrec
      (fun input : CompactTermBranchInput =>
        compactSyntaxFailure input.2.1 input.2.2) :=
    compactSyntaxFailure_primrec.comp htokens htasks
  have hsimple : Primrec
      (fun input : CompactTermBranchInput =>
        compactSyntaxContinue (input.2.1.drop 2) input.2.2) :=
    compactSyntaxContinue_primrec.comp hdropTwo htasks
  have hrepeat : Primrec
      (fun input : CompactTermBranchInput =>
        compactRepeatTermTask input.1
          (compactTokenAt 1 input.2.1)) :=
    compactRepeatTermTask_primrec.comp harity hargument
  have htasksFunction : Primrec
      (fun input : CompactTermBranchInput =>
        compactRepeatTermTask input.1
          (compactTokenAt 1 input.2.1) :: input.2.2) :=
    Primrec.list_cons.comp hrepeat htasks
  have hfunctionSuccess : Primrec
      (fun input : CompactTermBranchInput =>
        compactSyntaxContinue (input.2.1.drop 3)
          (compactRepeatTermTask input.1
            (compactTokenAt 1 input.2.1) :: input.2.2)) :=
    compactSyntaxContinue_primrec.comp hdropThree htasksFunction
  exact
    (Primrec.ite htwo
      (Primrec.ite htagZero
        (Primrec.ite hbvar hsimple hfailure)
        (Primrec.ite htagOne hsimple
          (Primrec.ite htagTwo
            (Primrec.ite hthree
              (Primrec.ite hfunction hfunctionSuccess hfailure)
              hfailure)
            hfailure)))
      hfailure).of_eq fun input => by
        simp only [compactTermTokenStep]

theorem compactFormulaTokenStep_primrec :
    Primrec compactFormulaTokenStep := by
  have harity : Primrec
      (fun input : CompactFormulaBranchInput => input.1) :=
    Primrec.fst
  have htokens : Primrec
      (fun input : CompactFormulaBranchInput => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have htasks : Primrec
      (fun input : CompactFormulaBranchInput => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hlength : Primrec
      (fun input : CompactFormulaBranchInput => input.2.1.length) :=
    Primrec.list_length.comp htokens
  have htag : Primrec
      (fun input : CompactFormulaBranchInput =>
        compactTokenAt 0 input.2.1) :=
    compactTokenAt_primrec.comp (Primrec.const 0) htokens
  have hrelationArity : Primrec
      (fun input : CompactFormulaBranchInput =>
        compactTokenAt 1 input.2.1) :=
    compactTokenAt_primrec.comp (Primrec.const 1) htokens
  have hrelationCode : Primrec
      (fun input : CompactFormulaBranchInput =>
        compactTokenAt 2 input.2.1) :=
    compactTokenAt_primrec.comp (Primrec.const 2) htokens
  have hone : PrimrecPred
      (fun input : CompactFormulaBranchInput => 1 <= input.2.1.length) :=
    Primrec.nat_le.comp (Primrec.const 1) hlength
  have hthree : PrimrecPred
      (fun input : CompactFormulaBranchInput => 3 <= input.2.1.length) :=
    Primrec.nat_le.comp (Primrec.const 3) hlength
  have htagZero : PrimrecPred
      (fun input : CompactFormulaBranchInput =>
        compactTokenAt 0 input.2.1 = 0) :=
    Primrec.eq.comp htag (Primrec.const 0)
  have htagOne : PrimrecPred
      (fun input : CompactFormulaBranchInput =>
        compactTokenAt 0 input.2.1 = 1) :=
    Primrec.eq.comp htag (Primrec.const 1)
  have htagTwo : PrimrecPred
      (fun input : CompactFormulaBranchInput =>
        compactTokenAt 0 input.2.1 = 2) :=
    Primrec.eq.comp htag (Primrec.const 2)
  have htagThree : PrimrecPred
      (fun input : CompactFormulaBranchInput =>
        compactTokenAt 0 input.2.1 = 3) :=
    Primrec.eq.comp htag (Primrec.const 3)
  have htagFour : PrimrecPred
      (fun input : CompactFormulaBranchInput =>
        compactTokenAt 0 input.2.1 = 4) :=
    Primrec.eq.comp htag (Primrec.const 4)
  have htagFive : PrimrecPred
      (fun input : CompactFormulaBranchInput =>
        compactTokenAt 0 input.2.1 = 5) :=
    Primrec.eq.comp htag (Primrec.const 5)
  have htagSix : PrimrecPred
      (fun input : CompactFormulaBranchInput =>
        compactTokenAt 0 input.2.1 = 6) :=
    Primrec.eq.comp htag (Primrec.const 6)
  have htagSeven : PrimrecPred
      (fun input : CompactFormulaBranchInput =>
        compactTokenAt 0 input.2.1 = 7) :=
    Primrec.eq.comp htag (Primrec.const 7)
  have hrelation : PrimrecPred
      (fun input : CompactFormulaBranchInput =>
        ArithmeticRelCodeValid
          (compactTokenAt 1 input.2.1)
          (compactTokenAt 2 input.2.1)) :=
    arithmeticRelCodeValid_primrec.comp hrelationArity hrelationCode
  have hdropOne : Primrec
      (fun input : CompactFormulaBranchInput => input.2.1.drop 1) :=
    Primrec.list_drop.comp (Primrec.const 1) htokens
  have hdropThree : Primrec
      (fun input : CompactFormulaBranchInput => input.2.1.drop 3) :=
    Primrec.list_drop.comp (Primrec.const 3) htokens
  have hfailure : Primrec
      (fun input : CompactFormulaBranchInput =>
        compactSyntaxFailure input.2.1 input.2.2) :=
    compactSyntaxFailure_primrec.comp htokens htasks
  have hleaf : Primrec
      (fun input : CompactFormulaBranchInput =>
        compactSyntaxContinue (input.2.1.drop 1) input.2.2) :=
    compactSyntaxContinue_primrec.comp hdropOne htasks
  have hrepeat : Primrec
      (fun input : CompactFormulaBranchInput =>
        compactRepeatTermTask input.1
          (compactTokenAt 1 input.2.1)) :=
    compactRepeatTermTask_primrec.comp harity hrelationArity
  have hatomTasks : Primrec
      (fun input : CompactFormulaBranchInput =>
        compactRepeatTermTask input.1
          (compactTokenAt 1 input.2.1) :: input.2.2) :=
    Primrec.list_cons.comp hrepeat htasks
  have hatomSuccess : Primrec
      (fun input : CompactFormulaBranchInput =>
        compactSyntaxContinue (input.2.1.drop 3)
          (compactRepeatTermTask input.1
            (compactTokenAt 1 input.2.1) :: input.2.2)) :=
    compactSyntaxContinue_primrec.comp hdropThree hatomTasks
  have hformulaTask : Primrec
      (fun input : CompactFormulaBranchInput =>
        compactFormulaTask input.1) :=
    compactFormulaTask_primrec.comp harity
  have hbinaryTasks : Primrec
      (fun input : CompactFormulaBranchInput =>
        compactFormulaTask input.1 ::
          compactFormulaTask input.1 :: input.2.2) :=
    Primrec.list_cons.comp hformulaTask
      (Primrec.list_cons.comp hformulaTask htasks)
  have hbinarySuccess : Primrec
      (fun input : CompactFormulaBranchInput =>
        compactSyntaxContinue (input.2.1.drop 1)
          (compactFormulaTask input.1 ::
            compactFormulaTask input.1 :: input.2.2)) :=
    compactSyntaxContinue_primrec.comp hdropOne hbinaryTasks
  have hsuccArity : Primrec
      (fun input : CompactFormulaBranchInput => input.1 + 1) :=
    Primrec.succ.comp harity
  have hquantifierTask : Primrec
      (fun input : CompactFormulaBranchInput =>
        compactFormulaTask (input.1 + 1)) :=
    compactFormulaTask_primrec.comp hsuccArity
  have hquantifierTasks : Primrec
      (fun input : CompactFormulaBranchInput =>
        compactFormulaTask (input.1 + 1) :: input.2.2) :=
    Primrec.list_cons.comp hquantifierTask htasks
  have hquantifierSuccess : Primrec
      (fun input : CompactFormulaBranchInput =>
        compactSyntaxContinue (input.2.1.drop 1)
          (compactFormulaTask (input.1 + 1) :: input.2.2)) :=
    compactSyntaxContinue_primrec.comp hdropOne hquantifierTasks
  have hatom : Primrec (fun input : CompactFormulaBranchInput =>
      if 3 <= input.2.1.length then
        if ArithmeticRelCodeValid
            (compactTokenAt 1 input.2.1)
            (compactTokenAt 2 input.2.1) then
          compactSyntaxContinue (input.2.1.drop 3)
            (compactRepeatTermTask input.1
              (compactTokenAt 1 input.2.1) :: input.2.2)
        else compactSyntaxFailure input.2.1 input.2.2
      else compactSyntaxFailure input.2.1 input.2.2) :=
    Primrec.ite hthree
      (Primrec.ite hrelation hatomSuccess hfailure) hfailure
  exact
    (Primrec.ite hone
      (Primrec.ite htagZero hatom
        (Primrec.ite htagOne hatom
          (Primrec.ite htagTwo hleaf
            (Primrec.ite htagThree hleaf
              (Primrec.ite htagFour hbinarySuccess
                (Primrec.ite htagFive hbinarySuccess
                  (Primrec.ite htagSix hquantifierSuccess
                    (Primrec.ite htagSeven hquantifierSuccess
                      hfailure))))))))
      hfailure).of_eq fun input => by
        simp only [compactFormulaTokenStep]

theorem compactRepeatTermTokenStep_primrec :
    Primrec compactRepeatTermTokenStep := by
  have htask : Primrec
      (fun input : CompactTaskBranchInput => input.1) :=
    Primrec.fst
  have harity : Primrec
      (fun input : CompactTaskBranchInput => input.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp htask)
  have hcount : Primrec
      (fun input : CompactTaskBranchInput => input.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp htask)
  have htokens : Primrec
      (fun input : CompactTaskBranchInput => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have htasks : Primrec
      (fun input : CompactTaskBranchInput => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hzero : PrimrecPred
      (fun input : CompactTaskBranchInput => input.1.2.2 = 0) :=
    Primrec.eq.comp hcount (Primrec.const 0)
  have hdone : Primrec
      (fun input : CompactTaskBranchInput =>
        compactSyntaxContinue input.2.1 input.2.2) :=
    compactSyntaxContinue_primrec.comp htokens htasks
  have hterm : Primrec
      (fun input : CompactTaskBranchInput =>
        compactTermTask input.1.2.1) :=
    compactTermTask_primrec.comp harity
  have hpred : Primrec
      (fun input : CompactTaskBranchInput => input.1.2.2 - 1) :=
    Primrec.nat_sub.comp hcount (Primrec.const 1)
  have hrepeat : Primrec
      (fun input : CompactTaskBranchInput =>
        compactRepeatTermTask input.1.2.1 (input.1.2.2 - 1)) :=
    compactRepeatTermTask_primrec.comp harity hpred
  have hnewTasks : Primrec
      (fun input : CompactTaskBranchInput =>
        compactTermTask input.1.2.1 ::
          compactRepeatTermTask input.1.2.1 (input.1.2.2 - 1) ::
            input.2.2) :=
    Primrec.list_cons.comp hterm
      (Primrec.list_cons.comp hrepeat htasks)
  have hnext : Primrec
      (fun input : CompactTaskBranchInput =>
        compactSyntaxContinue input.2.1
          (compactTermTask input.1.2.1 ::
            compactRepeatTermTask input.1.2.1 (input.1.2.2 - 1) ::
              input.2.2)) :=
    compactSyntaxContinue_primrec.comp htokens hnewTasks
  exact
    (Primrec.ite hzero hdone hnext).of_eq fun input => by
      simp only [compactRepeatTermTokenStep]

theorem compactSyntaxTaskTokenStep_primrec :
    Primrec compactSyntaxTaskTokenStep := by
  have htask : Primrec
      (fun input : CompactTaskBranchInput => input.1) :=
    Primrec.fst
  have hkind : Primrec
      (fun input : CompactTaskBranchInput => input.1.1) :=
    Primrec.fst.comp htask
  have harity : Primrec
      (fun input : CompactTaskBranchInput => input.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp htask)
  have htokens : Primrec
      (fun input : CompactTaskBranchInput => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have htasks : Primrec
      (fun input : CompactTaskBranchInput => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hkindZero : PrimrecPred
      (fun input : CompactTaskBranchInput => input.1.1 = 0) :=
    Primrec.eq.comp hkind (Primrec.const 0)
  have hkindOne : PrimrecPred
      (fun input : CompactTaskBranchInput => input.1.1 = 1) :=
    Primrec.eq.comp hkind (Primrec.const 1)
  have hkindTwo : PrimrecPred
      (fun input : CompactTaskBranchInput => input.1.1 = 2) :=
    Primrec.eq.comp hkind (Primrec.const 2)
  have hbranchInput : Primrec
      (fun input : CompactTaskBranchInput =>
        (input.1.2.1, input.2.1, input.2.2)) :=
    Primrec.pair harity (Primrec.pair htokens htasks)
  have hterm : Primrec
      (fun input : CompactTaskBranchInput =>
        compactTermTokenStep (input.1.2.1, input.2.1, input.2.2)) :=
    compactTermTokenStep_primrec.comp hbranchInput
  have hformula : Primrec
      (fun input : CompactTaskBranchInput =>
        compactFormulaTokenStep
          (input.1.2.1, input.2.1, input.2.2)) :=
    compactFormulaTokenStep_primrec.comp hbranchInput
  have hfailure : Primrec
      (fun input : CompactTaskBranchInput =>
        compactSyntaxFailure input.2.1 input.2.2) :=
    compactSyntaxFailure_primrec.comp htokens htasks
  exact
    (Primrec.ite hkindZero hterm
      (Primrec.ite hkindOne hformula
        (Primrec.ite hkindTwo compactRepeatTermTokenStep_primrec
          hfailure))).of_eq fun input => by
            simp only [compactSyntaxTaskTokenStep]

theorem compactSyntaxRunningStep_primrec :
    Primrec compactSyntaxRunningStep := by
  have htokens : Primrec
      (fun state : CompactSyntaxParserState => state.1) :=
    Primrec.fst
  have htasks : Primrec
      (fun state : CompactSyntaxParserState => state.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hempty : PrimrecPred
      (fun state : CompactSyntaxParserState => state.2.1 = []) :=
    Primrec.eq.comp htasks (Primrec.const [])
  have hsuccessStatus : Primrec
      (fun state : CompactSyntaxParserState =>
        some (some state.1)) :=
    Primrec.option_some.comp (Primrec.option_some.comp htokens)
  have hsuccess : Primrec
      (fun state : CompactSyntaxParserState =>
        (state.1, [], some (some state.1))) :=
    Primrec.pair htokens
      (Primrec.pair (Primrec.const ([] : List CompactSyntaxTask))
        hsuccessStatus)
  have hheadOption : Primrec
      (fun state : CompactSyntaxParserState => state.2.1.head?) :=
    Primrec.list_head?.comp htasks
  have hhead : Primrec
      (fun state : CompactSyntaxParserState =>
        state.2.1.head?.getD (compactTermTask 0)) :=
    Primrec.option_getD.comp hheadOption
      (Primrec.const (compactTermTask 0))
  have htail : Primrec
      (fun state : CompactSyntaxParserState => state.2.1.tail) :=
    Primrec.list_tail.comp htasks
  have hinput : Primrec
      (fun state : CompactSyntaxParserState =>
        (state.2.1.head?.getD (compactTermTask 0),
          state.1, state.2.1.tail)) :=
    Primrec.pair hhead (Primrec.pair htokens htail)
  have hbranch : Primrec
      (fun state : CompactSyntaxParserState =>
        compactSyntaxTaskTokenStep
          (state.2.1.head?.getD (compactTermTask 0),
            state.1, state.2.1.tail)) :=
    compactSyntaxTaskTokenStep_primrec.comp hinput
  exact
    (Primrec.ite hempty hsuccess hbranch).of_eq fun state => by
      cases htasksValue : state.2.1 <;>
        simp [compactSyntaxRunningStep, htasksValue]

theorem compactSyntaxParserStep_primrec :
    Primrec compactSyntaxParserStep := by
  have hstatus : Primrec
      (fun state : CompactSyntaxParserState => state.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hdone : Primrec
      (fun state : CompactSyntaxParserState => state.2.2.isSome) :=
    Primrec.option_isSome.comp hstatus
  exact
    (Primrec.cond hdone Primrec.id
      compactSyntaxRunningStep_primrec).of_eq fun state => by
        cases hstatusValue : state.2.2 <;>
          simp [compactSyntaxParserStep, hstatusValue]

theorem compactSyntaxRunFuelBound_primrec :
    Primrec compactSyntaxRunFuelBound := by
  have hsize : Primrec (fun tokens : List Nat => tokens.length + 1) :=
    Primrec.succ.comp Primrec.list_length
  have hsquare : Primrec
      (fun tokens : List Nat =>
        (tokens.length + 1) * (tokens.length + 1)) :=
    Primrec.nat_mul.comp hsize hsize
  have hscaled : Primrec
      (fun tokens : List Nat =>
        16 * ((tokens.length + 1) * (tokens.length + 1))) :=
    Primrec.nat_mul.comp (Primrec.const 16) hsquare
  exact
    (Primrec.nat_add.comp hscaled (Primrec.const 8)).of_eq
      fun tokens => by simp [compactSyntaxRunFuelBound, Nat.mul_assoc]

theorem compactTermParserInitialState_primrec :
    Primrec₂ compactTermParserInitialState := by
  have htaskList : Primrec₂
      (fun (binderArity : Nat) (_tokens : List Nat) =>
        [compactTermTask binderArity]) :=
    Primrec.list_cons.comp₂
      ((compactTermTask_primrec.comp Primrec.fst).to₂)
      (Primrec₂.const [])
  exact
    (Primrec₂.pair.comp₂ Primrec₂.right
      (Primrec₂.pair.comp₂ htaskList
        (Primrec₂.const (none : CompactSyntaxParserStatus)))).of_eq
      fun binderArity tokens => by rfl

theorem compactFormulaParserInitialState_primrec :
    Primrec₂ compactFormulaParserInitialState := by
  have htaskList : Primrec₂
      (fun (binderArity : Nat) (_tokens : List Nat) =>
        [compactFormulaTask binderArity]) :=
    Primrec.list_cons.comp₂
      ((compactFormulaTask_primrec.comp Primrec.fst).to₂)
      (Primrec₂.const [])
  exact
    (Primrec₂.pair.comp₂ Primrec₂.right
      (Primrec₂.pair.comp₂ htaskList
        (Primrec₂.const (none : CompactSyntaxParserStatus)))).of_eq
      fun binderArity tokens => by rfl

theorem compactTermTokenParserRun_primrec :
    Primrec₂ compactTermTokenParserRun := by
  apply Primrec₂.mk
  have hfuel : Primrec
      (fun input : Nat × List Nat =>
        compactSyntaxRunFuelBound input.2) :=
    compactSyntaxRunFuelBound_primrec.comp Primrec.snd
  have hinitial : Primrec
      (fun input : Nat × List Nat =>
        compactTermParserInitialState input.1 input.2) :=
    compactTermParserInitialState_primrec
  have hstep : Primrec₂
      (fun (_input : Nat × List Nat)
          (state : CompactSyntaxParserState) =>
        compactSyntaxParserStep state) :=
    (compactSyntaxParserStep_primrec.comp Primrec.snd).to₂
  exact
    (Primrec.nat_iterate hfuel hinitial hstep).of_eq
      fun input => by rfl

theorem compactFormulaTokenParserRun_primrec :
    Primrec₂ compactFormulaTokenParserRun := by
  apply Primrec₂.mk
  have hfuel : Primrec
      (fun input : Nat × List Nat =>
        compactSyntaxRunFuelBound input.2) :=
    compactSyntaxRunFuelBound_primrec.comp Primrec.snd
  have hinitial : Primrec
      (fun input : Nat × List Nat =>
        compactFormulaParserInitialState input.1 input.2) :=
    compactFormulaParserInitialState_primrec
  have hstep : Primrec₂
      (fun (_input : Nat × List Nat)
          (state : CompactSyntaxParserState) =>
        compactSyntaxParserStep state) :=
    (compactSyntaxParserStep_primrec.comp Primrec.snd).to₂
  exact
    (Primrec.nat_iterate hfuel hinitial hstep).of_eq
      fun input => by rfl

theorem compactSyntaxParserStateOutput_primrec :
    Primrec compactSyntaxParserStateOutput := by
  have hstatus : Primrec
      (fun state : CompactSyntaxParserState => state.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact
    (Primrec.option_getD.comp hstatus (Primrec.const none)).of_eq
      fun state => by rfl

theorem compactTermTokenParser_primrec :
    Primrec₂ compactTermTokenParser := by
  exact
    (compactSyntaxParserStateOutput_primrec.comp₂
      compactTermTokenParserRun_primrec).of_eq
      fun binderArity tokens => by rfl

theorem compactFormulaTokenParser_primrec :
    Primrec₂ compactFormulaTokenParser := by
  exact
    (compactSyntaxParserStateOutput_primrec.comp₂
      compactFormulaTokenParserRun_primrec).of_eq
      fun binderArity tokens => by rfl

#print axioms compactTokenAt_primrec
#print axioms compactTermTokenStep_primrec
#print axioms compactFormulaTokenStep_primrec
#print axioms compactSyntaxParserStep_primrec
#print axioms compactTermTokenParser_primrec
#print axioms compactFormulaTokenParser_primrec
#print axioms compactTermTask_execute
#print axioms compactFormulaTask_execute
#print axioms compactTermTokenParser_canonical_append
#print axioms compactFormulaTokenParser_canonical_append

end FoundationCompactSyntaxTokenMachine
