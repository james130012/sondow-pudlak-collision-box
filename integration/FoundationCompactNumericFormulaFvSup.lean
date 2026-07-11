import integration.FoundationCompactNumericFormulaConstructors
import integration.FoundationCompactSyntaxTransformationTraceCore

/-!
# Pure numeric formula free-variable supremum

The machine reuses the checked numeric syntax-task stack and emits exactly the
free-variable indices encountered in genuine term positions. Formula tags,
bound variables, and function headers emit nothing. Its runtime state contains
only naturals and lists of naturals; typed syntax is used solely in correctness.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericFormulaFvSup

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactSyntaxTransformationTraceCore

abbrev CompactFormulaFvListState :=
  CompactSyntaxParserState × List Nat

def compactFvListConsumedTermHeader
    (tokens : List Nat) : List Nat :=
  if tokens.length = 2 then
    if compactTokenAt 0 tokens = 1 then
      [compactTokenAt 1 tokens]
    else
      []
  else
    []

theorem compactFvListConsumedTermHeader_primrec :
    Primrec compactFvListConsumedTermHeader := by
  have htag : Primrec
      (fun tokens : List Nat => compactTokenAt 0 tokens) :=
    compactTokenAt_primrec.comp (Primrec.const 0) Primrec.id
  have hindex : Primrec
      (fun tokens : List Nat => compactTokenAt 1 tokens) :=
    compactTokenAt_primrec.comp (Primrec.const 1) Primrec.id
  have hlength : PrimrecPred
      (fun tokens : List Nat => tokens.length = 2) :=
    Primrec.eq.comp Primrec.list_length (Primrec.const 2)
  have hisFree : PrimrecPred
      (fun tokens : List Nat => compactTokenAt 0 tokens = 1) :=
    Primrec.eq.comp htag (Primrec.const 1)
  have hsingle : Primrec
      (fun tokens : List Nat => [compactTokenAt 1 tokens]) :=
    Primrec.list_cons.comp hindex (Primrec.const [])
  have htagged : Primrec
      (fun tokens : List Nat =>
        if compactTokenAt 0 tokens = 1 then
          [compactTokenAt 1 tokens]
        else []) :=
    Primrec.ite hisFree hsingle (Primrec.const [])
  exact
    (Primrec.ite hlength htagged (Primrec.const [])).of_eq fun tokens => by
      simp [compactFvListConsumedTermHeader]

def compactSyntaxCurrentTaskKind
    (state : CompactSyntaxParserState) : Nat :=
  (state.2.1.head?.map fun task => task.1).getD 3

theorem compactSyntaxCurrentTaskKind_primrec :
    Primrec compactSyntaxCurrentTaskKind := by
  have htasks : Primrec
      (fun state : CompactSyntaxParserState => state.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hhead : Primrec
      (fun state : CompactSyntaxParserState => state.2.1.head?) :=
    Primrec.list_head?.comp htasks
  have hkind : Primrec
      (fun state : CompactSyntaxParserState =>
        state.2.1.head?.map fun task => task.1) :=
    Primrec.option_map hhead
      ((Primrec.fst.comp Primrec.snd).to₂)
  exact
    (Primrec.option_getD.comp hkind (Primrec.const 3)).of_eq
      fun state => by rfl

def compactFormulaFvListEmission
    (taskKind : Nat) (consumed : List Nat) : List Nat :=
  if taskKind = 0 then
    compactFvListConsumedTermHeader consumed
  else
    []

theorem compactFormulaFvListEmission_primrec :
    Primrec₂ compactFormulaFvListEmission := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  have hterm : PrimrecPred (fun input : Input => input.1 = 0) :=
    Primrec.eq.comp Primrec.fst (Primrec.const 0)
  have htransformed : Primrec
      (fun input : Input =>
        compactFvListConsumedTermHeader input.2) :=
    compactFvListConsumedTermHeader_primrec.comp Primrec.snd
  exact
    (Primrec.ite hterm
      htransformed (Primrec.const [])).of_eq fun input => by
        simp only [compactFormulaFvListEmission]

def compactFormulaFvListStep
    (state : CompactFormulaFvListState) :
    CompactFormulaFvListState :=
  let parserState := state.1
  let nextParserState := compactSyntaxParserStep parserState
  let consumed := consumedTokenPrefix parserState.1 nextParserState.1
  let emitted := compactFormulaFvListEmission
    (compactSyntaxCurrentTaskKind parserState) consumed
  (nextParserState, state.2 ++ emitted)

theorem compactFormulaFvListStep_primrec :
    Primrec compactFormulaFvListStep := by
  have hparser : Primrec
      (fun state : CompactFormulaFvListState => state.1) :=
    Primrec.fst
  have hnext : Primrec
      (fun state : CompactFormulaFvListState =>
        compactSyntaxParserStep state.1) :=
    compactSyntaxParserStep_primrec.comp hparser
  have holdTokens : Primrec
      (fun state : CompactFormulaFvListState => state.1.1) :=
    Primrec.fst.comp hparser
  have hnextTokens : Primrec
      (fun state : CompactFormulaFvListState =>
        (compactSyntaxParserStep state.1).1) :=
    Primrec.fst.comp hnext
  have hconsumed : Primrec
      (fun state : CompactFormulaFvListState =>
        consumedTokenPrefix state.1.1
          (compactSyntaxParserStep state.1).1) :=
    consumedTokenPrefix_primrec.comp holdTokens hnextTokens
  have hkind : Primrec
      (fun state : CompactFormulaFvListState =>
        compactSyntaxCurrentTaskKind state.1) :=
    compactSyntaxCurrentTaskKind_primrec.comp hparser
  have hemitted : Primrec
      (fun state : CompactFormulaFvListState =>
        compactFormulaFvListEmission
          (compactSyntaxCurrentTaskKind state.1)
          (consumedTokenPrefix state.1.1
            (compactSyntaxParserStep state.1).1)) :=
    compactFormulaFvListEmission_primrec.comp hkind hconsumed
  have houtput : Primrec
      (fun state : CompactFormulaFvListState => state.2) :=
    Primrec.snd
  have hnextOutput : Primrec
      (fun state : CompactFormulaFvListState =>
        state.2 ++ compactFormulaFvListEmission
          (compactSyntaxCurrentTaskKind state.1)
          (consumedTokenPrefix state.1.1
            (compactSyntaxParserStep state.1).1)) :=
    Primrec.list_append.comp houtput hemitted
  exact
    (Primrec.pair hnext hnextOutput).of_eq fun state => by rfl

def compactFormulaFvListInitialState
    (binderArity : Nat) (tokens : List Nat) :
    CompactFormulaFvListState :=
  (compactFormulaParserInitialState binderArity tokens, [])

theorem compactFormulaFvListInitialState_primrec :
    Primrec₂ compactFormulaFvListInitialState := by
  exact Primrec₂.pair.comp₂
    compactFormulaParserInitialState_primrec
    (Primrec₂.const [])

def compactFormulaFvListRun
    (binderArity : Nat) (tokens : List Nat) :
    CompactFormulaFvListState :=
  (compactFormulaFvListStep^[compactSyntaxRunFuelBound tokens])
    (compactFormulaFvListInitialState binderArity tokens)

theorem compactFormulaFvListRun_primrec :
    Primrec₂ compactFormulaFvListRun := by
  apply Primrec₂.mk
  have hfuel : Primrec
      (fun input : Nat × List Nat =>
        compactSyntaxRunFuelBound input.2) :=
    compactSyntaxRunFuelBound_primrec.comp Primrec.snd
  have hinitial : Primrec
      (fun input : Nat × List Nat =>
        compactFormulaFvListInitialState input.1 input.2) :=
    compactFormulaFvListInitialState_primrec
  have hstep : Primrec₂
      (fun (_input : Nat × List Nat)
          (state : CompactFormulaFvListState) =>
        compactFormulaFvListStep state) :=
    (compactFormulaFvListStep_primrec.comp Primrec.snd).to₂
  exact
    (Primrec.nat_iterate hfuel hinitial hstep).of_eq
      fun input => by rfl

def compactFormulaFvListStateOutput
    (state : CompactFormulaFvListState) :
    Option (List Nat × List Nat) :=
  state.1.2.2.bind fun result =>
    result.map fun suffix => (state.2, suffix)

theorem compactFormulaFvListStateOutput_primrec :
    Primrec compactFormulaFvListStateOutput := by
  have hstatus : Primrec
      (fun state : CompactFormulaFvListState => state.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hinner : Primrec₂
      (fun (state : CompactFormulaFvListState)
          (result : Option (List Nat)) =>
        result.map fun suffix => (state.2, suffix)) := by
    apply Primrec₂.mk
    let Input := CompactFormulaFvListState × Option (List Nat)
    have hresult : Primrec (fun input : Input => input.2) :=
      Primrec.snd
    have hpair : Primrec₂
        (fun (input : Input) (suffix : List Nat) =>
          (input.1.2, suffix)) :=
      Primrec₂.pair.comp₂
        ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).to₂)
        Primrec₂.right
    exact Primrec.option_map hresult hpair
  exact
    (Primrec.option_bind hstatus hinner).of_eq fun state => by rfl

def compactFormulaFvListTokenTransform
    (binderArity : Nat) (tokens : List Nat) :
    Option (List Nat × List Nat) :=
  compactFormulaFvListStateOutput
    (compactFormulaFvListRun binderArity tokens)

theorem compactFormulaFvListTokenTransform_primrec :
    Primrec₂ compactFormulaFvListTokenTransform := by
  exact compactFormulaFvListStateOutput_primrec.comp₂
    compactFormulaFvListRun_primrec

/-! ## Exact task execution -/

theorem compactFormulaFvList_iterate_trans
    {start middle finish : CompactFormulaFvListState}
    {firstSteps secondSteps : Nat}
    (hfirst : (compactFormulaFvListStep^[firstSteps]) start = middle)
    (hsecond : (compactFormulaFvListStep^[secondSteps]) middle = finish) :
    (compactFormulaFvListStep^[firstSteps + secondSteps]) start = finish := by
  rw [Nat.add_comm, Function.iterate_add_apply, hfirst, hsecond]

theorem compactFormulaFvListStep_of_transition
    {parserState nextParserState : CompactSyntaxParserState}
    {consumed : List Nat} (output : List Nat)
    (hparser : compactSyntaxParserStep parserState = nextParserState)
    (hconsumed : consumedTokenPrefix parserState.1 nextParserState.1 =
      consumed) :
    compactFormulaFvListStep (parserState, output) =
      (nextParserState,
        output ++ compactFormulaFvListEmission
          (compactSyntaxCurrentTaskKind parserState) consumed) := by
  simp [compactFormulaFvListStep, hparser, hconsumed]

@[simp] theorem compactFormulaFvListStep_done
    (tokens : List Nat) (tasks : List CompactSyntaxTask)
    (result : Option (List Nat)) (output : List Nat) :
    compactFormulaFvListStep
        ((tokens, tasks, some result), output) =
      ((tokens, tasks, some result), output) := by
  refine (compactFormulaFvListStep_of_transition output
    (consumed := [])
    (compactSyntaxParserStep_done tokens tasks result) ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactFormulaFvListEmission,
      compactFvListConsumedTermHeader, compactTokenAt]

theorem compactFormulaFvListStep_iterate_done
    (fuel : Nat) (tokens : List Nat) (tasks : List CompactSyntaxTask)
    (result : Option (List Nat)) (output : List Nat) :
    (compactFormulaFvListStep^[fuel])
        ((tokens, tasks, some result), output) =
      ((tokens, tasks, some result), output) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply,
        compactFormulaFvListStep_done, ih]

@[simp] theorem compactFormulaFvListStep_empty
    (tokens output : List Nat) :
    compactFormulaFvListStep ((tokens, [], none), output) =
      ((tokens, [], some (some tokens)), output) := by
  refine (compactFormulaFvListStep_of_transition output
    (consumed := []) (compactSyntaxParserStep_empty tokens) ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTaskKind,
      compactFormulaFvListEmission]

@[simp] theorem compactFormulaFvListStep_repeat_zero
    (binderArity : Nat) (tokens output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFvListStep
        ((tokens, compactRepeatTermTask binderArity 0 :: tasks, none),
          output) =
      ((tokens, tasks, none), output) := by
  have hparser : compactSyntaxParserStep
      (tokens, compactRepeatTermTask binderArity 0 :: tasks, none) =
      (tokens, tasks, none) := by
    simpa [compactSyntaxContinue] using
      (compactSyntaxParserStep_repeat_zero binderArity tokens tasks)
  refine (compactFormulaFvListStep_of_transition output
    (consumed := []) hparser ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTaskKind, compactRepeatTermTask,
      compactFormulaFvListEmission]

@[simp] theorem compactFormulaFvListStep_repeat_succ
    (binderArity count : Nat) (tokens output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFvListStep
        ((tokens,
          compactRepeatTermTask binderArity (count + 1) :: tasks, none),
          output) =
      ((tokens,
        compactTermTask binderArity ::
          compactRepeatTermTask binderArity count :: tasks,
        none), output) := by
  have hparser : compactSyntaxParserStep
      (tokens,
        compactRepeatTermTask binderArity (count + 1) :: tasks, none) =
      (tokens,
        compactTermTask binderArity ::
          compactRepeatTermTask binderArity count :: tasks, none) := by
    simpa [compactSyntaxContinue] using
      (compactSyntaxParserStep_repeat_succ
        binderArity count tokens tasks)
  refine (compactFormulaFvListStep_of_transition output
    (consumed := []) hparser ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTaskKind, compactRepeatTermTask,
      compactFormulaFvListEmission]

@[simp] theorem compactFormulaFvListStep_term_bvar
    {binderArity : Nat} (index : Fin binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFvListStep
        ((compactArithmeticTermTokens (#index) ++ suffix,
          compactTermTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none),
        output) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticTermTokens (#index) ++ suffix,
        compactTermTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
    rw [compactSyntaxParserStep_term]
    exact compactTermTokenStep_bvar index suffix tasks
  have htokens : compactArithmeticTermTokens (#index) =
      [(0 : Nat), index.val] := rfl
  have hconsumed : consumedTokenPrefix
      (compactArithmeticTermTokens (#index) ++ suffix) suffix =
      [(0 : Nat), index.val] := by
    rw [htokens]
    exact consumedTokenPrefix_append _ _
  refine (compactFormulaFvListStep_of_transition output hparser
    hconsumed).trans ?_
  rw [htokens]
  simp [compactSyntaxCurrentTaskKind, compactTermTask,
    compactFormulaFvListEmission, compactFvListConsumedTermHeader,
    compactTokenAt]

@[simp] theorem compactFormulaFvListStep_term_fvar
    {binderArity : Nat} (freeIndex : Nat)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFvListStep
        ((compactArithmeticTermTokens
            (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) ++
              suffix,
          compactTermTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++ [freeIndex]) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticTermTokens
          (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) ++
            suffix,
        compactTermTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
    rw [compactSyntaxParserStep_term]
    exact compactTermTokenStep_fvar freeIndex suffix tasks
  refine (compactFormulaFvListStep_of_transition output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactTermTask,
    compactFormulaFvListEmission, compactFvListConsumedTermHeader,
    compactArithmeticTermTokens, compactTokenAt]

@[simp] theorem compactFormulaFvListStep_term_func
    {binderArity functionArity : Nat}
    (functionSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Func functionArity)
    (arguments : Fin functionArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFvListStep
        ((compactArithmeticTermTokens
              (Semiterm.func functionSymbol arguments) ++ suffix,
          compactTermTask binderArity :: tasks, none), output) =
      (((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix,
        compactRepeatTermTask binderArity functionArity :: tasks, none),
        output) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticTermTokens
          (Semiterm.func functionSymbol arguments) ++ suffix,
        compactTermTask binderArity :: tasks, none) =
      ((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix,
        compactRepeatTermTask binderArity functionArity :: tasks, none) := by
    rw [compactSyntaxParserStep_term]
    exact compactTermTokenStep_func functionSymbol arguments suffix tasks
  have hconsumed : consumedTokenPrefix
      (compactArithmeticTermTokens
          (Semiterm.func functionSymbol arguments) ++ suffix)
      ((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix) =
      [2, functionArity, Encodable.encode functionSymbol] := by
    simpa [compactArithmeticTermTokens, List.append_assoc] using
      (consumedTokenPrefix_append
        [2, functionArity, Encodable.encode functionSymbol]
        ((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix))
  refine (compactFormulaFvListStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactTermTask,
    compactFormulaFvListEmission, compactFvListConsumedTermHeader,
    compactTokenAt]

@[simp] theorem compactFormulaFvListStep_formula_rel
    {binderArity relationArity : Nat}
    (relationSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Rel relationArity)
    (arguments : Fin relationArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFvListStep
        ((compactArithmeticFormulaTokens
              (Semiformula.rel relationSymbol arguments) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      (((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix,
        compactRepeatTermTask binderArity relationArity :: tasks, none),
        output) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticFormulaTokens
          (Semiformula.rel relationSymbol arguments) ++ suffix,
        compactFormulaTask binderArity :: tasks, none) =
      ((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix,
        compactRepeatTermTask binderArity relationArity :: tasks, none) := by
    rw [compactSyntaxParserStep_formula]
    exact compactFormulaTokenStep_rel relationSymbol arguments suffix tasks
  have hconsumed : consumedTokenPrefix
      (compactArithmeticFormulaTokens
          (Semiformula.rel relationSymbol arguments) ++ suffix)
      ((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix) =
      [0, relationArity, Encodable.encode relationSymbol] := by
    simpa [compactArithmeticFormulaTokens, List.append_assoc] using
      (consumedTokenPrefix_append
        [0, relationArity, Encodable.encode relationSymbol]
        ((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix))
  refine (compactFormulaFvListStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaFvListEmission, compactFvListConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaFvListStep_formula_nrel
    {binderArity relationArity : Nat}
    (relationSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Rel relationArity)
    (arguments : Fin relationArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFvListStep
        ((compactArithmeticFormulaTokens
              (Semiformula.nrel relationSymbol arguments) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      (((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix,
        compactRepeatTermTask binderArity relationArity :: tasks, none),
        output) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticFormulaTokens
          (Semiformula.nrel relationSymbol arguments) ++ suffix,
        compactFormulaTask binderArity :: tasks, none) =
      ((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix,
        compactRepeatTermTask binderArity relationArity :: tasks, none) := by
    rw [compactSyntaxParserStep_formula]
    exact compactFormulaTokenStep_nrel relationSymbol arguments suffix tasks
  have hconsumed : consumedTokenPrefix
      (compactArithmeticFormulaTokens
          (Semiformula.nrel relationSymbol arguments) ++ suffix)
      ((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix) =
      [1, relationArity, Encodable.encode relationSymbol] := by
    simpa [compactArithmeticFormulaTokens, List.append_assoc] using
      (consumedTokenPrefix_append
        [1, relationArity, Encodable.encode relationSymbol]
        ((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix))
  refine (compactFormulaFvListStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaFvListEmission, compactFvListConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaFvListStep_formula_verum
    {binderArity : Nat} (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFvListStep
        ((compactArithmeticFormulaTokens
              (⊤ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none), output) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticFormulaTokens
          (⊤ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) ++ suffix,
        compactFormulaTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
    rw [compactSyntaxParserStep_formula]
    exact compactFormulaTokenStep_verum suffix tasks
  refine (compactFormulaFvListStep_of_transition output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaFvListEmission, compactFvListConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaFvListStep_formula_falsum
    {binderArity : Nat} (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFvListStep
        ((compactArithmeticFormulaTokens
              (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none), output) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticFormulaTokens
          (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) ++ suffix,
        compactFormulaTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
    rw [compactSyntaxParserStep_formula]
    exact compactFormulaTokenStep_falsum suffix tasks
  refine (compactFormulaFvListStep_of_transition output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaFvListEmission, compactFvListConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaFvListStep_formula_and
    {binderArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFvListStep
        ((compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((compactArithmeticFormulaTokens left ++
          compactArithmeticFormulaTokens right ++ suffix,
        compactFormulaTask binderArity ::
          compactFormulaTask binderArity :: tasks, none),
        output) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
        compactFormulaTask binderArity :: tasks, none) =
      (compactArithmeticFormulaTokens left ++
          compactArithmeticFormulaTokens right ++ suffix,
        compactFormulaTask binderArity ::
          compactFormulaTask binderArity :: tasks, none) := by
    rw [compactSyntaxParserStep_formula]
    exact compactFormulaTokenStep_and left right suffix tasks
  have hconsumed : consumedTokenPrefix
      (compactArithmeticFormulaTokens (left ⋏ right) ++ suffix)
      (compactArithmeticFormulaTokens left ++
        compactArithmeticFormulaTokens right ++ suffix) = [4] := by
    simpa [compactArithmeticFormulaTokens, List.append_assoc] using
      (consumedTokenPrefix_append [4]
        (compactArithmeticFormulaTokens left ++
          compactArithmeticFormulaTokens right ++ suffix))
  refine (compactFormulaFvListStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaFvListEmission, compactFvListConsumedTermHeader]

@[simp] theorem compactFormulaFvListStep_formula_or
    {binderArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFvListStep
        ((compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((compactArithmeticFormulaTokens left ++
          compactArithmeticFormulaTokens right ++ suffix,
        compactFormulaTask binderArity ::
          compactFormulaTask binderArity :: tasks, none),
        output) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
        compactFormulaTask binderArity :: tasks, none) =
      (compactArithmeticFormulaTokens left ++
          compactArithmeticFormulaTokens right ++ suffix,
        compactFormulaTask binderArity ::
          compactFormulaTask binderArity :: tasks, none) := by
    rw [compactSyntaxParserStep_formula]
    exact compactFormulaTokenStep_or left right suffix tasks
  have hconsumed : consumedTokenPrefix
      (compactArithmeticFormulaTokens (left ⋎ right) ++ suffix)
      (compactArithmeticFormulaTokens left ++
        compactArithmeticFormulaTokens right ++ suffix) = [5] := by
    simpa [compactArithmeticFormulaTokens, List.append_assoc] using
      (consumedTokenPrefix_append [5]
        (compactArithmeticFormulaTokens left ++
          compactArithmeticFormulaTokens right ++ suffix))
  refine (compactFormulaFvListStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaFvListEmission, compactFvListConsumedTermHeader]

@[simp] theorem compactFormulaFvListStep_formula_all
    {binderArity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (binderArity + 1))
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFvListStep
        ((compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((compactArithmeticFormulaTokens body ++ suffix,
        compactFormulaTask (binderArity + 1) :: tasks, none),
        output) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
        compactFormulaTask binderArity :: tasks, none) =
      (compactArithmeticFormulaTokens body ++ suffix,
        compactFormulaTask (binderArity + 1) :: tasks, none) := by
    rw [compactSyntaxParserStep_formula]
    exact compactFormulaTokenStep_all body suffix tasks
  have hconsumed : consumedTokenPrefix
      (compactArithmeticFormulaTokens (∀⁰ body) ++ suffix)
      (compactArithmeticFormulaTokens body ++ suffix) = [6] := by
    simpa [compactArithmeticFormulaTokens] using
      (consumedTokenPrefix_append [6]
        (compactArithmeticFormulaTokens body ++ suffix))
  refine (compactFormulaFvListStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaFvListEmission, compactFvListConsumedTermHeader]

@[simp] theorem compactFormulaFvListStep_formula_exs
    {binderArity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (binderArity + 1))
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFvListStep
        ((compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((compactArithmeticFormulaTokens body ++ suffix,
        compactFormulaTask (binderArity + 1) :: tasks, none),
        output) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
        compactFormulaTask binderArity :: tasks, none) =
      (compactArithmeticFormulaTokens body ++ suffix,
        compactFormulaTask (binderArity + 1) :: tasks, none) := by
    rw [compactSyntaxParserStep_formula]
    exact compactFormulaTokenStep_exs body suffix tasks
  have hconsumed : consumedTokenPrefix
      (compactArithmeticFormulaTokens (∃⁰ body) ++ suffix)
      (compactArithmeticFormulaTokens body ++ suffix) = [7] := by
    simpa [compactArithmeticFormulaTokens] using
      (consumedTokenPrefix_append [7]
        (compactArithmeticFormulaTokens body ++ suffix))
  refine (compactFormulaFvListStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaFvListEmission, compactFvListConsumedTermHeader]

def compactTermListFvarList {binderArity : Nat}
    (terms : List
      (LO.FirstOrder.ArithmeticSemiterm Nat binderArity)) : List Nat :=
  (terms.map fun term =>
    term.fvarList).flatten

theorem listOfFn_eq_matrixToList
    {alpha : Type*} {count : Nat} (values : Fin count -> alpha) :
    List.ofFn values = Matrix.toList values := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.ofFn_succ, Matrix.toList_succ]
      congr 1
      exact ih (values ∘ Fin.succ)

theorem compactFormulaFvListTermTask_execute
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    (compactFormulaFvListStep^[compactTermTaskSteps term])
        ((compactArithmeticTermTokens term ++ suffix,
          compactTermTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++ term.fvarList) := by
  induction term generalizing suffix tasks output with
  | bvar index =>
      simp [compactTermTaskSteps, Function.iterate_one,
        Semiterm.fvarList]
  | fvar freeIndex =>
      simp [compactTermTaskSteps, Function.iterate_one,
        Semiterm.fvarList]
  | @func functionArity functionSymbol arguments ih =>
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat binderArity) :=
        List.ofFn arguments
      have hmembers : ∀ member ∈ terms,
          ∀ (memberSuffix : List Nat)
            (memberTasks : List CompactSyntaxTask)
            (memberOutput : List Nat),
          (compactFormulaFvListStep^[compactTermTaskSteps member])
              ((compactArithmeticTermTokens member ++ memberSuffix,
                compactTermTask binderArity :: memberTasks, none),
                memberOutput) =
            ((memberSuffix, memberTasks, none),
              memberOutput ++
                member.fvarList) := by
        intro member hmember memberSuffix memberTasks memberOutput
        rw [List.mem_ofFn] at hmember
        rcases hmember with ⟨index, rfl⟩
        exact ih index memberSuffix memberTasks memberOutput
      have hrepeat : ∀ (termList : List
          (LO.FirstOrder.ArithmeticSemiterm Nat binderArity)),
          (∀ member ∈ termList,
            ∀ (memberSuffix : List Nat)
              (memberTasks : List CompactSyntaxTask)
              (memberOutput : List Nat),
            (compactFormulaFvListStep^[compactTermTaskSteps member])
                ((compactArithmeticTermTokens member ++ memberSuffix,
                  compactTermTask binderArity :: memberTasks, none),
                  memberOutput) =
              ((memberSuffix, memberTasks, none),
                memberOutput ++
                  member.fvarList)) ->
          ∀ (repeatSuffix : List Nat)
            (repeatTasks : List CompactSyntaxTask)
            (repeatOutput : List Nat),
          (compactFormulaFvListStep^[
              compactTermListRepeatSteps termList])
              ((compactTermListTokens termList ++ repeatSuffix,
                compactRepeatTermTask binderArity termList.length ::
                  repeatTasks, none), repeatOutput) =
            ((repeatSuffix, repeatTasks, none),
              repeatOutput ++ compactTermListFvarList termList) := by
        intro termList hall repeatSuffix repeatTasks repeatOutput
        induction termList generalizing repeatOutput with
        | nil =>
            simp [compactTermListRepeatSteps, compactTermListTokens,
              compactTermListFvarList, Function.iterate_one]
        | cons head tail ihTail =>
            have hhead := hall head (by simp)
            have htailMembers : ∀ member ∈ tail,
                ∀ (memberSuffix : List Nat)
                  (memberTasks : List CompactSyntaxTask)
                  (memberOutput : List Nat),
                (compactFormulaFvListStep^[compactTermTaskSteps member])
                    ((compactArithmeticTermTokens member ++ memberSuffix,
                      compactTermTask binderArity :: memberTasks, none),
                      memberOutput) =
                  ((memberSuffix, memberTasks, none),
                    memberOutput ++
                      member.fvarList) := by
              intro member hmember
              exact hall member (by simp [hmember])
            have hone :
                (compactFormulaFvListStep^[1])
                    ((compactTermListTokens (head :: tail) ++ repeatSuffix,
                      compactRepeatTermTask binderArity
                        (head :: tail).length :: repeatTasks,
                      none), repeatOutput) =
                  ((compactArithmeticTermTokens head ++
                      (compactTermListTokens tail ++ repeatSuffix),
                    compactTermTask binderArity ::
                      compactRepeatTermTask binderArity tail.length ::
                        repeatTasks,
                    none), repeatOutput) := by
              simp [compactTermListTokens, Function.iterate_one,
                List.append_assoc]
            have hheadRun := hhead
              (compactTermListTokens tail ++ repeatSuffix)
              (compactRepeatTermTask binderArity tail.length :: repeatTasks)
              repeatOutput
            have htailRun := ihTail htailMembers
              (repeatOutput ++
                head.fvarList)
            have hfirst := compactFormulaFvList_iterate_trans
              hone hheadRun
            have hallRun := compactFormulaFvList_iterate_trans
              hfirst htailRun
            simpa [compactTermListRepeatSteps, compactTermListTokens,
              compactTermListFvarList,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              List.append_assoc] using hallRun
      have hfirst :
          (compactFormulaFvListStep^[1])
              ((compactArithmeticTermTokens
                    (Semiterm.func functionSymbol arguments) ++ suffix,
                compactTermTask binderArity :: tasks, none), output) =
            ((compactTermListTokens terms ++ suffix,
              compactRepeatTermTask binderArity terms.length :: tasks,
              none),
              output) := by
        have htermsTokens : compactTermListTokens terms =
            (List.ofFn fun index =>
              compactArithmeticTermTokens (arguments index)).flatten := by
          exact compactTermListTokens_ofFn arguments
        rw [htermsTokens]
        simpa only [Function.iterate_one, terms, List.length_ofFn] using
          compactFormulaFvListStep_term_func functionSymbol arguments
            suffix output tasks
      have hrepeatRun := hrepeat terms hmembers suffix tasks output
      have hrun := compactFormulaFvList_iterate_trans hfirst hrepeatRun
      have hsteps :
          compactTermTaskSteps
              (Semiterm.func functionSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactTermTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have hshiftedTokens : compactTermListFvarList terms =
          (Matrix.toList fun index => (arguments index).fvarList).flatten := by
        simp only [compactTermListFvarList, terms, List.map_ofFn,
          Function.comp_def]
        rw [listOfFn_eq_matrixToList]
      rw [hshiftedTokens] at hrun
      simpa [Semiterm.fvarList, compactTermListFvarList,
        Function.comp_def, terms, List.append_assoc] using hrun

theorem compactFormulaFvListTermList_execute
    {binderArity : Nat}
    (terms : List
      (LO.FirstOrder.ArithmeticSemiterm Nat binderArity))
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    (compactFormulaFvListStep^[compactTermListRepeatSteps terms])
        ((compactTermListTokens terms ++ suffix,
          compactRepeatTermTask binderArity terms.length :: tasks, none),
          output) =
      ((suffix, tasks, none),
        output ++ compactTermListFvarList terms) := by
  induction terms generalizing output with
  | nil =>
      simp [compactTermListRepeatSteps, compactTermListTokens,
        compactTermListFvarList, Function.iterate_one]
  | cons head tail ih =>
      have hone :
          (compactFormulaFvListStep^[1])
              ((compactTermListTokens (head :: tail) ++ suffix,
                compactRepeatTermTask binderArity
                  (head :: tail).length :: tasks,
                none), output) =
            ((compactArithmeticTermTokens head ++
                (compactTermListTokens tail ++ suffix),
              compactTermTask binderArity ::
                compactRepeatTermTask binderArity tail.length :: tasks,
              none), output) := by
        simp [compactTermListTokens, Function.iterate_one,
          List.append_assoc]
      have hhead := compactFormulaFvListTermTask_execute head
        (compactTermListTokens tail ++ suffix)
        (compactRepeatTermTask binderArity tail.length :: tasks) output
      have hfirst := compactFormulaFvList_iterate_trans hone hhead
      have htail := ih
        (output ++ head.fvarList)
      have hall := compactFormulaFvList_iterate_trans hfirst htail
      simpa [compactTermListRepeatSteps, compactTermListTokens,
        compactTermListFvarList,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using hall

theorem compactFormulaFvListFormulaTask_execute
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    (compactFormulaFvListStep^[compactFormulaTaskSteps formula])
        ((compactArithmeticFormulaTokens formula ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++
          formula.fvarList) := by
  revert suffix tasks output
  let P : (arity : Nat) ->
      LO.FirstOrder.ArithmeticSemiformula Nat arity -> Prop :=
    fun arity formula =>
      ∀ (suffix : List Nat) (tasks : List CompactSyntaxTask)
        (output : List Nat),
        (compactFormulaFvListStep^[compactFormulaTaskSteps formula])
            ((compactArithmeticFormulaTokens formula ++ suffix,
              compactFormulaTask arity :: tasks, none), output) =
          ((suffix, tasks, none),
            output ++
              formula.fvarList)
  change P binderArity formula
  induction formula with
  | @rel formulaArity relationArity relationSymbol arguments =>
      intro suffix tasks output
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat formulaArity) :=
        List.ofFn arguments
      have hfirst :
          (compactFormulaFvListStep^[1])
              ((compactArithmeticFormulaTokens
                    (Semiformula.rel relationSymbol arguments) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none), output) =
            ((compactTermListTokens terms ++ suffix,
              compactRepeatTermTask formulaArity terms.length :: tasks,
              none),
              output) := by
        have htermsTokens : compactTermListTokens terms =
            (List.ofFn fun index =>
              compactArithmeticTermTokens (arguments index)).flatten :=
          compactTermListTokens_ofFn arguments
        rw [htermsTokens]
        simpa only [Function.iterate_one, terms, List.length_ofFn] using
          compactFormulaFvListStep_formula_rel relationSymbol arguments
            suffix output tasks
      have hterms := compactFormulaFvListTermList_execute terms suffix tasks
        output
      have hrun := compactFormulaFvList_iterate_trans hfirst hterms
      have hsteps :
          compactFormulaTaskSteps
              (Semiformula.rel relationSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactFormulaTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have hshiftedTokens : compactTermListFvarList terms =
          (Matrix.toList fun index => (arguments index).fvarList).flatten := by
        simp only [compactTermListFvarList, terms, List.map_ofFn,
          Function.comp_def]
        rw [listOfFn_eq_matrixToList]
      rw [hshiftedTokens] at hrun
      simpa [Semiformula.fvarList, compactTermListFvarList,
        Function.comp_def, terms,
        List.append_assoc] using hrun
  | @nrel formulaArity relationArity relationSymbol arguments =>
      intro suffix tasks output
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat formulaArity) :=
        List.ofFn arguments
      have hfirst :
          (compactFormulaFvListStep^[1])
              ((compactArithmeticFormulaTokens
                    (Semiformula.nrel relationSymbol arguments) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none), output) =
            ((compactTermListTokens terms ++ suffix,
              compactRepeatTermTask formulaArity terms.length :: tasks,
              none),
              output) := by
        have htermsTokens : compactTermListTokens terms =
            (List.ofFn fun index =>
              compactArithmeticTermTokens (arguments index)).flatten :=
          compactTermListTokens_ofFn arguments
        rw [htermsTokens]
        simpa only [Function.iterate_one, terms, List.length_ofFn] using
          compactFormulaFvListStep_formula_nrel relationSymbol arguments
            suffix output tasks
      have hterms := compactFormulaFvListTermList_execute terms suffix tasks
        output
      have hrun := compactFormulaFvList_iterate_trans hfirst hterms
      have hsteps :
          compactFormulaTaskSteps
              (Semiformula.nrel relationSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactFormulaTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have hshiftedTokens : compactTermListFvarList terms =
          (Matrix.toList fun index => (arguments index).fvarList).flatten := by
        simp only [compactTermListFvarList, terms, List.map_ofFn,
          Function.comp_def]
        rw [listOfFn_eq_matrixToList]
      rw [hshiftedTokens] at hrun
      simpa [Semiformula.fvarList, compactTermListFvarList,
        Function.comp_def, terms,
        List.append_assoc] using hrun
  | @verum formulaArity =>
      intro suffix tasks output
      simp only [compactFormulaTaskSteps, Semiformula.fvarList,
        List.append_nil, Function.iterate_one]
      change compactFormulaFvListStep
        ((compactArithmeticFormulaTokens
            (⊤ : LO.FirstOrder.ArithmeticSemiformula Nat formulaArity) ++
              suffix,
          compactFormulaTask formulaArity :: tasks, none), output) =
        ((suffix, tasks, none), output)
      exact compactFormulaFvListStep_formula_verum suffix output tasks
  | @falsum formulaArity =>
      intro suffix tasks output
      simp only [compactFormulaTaskSteps, Semiformula.fvarList,
        List.append_nil, Function.iterate_one]
      change compactFormulaFvListStep
        ((compactArithmeticFormulaTokens
            (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat formulaArity) ++
              suffix,
          compactFormulaTask formulaArity :: tasks, none), output) =
        ((suffix, tasks, none), output)
      exact compactFormulaFvListStep_formula_falsum suffix output tasks
  | @and formulaArity left right ihLeft ihRight =>
      intro suffix tasks output
      have hone :
          (compactFormulaFvListStep^[1])
              ((compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none), output) =
            ((compactArithmeticFormulaTokens left ++
                (compactArithmeticFormulaTokens right ++ suffix),
              compactFormulaTask formulaArity ::
                compactFormulaTask formulaArity :: tasks,
              none), output) := by
        simpa [Function.iterate_one, List.append_assoc] using
          compactFormulaFvListStep_formula_and left right suffix output tasks
      have hleft := ihLeft
        (compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask formulaArity :: tasks) output
      have hright := ihRight suffix tasks (output ++ left.fvarList)
      have hfirst := compactFormulaFvList_iterate_trans hone hleft
      have hrun := compactFormulaFvList_iterate_trans hfirst hright
      change
        (compactFormulaFvListStep^[compactFormulaTaskSteps (left ⋏ right)])
            ((compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none), output) =
          ((suffix, tasks, none),
            output ++ (left ⋏ right).fvarList)
      simpa [compactFormulaTaskSteps, Semiformula.fvarList,
        List.append_assoc] using hrun
  | @or formulaArity left right ihLeft ihRight =>
      intro suffix tasks output
      have hone :
          (compactFormulaFvListStep^[1])
              ((compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none), output) =
            ((compactArithmeticFormulaTokens left ++
                (compactArithmeticFormulaTokens right ++ suffix),
              compactFormulaTask formulaArity ::
                compactFormulaTask formulaArity :: tasks,
              none), output) := by
        simpa [Function.iterate_one, List.append_assoc] using
          compactFormulaFvListStep_formula_or left right suffix output tasks
      have hleft := ihLeft
        (compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask formulaArity :: tasks) output
      have hright := ihRight suffix tasks (output ++ left.fvarList)
      have hfirst := compactFormulaFvList_iterate_trans hone hleft
      have hrun := compactFormulaFvList_iterate_trans hfirst hright
      change
        (compactFormulaFvListStep^[compactFormulaTaskSteps (left ⋎ right)])
            ((compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none), output) =
          ((suffix, tasks, none),
            output ++ (left ⋎ right).fvarList)
      simpa [compactFormulaTaskSteps, Semiformula.fvarList,
        List.append_assoc] using hrun
  | @all formulaArity body ih =>
      intro suffix tasks output
      have hone :
          (compactFormulaFvListStep^[1])
              ((compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none), output) =
            ((compactArithmeticFormulaTokens body ++ suffix,
              compactFormulaTask (formulaArity + 1) :: tasks, none),
              output) := by
        simpa [Function.iterate_one] using
          compactFormulaFvListStep_formula_all body suffix output tasks
      have hbody := ih suffix tasks output
      have hrun := compactFormulaFvList_iterate_trans hone hbody
      change
        (compactFormulaFvListStep^[compactFormulaTaskSteps (∀⁰ body)])
            ((compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none), output) =
          ((suffix, tasks, none),
            output ++ (∀⁰ body).fvarList)
      simpa [compactFormulaTaskSteps, Semiformula.fvarList,
        List.append_assoc] using hrun
  | @exs formulaArity body ih =>
      intro suffix tasks output
      have hone :
          (compactFormulaFvListStep^[1])
              ((compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none), output) =
            ((compactArithmeticFormulaTokens body ++ suffix,
              compactFormulaTask (formulaArity + 1) :: tasks, none),
              output) := by
        simpa [Function.iterate_one] using
          compactFormulaFvListStep_formula_exs body suffix output tasks
      have hbody := ih suffix tasks output
      have hrun := compactFormulaFvList_iterate_trans hone hbody
      change
        (compactFormulaFvListStep^[compactFormulaTaskSteps (∃⁰ body)])
            ((compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none), output) =
          ((suffix, tasks, none),
            output ++ (∃⁰ body).fvarList)
      simpa [compactFormulaTaskSteps, Semiformula.fvarList,
        List.append_assoc] using hrun

theorem compactFormulaFvListTokenTransform_canonical_append
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix : List Nat) :
    compactFormulaFvListTokenTransform binderArity
        (compactArithmeticFormulaTokens formula ++ suffix) =
      some (formula.fvarList,
        suffix) := by
  let tokens := compactArithmeticFormulaTokens formula ++ suffix
  let fvarList := formula.fvarList
  let used := compactFormulaTaskSteps formula + 1
  have htask := compactFormulaFvListFormulaTask_execute formula suffix [] []
  have hfinish :
      (compactFormulaFvListStep^[used])
          ((tokens, [compactFormulaTask binderArity], none), []) =
        ((suffix, [], some (some suffix)), fvarList) := by
    apply compactFormulaFvList_iterate_trans htask
    simp [Function.iterate_one, fvarList]
  have hformula := compactFormulaTaskSteps_le_tokenLength formula
  have hinputLength :
      (compactArithmeticFormulaTokens formula).length <= tokens.length := by
    simp [tokens]
  have hfuelLength := compactSyntaxRunFuelBound_length_add_one tokens
  have hused : used <= compactSyntaxRunFuelBound tokens := by
    omega
  obtain ⟨extra, hfuel⟩ := exists_add_of_le hused
  have hrun :
      (compactFormulaFvListStep^[compactSyntaxRunFuelBound tokens])
          ((tokens, [compactFormulaTask binderArity], none), []) =
        ((suffix, [], some (some suffix)), fvarList) := by
    rw [hfuel]
    exact compactFormulaFvList_iterate_trans hfinish
      (compactFormulaFvListStep_iterate_done extra suffix []
        (some suffix) fvarList)
  simp [compactFormulaFvListTokenTransform, compactFormulaFvListRun,
    compactFormulaFvListInitialState, compactFormulaParserInitialState,
    compactFormulaFvListStateOutput, tokens, fvarList, hrun]

theorem listFvSup_primrec : Primrec listFvSup := by
  have hstep : Primrec₂
      (fun (_values : List Nat) (indexAndMaximum : Nat × Nat) =>
        max (indexAndMaximum.1 + 1) indexAndMaximum.2) := by
    apply Primrec₂.mk
    let Input := List Nat × (Nat × Nat)
    have hleft : Primrec (fun input : Input => input.2.1 + 1) :=
      Primrec.succ.comp (Primrec.fst.comp Primrec.snd)
    have hright : Primrec (fun input : Input => input.2.2) :=
      Primrec.snd.comp Primrec.snd
    have hle : PrimrecPred (fun input : Input =>
        input.2.1 + 1 <= input.2.2) :=
      Primrec.nat_le.comp hleft hright
    exact
      (Primrec.ite hle hright hleft).of_eq fun input => by
        split <;> rename_i hcomparison
        · exact (max_eq_right hcomparison).symm
        · exact (max_eq_left
            (Nat.le_of_lt (Nat.lt_of_not_ge hcomparison))).symm
  exact
    (Primrec.list_foldr Primrec.id (Primrec.const 0) hstep).of_eq
      fun values => by
        induction values with
        | nil => rfl
        | cons value values ih =>
            change List.foldr (fun index maximum =>
              max (index + 1) maximum) 0 values = listFvSup values at ih
            simp only [List.foldr_cons, id_eq, listFvSup]
            rw [ih]

def compactFormulaFvSupTokenTransform
    (binderArity : Nat) (tokens : List Nat) :
    Option (Nat × List Nat) :=
  (compactFormulaFvListTokenTransform binderArity tokens).map
    fun fvarListAndSuffix =>
      (listFvSup fvarListAndSuffix.1, fvarListAndSuffix.2)

theorem compactFormulaFvSupTokenTransform_primrec :
    Primrec₂ compactFormulaFvSupTokenTransform := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  have hlist : Primrec (fun input : Input =>
      compactFormulaFvListTokenTransform input.1 input.2) :=
    compactFormulaFvListTokenTransform_primrec
  have hmaximum : Primrec₂
      (fun (_input : Input) (fvarListAndSuffix : List Nat × List Nat) =>
        listFvSup fvarListAndSuffix.1) :=
    listFvSup_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
  have hresult : Primrec₂
      (fun (_input : Input) (fvarListAndSuffix : List Nat × List Nat) =>
        (listFvSup fvarListAndSuffix.1, fvarListAndSuffix.2)) :=
    Primrec₂.pair.comp₂ hmaximum
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.option_map hlist hresult).of_eq fun input => by
      simp [compactFormulaFvSupTokenTransform]

theorem compactFormulaFvSupTokenTransform_canonical_append
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix : List Nat) :
    compactFormulaFvSupTokenTransform binderArity
        (compactArithmeticFormulaTokens formula ++ suffix) =
      some (formula.fvSup, suffix) := by
  simp [compactFormulaFvSupTokenTransform,
    compactFormulaFvListTokenTransform_canonical_append,
    listFvSup_formula_eq_fvSup]

#print axioms compactFvListConsumedTermHeader_primrec
#print axioms compactSyntaxCurrentTaskKind_primrec
#print axioms compactFormulaFvListEmission_primrec
#print axioms compactFormulaFvListStep_primrec
#print axioms compactFormulaFvListRun_primrec
#print axioms compactFormulaFvListTokenTransform_primrec
#print axioms compactFormulaFvListStep_term_func
#print axioms compactFormulaFvListStep_formula_rel
#print axioms compactFormulaFvListStep_formula_and
#print axioms compactFormulaFvListTermTask_execute
#print axioms compactFormulaFvListTermList_execute
#print axioms compactFormulaFvListFormulaTask_execute
#print axioms compactFormulaFvListTokenTransform_canonical_append
#print axioms listFvSup_primrec
#print axioms compactFormulaFvSupTokenTransform_primrec
#print axioms compactFormulaFvSupTokenTransform_canonical_append

end FoundationCompactNumericFormulaFvSup
