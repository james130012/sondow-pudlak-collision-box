import integration.FoundationCompactNumericFormulaConstructors

/-!
# Pure numeric formula free-variable lowering

The machine reuses the checked numeric syntax-task stack.  At source arity
`n + 1`, the final bound variable becomes free variable zero, earlier bound
variables are preserved, and every old free-variable index is incremented.
The task stack supplies the current source arity below quantifiers.  Runtime
state contains only naturals and lists of naturals; typed syntax is used solely
in the correctness theorem.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericFormulaFree

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser

abbrev CompactFormulaFreeState :=
  CompactSyntaxParserState × List Nat

def compactFreeConsumedTermHeader
    (binderArity : Nat) (tokens : List Nat) : List Nat :=
  if tokens.length = 2 then
    if compactTokenAt 0 tokens = 0 then
      if compactTokenAt 1 tokens + 1 = binderArity then
        [1, 0]
      else
        tokens
    else if compactTokenAt 0 tokens = 1 then
      [1, compactTokenAt 1 tokens + 1]
    else
      tokens
  else
    tokens

theorem compactFreeConsumedTermHeader_primrec :
    Primrec₂ compactFreeConsumedTermHeader := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  have harity : Primrec (fun input : Input => input.1) := Primrec.fst
  have htokens : Primrec (fun input : Input => input.2) := Primrec.snd
  have hlength : Primrec (fun input : Input => input.2.length) :=
    Primrec.list_length.comp htokens
  have hisPair : PrimrecPred
      (fun input : Input => input.2.length = 2) :=
    Primrec.eq.comp hlength (Primrec.const 2)
  have htag : Primrec
      (fun input : Input => compactTokenAt 0 input.2) :=
    compactTokenAt_primrec.comp (Primrec.const 0) htokens
  have hindex : Primrec
      (fun input : Input => compactTokenAt 1 input.2) :=
    compactTokenAt_primrec.comp (Primrec.const 1) htokens
  have hisBound : PrimrecPred
      (fun input : Input => compactTokenAt 0 input.2 = 0) :=
    Primrec.eq.comp htag (Primrec.const 0)
  have hisFree : PrimrecPred
      (fun input : Input => compactTokenAt 0 input.2 = 1) :=
    Primrec.eq.comp htag (Primrec.const 1)
  have hisLast : PrimrecPred
      (fun input : Input => compactTokenAt 1 input.2 + 1 = input.1) :=
    Primrec.eq.comp (Primrec.succ.comp hindex) harity
  have htail : Primrec
      (fun input : Input => [compactTokenAt 1 input.2 + 1]) :=
    Primrec.list_cons.comp (Primrec.succ.comp hindex) (Primrec.const [])
  have hshifted : Primrec
      (fun input : Input => [1, compactTokenAt 1 input.2 + 1]) :=
    Primrec.list_cons.comp (Primrec.const 1) htail
  have hlowered : Primrec (fun _input : Input => [1, 0]) :=
    Primrec.const [1, 0]
  have hbound : Primrec
      (fun input : Input =>
        if compactTokenAt 1 input.2 + 1 = input.1 then [1, 0]
        else input.2) :=
    Primrec.ite hisLast hlowered htokens
  have hbody : Primrec
      (fun input : Input =>
        if compactTokenAt 0 input.2 = 0 then
          if compactTokenAt 1 input.2 + 1 = input.1 then [1, 0]
          else input.2
        else if compactTokenAt 0 input.2 = 1 then
          [1, compactTokenAt 1 input.2 + 1]
        else input.2) :=
    Primrec.ite hisBound hbound
      (Primrec.ite hisFree hshifted htokens)
  exact
    (Primrec.ite hisPair hbody htokens).of_eq fun input => by
      simp [compactFreeConsumedTermHeader]

def compactSyntaxCurrentTask
    (state : CompactSyntaxParserState) : CompactSyntaxTask :=
  state.2.1.head?.getD (3, 0, 0)

theorem compactSyntaxCurrentTask_primrec :
    Primrec compactSyntaxCurrentTask := by
  have htasks : Primrec
      (fun state : CompactSyntaxParserState => state.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hhead : Primrec
      (fun state : CompactSyntaxParserState => state.2.1.head?) :=
    Primrec.list_head?.comp htasks
  exact
    (Primrec.option_getD.comp hhead (Primrec.const (3, 0, 0))).of_eq
      fun state => by rfl

def compactFormulaFreeEmission
    (task : CompactSyntaxTask) (consumed : List Nat) : List Nat :=
  if task.1 = 0 then
    compactFreeConsumedTermHeader task.2.1 consumed
  else
    consumed

theorem compactFormulaFreeEmission_primrec :
    Primrec₂ compactFormulaFreeEmission := by
  apply Primrec₂.mk
  let Input := CompactSyntaxTask × List Nat
  have htask : Primrec (fun input : Input => input.1) := Primrec.fst
  have htokens : Primrec (fun input : Input => input.2) := Primrec.snd
  have hkind : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp htask
  have harity : Primrec (fun input : Input => input.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp htask)
  have hterm : PrimrecPred (fun input : Input => input.1.1 = 0) :=
    Primrec.eq.comp hkind (Primrec.const 0)
  have htransformed : Primrec
      (fun input : Input =>
        compactFreeConsumedTermHeader input.1.2.1 input.2) :=
    compactFreeConsumedTermHeader_primrec.comp harity htokens
  exact
    (Primrec.ite hterm
      htransformed htokens).of_eq fun input => by
        simp only [compactFormulaFreeEmission]

def compactFormulaFreeStep
    (state : CompactFormulaFreeState) :
    CompactFormulaFreeState :=
  let parserState := state.1
  let nextParserState := compactSyntaxParserStep parserState
  let consumed := consumedTokenPrefix parserState.1 nextParserState.1
  let emitted := compactFormulaFreeEmission
    (compactSyntaxCurrentTask parserState) consumed
  (nextParserState, state.2 ++ emitted)

theorem compactFormulaFreeStep_primrec :
    Primrec compactFormulaFreeStep := by
  have hparser : Primrec
      (fun state : CompactFormulaFreeState => state.1) :=
    Primrec.fst
  have hnext : Primrec
      (fun state : CompactFormulaFreeState =>
        compactSyntaxParserStep state.1) :=
    compactSyntaxParserStep_primrec.comp hparser
  have holdTokens : Primrec
      (fun state : CompactFormulaFreeState => state.1.1) :=
    Primrec.fst.comp hparser
  have hnextTokens : Primrec
      (fun state : CompactFormulaFreeState =>
        (compactSyntaxParserStep state.1).1) :=
    Primrec.fst.comp hnext
  have hconsumed : Primrec
      (fun state : CompactFormulaFreeState =>
        consumedTokenPrefix state.1.1
          (compactSyntaxParserStep state.1).1) :=
    consumedTokenPrefix_primrec.comp holdTokens hnextTokens
  have htask : Primrec
      (fun state : CompactFormulaFreeState =>
        compactSyntaxCurrentTask state.1) :=
    compactSyntaxCurrentTask_primrec.comp hparser
  have hemitted : Primrec
      (fun state : CompactFormulaFreeState =>
        compactFormulaFreeEmission
          (compactSyntaxCurrentTask state.1)
          (consumedTokenPrefix state.1.1
            (compactSyntaxParserStep state.1).1)) :=
    compactFormulaFreeEmission_primrec.comp htask hconsumed
  have houtput : Primrec
      (fun state : CompactFormulaFreeState => state.2) :=
    Primrec.snd
  have hnextOutput : Primrec
      (fun state : CompactFormulaFreeState =>
        state.2 ++ compactFormulaFreeEmission
          (compactSyntaxCurrentTask state.1)
          (consumedTokenPrefix state.1.1
            (compactSyntaxParserStep state.1).1)) :=
    Primrec.list_append.comp houtput hemitted
  exact
    (Primrec.pair hnext hnextOutput).of_eq fun state => by rfl

def compactFormulaFreeInitialState
    (binderArity : Nat) (tokens : List Nat) :
    CompactFormulaFreeState :=
  (compactFormulaParserInitialState binderArity tokens, [])

theorem compactFormulaFreeInitialState_primrec :
    Primrec₂ compactFormulaFreeInitialState := by
  exact Primrec₂.pair.comp₂
    compactFormulaParserInitialState_primrec
    (Primrec₂.const [])

def compactFormulaFreeRun
    (binderArity : Nat) (tokens : List Nat) :
    CompactFormulaFreeState :=
  (compactFormulaFreeStep^[compactSyntaxRunFuelBound tokens])
    (compactFormulaFreeInitialState binderArity tokens)

theorem compactFormulaFreeRun_primrec :
    Primrec₂ compactFormulaFreeRun := by
  apply Primrec₂.mk
  have hfuel : Primrec
      (fun input : Nat × List Nat =>
        compactSyntaxRunFuelBound input.2) :=
    compactSyntaxRunFuelBound_primrec.comp Primrec.snd
  have hinitial : Primrec
      (fun input : Nat × List Nat =>
        compactFormulaFreeInitialState input.1 input.2) :=
    compactFormulaFreeInitialState_primrec
  have hstep : Primrec₂
      (fun (_input : Nat × List Nat)
          (state : CompactFormulaFreeState) =>
        compactFormulaFreeStep state) :=
    (compactFormulaFreeStep_primrec.comp Primrec.snd).to₂
  exact
    (Primrec.nat_iterate hfuel hinitial hstep).of_eq
      fun input => by rfl

def compactFormulaFreeStateOutput
    (state : CompactFormulaFreeState) :
    Option (List Nat × List Nat) :=
  state.1.2.2.bind fun result =>
    result.map fun suffix => (state.2, suffix)

theorem compactFormulaFreeStateOutput_primrec :
    Primrec compactFormulaFreeStateOutput := by
  have hstatus : Primrec
      (fun state : CompactFormulaFreeState => state.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hinner : Primrec₂
      (fun (state : CompactFormulaFreeState)
          (result : Option (List Nat)) =>
        result.map fun suffix => (state.2, suffix)) := by
    apply Primrec₂.mk
    let Input := CompactFormulaFreeState × Option (List Nat)
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

def compactFormulaFreeTokenTransform
    (binderArity : Nat) (tokens : List Nat) :
    Option (List Nat × List Nat) :=
  compactFormulaFreeStateOutput
    (compactFormulaFreeRun binderArity tokens)

theorem compactFormulaFreeTokenTransform_primrec :
    Primrec₂ compactFormulaFreeTokenTransform := by
  exact compactFormulaFreeStateOutput_primrec.comp₂
    compactFormulaFreeRun_primrec

/-! ## Exact task execution -/

theorem compactFormulaFree_iterate_trans
    {start middle finish : CompactFormulaFreeState}
    {firstSteps secondSteps : Nat}
    (hfirst : (compactFormulaFreeStep^[firstSteps]) start = middle)
    (hsecond : (compactFormulaFreeStep^[secondSteps]) middle = finish) :
    (compactFormulaFreeStep^[firstSteps + secondSteps]) start = finish := by
  rw [Nat.add_comm, Function.iterate_add_apply, hfirst, hsecond]

theorem compactFormulaFreeStep_of_transition
    {parserState nextParserState : CompactSyntaxParserState}
    {consumed : List Nat} (output : List Nat)
    (hparser : compactSyntaxParserStep parserState = nextParserState)
    (hconsumed : consumedTokenPrefix parserState.1 nextParserState.1 =
      consumed) :
    compactFormulaFreeStep (parserState, output) =
      (nextParserState,
        output ++ compactFormulaFreeEmission
          (compactSyntaxCurrentTask parserState) consumed) := by
  simp [compactFormulaFreeStep, hparser, hconsumed]

@[simp] theorem compactFormulaFreeStep_done
    (tokens : List Nat) (tasks : List CompactSyntaxTask)
    (result : Option (List Nat)) (output : List Nat) :
    compactFormulaFreeStep
        ((tokens, tasks, some result), output) =
      ((tokens, tasks, some result), output) := by
  refine (compactFormulaFreeStep_of_transition output
    (consumed := [])
    (compactSyntaxParserStep_done tokens tasks result) ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactFormulaFreeEmission,
      compactFreeConsumedTermHeader, compactTokenAt]

theorem compactFormulaFreeStep_iterate_done
    (fuel : Nat) (tokens : List Nat) (tasks : List CompactSyntaxTask)
    (result : Option (List Nat)) (output : List Nat) :
    (compactFormulaFreeStep^[fuel])
        ((tokens, tasks, some result), output) =
      ((tokens, tasks, some result), output) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply,
        compactFormulaFreeStep_done, ih]

@[simp] theorem compactFormulaFreeStep_empty
    (tokens output : List Nat) :
    compactFormulaFreeStep ((tokens, [], none), output) =
      ((tokens, [], some (some tokens)), output) := by
  refine (compactFormulaFreeStep_of_transition output
    (consumed := []) (compactSyntaxParserStep_empty tokens) ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTask,
      compactFormulaFreeEmission]

@[simp] theorem compactFormulaFreeStep_repeat_zero
    (binderArity : Nat) (tokens output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFreeStep
        ((tokens, compactRepeatTermTask binderArity 0 :: tasks, none),
          output) =
      ((tokens, tasks, none), output) := by
  have hparser : compactSyntaxParserStep
      (tokens, compactRepeatTermTask binderArity 0 :: tasks, none) =
      (tokens, tasks, none) := by
    simpa [compactSyntaxContinue] using
      (compactSyntaxParserStep_repeat_zero binderArity tokens tasks)
  refine (compactFormulaFreeStep_of_transition output
    (consumed := []) hparser ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTask, compactRepeatTermTask,
      compactFormulaFreeEmission]

@[simp] theorem compactFormulaFreeStep_repeat_succ
    (binderArity count : Nat) (tokens output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFreeStep
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
  refine (compactFormulaFreeStep_of_transition output
    (consumed := []) hparser ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTask, compactRepeatTermTask,
      compactFormulaFreeEmission]

@[simp] theorem compactFormulaFreeStep_term_bvar
    {binderArity : Nat} (index : Fin binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFreeStep
        ((compactArithmeticTermTokens (#index) ++ suffix,
          compactTermTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++
          if index.val + 1 = binderArity then [1, 0]
          else [(0 : Nat), index.val]) := by
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
  refine (compactFormulaFreeStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactTermTask,
    compactFormulaFreeEmission, compactFreeConsumedTermHeader,
    compactTokenAt, htokens]

@[simp] theorem compactFormulaFreeStep_term_fvar
    {binderArity : Nat} (freeIndex : Nat)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFreeStep
        ((compactArithmeticTermTokens
            (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) ++
              suffix,
          compactTermTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++ [1, freeIndex + 1]) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticTermTokens
          (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) ++
            suffix,
        compactTermTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
    rw [compactSyntaxParserStep_term]
    exact compactTermTokenStep_fvar freeIndex suffix tasks
  refine (compactFormulaFreeStep_of_transition output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTask, compactTermTask,
    compactFormulaFreeEmission, compactFreeConsumedTermHeader,
    compactArithmeticTermTokens, compactTokenAt]

@[simp] theorem compactFormulaFreeStep_term_func
    {binderArity functionArity : Nat}
    (functionSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Func functionArity)
    (arguments : Fin functionArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFreeStep
        ((compactArithmeticTermTokens
              (Semiterm.func functionSymbol arguments) ++ suffix,
          compactTermTask binderArity :: tasks, none), output) =
      (((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix,
        compactRepeatTermTask binderArity functionArity :: tasks, none),
        output ++ [2, functionArity, Encodable.encode functionSymbol]) := by
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
  refine (compactFormulaFreeStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactTermTask,
    compactFormulaFreeEmission, compactFreeConsumedTermHeader,
    compactTokenAt]

@[simp] theorem compactFormulaFreeStep_formula_rel
    {binderArity relationArity : Nat}
    (relationSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Rel relationArity)
    (arguments : Fin relationArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFreeStep
        ((compactArithmeticFormulaTokens
              (Semiformula.rel relationSymbol arguments) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      (((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix,
        compactRepeatTermTask binderArity relationArity :: tasks, none),
        output ++ [0, relationArity, Encodable.encode relationSymbol]) := by
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
  refine (compactFormulaFreeStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaFreeEmission, compactFreeConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaFreeStep_formula_nrel
    {binderArity relationArity : Nat}
    (relationSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Rel relationArity)
    (arguments : Fin relationArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFreeStep
        ((compactArithmeticFormulaTokens
              (Semiformula.nrel relationSymbol arguments) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      (((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix,
        compactRepeatTermTask binderArity relationArity :: tasks, none),
        output ++ [1, relationArity, Encodable.encode relationSymbol]) := by
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
  refine (compactFormulaFreeStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaFreeEmission, compactFreeConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaFreeStep_formula_verum
    {binderArity : Nat} (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFreeStep
        ((compactArithmeticFormulaTokens
              (⊤ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none), output ++ [2]) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticFormulaTokens
          (⊤ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) ++ suffix,
        compactFormulaTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
    rw [compactSyntaxParserStep_formula]
    exact compactFormulaTokenStep_verum suffix tasks
  refine (compactFormulaFreeStep_of_transition output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaFreeEmission, compactFreeConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaFreeStep_formula_falsum
    {binderArity : Nat} (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFreeStep
        ((compactArithmeticFormulaTokens
              (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none), output ++ [3]) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticFormulaTokens
          (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) ++ suffix,
        compactFormulaTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
    rw [compactSyntaxParserStep_formula]
    exact compactFormulaTokenStep_falsum suffix tasks
  refine (compactFormulaFreeStep_of_transition output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaFreeEmission, compactFreeConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaFreeStep_formula_and
    {binderArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFreeStep
        ((compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((compactArithmeticFormulaTokens left ++
          compactArithmeticFormulaTokens right ++ suffix,
        compactFormulaTask binderArity ::
          compactFormulaTask binderArity :: tasks, none),
        output ++ [4]) := by
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
  refine (compactFormulaFreeStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaFreeEmission, compactFreeConsumedTermHeader]

@[simp] theorem compactFormulaFreeStep_formula_or
    {binderArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFreeStep
        ((compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((compactArithmeticFormulaTokens left ++
          compactArithmeticFormulaTokens right ++ suffix,
        compactFormulaTask binderArity ::
          compactFormulaTask binderArity :: tasks, none),
        output ++ [5]) := by
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
  refine (compactFormulaFreeStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaFreeEmission, compactFreeConsumedTermHeader]

@[simp] theorem compactFormulaFreeStep_formula_all
    {binderArity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (binderArity + 1))
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFreeStep
        ((compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((compactArithmeticFormulaTokens body ++ suffix,
        compactFormulaTask (binderArity + 1) :: tasks, none),
        output ++ [6]) := by
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
  refine (compactFormulaFreeStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaFreeEmission, compactFreeConsumedTermHeader]

@[simp] theorem compactFormulaFreeStep_formula_exs
    {binderArity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (binderArity + 1))
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaFreeStep
        ((compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((compactArithmeticFormulaTokens body ++ suffix,
        compactFormulaTask (binderArity + 1) :: tasks, none),
        output ++ [7]) := by
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
  refine (compactFormulaFreeStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaFreeEmission, compactFreeConsumedTermHeader]

def compactFreedTermListTokens {targetArity : Nat}
    (terms : List
      (LO.FirstOrder.ArithmeticSemiterm Nat (targetArity + 1))) : List Nat :=
  (terms.map fun term =>
    compactArithmeticTermTokens (Rew.free term)).flatten

theorem compactFreeBvarHeader_tokens
    {targetArity : Nat} (index : Fin (targetArity + 1)) :
    (if index.val + 1 = targetArity + 1 then [1, 0]
      else [(0 : Nat), index.val]) =
      compactArithmeticTermTokens (Rew.free (#index)) := by
  cases index using Fin.lastCases with
  | last =>
      simp [compactArithmeticTermTokens, Rew.free]
  | cast previous =>
      have hprevious := previous.isLt
      simp [compactArithmeticTermTokens, Rew.free]
      omega

theorem compactFormulaFreeTermTask_execute
    {targetArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat (targetArity + 1))
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    (compactFormulaFreeStep^[compactTermTaskSteps term])
        ((compactArithmeticTermTokens term ++ suffix,
          compactTermTask (targetArity + 1) :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++ compactArithmeticTermTokens (Rew.free term)) := by
  induction term generalizing suffix tasks output with
  | bvar index =>
      have hstep := compactFormulaFreeStep_term_bvar
        index suffix output tasks
      simpa only [compactTermTaskSteps, Function.iterate_one,
        compactFreeBvarHeader_tokens] using hstep
  | fvar freeIndex =>
      have hstep := compactFormulaFreeStep_term_fvar
        (binderArity := targetArity + 1) freeIndex suffix output tasks
      simpa [compactTermTaskSteps, Function.iterate_one,
        compactArithmeticTermTokens, Rew.free] using hstep
  | @func functionArity functionSymbol arguments ih =>
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat (targetArity + 1)) :=
        List.ofFn arguments
      have hmembers : ∀ member ∈ terms,
          ∀ (memberSuffix : List Nat)
            (memberTasks : List CompactSyntaxTask)
            (memberOutput : List Nat),
          (compactFormulaFreeStep^[compactTermTaskSteps member])
              ((compactArithmeticTermTokens member ++ memberSuffix,
                compactTermTask (targetArity + 1) :: memberTasks, none),
                memberOutput) =
            ((memberSuffix, memberTasks, none),
              memberOutput ++
                compactArithmeticTermTokens (Rew.free member)) := by
        intro member hmember memberSuffix memberTasks memberOutput
        rw [List.mem_ofFn] at hmember
        rcases hmember with ⟨index, rfl⟩
        exact ih index memberSuffix memberTasks memberOutput
      have hrepeat : ∀ (termList : List
          (LO.FirstOrder.ArithmeticSemiterm Nat (targetArity + 1))),
          (∀ member ∈ termList,
            ∀ (memberSuffix : List Nat)
              (memberTasks : List CompactSyntaxTask)
              (memberOutput : List Nat),
            (compactFormulaFreeStep^[compactTermTaskSteps member])
                ((compactArithmeticTermTokens member ++ memberSuffix,
                  compactTermTask (targetArity + 1) :: memberTasks, none),
                  memberOutput) =
              ((memberSuffix, memberTasks, none),
                memberOutput ++
                  compactArithmeticTermTokens (Rew.free member))) ->
          ∀ (repeatSuffix : List Nat)
            (repeatTasks : List CompactSyntaxTask)
            (repeatOutput : List Nat),
          (compactFormulaFreeStep^[
              compactTermListRepeatSteps termList])
              ((compactTermListTokens termList ++ repeatSuffix,
                compactRepeatTermTask (targetArity + 1) termList.length ::
                  repeatTasks, none), repeatOutput) =
            ((repeatSuffix, repeatTasks, none),
              repeatOutput ++ compactFreedTermListTokens termList) := by
        intro termList hall repeatSuffix repeatTasks repeatOutput
        induction termList generalizing repeatOutput with
        | nil =>
            simp [compactTermListRepeatSteps, compactTermListTokens,
              compactFreedTermListTokens, Function.iterate_one]
        | cons head tail ihTail =>
            have hhead := hall head (by simp)
            have htailMembers : ∀ member ∈ tail,
                ∀ (memberSuffix : List Nat)
                  (memberTasks : List CompactSyntaxTask)
                  (memberOutput : List Nat),
                (compactFormulaFreeStep^[compactTermTaskSteps member])
                    ((compactArithmeticTermTokens member ++ memberSuffix,
                      compactTermTask (targetArity + 1) :: memberTasks, none),
                      memberOutput) =
                  ((memberSuffix, memberTasks, none),
                    memberOutput ++
                      compactArithmeticTermTokens (Rew.free member)) := by
              intro member hmember
              exact hall member (by simp [hmember])
            have hone :
                (compactFormulaFreeStep^[1])
                    ((compactTermListTokens (head :: tail) ++ repeatSuffix,
                      compactRepeatTermTask (targetArity + 1)
                        (head :: tail).length :: repeatTasks,
                      none), repeatOutput) =
                  ((compactArithmeticTermTokens head ++
                      (compactTermListTokens tail ++ repeatSuffix),
                    compactTermTask (targetArity + 1) ::
                      compactRepeatTermTask (targetArity + 1) tail.length ::
                        repeatTasks,
                    none), repeatOutput) := by
              simp [compactTermListTokens, Function.iterate_one,
                List.append_assoc]
            have hheadRun := hhead
              (compactTermListTokens tail ++ repeatSuffix)
              (compactRepeatTermTask (targetArity + 1) tail.length ::
                repeatTasks)
              repeatOutput
            have htailRun := ihTail htailMembers
              (repeatOutput ++
                compactArithmeticTermTokens (Rew.free head))
            have hfirst := compactFormulaFree_iterate_trans
              hone hheadRun
            have hallRun := compactFormulaFree_iterate_trans
              hfirst htailRun
            simpa [compactTermListRepeatSteps, compactTermListTokens,
              compactFreedTermListTokens,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              List.append_assoc] using hallRun
      have hfirst :
          (compactFormulaFreeStep^[1])
              ((compactArithmeticTermTokens
                    (Semiterm.func functionSymbol arguments) ++ suffix,
                compactTermTask (targetArity + 1) :: tasks, none), output) =
            ((compactTermListTokens terms ++ suffix,
              compactRepeatTermTask (targetArity + 1) terms.length :: tasks,
              none),
              output ++ [2, functionArity,
                Encodable.encode functionSymbol]) := by
        have htermsTokens : compactTermListTokens terms =
            (List.ofFn fun index =>
              compactArithmeticTermTokens (arguments index)).flatten := by
          exact compactTermListTokens_ofFn arguments
        rw [htermsTokens]
        simpa only [Function.iterate_one, terms, List.length_ofFn] using
          compactFormulaFreeStep_term_func functionSymbol arguments
            suffix output tasks
      have hrepeatRun := hrepeat terms hmembers suffix tasks
        (output ++ [2, functionArity, Encodable.encode functionSymbol])
      have hrun := compactFormulaFree_iterate_trans hfirst hrepeatRun
      have hsteps :
          compactTermTaskSteps
              (Semiterm.func functionSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactTermTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have hfreedTokens : compactFreedTermListTokens terms =
          (List.ofFn fun index => compactArithmeticTermTokens
            (Rew.free (arguments index))).flatten := by
        simp only [compactFreedTermListTokens, terms, List.map_ofFn,
          Function.comp_def]
      rw [hfreedTokens] at hrun
      simpa [compactArithmeticTermTokens, compactFreedTermListTokens,
        Rew.func, Function.comp_def, terms, List.append_assoc] using hrun

theorem compactFormulaFreeTermList_execute
    {targetArity : Nat}
    (terms : List
      (LO.FirstOrder.ArithmeticSemiterm Nat (targetArity + 1)))
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    (compactFormulaFreeStep^[compactTermListRepeatSteps terms])
        ((compactTermListTokens terms ++ suffix,
          compactRepeatTermTask (targetArity + 1) terms.length :: tasks,
          none),
          output) =
      ((suffix, tasks, none),
        output ++ compactFreedTermListTokens terms) := by
  induction terms generalizing output with
  | nil =>
      simp [compactTermListRepeatSteps, compactTermListTokens,
        compactFreedTermListTokens, Function.iterate_one]
  | cons head tail ih =>
      have hone :
          (compactFormulaFreeStep^[1])
              ((compactTermListTokens (head :: tail) ++ suffix,
                compactRepeatTermTask (targetArity + 1)
                  (head :: tail).length :: tasks,
                none), output) =
            ((compactArithmeticTermTokens head ++
                (compactTermListTokens tail ++ suffix),
              compactTermTask (targetArity + 1) ::
                compactRepeatTermTask (targetArity + 1) tail.length :: tasks,
              none), output) := by
        simp [compactTermListTokens, Function.iterate_one,
          List.append_assoc]
      have hhead := compactFormulaFreeTermTask_execute head
        (compactTermListTokens tail ++ suffix)
        (compactRepeatTermTask (targetArity + 1) tail.length :: tasks) output
      have hfirst := compactFormulaFree_iterate_trans hone hhead
      have htail := ih
        (output ++ compactArithmeticTermTokens (Rew.free head))
      have hall := compactFormulaFree_iterate_trans hfirst htail
      simpa [compactTermListRepeatSteps, compactTermListTokens,
        compactFreedTermListTokens,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using hall

def compactFreeFormulaAlong
    {sourceArity targetArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat sourceArity)
    (harity : sourceArity = targetArity + 1) :
    LO.FirstOrder.ArithmeticSemiformula Nat targetArity := by
  subst sourceArity
  exact Rewriting.free formula

theorem compactFormulaFreeFormulaTask_execute_along
    {sourceArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat sourceArity) :
    ∀ {targetArity : Nat}
      (harity : sourceArity = targetArity + 1)
      (suffix : List Nat) (tasks : List CompactSyntaxTask)
      (output : List Nat),
      (compactFormulaFreeStep^[compactFormulaTaskSteps formula])
          ((compactArithmeticFormulaTokens formula ++ suffix,
            compactFormulaTask sourceArity :: tasks, none), output) =
        ((suffix, tasks, none),
          output ++ compactArithmeticFormulaTokens
            (compactFreeFormulaAlong formula harity)) := by
  induction formula using Semiformula.rec' with
  | hverum =>
      intro targetArity harity suffix tasks output
      cases harity
      change
        (compactFormulaFreeStep^[1])
            ((compactArithmeticFormulaTokens
                (⊤ : LO.FirstOrder.ArithmeticSemiformula Nat
                  (targetArity + 1)) ++ suffix,
              compactFormulaTask (targetArity + 1) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ [2])
      simpa only [Function.iterate_one] using
        (compactFormulaFreeStep_formula_verum
          (binderArity := targetArity + 1) suffix output tasks)
  | hfalsum =>
      intro targetArity harity suffix tasks output
      cases harity
      change
        (compactFormulaFreeStep^[1])
            ((compactArithmeticFormulaTokens
                (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat
                  (targetArity + 1)) ++ suffix,
              compactFormulaTask (targetArity + 1) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ [3])
      simpa only [Function.iterate_one] using
        (compactFormulaFreeStep_formula_falsum
          (binderArity := targetArity + 1) suffix output tasks)
  | @hrel sourceArity relationArity relationSymbol arguments =>
      intro targetArity harity suffix tasks output
      cases harity
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat (targetArity + 1)) :=
        List.ofFn arguments
      have hfirst :
          (compactFormulaFreeStep^[1])
              ((compactArithmeticFormulaTokens
                    (Semiformula.rel relationSymbol arguments) ++ suffix,
                compactFormulaTask (targetArity + 1) :: tasks, none),
                output) =
            ((compactTermListTokens terms ++ suffix,
              compactRepeatTermTask (targetArity + 1) terms.length :: tasks,
              none),
              output ++ [0, relationArity,
                Encodable.encode relationSymbol]) := by
        have htermsTokens : compactTermListTokens terms =
            (List.ofFn fun index =>
              compactArithmeticTermTokens (arguments index)).flatten :=
          compactTermListTokens_ofFn arguments
        rw [htermsTokens]
        simpa only [Function.iterate_one, terms, List.length_ofFn] using
          compactFormulaFreeStep_formula_rel relationSymbol arguments
            suffix output tasks
      have hterms := compactFormulaFreeTermList_execute terms suffix tasks
        (output ++ [0, relationArity, Encodable.encode relationSymbol])
      have hrun := compactFormulaFree_iterate_trans hfirst hterms
      have hsteps :
          compactFormulaTaskSteps
              (Semiformula.rel relationSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactFormulaTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have hfreedTokens : compactFreedTermListTokens terms =
          (List.ofFn fun index => compactArithmeticTermTokens
            (Rew.free (arguments index))).flatten := by
        simp only [compactFreedTermListTokens, terms, List.map_ofFn,
          Function.comp_def]
      rw [hfreedTokens] at hrun
      simpa [compactFreeFormulaAlong, compactArithmeticFormulaTokens,
        Semiformula.rew_rel, Function.comp_def, terms,
        List.append_assoc] using hrun
  | @hnrel sourceArity relationArity relationSymbol arguments =>
      intro targetArity harity suffix tasks output
      cases harity
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat (targetArity + 1)) :=
        List.ofFn arguments
      have hfirst :
          (compactFormulaFreeStep^[1])
              ((compactArithmeticFormulaTokens
                    (Semiformula.nrel relationSymbol arguments) ++ suffix,
                compactFormulaTask (targetArity + 1) :: tasks, none),
                output) =
            ((compactTermListTokens terms ++ suffix,
              compactRepeatTermTask (targetArity + 1) terms.length :: tasks,
              none),
              output ++ [1, relationArity,
                Encodable.encode relationSymbol]) := by
        have htermsTokens : compactTermListTokens terms =
            (List.ofFn fun index =>
              compactArithmeticTermTokens (arguments index)).flatten :=
          compactTermListTokens_ofFn arguments
        rw [htermsTokens]
        simpa only [Function.iterate_one, terms, List.length_ofFn] using
          compactFormulaFreeStep_formula_nrel relationSymbol arguments
            suffix output tasks
      have hterms := compactFormulaFreeTermList_execute terms suffix tasks
        (output ++ [1, relationArity, Encodable.encode relationSymbol])
      have hrun := compactFormulaFree_iterate_trans hfirst hterms
      have hsteps :
          compactFormulaTaskSteps
              (Semiformula.nrel relationSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactFormulaTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have hfreedTokens : compactFreedTermListTokens terms =
          (List.ofFn fun index => compactArithmeticTermTokens
            (Rew.free (arguments index))).flatten := by
        simp only [compactFreedTermListTokens, terms, List.map_ofFn,
          Function.comp_def]
      rw [hfreedTokens] at hrun
      simpa [compactFreeFormulaAlong, compactArithmeticFormulaTokens,
        Semiformula.rew_nrel, Function.comp_def, terms,
        List.append_assoc] using hrun
  | @hand sourceArity left right ihLeft ihRight =>
      intro targetArity harity suffix tasks output
      cases harity
      have hone :
          (compactFormulaFreeStep^[1])
              ((compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
                compactFormulaTask (targetArity + 1) :: tasks, none),
                output) =
            ((compactArithmeticFormulaTokens left ++
                (compactArithmeticFormulaTokens right ++ suffix),
              compactFormulaTask (targetArity + 1) ::
                compactFormulaTask (targetArity + 1) :: tasks,
              none), output ++ [4]) := by
        simpa [Function.iterate_one, List.append_assoc] using
          compactFormulaFreeStep_formula_and left right suffix output tasks
      have hleft := ihLeft (targetArity := targetArity) rfl
        (compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask (targetArity + 1) :: tasks) (output ++ [4])
      have hright := ihRight (targetArity := targetArity) rfl suffix tasks
        (output ++ [4] ++ compactArithmeticFormulaTokens
          (compactFreeFormulaAlong left rfl))
      have hfirst := compactFormulaFree_iterate_trans hone hleft
      have hrun := compactFormulaFree_iterate_trans hfirst hright
      change
        (compactFormulaFreeStep^[compactFormulaTaskSteps (left ⋏ right)])
            ((compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
              compactFormulaTask (targetArity + 1) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ compactArithmeticFormulaTokens
            (compactFreeFormulaAlong (left ⋏ right) rfl))
      simpa [compactFormulaTaskSteps, compactFreeFormulaAlong,
        compactArithmeticFormulaTokens,
        LogicalConnective.HomClass.map_and, List.append_assoc] using hrun
  | @hor sourceArity left right ihLeft ihRight =>
      intro targetArity harity suffix tasks output
      cases harity
      have hone :
          (compactFormulaFreeStep^[1])
              ((compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
                compactFormulaTask (targetArity + 1) :: tasks, none),
                output) =
            ((compactArithmeticFormulaTokens left ++
                (compactArithmeticFormulaTokens right ++ suffix),
              compactFormulaTask (targetArity + 1) ::
                compactFormulaTask (targetArity + 1) :: tasks,
              none), output ++ [5]) := by
        simpa [Function.iterate_one, List.append_assoc] using
          compactFormulaFreeStep_formula_or left right suffix output tasks
      have hleft := ihLeft (targetArity := targetArity) rfl
        (compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask (targetArity + 1) :: tasks) (output ++ [5])
      have hright := ihRight (targetArity := targetArity) rfl suffix tasks
        (output ++ [5] ++ compactArithmeticFormulaTokens
          (compactFreeFormulaAlong left rfl))
      have hfirst := compactFormulaFree_iterate_trans hone hleft
      have hrun := compactFormulaFree_iterate_trans hfirst hright
      change
        (compactFormulaFreeStep^[compactFormulaTaskSteps (left ⋎ right)])
            ((compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
              compactFormulaTask (targetArity + 1) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ compactArithmeticFormulaTokens
            (compactFreeFormulaAlong (left ⋎ right) rfl))
      simpa [compactFormulaTaskSteps, compactFreeFormulaAlong,
        compactArithmeticFormulaTokens,
        LogicalConnective.HomClass.map_or, List.append_assoc] using hrun
  | @hall sourceArity body ih =>
      intro targetArity harity suffix tasks output
      cases harity
      have hone :
          (compactFormulaFreeStep^[1])
              ((compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
                compactFormulaTask (targetArity + 1) :: tasks, none),
                output) =
            ((compactArithmeticFormulaTokens body ++ suffix,
              compactFormulaTask ((targetArity + 1) + 1) :: tasks, none),
              output ++ [6]) := by
        simpa [Function.iterate_one] using
          compactFormulaFreeStep_formula_all body suffix output tasks
      have hbody := ih (targetArity := targetArity + 1) rfl suffix tasks
        (output ++ [6])
      have hrun := compactFormulaFree_iterate_trans hone hbody
      change
        (compactFormulaFreeStep^[compactFormulaTaskSteps (∀⁰ body)])
            ((compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
              compactFormulaTask (targetArity + 1) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ compactArithmeticFormulaTokens
            (compactFreeFormulaAlong (∀⁰ body) rfl))
      simpa [compactFormulaTaskSteps, compactFreeFormulaAlong,
        compactArithmeticFormulaTokens, Rewriting.app_all, Rew.q_free,
        List.append_assoc] using hrun
  | @hexs sourceArity body ih =>
      intro targetArity harity suffix tasks output
      cases harity
      have hone :
          (compactFormulaFreeStep^[1])
              ((compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
                compactFormulaTask (targetArity + 1) :: tasks, none),
                output) =
            ((compactArithmeticFormulaTokens body ++ suffix,
              compactFormulaTask ((targetArity + 1) + 1) :: tasks, none),
              output ++ [7]) := by
        simpa [Function.iterate_one] using
          compactFormulaFreeStep_formula_exs body suffix output tasks
      have hbody := ih (targetArity := targetArity + 1) rfl suffix tasks
        (output ++ [7])
      have hrun := compactFormulaFree_iterate_trans hone hbody
      change
        (compactFormulaFreeStep^[compactFormulaTaskSteps (∃⁰ body)])
            ((compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
              compactFormulaTask (targetArity + 1) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ compactArithmeticFormulaTokens
            (compactFreeFormulaAlong (∃⁰ body) rfl))
      simpa [compactFormulaTaskSteps, compactFreeFormulaAlong,
        compactArithmeticFormulaTokens, Rewriting.app_exs, Rew.q_free,
        List.append_assoc] using hrun

theorem compactFormulaFreeFormulaTask_execute
    {targetArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat (targetArity + 1))
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    (compactFormulaFreeStep^[compactFormulaTaskSteps formula])
        ((compactArithmeticFormulaTokens formula ++ suffix,
          compactFormulaTask (targetArity + 1) :: tasks, none), output) =
      ((suffix, tasks, none), output ++
        compactArithmeticFormulaTokens (Rewriting.free formula)) := by
  simpa [compactFreeFormulaAlong] using
    (compactFormulaFreeFormulaTask_execute_along formula rfl suffix tasks
      output)

theorem compactFormulaFreeTokenTransform_canonical_append
    {targetArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat (targetArity + 1))
    (suffix : List Nat) :
    compactFormulaFreeTokenTransform (targetArity + 1)
        (compactArithmeticFormulaTokens formula ++ suffix) =
      some (compactArithmeticFormulaTokens (Rewriting.free formula),
        suffix) := by
  let tokens := compactArithmeticFormulaTokens formula ++ suffix
  let freedTokens := compactArithmeticFormulaTokens
    (Rewriting.free formula)
  let used := compactFormulaTaskSteps formula + 1
  have htask := compactFormulaFreeFormulaTask_execute formula suffix [] []
  have hfinish :
      (compactFormulaFreeStep^[used])
          ((tokens, [compactFormulaTask (targetArity + 1)], none), []) =
        ((suffix, [], some (some suffix)), freedTokens) := by
    apply compactFormulaFree_iterate_trans htask
    simp [Function.iterate_one, freedTokens]
  have hformula := compactFormulaTaskSteps_le_tokenLength formula
  have hinputLength :
      (compactArithmeticFormulaTokens formula).length <= tokens.length := by
    simp [tokens]
  have hfuelLength := compactSyntaxRunFuelBound_length_add_one tokens
  have hused : used <= compactSyntaxRunFuelBound tokens := by
    omega
  obtain ⟨extra, hfuel⟩ := exists_add_of_le hused
  have hrun :
      (compactFormulaFreeStep^[compactSyntaxRunFuelBound tokens])
          ((tokens, [compactFormulaTask (targetArity + 1)], none), []) =
        ((suffix, [], some (some suffix)), freedTokens) := by
    rw [hfuel]
    exact compactFormulaFree_iterate_trans hfinish
      (compactFormulaFreeStep_iterate_done extra suffix []
        (some suffix) freedTokens)
  simp [compactFormulaFreeTokenTransform, compactFormulaFreeRun,
    compactFormulaFreeInitialState, compactFormulaParserInitialState,
    compactFormulaFreeStateOutput, tokens, freedTokens, hrun]

#print axioms compactFreeConsumedTermHeader_primrec
#print axioms compactSyntaxCurrentTask_primrec
#print axioms compactFormulaFreeEmission_primrec
#print axioms compactFormulaFreeStep_primrec
#print axioms compactFormulaFreeRun_primrec
#print axioms compactFormulaFreeTokenTransform_primrec
#print axioms compactFormulaFreeStep_term_func
#print axioms compactFormulaFreeStep_formula_rel
#print axioms compactFormulaFreeStep_formula_and
#print axioms compactFormulaFreeTermTask_execute
#print axioms compactFormulaFreeTermList_execute
#print axioms compactFormulaFreeFormulaTask_execute
#print axioms compactFormulaFreeTokenTransform_canonical_append

end FoundationCompactNumericFormulaFree
