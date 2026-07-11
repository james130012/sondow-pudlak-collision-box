import integration.FoundationCompactNumericFormulaConstructors

/-!
# Pure numeric iterated free-variable capture

The machine computes `Rew.fixitr n m` in one syntax traversal.  At the current
source binder arity `a`, free variable `i < m` becomes bound variable `a + i`,
while every other free variable becomes `i - m`; bound variables and syntax
headers are unchanged.  The task stack supplies `a` below quantifiers. Runtime
state contains only naturals and lists of naturals; typed syntax is used solely
in correctness.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericFormulaFixitr

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser

abbrev CompactFormulaFixitrState :=
  CompactSyntaxParserState × List Nat

def compactFixitrConsumedTermHeader
    (binderAndCount : Nat × Nat) (tokens : List Nat) : List Nat :=
  if tokens.length = 2 then
    if compactTokenAt 0 tokens = 1 then
      if compactTokenAt 1 tokens < binderAndCount.2 then
        [0, binderAndCount.1 + compactTokenAt 1 tokens]
      else
        [1, compactTokenAt 1 tokens - binderAndCount.2]
    else
      tokens
  else
    tokens

theorem compactFixitrConsumedTermHeader_primrec :
    Primrec₂ compactFixitrConsumedTermHeader := by
  apply Primrec₂.mk
  let Input := (Nat × Nat) × List Nat
  have harity : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hcount : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
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
  have hisFree : PrimrecPred
      (fun input : Input => compactTokenAt 0 input.2 = 1) :=
    Primrec.eq.comp htag (Primrec.const 1)
  have hisCaptured : PrimrecPred
      (fun input : Input => compactTokenAt 1 input.2 < input.1.2) :=
    Primrec.nat_lt.comp hindex hcount
  have hboundIndex : Primrec
      (fun input : Input => input.1.1 + compactTokenAt 1 input.2) :=
    Primrec.nat_add.comp harity hindex
  have hboundTail : Primrec
      (fun input : Input => [input.1.1 + compactTokenAt 1 input.2]) :=
    Primrec.list_cons.comp hboundIndex (Primrec.const [])
  have hboundHeader : Primrec
      (fun input : Input => [0, input.1.1 + compactTokenAt 1 input.2]) :=
    Primrec.list_cons.comp (Primrec.const 0) hboundTail
  have hfreeIndex : Primrec
      (fun input : Input => compactTokenAt 1 input.2 - input.1.2) :=
    Primrec.nat_sub.comp hindex hcount
  have hfreeTail : Primrec
      (fun input : Input => [compactTokenAt 1 input.2 - input.1.2]) :=
    Primrec.list_cons.comp hfreeIndex (Primrec.const [])
  have hfreeHeader : Primrec
      (fun input : Input => [1, compactTokenAt 1 input.2 - input.1.2]) :=
    Primrec.list_cons.comp (Primrec.const 1) hfreeTail
  have hfree : Primrec
      (fun input : Input =>
        if compactTokenAt 1 input.2 < input.1.2 then
          [0, input.1.1 + compactTokenAt 1 input.2]
        else
          [1, compactTokenAt 1 input.2 - input.1.2]) :=
    Primrec.ite hisCaptured hboundHeader hfreeHeader
  have hbody : Primrec
      (fun input : Input =>
        if compactTokenAt 0 input.2 = 1 then
          if compactTokenAt 1 input.2 < input.1.2 then
            [0, input.1.1 + compactTokenAt 1 input.2]
          else
            [1, compactTokenAt 1 input.2 - input.1.2]
        else input.2) :=
    Primrec.ite hisFree hfree htokens
  exact
    (Primrec.ite hisPair hbody htokens).of_eq fun input => by
      simp [compactFixitrConsumedTermHeader]

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

def compactFormulaFixitrEmission
    (task : CompactSyntaxTask)
    (captureAndConsumed : Nat × List Nat) : List Nat :=
  if task.1 = 0 then
    compactFixitrConsumedTermHeader
      (task.2.1, captureAndConsumed.1) captureAndConsumed.2
  else
    captureAndConsumed.2

theorem compactFormulaFixitrEmission_primrec :
    Primrec₂ compactFormulaFixitrEmission := by
  apply Primrec₂.mk
  let Input := CompactSyntaxTask × (Nat × List Nat)
  have htask : Primrec (fun input : Input => input.1) := Primrec.fst
  have hcapture : Primrec (fun input : Input => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have htokens : Primrec (fun input : Input => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hkind : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp htask
  have harity : Primrec (fun input : Input => input.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp htask)
  have harityCount : Primrec
      (fun input : Input => (input.1.2.1, input.2.1)) :=
    Primrec.pair harity hcapture
  have hterm : PrimrecPred (fun input : Input => input.1.1 = 0) :=
    Primrec.eq.comp hkind (Primrec.const 0)
  have htransformed : Primrec
      (fun input : Input =>
        compactFixitrConsumedTermHeader
          (input.1.2.1, input.2.1) input.2.2) :=
    compactFixitrConsumedTermHeader_primrec.comp harityCount htokens
  exact
    (Primrec.ite hterm
      htransformed htokens).of_eq fun input => by
        simp only [compactFormulaFixitrEmission]

def compactFormulaFixitrStep
    (captureCount : Nat) (state : CompactFormulaFixitrState) :
    CompactFormulaFixitrState :=
  let parserState := state.1
  let nextParserState := compactSyntaxParserStep parserState
  let consumed := consumedTokenPrefix parserState.1 nextParserState.1
  let emitted := compactFormulaFixitrEmission
    (compactSyntaxCurrentTask parserState) (captureCount, consumed)
  (nextParserState, state.2 ++ emitted)

theorem compactFormulaFixitrStep_primrec :
    Primrec₂ compactFormulaFixitrStep := by
  apply Primrec₂.mk
  let Input := Nat × CompactFormulaFixitrState
  have hcapture : Primrec (fun input : Input => input.1) := Primrec.fst
  have hparser : Primrec
      (fun input : Input => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hnext : Primrec
      (fun input : Input =>
        compactSyntaxParserStep input.2.1) :=
    compactSyntaxParserStep_primrec.comp hparser
  have holdTokens : Primrec
      (fun input : Input => input.2.1.1) :=
    Primrec.fst.comp hparser
  have hnextTokens : Primrec
      (fun input : Input =>
        (compactSyntaxParserStep input.2.1).1) :=
    Primrec.fst.comp hnext
  have hconsumed : Primrec
      (fun input : Input =>
        consumedTokenPrefix input.2.1.1
          (compactSyntaxParserStep input.2.1).1) :=
    consumedTokenPrefix_primrec.comp holdTokens hnextTokens
  have htask : Primrec
      (fun input : Input =>
        compactSyntaxCurrentTask input.2.1) :=
    compactSyntaxCurrentTask_primrec.comp hparser
  have hcaptureConsumed : Primrec
      (fun input : Input =>
        (input.1, consumedTokenPrefix input.2.1.1
          (compactSyntaxParserStep input.2.1).1)) :=
    Primrec.pair hcapture hconsumed
  have hemitted : Primrec
      (fun input : Input =>
        compactFormulaFixitrEmission
          (compactSyntaxCurrentTask input.2.1)
          (input.1, consumedTokenPrefix input.2.1.1
            (compactSyntaxParserStep input.2.1).1)) :=
    compactFormulaFixitrEmission_primrec.comp htask hcaptureConsumed
  have houtput : Primrec
      (fun input : Input => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hnextOutput : Primrec
      (fun input : Input =>
        input.2.2 ++ compactFormulaFixitrEmission
          (compactSyntaxCurrentTask input.2.1)
          (input.1, consumedTokenPrefix input.2.1.1
            (compactSyntaxParserStep input.2.1).1)) :=
    Primrec.list_append.comp houtput hemitted
  exact
    (Primrec.pair hnext hnextOutput).of_eq fun input => by rfl

def compactFormulaFixitrInitialState
    (binderArity : Nat) (tokens : List Nat) :
    CompactFormulaFixitrState :=
  (compactFormulaParserInitialState binderArity tokens, [])

theorem compactFormulaFixitrInitialState_primrec :
    Primrec₂ compactFormulaFixitrInitialState := by
  exact Primrec₂.pair.comp₂
    compactFormulaParserInitialState_primrec
    (Primrec₂.const [])

def compactFormulaFixitrRun
    (binderArity : Nat) (captureAndTokens : Nat × List Nat) :
    CompactFormulaFixitrState :=
  ((compactFormulaFixitrStep captureAndTokens.1)^[
      compactSyntaxRunFuelBound captureAndTokens.2])
    (compactFormulaFixitrInitialState binderArity captureAndTokens.2)

theorem compactFormulaFixitrRun_primrec :
    Primrec₂ compactFormulaFixitrRun := by
  apply Primrec₂.mk
  have hfuel : Primrec
      (fun input : Nat × (Nat × List Nat) =>
        compactSyntaxRunFuelBound input.2.2) :=
    compactSyntaxRunFuelBound_primrec.comp
      (Primrec.snd.comp Primrec.snd)
  have hinitial : Primrec
      (fun input : Nat × (Nat × List Nat) =>
        compactFormulaFixitrInitialState input.1 input.2.2) :=
    compactFormulaFixitrInitialState_primrec.comp
      Primrec.fst (Primrec.snd.comp Primrec.snd)
  have hstep : Primrec₂
      (fun (input : Nat × (Nat × List Nat))
          (state : CompactFormulaFixitrState) =>
        compactFormulaFixitrStep input.2.1 state) :=
    compactFormulaFixitrStep_primrec.comp₂
      (Primrec.fst.comp₂ (Primrec.snd.comp₂ Primrec₂.left))
      Primrec₂.right
  exact
    (Primrec.nat_iterate hfuel hinitial hstep).of_eq
      fun input => by rfl

def compactFormulaFixitrStateOutput
    (state : CompactFormulaFixitrState) :
    Option (List Nat × List Nat) :=
  state.1.2.2.bind fun result =>
    result.map fun suffix => (state.2, suffix)

theorem compactFormulaFixitrStateOutput_primrec :
    Primrec compactFormulaFixitrStateOutput := by
  have hstatus : Primrec
      (fun state : CompactFormulaFixitrState => state.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hinner : Primrec₂
      (fun (state : CompactFormulaFixitrState)
          (result : Option (List Nat)) =>
        result.map fun suffix => (state.2, suffix)) := by
    apply Primrec₂.mk
    let Input := CompactFormulaFixitrState × Option (List Nat)
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

def compactFormulaFixitrTokenTransform
    (binderArity : Nat) (captureAndTokens : Nat × List Nat) :
    Option (List Nat × List Nat) :=
  compactFormulaFixitrStateOutput
    (compactFormulaFixitrRun binderArity captureAndTokens)

theorem compactFormulaFixitrTokenTransform_primrec :
    Primrec₂ compactFormulaFixitrTokenTransform := by
  exact compactFormulaFixitrStateOutput_primrec.comp₂
    compactFormulaFixitrRun_primrec

/-! ## Exact task execution -/

theorem compactFormulaFixitr_iterate_trans
    (captureCount : Nat)
    {start middle finish : CompactFormulaFixitrState}
    {firstSteps secondSteps : Nat}
    (hfirst : ((compactFormulaFixitrStep captureCount)^[firstSteps])
      start = middle)
    (hsecond : ((compactFormulaFixitrStep captureCount)^[secondSteps])
      middle = finish) :
    ((compactFormulaFixitrStep captureCount)^[firstSteps + secondSteps])
      start = finish := by
  rw [Nat.add_comm, Function.iterate_add_apply, hfirst, hsecond]

theorem compactFormulaFixitrStep_of_transition
    {parserState nextParserState : CompactSyntaxParserState}
    {consumed : List Nat} (captureCount : Nat) (output : List Nat)
    (hparser : compactSyntaxParserStep parserState = nextParserState)
    (hconsumed : consumedTokenPrefix parserState.1 nextParserState.1 =
      consumed) :
    compactFormulaFixitrStep captureCount (parserState, output) =
      (nextParserState,
        output ++ compactFormulaFixitrEmission
          (compactSyntaxCurrentTask parserState) (captureCount, consumed)) := by
  simp [compactFormulaFixitrStep, hparser, hconsumed]

@[simp] theorem compactFormulaFixitrStep_done
    (captureCount : Nat) (tokens : List Nat)
    (tasks : List CompactSyntaxTask)
    (result : Option (List Nat)) (output : List Nat) :
    compactFormulaFixitrStep captureCount
        ((tokens, tasks, some result), output) =
      ((tokens, tasks, some result), output) := by
  refine (compactFormulaFixitrStep_of_transition captureCount output
    (consumed := [])
    (compactSyntaxParserStep_done tokens tasks result) ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactFormulaFixitrEmission,
      compactFixitrConsumedTermHeader, compactTokenAt]

theorem compactFormulaFixitrStep_iterate_done
    (captureCount fuel : Nat) (tokens : List Nat)
    (tasks : List CompactSyntaxTask)
    (result : Option (List Nat)) (output : List Nat) :
    ((compactFormulaFixitrStep captureCount)^[fuel])
        ((tokens, tasks, some result), output) =
      ((tokens, tasks, some result), output) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply,
        compactFormulaFixitrStep_done, ih]

@[simp] theorem compactFormulaFixitrStep_empty
    (captureCount : Nat) (tokens output : List Nat) :
    compactFormulaFixitrStep captureCount ((tokens, [], none), output) =
      ((tokens, [], some (some tokens)), output) := by
  refine (compactFormulaFixitrStep_of_transition captureCount output
    (consumed := []) (compactSyntaxParserStep_empty tokens) ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTask,
      compactFormulaFixitrEmission]

@[simp] theorem compactFormulaFixitrStep_repeat_zero
    (captureCount binderArity : Nat) (tokens output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFixitrStep captureCount
        ((tokens, compactRepeatTermTask binderArity 0 :: tasks, none),
          output) =
      ((tokens, tasks, none), output) := by
  have hparser : compactSyntaxParserStep
      (tokens, compactRepeatTermTask binderArity 0 :: tasks, none) =
      (tokens, tasks, none) := by
    simpa [compactSyntaxContinue] using
      (compactSyntaxParserStep_repeat_zero binderArity tokens tasks)
  refine (compactFormulaFixitrStep_of_transition captureCount output
    (consumed := []) hparser ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTask, compactRepeatTermTask,
      compactFormulaFixitrEmission]

@[simp] theorem compactFormulaFixitrStep_repeat_succ
    (captureCount binderArity count : Nat) (tokens output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFixitrStep captureCount
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
  refine (compactFormulaFixitrStep_of_transition captureCount output
    (consumed := []) hparser ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTask, compactRepeatTermTask,
      compactFormulaFixitrEmission]

@[simp] theorem compactFormulaFixitrStep_term_bvar
    {binderArity : Nat} (index : Fin binderArity)
    (captureCount : Nat) (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFixitrStep captureCount
        ((compactArithmeticTermTokens (#index) ++ suffix,
          compactTermTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none), output ++ [(0 : Nat), index.val]) := by
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
  refine (compactFormulaFixitrStep_of_transition captureCount output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactTermTask,
    compactFormulaFixitrEmission, compactFixitrConsumedTermHeader,
    compactTokenAt, htokens]

@[simp] theorem compactFormulaFixitrStep_term_fvar
    {binderArity : Nat} (freeIndex : Nat)
    (captureCount : Nat) (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFixitrStep captureCount
        ((compactArithmeticTermTokens
            (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) ++
              suffix,
          compactTermTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++ if freeIndex < captureCount then
          [0, binderArity + freeIndex]
        else
          [1, freeIndex - captureCount]) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticTermTokens
          (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) ++
            suffix,
        compactTermTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
    rw [compactSyntaxParserStep_term]
    exact compactTermTokenStep_fvar freeIndex suffix tasks
  refine (compactFormulaFixitrStep_of_transition captureCount output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTask, compactTermTask,
    compactFormulaFixitrEmission, compactFixitrConsumedTermHeader,
    compactArithmeticTermTokens, compactTokenAt]

@[simp] theorem compactFormulaFixitrStep_term_func
    {binderArity functionArity : Nat}
    (functionSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Func functionArity)
    (arguments : Fin functionArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (captureCount : Nat) (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFixitrStep captureCount
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
  refine (compactFormulaFixitrStep_of_transition captureCount output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactTermTask,
    compactFormulaFixitrEmission, compactFixitrConsumedTermHeader,
    compactTokenAt]

@[simp] theorem compactFormulaFixitrStep_formula_rel
    {binderArity relationArity : Nat}
    (relationSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Rel relationArity)
    (arguments : Fin relationArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (captureCount : Nat) (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFixitrStep captureCount
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
  refine (compactFormulaFixitrStep_of_transition captureCount output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaFixitrEmission, compactFixitrConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaFixitrStep_formula_nrel
    {binderArity relationArity : Nat}
    (relationSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Rel relationArity)
    (arguments : Fin relationArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (captureCount : Nat) (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFixitrStep captureCount
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
  refine (compactFormulaFixitrStep_of_transition captureCount output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaFixitrEmission, compactFixitrConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaFixitrStep_formula_verum
    {binderArity : Nat} (captureCount : Nat) (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFixitrStep captureCount
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
  refine (compactFormulaFixitrStep_of_transition captureCount output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaFixitrEmission, compactFixitrConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaFixitrStep_formula_falsum
    {binderArity : Nat} (captureCount : Nat) (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFixitrStep captureCount
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
  refine (compactFormulaFixitrStep_of_transition captureCount output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaFixitrEmission, compactFixitrConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaFixitrStep_formula_and
    {binderArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (captureCount : Nat) (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFixitrStep captureCount
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
  refine (compactFormulaFixitrStep_of_transition captureCount output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaFixitrEmission, compactFixitrConsumedTermHeader]

@[simp] theorem compactFormulaFixitrStep_formula_or
    {binderArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (captureCount : Nat) (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFixitrStep captureCount
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
  refine (compactFormulaFixitrStep_of_transition captureCount output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaFixitrEmission, compactFixitrConsumedTermHeader]

@[simp] theorem compactFormulaFixitrStep_formula_all
    {binderArity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (binderArity + 1))
    (captureCount : Nat) (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFixitrStep captureCount
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
  refine (compactFormulaFixitrStep_of_transition captureCount output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaFixitrEmission, compactFixitrConsumedTermHeader]

@[simp] theorem compactFormulaFixitrStep_formula_exs
    {binderArity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (binderArity + 1))
    (captureCount : Nat) (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaFixitrStep captureCount
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
  refine (compactFormulaFixitrStep_of_transition captureCount output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaFixitrEmission, compactFixitrConsumedTermHeader]

/-! ## Checked fixitr semantics -/

def compactFixitrBVarResult
    (baseArity captureCount depth : Nat)
    (index : Fin (baseArity + depth)) :
    LO.FirstOrder.ArithmeticSemiterm Nat
      ((baseArity + captureCount) + depth) :=
  #(⟨index.val, by omega⟩ :
    Fin ((baseArity + captureCount) + depth))

theorem compactFixitrBVarResult_eq_qpow
    (baseArity captureCount : Nat) :
    forall (depth : Nat) (index : Fin (baseArity + depth)),
      compactFixitrBVarResult baseArity captureCount depth index =
        ((Rew.fixitr (L := ℒₒᵣ) baseArity captureCount).qpow depth)
          (#index : LO.FirstOrder.ArithmeticSemiterm Nat
            (baseArity + depth)) := by
  intro depth
  induction depth with
  | zero =>
      intro index
      simp only [compactFixitrBVarResult, Rew.qpow_zero,
        Rew.fixitr_bvar]
      congr 1
  | succ depth ih =>
      intro index
      cases index using Fin.cases with
      | zero =>
          simp [compactFixitrBVarResult, Rew.qpow]
      | succ index =>
          rw [Rew.qpow_succ, Rew.q_bvar_succ, ← ih index]
          simp [compactFixitrBVarResult]

def compactFixitrFVarResult
    (baseArity captureCount depth freeIndex : Nat) :
    LO.FirstOrder.ArithmeticSemiterm Nat
      ((baseArity + captureCount) + depth) :=
  if h : freeIndex < captureCount then
    #(⟨baseArity + depth + freeIndex, by omega⟩ :
      Fin ((baseArity + captureCount) + depth))
  else
    &(freeIndex - captureCount)

theorem compactFixitrFVarResult_eq_qpow
    (baseArity captureCount : Nat) :
    forall (depth freeIndex : Nat),
      compactFixitrFVarResult baseArity captureCount depth freeIndex =
        ((Rew.fixitr (L := ℒₒᵣ) baseArity captureCount).qpow depth)
          (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat
            (baseArity + depth)) := by
  intro depth
  induction depth with
  | zero =>
      intro freeIndex
      rw [Rew.qpow_zero, Rew.fixitr_fvar]
      by_cases h : freeIndex < captureCount
      · simp [compactFixitrFVarResult, h]
      · simp [compactFixitrFVarResult, h]
  | succ depth ih =>
      intro freeIndex
      rw [Rew.qpow_succ, Rew.q_fvar, ← ih freeIndex]
      by_cases h : freeIndex < captureCount
      · simp only [compactFixitrFVarResult, h, dite_true,
          Rew.bShift_bvar]
        congr 1
        apply Fin.ext
        simp
        omega
      · simp [compactFixitrFVarResult, h]

theorem compactFixitrBVarHeader_tokens
    (baseArity captureCount depth : Nat)
    (index : Fin (baseArity + depth)) :
    [(0 : Nat), index.val] =
      compactArithmeticTermTokens
        (((Rew.fixitr (L := ℒₒᵣ) baseArity captureCount).qpow depth)
          (#index : LO.FirstOrder.ArithmeticSemiterm Nat
            (baseArity + depth))) := by
  rw [← compactFixitrBVarResult_eq_qpow]
  rfl

theorem compactFixitrFVarHeader_tokens
    (baseArity captureCount depth freeIndex : Nat) :
    (if freeIndex < captureCount then
        [0, baseArity + depth + freeIndex]
      else
        [1, freeIndex - captureCount]) =
      compactArithmeticTermTokens
        (((Rew.fixitr (L := ℒₒᵣ) baseArity captureCount).qpow depth)
          (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat
            (baseArity + depth))) := by
  rw [← compactFixitrFVarResult_eq_qpow]
  by_cases h : freeIndex < captureCount
  · simp [compactFixitrFVarResult, h, compactArithmeticTermTokens]
  · simp [compactFixitrFVarResult, h, compactArithmeticTermTokens]

def compactFixitrTermListTokens
    (baseArity captureCount depth : Nat)
    (terms : List
      (LO.FirstOrder.ArithmeticSemiterm Nat (baseArity + depth))) :
    List Nat :=
  (terms.map fun term =>
    compactArithmeticTermTokens
      (((Rew.fixitr (L := ℒₒᵣ) baseArity captureCount).qpow depth)
        term)).flatten

theorem compactFormulaFixitrTermTask_execute
    (baseArity captureCount depth : Nat)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat (baseArity + depth))
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    ((compactFormulaFixitrStep captureCount)^[compactTermTaskSteps term])
        ((compactArithmeticTermTokens term ++ suffix,
          compactTermTask (baseArity + depth) :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++ compactArithmeticTermTokens
          (((Rew.fixitr (L := ℒₒᵣ) baseArity captureCount).qpow depth)
            term)) := by
  induction term generalizing suffix tasks output with
  | bvar index =>
      have hstep := compactFormulaFixitrStep_term_bvar
        index captureCount suffix output tasks
      have hheader := compactFixitrBVarHeader_tokens
        baseArity captureCount depth index
      simpa only [compactTermTaskSteps, Function.iterate_one,
        hheader] using hstep
  | fvar freeIndex =>
      have hstep := compactFormulaFixitrStep_term_fvar
        (binderArity := baseArity + depth) freeIndex captureCount
        suffix output tasks
      simpa [compactTermTaskSteps, Function.iterate_one,
        compactFixitrFVarHeader_tokens] using hstep
  | @func functionArity functionSymbol arguments ih =>
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat (baseArity + depth)) :=
        List.ofFn arguments
      have hmembers : ∀ member ∈ terms,
          ∀ (memberSuffix : List Nat)
            (memberTasks : List CompactSyntaxTask)
            (memberOutput : List Nat),
          ((compactFormulaFixitrStep captureCount)^[
              compactTermTaskSteps member])
              ((compactArithmeticTermTokens member ++ memberSuffix,
                compactTermTask (baseArity + depth) :: memberTasks, none),
                memberOutput) =
            ((memberSuffix, memberTasks, none),
              memberOutput ++ compactArithmeticTermTokens
                (((Rew.fixitr (L := ℒₒᵣ) baseArity captureCount).qpow
                  depth) member)) := by
        intro member hmember memberSuffix memberTasks memberOutput
        rw [List.mem_ofFn] at hmember
        rcases hmember with ⟨index, rfl⟩
        exact ih index memberSuffix memberTasks memberOutput
      have hrepeat : ∀ (termList : List
          (LO.FirstOrder.ArithmeticSemiterm Nat (baseArity + depth))),
          (∀ member ∈ termList,
            ∀ (memberSuffix : List Nat)
              (memberTasks : List CompactSyntaxTask)
              (memberOutput : List Nat),
            ((compactFormulaFixitrStep captureCount)^[
                compactTermTaskSteps member])
                ((compactArithmeticTermTokens member ++ memberSuffix,
                  compactTermTask (baseArity + depth) :: memberTasks, none),
                  memberOutput) =
              ((memberSuffix, memberTasks, none),
                memberOutput ++ compactArithmeticTermTokens
                  (((Rew.fixitr (L := ℒₒᵣ) baseArity captureCount).qpow
                    depth) member))) ->
          ∀ (repeatSuffix : List Nat)
            (repeatTasks : List CompactSyntaxTask)
            (repeatOutput : List Nat),
          ((compactFormulaFixitrStep captureCount)^[
              compactTermListRepeatSteps termList])
              ((compactTermListTokens termList ++ repeatSuffix,
                compactRepeatTermTask (baseArity + depth) termList.length ::
                  repeatTasks, none), repeatOutput) =
            ((repeatSuffix, repeatTasks, none),
              repeatOutput ++
                compactFixitrTermListTokens
                  baseArity captureCount depth termList) := by
        intro termList hall repeatSuffix repeatTasks repeatOutput
        induction termList generalizing repeatOutput with
        | nil =>
            simp [compactTermListRepeatSteps, compactTermListTokens,
              compactFixitrTermListTokens, Function.iterate_one]
        | cons head tail ihTail =>
            have hhead := hall head (by simp)
            have htailMembers : ∀ member ∈ tail,
                ∀ (memberSuffix : List Nat)
                  (memberTasks : List CompactSyntaxTask)
                  (memberOutput : List Nat),
                ((compactFormulaFixitrStep captureCount)^[
                    compactTermTaskSteps member])
                    ((compactArithmeticTermTokens member ++ memberSuffix,
                      compactTermTask (baseArity + depth) :: memberTasks, none),
                      memberOutput) =
                  ((memberSuffix, memberTasks, none),
                    memberOutput ++ compactArithmeticTermTokens
                      (((Rew.fixitr (L := ℒₒᵣ) baseArity captureCount).qpow
                        depth) member)) := by
              intro member hmember
              exact hall member (by simp [hmember])
            have hone :
                ((compactFormulaFixitrStep captureCount)^[1])
                    ((compactTermListTokens (head :: tail) ++ repeatSuffix,
                      compactRepeatTermTask (baseArity + depth)
                        (head :: tail).length :: repeatTasks,
                      none), repeatOutput) =
                  ((compactArithmeticTermTokens head ++
                      (compactTermListTokens tail ++ repeatSuffix),
                    compactTermTask (baseArity + depth) ::
                      compactRepeatTermTask (baseArity + depth) tail.length ::
                        repeatTasks,
                    none), repeatOutput) := by
              simp [compactTermListTokens, Function.iterate_one,
                List.append_assoc]
            have hheadRun := hhead
              (compactTermListTokens tail ++ repeatSuffix)
              (compactRepeatTermTask (baseArity + depth) tail.length ::
                repeatTasks) repeatOutput
            have htailRun := ihTail htailMembers
              (repeatOutput ++ compactArithmeticTermTokens
                (((Rew.fixitr (L := ℒₒᵣ) baseArity captureCount).qpow
                  depth) head))
            have hfirst := compactFormulaFixitr_iterate_trans
              captureCount hone hheadRun
            have hallRun := compactFormulaFixitr_iterate_trans
              captureCount hfirst htailRun
            simpa [compactTermListRepeatSteps, compactTermListTokens,
              compactFixitrTermListTokens,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              List.append_assoc] using hallRun
      have hfirst :
          ((compactFormulaFixitrStep captureCount)^[1])
              ((compactArithmeticTermTokens
                    (Semiterm.func functionSymbol arguments) ++ suffix,
                compactTermTask (baseArity + depth) :: tasks, none), output) =
            ((compactTermListTokens terms ++ suffix,
              compactRepeatTermTask (baseArity + depth) terms.length :: tasks,
              none), output ++ [2, functionArity,
                Encodable.encode functionSymbol]) := by
        have htermsTokens : compactTermListTokens terms =
            (List.ofFn fun index =>
              compactArithmeticTermTokens (arguments index)).flatten :=
          compactTermListTokens_ofFn arguments
        rw [htermsTokens]
        simpa only [Function.iterate_one, terms, List.length_ofFn] using
          compactFormulaFixitrStep_term_func functionSymbol arguments
            captureCount suffix output tasks
      have hrepeatRun := hrepeat terms hmembers suffix tasks
        (output ++ [2, functionArity, Encodable.encode functionSymbol])
      have hrun := compactFormulaFixitr_iterate_trans
        captureCount hfirst hrepeatRun
      have hsteps :
          compactTermTaskSteps
              (Semiterm.func functionSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactTermTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have hfixedTokens :
          compactFixitrTermListTokens baseArity captureCount depth terms =
            (List.ofFn fun index => compactArithmeticTermTokens
              (((Rew.fixitr (L := ℒₒᵣ) baseArity captureCount).qpow
                depth) (arguments index))).flatten := by
        simp only [compactFixitrTermListTokens, terms, List.map_ofFn,
          Function.comp_def]
      rw [hfixedTokens] at hrun
      simpa [compactArithmeticTermTokens, compactFixitrTermListTokens,
        Rew.func, Function.comp_def, terms, List.append_assoc] using hrun

theorem compactFormulaFixitrTermList_execute
    (baseArity captureCount depth : Nat)
    (terms : List
      (LO.FirstOrder.ArithmeticSemiterm Nat (baseArity + depth)))
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    ((compactFormulaFixitrStep captureCount)^[
        compactTermListRepeatSteps terms])
        ((compactTermListTokens terms ++ suffix,
          compactRepeatTermTask (baseArity + depth) terms.length :: tasks,
          none), output) =
      ((suffix, tasks, none), output ++
        compactFixitrTermListTokens baseArity captureCount depth terms) := by
  induction terms generalizing output with
  | nil =>
      simp [compactTermListRepeatSteps, compactTermListTokens,
        compactFixitrTermListTokens, Function.iterate_one]
  | cons head tail ih =>
      have hone :
          ((compactFormulaFixitrStep captureCount)^[1])
              ((compactTermListTokens (head :: tail) ++ suffix,
                compactRepeatTermTask (baseArity + depth)
                  (head :: tail).length :: tasks,
                none), output) =
            ((compactArithmeticTermTokens head ++
                (compactTermListTokens tail ++ suffix),
              compactTermTask (baseArity + depth) ::
                compactRepeatTermTask (baseArity + depth) tail.length :: tasks,
              none), output) := by
        simp [compactTermListTokens, Function.iterate_one,
          List.append_assoc]
      have hhead := compactFormulaFixitrTermTask_execute
        baseArity captureCount depth head
        (compactTermListTokens tail ++ suffix)
        (compactRepeatTermTask (baseArity + depth) tail.length :: tasks) output
      have hfirst := compactFormulaFixitr_iterate_trans
        captureCount hone hhead
      have htail := ih
        (output ++ compactArithmeticTermTokens
          (((Rew.fixitr (L := ℒₒᵣ) baseArity captureCount).qpow depth)
            head))
      have hall := compactFormulaFixitr_iterate_trans
        captureCount hfirst htail
      simpa [compactTermListRepeatSteps, compactTermListTokens,
        compactFixitrTermListTokens,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using hall

def compactFixitrFormulaAlong
    (baseArity captureCount depth : Nat)
    {sourceArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat sourceArity)
    (harity : sourceArity = baseArity + depth) :
    LO.FirstOrder.ArithmeticSemiformula Nat
      ((baseArity + captureCount) + depth) := by
  subst sourceArity
  exact Rewriting.app
    ((Rew.fixitr (L := ℒₒᵣ) baseArity captureCount).qpow depth)
    formula

theorem compactFormulaFixitrFormulaTask_execute_along
    (baseArity captureCount : Nat)
    {sourceArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat sourceArity) :
    ∀ (depth : Nat)
      (harity : sourceArity = baseArity + depth)
      (suffix : List Nat) (tasks : List CompactSyntaxTask)
      (output : List Nat),
      ((compactFormulaFixitrStep captureCount)^[
          compactFormulaTaskSteps formula])
          ((compactArithmeticFormulaTokens formula ++ suffix,
            compactFormulaTask sourceArity :: tasks, none), output) =
        ((suffix, tasks, none), output ++ compactArithmeticFormulaTokens
          (compactFixitrFormulaAlong
            baseArity captureCount depth formula harity)) := by
  induction formula using Semiformula.rec' with
  | hverum =>
      intro depth harity suffix tasks output
      cases harity
      change
        ((compactFormulaFixitrStep captureCount)^[1])
            ((compactArithmeticFormulaTokens
                (⊤ : LO.FirstOrder.ArithmeticSemiformula Nat
                  (baseArity + depth)) ++ suffix,
              compactFormulaTask (baseArity + depth) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ [2])
      simpa only [Function.iterate_one] using
        (compactFormulaFixitrStep_formula_verum
          (binderArity := baseArity + depth) captureCount suffix output tasks)
  | hfalsum =>
      intro depth harity suffix tasks output
      cases harity
      change
        ((compactFormulaFixitrStep captureCount)^[1])
            ((compactArithmeticFormulaTokens
                (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat
                  (baseArity + depth)) ++ suffix,
              compactFormulaTask (baseArity + depth) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ [3])
      simpa only [Function.iterate_one] using
        (compactFormulaFixitrStep_formula_falsum
          (binderArity := baseArity + depth) captureCount suffix output tasks)
  | @hrel sourceArity relationArity relationSymbol arguments =>
      intro depth harity suffix tasks output
      cases harity
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat (baseArity + depth)) :=
        List.ofFn arguments
      have hfirst :
          ((compactFormulaFixitrStep captureCount)^[1])
              ((compactArithmeticFormulaTokens
                    (Semiformula.rel relationSymbol arguments) ++ suffix,
                compactFormulaTask (baseArity + depth) :: tasks, none),
                output) =
            ((compactTermListTokens terms ++ suffix,
              compactRepeatTermTask (baseArity + depth) terms.length :: tasks,
              none), output ++ [0, relationArity,
                Encodable.encode relationSymbol]) := by
        have htermsTokens : compactTermListTokens terms =
            (List.ofFn fun index =>
              compactArithmeticTermTokens (arguments index)).flatten :=
          compactTermListTokens_ofFn arguments
        rw [htermsTokens]
        simpa only [Function.iterate_one, terms, List.length_ofFn] using
          compactFormulaFixitrStep_formula_rel relationSymbol arguments
            captureCount suffix output tasks
      have hterms := compactFormulaFixitrTermList_execute
        baseArity captureCount depth terms suffix tasks
        (output ++ [0, relationArity, Encodable.encode relationSymbol])
      have hrun := compactFormulaFixitr_iterate_trans
        captureCount hfirst hterms
      have hsteps :
          compactFormulaTaskSteps
              (Semiformula.rel relationSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactFormulaTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have hfixedTokens :
          compactFixitrTermListTokens baseArity captureCount depth terms =
            (List.ofFn fun index => compactArithmeticTermTokens
              (((Rew.fixitr (L := ℒₒᵣ) baseArity captureCount).qpow
                depth) (arguments index))).flatten := by
        simp only [compactFixitrTermListTokens, terms, List.map_ofFn,
          Function.comp_def]
      rw [hfixedTokens] at hrun
      simpa [compactFixitrFormulaAlong, compactArithmeticFormulaTokens,
        Semiformula.rew_rel, Function.comp_def, terms,
        List.append_assoc] using hrun
  | @hnrel sourceArity relationArity relationSymbol arguments =>
      intro depth harity suffix tasks output
      cases harity
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat (baseArity + depth)) :=
        List.ofFn arguments
      have hfirst :
          ((compactFormulaFixitrStep captureCount)^[1])
              ((compactArithmeticFormulaTokens
                    (Semiformula.nrel relationSymbol arguments) ++ suffix,
                compactFormulaTask (baseArity + depth) :: tasks, none),
                output) =
            ((compactTermListTokens terms ++ suffix,
              compactRepeatTermTask (baseArity + depth) terms.length :: tasks,
              none), output ++ [1, relationArity,
                Encodable.encode relationSymbol]) := by
        have htermsTokens : compactTermListTokens terms =
            (List.ofFn fun index =>
              compactArithmeticTermTokens (arguments index)).flatten :=
          compactTermListTokens_ofFn arguments
        rw [htermsTokens]
        simpa only [Function.iterate_one, terms, List.length_ofFn] using
          compactFormulaFixitrStep_formula_nrel relationSymbol arguments
            captureCount suffix output tasks
      have hterms := compactFormulaFixitrTermList_execute
        baseArity captureCount depth terms suffix tasks
        (output ++ [1, relationArity, Encodable.encode relationSymbol])
      have hrun := compactFormulaFixitr_iterate_trans
        captureCount hfirst hterms
      have hsteps :
          compactFormulaTaskSteps
              (Semiformula.nrel relationSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactFormulaTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have hfixedTokens :
          compactFixitrTermListTokens baseArity captureCount depth terms =
            (List.ofFn fun index => compactArithmeticTermTokens
              (((Rew.fixitr (L := ℒₒᵣ) baseArity captureCount).qpow
                depth) (arguments index))).flatten := by
        simp only [compactFixitrTermListTokens, terms, List.map_ofFn,
          Function.comp_def]
      rw [hfixedTokens] at hrun
      simpa [compactFixitrFormulaAlong, compactArithmeticFormulaTokens,
        Semiformula.rew_nrel, Function.comp_def, terms,
        List.append_assoc] using hrun
  | @hand sourceArity left right ihLeft ihRight =>
      intro depth harity suffix tasks output
      cases harity
      have hone :
          ((compactFormulaFixitrStep captureCount)^[1])
              ((compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
                compactFormulaTask (baseArity + depth) :: tasks, none),
                output) =
            ((compactArithmeticFormulaTokens left ++
                (compactArithmeticFormulaTokens right ++ suffix),
              compactFormulaTask (baseArity + depth) ::
                compactFormulaTask (baseArity + depth) :: tasks, none),
              output ++ [4]) := by
        simpa [Function.iterate_one, List.append_assoc] using
          compactFormulaFixitrStep_formula_and left right captureCount
            suffix output tasks
      have hleft := ihLeft depth rfl
        (compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask (baseArity + depth) :: tasks) (output ++ [4])
      have hright := ihRight depth rfl suffix tasks
        (output ++ [4] ++ compactArithmeticFormulaTokens
          (compactFixitrFormulaAlong
            baseArity captureCount depth left rfl))
      have hfirst := compactFormulaFixitr_iterate_trans
        captureCount hone hleft
      have hrun := compactFormulaFixitr_iterate_trans
        captureCount hfirst hright
      change
        ((compactFormulaFixitrStep captureCount)^[
            compactFormulaTaskSteps (left ⋏ right)])
            ((compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
              compactFormulaTask (baseArity + depth) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ compactArithmeticFormulaTokens
            (compactFixitrFormulaAlong
              baseArity captureCount depth (left ⋏ right) rfl))
      simpa [compactFormulaTaskSteps, compactFixitrFormulaAlong,
        compactArithmeticFormulaTokens,
        LogicalConnective.HomClass.map_and, List.append_assoc] using hrun
  | @hor sourceArity left right ihLeft ihRight =>
      intro depth harity suffix tasks output
      cases harity
      have hone :
          ((compactFormulaFixitrStep captureCount)^[1])
              ((compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
                compactFormulaTask (baseArity + depth) :: tasks, none),
                output) =
            ((compactArithmeticFormulaTokens left ++
                (compactArithmeticFormulaTokens right ++ suffix),
              compactFormulaTask (baseArity + depth) ::
                compactFormulaTask (baseArity + depth) :: tasks, none),
              output ++ [5]) := by
        simpa [Function.iterate_one, List.append_assoc] using
          compactFormulaFixitrStep_formula_or left right captureCount
            suffix output tasks
      have hleft := ihLeft depth rfl
        (compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask (baseArity + depth) :: tasks) (output ++ [5])
      have hright := ihRight depth rfl suffix tasks
        (output ++ [5] ++ compactArithmeticFormulaTokens
          (compactFixitrFormulaAlong
            baseArity captureCount depth left rfl))
      have hfirst := compactFormulaFixitr_iterate_trans
        captureCount hone hleft
      have hrun := compactFormulaFixitr_iterate_trans
        captureCount hfirst hright
      change
        ((compactFormulaFixitrStep captureCount)^[
            compactFormulaTaskSteps (left ⋎ right)])
            ((compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
              compactFormulaTask (baseArity + depth) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ compactArithmeticFormulaTokens
            (compactFixitrFormulaAlong
              baseArity captureCount depth (left ⋎ right) rfl))
      simpa [compactFormulaTaskSteps, compactFixitrFormulaAlong,
        compactArithmeticFormulaTokens,
        LogicalConnective.HomClass.map_or, List.append_assoc] using hrun
  | @hall sourceArity body ih =>
      intro depth harity suffix tasks output
      cases harity
      have hone :
          ((compactFormulaFixitrStep captureCount)^[1])
              ((compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
                compactFormulaTask (baseArity + depth) :: tasks, none),
                output) =
            ((compactArithmeticFormulaTokens body ++ suffix,
              compactFormulaTask ((baseArity + depth) + 1) :: tasks, none),
              output ++ [6]) := by
        simpa [Function.iterate_one] using
          compactFormulaFixitrStep_formula_all body captureCount
            suffix output tasks
      have hbody := ih (depth + 1) rfl suffix tasks (output ++ [6])
      have hrun := compactFormulaFixitr_iterate_trans
        captureCount hone hbody
      change
        ((compactFormulaFixitrStep captureCount)^[
            compactFormulaTaskSteps (∀⁰ body)])
            ((compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
              compactFormulaTask (baseArity + depth) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ compactArithmeticFormulaTokens
            (compactFixitrFormulaAlong
              baseArity captureCount depth (∀⁰ body) rfl))
      simpa [compactFormulaTaskSteps, compactFixitrFormulaAlong,
        compactArithmeticFormulaTokens, Rewriting.app_all, Rew.qpow,
        List.append_assoc] using hrun
  | @hexs sourceArity body ih =>
      intro depth harity suffix tasks output
      cases harity
      have hone :
          ((compactFormulaFixitrStep captureCount)^[1])
              ((compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
                compactFormulaTask (baseArity + depth) :: tasks, none),
                output) =
            ((compactArithmeticFormulaTokens body ++ suffix,
              compactFormulaTask ((baseArity + depth) + 1) :: tasks, none),
              output ++ [7]) := by
        simpa [Function.iterate_one] using
          compactFormulaFixitrStep_formula_exs body captureCount
            suffix output tasks
      have hbody := ih (depth + 1) rfl suffix tasks (output ++ [7])
      have hrun := compactFormulaFixitr_iterate_trans
        captureCount hone hbody
      change
        ((compactFormulaFixitrStep captureCount)^[
            compactFormulaTaskSteps (∃⁰ body)])
            ((compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
              compactFormulaTask (baseArity + depth) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ compactArithmeticFormulaTokens
            (compactFixitrFormulaAlong
              baseArity captureCount depth (∃⁰ body) rfl))
      simpa [compactFormulaTaskSteps, compactFixitrFormulaAlong,
        compactArithmeticFormulaTokens, Rewriting.app_exs, Rew.qpow,
        List.append_assoc] using hrun

theorem compactFormulaFixitrFormulaTask_execute
    (baseArity captureCount : Nat)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat baseArity)
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    ((compactFormulaFixitrStep captureCount)^[
        compactFormulaTaskSteps formula])
        ((compactArithmeticFormulaTokens formula ++ suffix,
          compactFormulaTask baseArity :: tasks, none), output) =
      ((suffix, tasks, none), output ++ compactArithmeticFormulaTokens
        (Rewriting.app
          (Rew.fixitr (L := ℒₒᵣ) baseArity captureCount) formula)) := by
  simpa [compactFixitrFormulaAlong, Rew.qpow] using
    (compactFormulaFixitrFormulaTask_execute_along
      baseArity captureCount formula 0 rfl suffix tasks output)

theorem compactFormulaFixitrTokenTransform_canonical_append
    (baseArity captureCount : Nat)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat baseArity)
    (suffix : List Nat) :
    compactFormulaFixitrTokenTransform baseArity
        (captureCount, compactArithmeticFormulaTokens formula ++ suffix) =
      some (compactArithmeticFormulaTokens
        (Rewriting.app
          (Rew.fixitr (L := ℒₒᵣ) baseArity captureCount) formula),
        suffix) := by
  let tokens := compactArithmeticFormulaTokens formula ++ suffix
  let fixedTokens := compactArithmeticFormulaTokens
    (Rewriting.app
      (Rew.fixitr (L := ℒₒᵣ) baseArity captureCount) formula)
  let used := compactFormulaTaskSteps formula + 1
  have htask := compactFormulaFixitrFormulaTask_execute
    baseArity captureCount formula suffix [] []
  have hfinish :
      ((compactFormulaFixitrStep captureCount)^[used])
          ((tokens, [compactFormulaTask baseArity], none), []) =
        ((suffix, [], some (some suffix)), fixedTokens) := by
    apply compactFormulaFixitr_iterate_trans captureCount htask
    simp [Function.iterate_one, fixedTokens]
  have hformula := compactFormulaTaskSteps_le_tokenLength formula
  have hinputLength :
      (compactArithmeticFormulaTokens formula).length <= tokens.length := by
    simp [tokens]
  have hfuelLength := compactSyntaxRunFuelBound_length_add_one tokens
  have hused : used <= compactSyntaxRunFuelBound tokens := by
    omega
  obtain ⟨extra, hfuel⟩ := exists_add_of_le hused
  have hrun :
      ((compactFormulaFixitrStep captureCount)^[
          compactSyntaxRunFuelBound tokens])
          ((tokens, [compactFormulaTask baseArity], none), []) =
        ((suffix, [], some (some suffix)), fixedTokens) := by
    rw [hfuel]
    exact compactFormulaFixitr_iterate_trans captureCount hfinish
      (compactFormulaFixitrStep_iterate_done captureCount extra suffix []
        (some suffix) fixedTokens)
  simp [compactFormulaFixitrTokenTransform, compactFormulaFixitrRun,
    compactFormulaFixitrInitialState, compactFormulaParserInitialState,
    compactFormulaFixitrStateOutput, tokens, fixedTokens, hrun]

#print axioms compactFixitrConsumedTermHeader_primrec
#print axioms compactFormulaFixitrStep_primrec
#print axioms compactFormulaFixitrRun_primrec
#print axioms compactFormulaFixitrTokenTransform_primrec
#print axioms compactFixitrBVarResult_eq_qpow
#print axioms compactFixitrFVarResult_eq_qpow
#print axioms compactFormulaFixitrTermTask_execute
#print axioms compactFormulaFixitrTermList_execute
#print axioms compactFormulaFixitrFormulaTask_execute
#print axioms compactFormulaFixitrTokenTransform_canonical_append

end FoundationCompactNumericFormulaFixitr
