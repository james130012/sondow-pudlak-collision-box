import integration.FoundationCompactNumericFormulaConstructors

/-!
# Pure numeric formula one-variable substitution

The machine reuses the checked numeric syntax-task stack.  At source arity
`1 + depth`, the final bound-variable header is replaced by the complete token
list of a fixed arity-zero witness; earlier bound variables, free variables,
function headers, and formula headers are preserved.  The task stack supplies
the current source arity below quantifiers.  Runtime state contains only
naturals and lists of naturals; typed syntax is used solely in correctness.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericFormulaSubstitution

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser

abbrev CompactFormulaSubstitutionState :=
  CompactSyntaxParserState × List Nat

def compactSubstituteConsumedTermHeader
    (binderArity : Nat)
    (witnessAndConsumed : List Nat × List Nat) : List Nat :=
  let witness := witnessAndConsumed.1
  let consumed := witnessAndConsumed.2
  if consumed.length = 2 then
    if compactTokenAt 0 consumed = 0 then
      if compactTokenAt 1 consumed + 1 = binderArity then
        witness
      else
        consumed
    else
      consumed
  else
    consumed

theorem compactSubstituteConsumedTermHeader_primrec :
    Primrec₂ compactSubstituteConsumedTermHeader := by
  apply Primrec₂.mk
  let Input := Nat × (List Nat × List Nat)
  have harity : Primrec (fun input : Input => input.1) := Primrec.fst
  have hwitness : Primrec (fun input : Input => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hconsumed : Primrec (fun input : Input => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hlength : Primrec (fun input : Input => input.2.2.length) :=
    Primrec.list_length.comp hconsumed
  have hisPair : PrimrecPred
      (fun input : Input => input.2.2.length = 2) :=
    Primrec.eq.comp hlength (Primrec.const 2)
  have htag : Primrec
      (fun input : Input => compactTokenAt 0 input.2.2) :=
    compactTokenAt_primrec.comp (Primrec.const 0) hconsumed
  have hindex : Primrec
      (fun input : Input => compactTokenAt 1 input.2.2) :=
    compactTokenAt_primrec.comp (Primrec.const 1) hconsumed
  have hisBound : PrimrecPred
      (fun input : Input => compactTokenAt 0 input.2.2 = 0) :=
    Primrec.eq.comp htag (Primrec.const 0)
  have hisLast : PrimrecPred
      (fun input : Input => compactTokenAt 1 input.2.2 + 1 = input.1) :=
    Primrec.eq.comp (Primrec.succ.comp hindex) harity
  have hlast : Primrec
      (fun input : Input =>
        if compactTokenAt 1 input.2.2 + 1 = input.1 then
          input.2.1
        else
          input.2.2) :=
    Primrec.ite hisLast hwitness hconsumed
  have hbound : Primrec
      (fun input : Input =>
        if compactTokenAt 0 input.2.2 = 0 then
          if compactTokenAt 1 input.2.2 + 1 = input.1 then
            input.2.1
          else
            input.2.2
        else
          input.2.2) :=
    Primrec.ite hisBound hlast hconsumed
  exact
    (Primrec.ite hisPair hbound hconsumed).of_eq fun input => by
      simp [compactSubstituteConsumedTermHeader]

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

def compactFormulaSubstitutionEmission
    (task : CompactSyntaxTask)
    (witnessAndConsumed : List Nat × List Nat) : List Nat :=
  if task.1 = 0 then
    compactSubstituteConsumedTermHeader task.2.1 witnessAndConsumed
  else
    witnessAndConsumed.2

theorem compactFormulaSubstitutionEmission_primrec :
    Primrec₂ compactFormulaSubstitutionEmission := by
  apply Primrec₂.mk
  let Input := CompactSyntaxTask × (List Nat × List Nat)
  have htask : Primrec (fun input : Input => input.1) := Primrec.fst
  have hwitnessConsumed : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have hconsumed : Primrec (fun input : Input => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hkind : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp htask
  have harity : Primrec (fun input : Input => input.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp htask)
  have hterm : PrimrecPred (fun input : Input => input.1.1 = 0) :=
    Primrec.eq.comp hkind (Primrec.const 0)
  have htransformed : Primrec
      (fun input : Input =>
        compactSubstituteConsumedTermHeader input.1.2.1 input.2) :=
    compactSubstituteConsumedTermHeader_primrec.comp harity hwitnessConsumed
  exact
    (Primrec.ite hterm
      htransformed hconsumed).of_eq fun input => by
        simp only [compactFormulaSubstitutionEmission]

def compactFormulaSubstitutionStep
    (witness : List Nat) (state : CompactFormulaSubstitutionState) :
    CompactFormulaSubstitutionState :=
  let parserState := state.1
  let nextParserState := compactSyntaxParserStep parserState
  let consumed := consumedTokenPrefix parserState.1 nextParserState.1
  let emitted := compactFormulaSubstitutionEmission
    (compactSyntaxCurrentTask parserState) (witness, consumed)
  (nextParserState, state.2 ++ emitted)

theorem compactFormulaSubstitutionStep_primrec :
    Primrec₂ compactFormulaSubstitutionStep := by
  apply Primrec₂.mk
  let Input := List Nat × CompactFormulaSubstitutionState
  have hwitness : Primrec (fun input : Input => input.1) := Primrec.fst
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
  have hwitnessConsumed : Primrec
      (fun input : Input =>
        (input.1, consumedTokenPrefix input.2.1.1
          (compactSyntaxParserStep input.2.1).1)) :=
    Primrec.pair hwitness hconsumed
  have hemitted : Primrec
      (fun input : Input =>
        compactFormulaSubstitutionEmission
          (compactSyntaxCurrentTask input.2.1)
          (input.1, consumedTokenPrefix input.2.1.1
            (compactSyntaxParserStep input.2.1).1)) :=
    compactFormulaSubstitutionEmission_primrec.comp htask hwitnessConsumed
  have houtput : Primrec
      (fun input : Input => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hnextOutput : Primrec
      (fun input : Input =>
        input.2.2 ++ compactFormulaSubstitutionEmission
          (compactSyntaxCurrentTask input.2.1)
          (input.1, consumedTokenPrefix input.2.1.1
            (compactSyntaxParserStep input.2.1).1)) :=
    Primrec.list_append.comp houtput hemitted
  exact
    (Primrec.pair hnext hnextOutput).of_eq fun input => by rfl

def compactFormulaSubstitutionInitialState
    (binderArity : Nat) (tokens : List Nat) :
    CompactFormulaSubstitutionState :=
  (compactFormulaParserInitialState binderArity tokens, [])

theorem compactFormulaSubstitutionInitialState_primrec :
    Primrec₂ compactFormulaSubstitutionInitialState := by
  exact Primrec₂.pair.comp₂
    compactFormulaParserInitialState_primrec
    (Primrec₂.const [])

def compactFormulaSubstitutionRun
    (binderArity : Nat) (witnessAndTokens : List Nat × List Nat) :
    CompactFormulaSubstitutionState :=
  ((compactFormulaSubstitutionStep witnessAndTokens.1)^[
      compactSyntaxRunFuelBound witnessAndTokens.2])
    (compactFormulaSubstitutionInitialState binderArity witnessAndTokens.2)

theorem compactFormulaSubstitutionRun_primrec :
    Primrec₂ compactFormulaSubstitutionRun := by
  apply Primrec₂.mk
  have hfuel : Primrec
      (fun input : Nat × (List Nat × List Nat) =>
        compactSyntaxRunFuelBound input.2.2) :=
    compactSyntaxRunFuelBound_primrec.comp
      (Primrec.snd.comp Primrec.snd)
  have hinitial : Primrec
      (fun input : Nat × (List Nat × List Nat) =>
        compactFormulaSubstitutionInitialState input.1 input.2.2) :=
    compactFormulaSubstitutionInitialState_primrec.comp
      Primrec.fst (Primrec.snd.comp Primrec.snd)
  have hstep : Primrec₂
      (fun (input : Nat × (List Nat × List Nat))
          (state : CompactFormulaSubstitutionState) =>
        compactFormulaSubstitutionStep input.2.1 state) :=
    compactFormulaSubstitutionStep_primrec.comp₂
      (Primrec.fst.comp₂ (Primrec.snd.comp₂ Primrec₂.left))
      Primrec₂.right
  exact
    (Primrec.nat_iterate hfuel hinitial hstep).of_eq
      fun input => by rfl

def compactFormulaSubstitutionStateOutput
    (state : CompactFormulaSubstitutionState) :
    Option (List Nat × List Nat) :=
  state.1.2.2.bind fun result =>
    result.map fun suffix => (state.2, suffix)

theorem compactFormulaSubstitutionStateOutput_primrec :
    Primrec compactFormulaSubstitutionStateOutput := by
  have hstatus : Primrec
      (fun state : CompactFormulaSubstitutionState => state.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hinner : Primrec₂
      (fun (state : CompactFormulaSubstitutionState)
          (result : Option (List Nat)) =>
        result.map fun suffix => (state.2, suffix)) := by
    apply Primrec₂.mk
    let Input := CompactFormulaSubstitutionState × Option (List Nat)
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

def compactFormulaSubstitutionTokenTransform
    (binderArity : Nat) (witnessAndTokens : List Nat × List Nat) :
    Option (List Nat × List Nat) :=
  compactFormulaSubstitutionStateOutput
    (compactFormulaSubstitutionRun binderArity witnessAndTokens)

theorem compactFormulaSubstitutionTokenTransform_primrec :
    Primrec₂ compactFormulaSubstitutionTokenTransform := by
  exact compactFormulaSubstitutionStateOutput_primrec.comp₂
    compactFormulaSubstitutionRun_primrec

/-! ## Exact task execution -/

theorem compactFormulaSubstitution_iterate_trans
    (witness : List Nat)
    {start middle finish : CompactFormulaSubstitutionState}
    {firstSteps secondSteps : Nat}
    (hfirst : ((compactFormulaSubstitutionStep witness)^[firstSteps])
      start = middle)
    (hsecond : ((compactFormulaSubstitutionStep witness)^[secondSteps])
      middle = finish) :
    ((compactFormulaSubstitutionStep witness)^[firstSteps + secondSteps])
      start = finish := by
  rw [Nat.add_comm, Function.iterate_add_apply, hfirst, hsecond]

theorem compactFormulaSubstitutionStep_of_transition
    {parserState nextParserState : CompactSyntaxParserState}
    {consumed : List Nat} (witness output : List Nat)
    (hparser : compactSyntaxParserStep parserState = nextParserState)
    (hconsumed : consumedTokenPrefix parserState.1 nextParserState.1 =
      consumed) :
    compactFormulaSubstitutionStep witness (parserState, output) =
      (nextParserState,
        output ++ compactFormulaSubstitutionEmission
          (compactSyntaxCurrentTask parserState) (witness, consumed)) := by
  simp [compactFormulaSubstitutionStep, hparser, hconsumed]

@[simp] theorem compactFormulaSubstitutionStep_done
    (witness tokens : List Nat) (tasks : List CompactSyntaxTask)
    (result : Option (List Nat)) (output : List Nat) :
    compactFormulaSubstitutionStep witness
        ((tokens, tasks, some result), output) =
      ((tokens, tasks, some result), output) := by
  refine (compactFormulaSubstitutionStep_of_transition witness output
    (consumed := [])
    (compactSyntaxParserStep_done tokens tasks result) ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactFormulaSubstitutionEmission,
      compactSubstituteConsumedTermHeader, compactTokenAt]

theorem compactFormulaSubstitutionStep_iterate_done
    (witness : List Nat) (fuel : Nat) (tokens : List Nat)
    (tasks : List CompactSyntaxTask)
    (result : Option (List Nat)) (output : List Nat) :
    ((compactFormulaSubstitutionStep witness)^[fuel])
        ((tokens, tasks, some result), output) =
      ((tokens, tasks, some result), output) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply,
        compactFormulaSubstitutionStep_done, ih]

@[simp] theorem compactFormulaSubstitutionStep_empty
    (witness tokens output : List Nat) :
    compactFormulaSubstitutionStep witness ((tokens, [], none), output) =
      ((tokens, [], some (some tokens)), output) := by
  refine (compactFormulaSubstitutionStep_of_transition witness output
    (consumed := []) (compactSyntaxParserStep_empty tokens) ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTask,
      compactFormulaSubstitutionEmission]

@[simp] theorem compactFormulaSubstitutionStep_repeat_zero
    (witness : List Nat) (binderArity : Nat) (tokens output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaSubstitutionStep witness
        ((tokens, compactRepeatTermTask binderArity 0 :: tasks, none),
          output) =
      ((tokens, tasks, none), output) := by
  have hparser : compactSyntaxParserStep
      (tokens, compactRepeatTermTask binderArity 0 :: tasks, none) =
      (tokens, tasks, none) := by
    simpa [compactSyntaxContinue] using
      (compactSyntaxParserStep_repeat_zero binderArity tokens tasks)
  refine (compactFormulaSubstitutionStep_of_transition witness output
    (consumed := []) hparser ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTask, compactRepeatTermTask,
      compactFormulaSubstitutionEmission]

@[simp] theorem compactFormulaSubstitutionStep_repeat_succ
    (witness : List Nat) (binderArity count : Nat)
    (tokens output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaSubstitutionStep witness
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
  refine (compactFormulaSubstitutionStep_of_transition witness output
    (consumed := []) hparser ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTask, compactRepeatTermTask,
      compactFormulaSubstitutionEmission]

@[simp] theorem compactFormulaSubstitutionStep_term_bvar
    {binderArity : Nat} (index : Fin binderArity)
    (witness suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaSubstitutionStep witness
        ((compactArithmeticTermTokens (#index) ++ suffix,
          compactTermTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++
          if index.val + 1 = binderArity then witness
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
  refine (compactFormulaSubstitutionStep_of_transition witness output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactTermTask,
    compactFormulaSubstitutionEmission, compactSubstituteConsumedTermHeader,
    compactTokenAt, htokens]

@[simp] theorem compactFormulaSubstitutionStep_term_fvar
    {binderArity : Nat} (freeIndex : Nat)
    (witness suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaSubstitutionStep witness
        ((compactArithmeticTermTokens
            (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) ++
              suffix,
          compactTermTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++ [1, freeIndex]) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticTermTokens
          (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) ++
            suffix,
        compactTermTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
    rw [compactSyntaxParserStep_term]
    exact compactTermTokenStep_fvar freeIndex suffix tasks
  refine (compactFormulaSubstitutionStep_of_transition witness output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTask, compactTermTask,
    compactFormulaSubstitutionEmission, compactSubstituteConsumedTermHeader,
    compactArithmeticTermTokens, compactTokenAt]

@[simp] theorem compactFormulaSubstitutionStep_term_func
    {binderArity functionArity : Nat}
    (functionSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Func functionArity)
    (arguments : Fin functionArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (witness suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaSubstitutionStep witness
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
  refine (compactFormulaSubstitutionStep_of_transition witness output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactTermTask,
    compactFormulaSubstitutionEmission, compactSubstituteConsumedTermHeader,
    compactTokenAt]

@[simp] theorem compactFormulaSubstitutionStep_formula_rel
    {binderArity relationArity : Nat}
    (relationSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Rel relationArity)
    (arguments : Fin relationArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (witness suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaSubstitutionStep witness
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
  refine (compactFormulaSubstitutionStep_of_transition witness output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaSubstitutionEmission, compactSubstituteConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaSubstitutionStep_formula_nrel
    {binderArity relationArity : Nat}
    (relationSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Rel relationArity)
    (arguments : Fin relationArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (witness suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaSubstitutionStep witness
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
  refine (compactFormulaSubstitutionStep_of_transition witness output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaSubstitutionEmission, compactSubstituteConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaSubstitutionStep_formula_verum
    {binderArity : Nat} (witness suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaSubstitutionStep witness
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
  refine (compactFormulaSubstitutionStep_of_transition witness output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaSubstitutionEmission, compactSubstituteConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaSubstitutionStep_formula_falsum
    {binderArity : Nat} (witness suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaSubstitutionStep witness
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
  refine (compactFormulaSubstitutionStep_of_transition witness output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaSubstitutionEmission, compactSubstituteConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaSubstitutionStep_formula_and
    {binderArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (witness suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaSubstitutionStep witness
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
  refine (compactFormulaSubstitutionStep_of_transition witness output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaSubstitutionEmission, compactSubstituteConsumedTermHeader]

@[simp] theorem compactFormulaSubstitutionStep_formula_or
    {binderArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (witness suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaSubstitutionStep witness
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
  refine (compactFormulaSubstitutionStep_of_transition witness output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaSubstitutionEmission, compactSubstituteConsumedTermHeader]

@[simp] theorem compactFormulaSubstitutionStep_formula_all
    {binderArity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (binderArity + 1))
    (witness suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaSubstitutionStep witness
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
  refine (compactFormulaSubstitutionStep_of_transition witness output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaSubstitutionEmission, compactSubstituteConsumedTermHeader]

@[simp] theorem compactFormulaSubstitutionStep_formula_exs
    {binderArity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (binderArity + 1))
    (witness suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaSubstitutionStep witness
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
  refine (compactFormulaSubstitutionStep_of_transition witness output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTask, compactFormulaTask,
    compactFormulaSubstitutionEmission, compactSubstituteConsumedTermHeader]

/-! ## Checked substitution semantics -/

def compactLiftClosedTerm (targetArity : Nat) :
    LO.FirstOrder.ArithmeticSemiterm Nat 0 ->
      LO.FirstOrder.ArithmeticSemiterm Nat targetArity
  | #index => Fin.elim0 index
  | &freeIndex => &freeIndex
  | Semiterm.func functionSymbol arguments =>
      Semiterm.func functionSymbol fun index =>
        compactLiftClosedTerm targetArity (arguments index)

@[simp] theorem compactLiftClosedTerm_zero
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    compactLiftClosedTerm 0 term = term := by
  induction term with
  | bvar index => exact Fin.elim0 index
  | fvar freeIndex => rfl
  | func functionSymbol arguments ih =>
      simp only [compactLiftClosedTerm]
      congr
      funext index
      exact ih index

@[simp] theorem compactLiftClosedTerm_bShift
    (targetArity : Nat)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    Rew.bShift (compactLiftClosedTerm targetArity term) =
      compactLiftClosedTerm (targetArity + 1) term := by
  induction term with
  | bvar index => exact Fin.elim0 index
  | fvar freeIndex => rfl
  | func functionSymbol arguments ih =>
      simp only [compactLiftClosedTerm, Rew.func]
      congr 1
      funext index
      exact ih index

@[simp] theorem compactLiftClosedTerm_tokens
    (targetArity : Nat)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    compactArithmeticTermTokens (compactLiftClosedTerm targetArity term) =
      compactArithmeticTermTokens term := by
  induction term with
  | bvar index => exact Fin.elim0 index
  | fvar freeIndex => rfl
  | func functionSymbol arguments ih =>
      simp only [compactLiftClosedTerm, compactArithmeticTermTokens]
      simp_rw [ih]

def compactSubstitutionBVarResult
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat) (index : Fin (1 + depth)) :
    LO.FirstOrder.ArithmeticSemiterm Nat (0 + depth) :=
  if hlast : index.val + 1 = 1 + depth then
    compactLiftClosedTerm (0 + depth) witness
  else
    #(⟨index.val, by omega⟩ : Fin (0 + depth))

theorem compactSubstitutionBVarResult_eq_qpow
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    forall (depth : Nat) (index : Fin (1 + depth)),
      compactSubstitutionBVarResult witness depth index =
        ((Rew.subst ![witness]).qpow depth)
          (#index : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth)) := by
  intro depth
  induction depth with
  | zero =>
      intro index
      have hindex : index = 0 := Fin.eq_zero index
      subst index
      simp [compactSubstitutionBVarResult, Rew.qpow]
  | succ depth ih =>
      intro index
      cases index using Fin.cases with
      | zero =>
          simp [compactSubstitutionBVarResult, Rew.qpow]
      | succ index =>
          by_cases hlast : index.val + 1 = 1 + depth
          · rw [Rew.qpow_succ, Rew.q_bvar_succ, ← ih index]
            simp [compactSubstitutionBVarResult, hlast, Nat.add_assoc]
            rfl
          · rw [Rew.qpow_succ, Rew.q_bvar_succ, ← ih index]
            have hcurrent : ¬(index.val + 1 + 1 = 1 + (depth + 1)) := by
              omega
            simp [compactSubstitutionBVarResult, hlast, hcurrent]

theorem compactSubstitutionBVarHeader_tokens
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat) (index : Fin (1 + depth)) :
    (if index.val + 1 = 1 + depth then
        compactArithmeticTermTokens witness
      else
        [(0 : Nat), index.val]) =
      compactArithmeticTermTokens
        (((Rew.subst ![witness]).qpow depth)
          (#index : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth))) := by
  rw [← compactSubstitutionBVarResult_eq_qpow]
  by_cases hlast : index.val + 1 = 1 + depth
  · simp [compactSubstitutionBVarResult, hlast]
  · simp [compactSubstitutionBVarResult, hlast,
      compactArithmeticTermTokens]

theorem compactSubstitutionFVar_eq_qpow
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    forall (depth freeIndex : Nat),
      ((Rew.subst ![witness]).qpow depth)
          (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth)) =
        (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat (0 + depth)) := by
  intro depth
  induction depth with
  | zero =>
      intro freeIndex
      simp [Rew.qpow]
  | succ depth ih =>
      intro freeIndex
      simp [Rew.qpow, ih]

def compactSubstitutedTermListTokens
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat)
    (terms : List
      (LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth))) : List Nat :=
  (terms.map fun term =>
    compactArithmeticTermTokens
      (((Rew.subst ![witness]).qpow depth) term)).flatten

theorem compactFormulaSubstitutionTermTask_execute
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth))
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    ((compactFormulaSubstitutionStep
        (compactArithmeticTermTokens witness))^[compactTermTaskSteps term])
        ((compactArithmeticTermTokens term ++ suffix,
          compactTermTask (1 + depth) :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++ compactArithmeticTermTokens
          (((Rew.subst ![witness]).qpow depth) term)) := by
  induction term generalizing suffix tasks output with
  | bvar index =>
      have hstep := compactFormulaSubstitutionStep_term_bvar
        index (compactArithmeticTermTokens witness) suffix output tasks
      simpa only [compactTermTaskSteps, Function.iterate_one,
        compactSubstitutionBVarHeader_tokens] using hstep
  | fvar freeIndex =>
      have hstep := compactFormulaSubstitutionStep_term_fvar
        (binderArity := 1 + depth) freeIndex
        (compactArithmeticTermTokens witness) suffix output tasks
      simpa [compactTermTaskSteps, Function.iterate_one,
        compactArithmeticTermTokens,
        compactSubstitutionFVar_eq_qpow] using hstep
  | @func functionArity functionSymbol arguments ih =>
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth)) :=
        List.ofFn arguments
      have hmembers : ∀ member ∈ terms,
          ∀ (memberSuffix : List Nat)
            (memberTasks : List CompactSyntaxTask)
            (memberOutput : List Nat),
          ((compactFormulaSubstitutionStep
              (compactArithmeticTermTokens witness))^[
                compactTermTaskSteps member])
              ((compactArithmeticTermTokens member ++ memberSuffix,
                compactTermTask (1 + depth) :: memberTasks, none),
                memberOutput) =
            ((memberSuffix, memberTasks, none),
              memberOutput ++ compactArithmeticTermTokens
                (((Rew.subst ![witness]).qpow depth) member)) := by
        intro member hmember memberSuffix memberTasks memberOutput
        rw [List.mem_ofFn] at hmember
        rcases hmember with ⟨index, rfl⟩
        exact ih index memberSuffix memberTasks memberOutput
      have hrepeat : ∀ (termList : List
          (LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth))),
          (∀ member ∈ termList,
            ∀ (memberSuffix : List Nat)
              (memberTasks : List CompactSyntaxTask)
              (memberOutput : List Nat),
            ((compactFormulaSubstitutionStep
                (compactArithmeticTermTokens witness))^[
                  compactTermTaskSteps member])
                ((compactArithmeticTermTokens member ++ memberSuffix,
                  compactTermTask (1 + depth) :: memberTasks, none),
                  memberOutput) =
              ((memberSuffix, memberTasks, none),
                memberOutput ++ compactArithmeticTermTokens
                  (((Rew.subst ![witness]).qpow depth) member))) ->
          ∀ (repeatSuffix : List Nat)
            (repeatTasks : List CompactSyntaxTask)
            (repeatOutput : List Nat),
          ((compactFormulaSubstitutionStep
              (compactArithmeticTermTokens witness))^[
                compactTermListRepeatSteps termList])
              ((compactTermListTokens termList ++ repeatSuffix,
                compactRepeatTermTask (1 + depth) termList.length ::
                  repeatTasks, none), repeatOutput) =
            ((repeatSuffix, repeatTasks, none),
              repeatOutput ++
                compactSubstitutedTermListTokens witness depth termList) := by
        intro termList hall repeatSuffix repeatTasks repeatOutput
        induction termList generalizing repeatOutput with
        | nil =>
            simp [compactTermListRepeatSteps, compactTermListTokens,
              compactSubstitutedTermListTokens, Function.iterate_one]
        | cons head tail ihTail =>
            have hhead := hall head (by simp)
            have htailMembers : ∀ member ∈ tail,
                ∀ (memberSuffix : List Nat)
                  (memberTasks : List CompactSyntaxTask)
                  (memberOutput : List Nat),
                ((compactFormulaSubstitutionStep
                    (compactArithmeticTermTokens witness))^[
                      compactTermTaskSteps member])
                    ((compactArithmeticTermTokens member ++ memberSuffix,
                      compactTermTask (1 + depth) :: memberTasks, none),
                      memberOutput) =
                  ((memberSuffix, memberTasks, none),
                    memberOutput ++ compactArithmeticTermTokens
                      (((Rew.subst ![witness]).qpow depth) member)) := by
              intro member hmember
              exact hall member (by simp [hmember])
            have hone :
                ((compactFormulaSubstitutionStep
                    (compactArithmeticTermTokens witness))^[1])
                    ((compactTermListTokens (head :: tail) ++ repeatSuffix,
                      compactRepeatTermTask (1 + depth)
                        (head :: tail).length :: repeatTasks,
                      none), repeatOutput) =
                  ((compactArithmeticTermTokens head ++
                      (compactTermListTokens tail ++ repeatSuffix),
                    compactTermTask (1 + depth) ::
                      compactRepeatTermTask (1 + depth) tail.length ::
                        repeatTasks,
                    none), repeatOutput) := by
              simp [compactTermListTokens, Function.iterate_one,
                List.append_assoc]
            have hheadRun := hhead
              (compactTermListTokens tail ++ repeatSuffix)
              (compactRepeatTermTask (1 + depth) tail.length :: repeatTasks)
              repeatOutput
            have htailRun := ihTail htailMembers
              (repeatOutput ++ compactArithmeticTermTokens
                (((Rew.subst ![witness]).qpow depth) head))
            have hfirst := compactFormulaSubstitution_iterate_trans
              (compactArithmeticTermTokens witness) hone hheadRun
            have hallRun := compactFormulaSubstitution_iterate_trans
              (compactArithmeticTermTokens witness) hfirst htailRun
            simpa [compactTermListRepeatSteps, compactTermListTokens,
              compactSubstitutedTermListTokens,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              List.append_assoc] using hallRun
      have hfirst :
          ((compactFormulaSubstitutionStep
              (compactArithmeticTermTokens witness))^[1])
              ((compactArithmeticTermTokens
                    (Semiterm.func functionSymbol arguments) ++ suffix,
                compactTermTask (1 + depth) :: tasks, none), output) =
            ((compactTermListTokens terms ++ suffix,
              compactRepeatTermTask (1 + depth) terms.length :: tasks, none),
              output ++ [2, functionArity,
                Encodable.encode functionSymbol]) := by
        have htermsTokens : compactTermListTokens terms =
            (List.ofFn fun index =>
              compactArithmeticTermTokens (arguments index)).flatten :=
          compactTermListTokens_ofFn arguments
        rw [htermsTokens]
        simpa only [Function.iterate_one, terms, List.length_ofFn] using
          compactFormulaSubstitutionStep_term_func functionSymbol arguments
            (compactArithmeticTermTokens witness) suffix output tasks
      have hrepeatRun := hrepeat terms hmembers suffix tasks
        (output ++ [2, functionArity, Encodable.encode functionSymbol])
      have hrun := compactFormulaSubstitution_iterate_trans
        (compactArithmeticTermTokens witness) hfirst hrepeatRun
      have hsteps :
          compactTermTaskSteps
              (Semiterm.func functionSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactTermTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have hsubstitutedTokens :
          compactSubstitutedTermListTokens witness depth terms =
            (List.ofFn fun index => compactArithmeticTermTokens
              (((Rew.subst ![witness]).qpow depth)
                (arguments index))).flatten := by
        simp only [compactSubstitutedTermListTokens, terms, List.map_ofFn,
          Function.comp_def]
      rw [hsubstitutedTokens] at hrun
      simpa [compactArithmeticTermTokens,
        compactSubstitutedTermListTokens, Rew.func,
        Function.comp_def, terms, List.append_assoc] using hrun

theorem compactFormulaSubstitutionTermList_execute
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat)
    (terms : List
      (LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth)))
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    ((compactFormulaSubstitutionStep
        (compactArithmeticTermTokens witness))^[
          compactTermListRepeatSteps terms])
        ((compactTermListTokens terms ++ suffix,
          compactRepeatTermTask (1 + depth) terms.length :: tasks, none),
          output) =
      ((suffix, tasks, none),
        output ++ compactSubstitutedTermListTokens witness depth terms) := by
  induction terms generalizing output with
  | nil =>
      simp [compactTermListRepeatSteps, compactTermListTokens,
        compactSubstitutedTermListTokens, Function.iterate_one]
  | cons head tail ih =>
      have hone :
          ((compactFormulaSubstitutionStep
              (compactArithmeticTermTokens witness))^[1])
              ((compactTermListTokens (head :: tail) ++ suffix,
                compactRepeatTermTask (1 + depth)
                  (head :: tail).length :: tasks,
                none), output) =
            ((compactArithmeticTermTokens head ++
                (compactTermListTokens tail ++ suffix),
              compactTermTask (1 + depth) ::
                compactRepeatTermTask (1 + depth) tail.length :: tasks,
              none), output) := by
        simp [compactTermListTokens, Function.iterate_one,
          List.append_assoc]
      have hhead := compactFormulaSubstitutionTermTask_execute
        witness depth head (compactTermListTokens tail ++ suffix)
        (compactRepeatTermTask (1 + depth) tail.length :: tasks) output
      have hfirst := compactFormulaSubstitution_iterate_trans
        (compactArithmeticTermTokens witness) hone hhead
      have htail := ih
        (output ++ compactArithmeticTermTokens
          (((Rew.subst ![witness]).qpow depth) head))
      have hall := compactFormulaSubstitution_iterate_trans
        (compactArithmeticTermTokens witness) hfirst htail
      simpa [compactTermListRepeatSteps, compactTermListTokens,
        compactSubstitutedTermListTokens,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using hall

def compactSubstituteFormulaAlong
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (depth : Nat)
    {sourceArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat sourceArity)
    (harity : sourceArity = 1 + depth) :
    LO.FirstOrder.ArithmeticSemiformula Nat (0 + depth) := by
  subst sourceArity
  exact Rewriting.app ((Rew.subst ![witness]).qpow depth) formula

theorem compactFormulaSubstitutionFormulaTask_execute_along
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    {sourceArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat sourceArity) :
    ∀ (depth : Nat)
      (harity : sourceArity = 1 + depth)
      (suffix : List Nat) (tasks : List CompactSyntaxTask)
      (output : List Nat),
      ((compactFormulaSubstitutionStep
          (compactArithmeticTermTokens witness))^[
            compactFormulaTaskSteps formula])
          ((compactArithmeticFormulaTokens formula ++ suffix,
            compactFormulaTask sourceArity :: tasks, none), output) =
        ((suffix, tasks, none),
          output ++ compactArithmeticFormulaTokens
            (compactSubstituteFormulaAlong witness depth formula harity)) := by
  induction formula using Semiformula.rec' with
  | hverum =>
      intro depth harity suffix tasks output
      cases harity
      change
        ((compactFormulaSubstitutionStep
            (compactArithmeticTermTokens witness))^[1])
            ((compactArithmeticFormulaTokens
                (⊤ : LO.FirstOrder.ArithmeticSemiformula Nat
                  (1 + depth)) ++ suffix,
              compactFormulaTask (1 + depth) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ [2])
      simpa only [Function.iterate_one] using
        (compactFormulaSubstitutionStep_formula_verum
          (binderArity := 1 + depth) (compactArithmeticTermTokens witness)
          suffix output tasks)
  | hfalsum =>
      intro depth harity suffix tasks output
      cases harity
      change
        ((compactFormulaSubstitutionStep
            (compactArithmeticTermTokens witness))^[1])
            ((compactArithmeticFormulaTokens
                (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat
                  (1 + depth)) ++ suffix,
              compactFormulaTask (1 + depth) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ [3])
      simpa only [Function.iterate_one] using
        (compactFormulaSubstitutionStep_formula_falsum
          (binderArity := 1 + depth) (compactArithmeticTermTokens witness)
          suffix output tasks)
  | @hrel sourceArity relationArity relationSymbol arguments =>
      intro depth harity suffix tasks output
      cases harity
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth)) :=
        List.ofFn arguments
      have hfirst :
          ((compactFormulaSubstitutionStep
              (compactArithmeticTermTokens witness))^[1])
              ((compactArithmeticFormulaTokens
                    (Semiformula.rel relationSymbol arguments) ++ suffix,
                compactFormulaTask (1 + depth) :: tasks, none), output) =
            ((compactTermListTokens terms ++ suffix,
              compactRepeatTermTask (1 + depth) terms.length :: tasks, none),
              output ++ [0, relationArity,
                Encodable.encode relationSymbol]) := by
        have htermsTokens : compactTermListTokens terms =
            (List.ofFn fun index =>
              compactArithmeticTermTokens (arguments index)).flatten :=
          compactTermListTokens_ofFn arguments
        rw [htermsTokens]
        simpa only [Function.iterate_one, terms, List.length_ofFn] using
          compactFormulaSubstitutionStep_formula_rel relationSymbol arguments
            (compactArithmeticTermTokens witness) suffix output tasks
      have hterms := compactFormulaSubstitutionTermList_execute
        witness depth terms suffix tasks
        (output ++ [0, relationArity, Encodable.encode relationSymbol])
      have hrun := compactFormulaSubstitution_iterate_trans
        (compactArithmeticTermTokens witness) hfirst hterms
      have hsteps :
          compactFormulaTaskSteps
              (Semiformula.rel relationSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactFormulaTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have hsubstitutedTokens :
          compactSubstitutedTermListTokens witness depth terms =
            (List.ofFn fun index => compactArithmeticTermTokens
              (((Rew.subst ![witness]).qpow depth)
                (arguments index))).flatten := by
        simp only [compactSubstitutedTermListTokens, terms, List.map_ofFn,
          Function.comp_def]
      rw [hsubstitutedTokens] at hrun
      simpa [compactSubstituteFormulaAlong,
        compactArithmeticFormulaTokens, Semiformula.rew_rel,
        Function.comp_def, terms, List.append_assoc] using hrun
  | @hnrel sourceArity relationArity relationSymbol arguments =>
      intro depth harity suffix tasks output
      cases harity
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat (1 + depth)) :=
        List.ofFn arguments
      have hfirst :
          ((compactFormulaSubstitutionStep
              (compactArithmeticTermTokens witness))^[1])
              ((compactArithmeticFormulaTokens
                    (Semiformula.nrel relationSymbol arguments) ++ suffix,
                compactFormulaTask (1 + depth) :: tasks, none), output) =
            ((compactTermListTokens terms ++ suffix,
              compactRepeatTermTask (1 + depth) terms.length :: tasks, none),
              output ++ [1, relationArity,
                Encodable.encode relationSymbol]) := by
        have htermsTokens : compactTermListTokens terms =
            (List.ofFn fun index =>
              compactArithmeticTermTokens (arguments index)).flatten :=
          compactTermListTokens_ofFn arguments
        rw [htermsTokens]
        simpa only [Function.iterate_one, terms, List.length_ofFn] using
          compactFormulaSubstitutionStep_formula_nrel relationSymbol arguments
            (compactArithmeticTermTokens witness) suffix output tasks
      have hterms := compactFormulaSubstitutionTermList_execute
        witness depth terms suffix tasks
        (output ++ [1, relationArity, Encodable.encode relationSymbol])
      have hrun := compactFormulaSubstitution_iterate_trans
        (compactArithmeticTermTokens witness) hfirst hterms
      have hsteps :
          compactFormulaTaskSteps
              (Semiformula.nrel relationSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactFormulaTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have hsubstitutedTokens :
          compactSubstitutedTermListTokens witness depth terms =
            (List.ofFn fun index => compactArithmeticTermTokens
              (((Rew.subst ![witness]).qpow depth)
                (arguments index))).flatten := by
        simp only [compactSubstitutedTermListTokens, terms, List.map_ofFn,
          Function.comp_def]
      rw [hsubstitutedTokens] at hrun
      simpa [compactSubstituteFormulaAlong,
        compactArithmeticFormulaTokens, Semiformula.rew_nrel,
        Function.comp_def, terms, List.append_assoc] using hrun
  | @hand sourceArity left right ihLeft ihRight =>
      intro depth harity suffix tasks output
      cases harity
      have hone :
          ((compactFormulaSubstitutionStep
              (compactArithmeticTermTokens witness))^[1])
              ((compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
                compactFormulaTask (1 + depth) :: tasks, none), output) =
            ((compactArithmeticFormulaTokens left ++
                (compactArithmeticFormulaTokens right ++ suffix),
              compactFormulaTask (1 + depth) ::
                compactFormulaTask (1 + depth) :: tasks, none),
              output ++ [4]) := by
        simpa [Function.iterate_one, List.append_assoc] using
          compactFormulaSubstitutionStep_formula_and left right
            (compactArithmeticTermTokens witness) suffix output tasks
      have hleft := ihLeft depth rfl
        (compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask (1 + depth) :: tasks) (output ++ [4])
      have hright := ihRight depth rfl suffix tasks
        (output ++ [4] ++ compactArithmeticFormulaTokens
          (compactSubstituteFormulaAlong witness depth left rfl))
      have hfirst := compactFormulaSubstitution_iterate_trans
        (compactArithmeticTermTokens witness) hone hleft
      have hrun := compactFormulaSubstitution_iterate_trans
        (compactArithmeticTermTokens witness) hfirst hright
      change
        ((compactFormulaSubstitutionStep
            (compactArithmeticTermTokens witness))^[
              compactFormulaTaskSteps (left ⋏ right)])
            ((compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
              compactFormulaTask (1 + depth) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ compactArithmeticFormulaTokens
            (compactSubstituteFormulaAlong witness depth (left ⋏ right) rfl))
      simpa [compactFormulaTaskSteps, compactSubstituteFormulaAlong,
        compactArithmeticFormulaTokens,
        LogicalConnective.HomClass.map_and, List.append_assoc] using hrun
  | @hor sourceArity left right ihLeft ihRight =>
      intro depth harity suffix tasks output
      cases harity
      have hone :
          ((compactFormulaSubstitutionStep
              (compactArithmeticTermTokens witness))^[1])
              ((compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
                compactFormulaTask (1 + depth) :: tasks, none), output) =
            ((compactArithmeticFormulaTokens left ++
                (compactArithmeticFormulaTokens right ++ suffix),
              compactFormulaTask (1 + depth) ::
                compactFormulaTask (1 + depth) :: tasks, none),
              output ++ [5]) := by
        simpa [Function.iterate_one, List.append_assoc] using
          compactFormulaSubstitutionStep_formula_or left right
            (compactArithmeticTermTokens witness) suffix output tasks
      have hleft := ihLeft depth rfl
        (compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask (1 + depth) :: tasks) (output ++ [5])
      have hright := ihRight depth rfl suffix tasks
        (output ++ [5] ++ compactArithmeticFormulaTokens
          (compactSubstituteFormulaAlong witness depth left rfl))
      have hfirst := compactFormulaSubstitution_iterate_trans
        (compactArithmeticTermTokens witness) hone hleft
      have hrun := compactFormulaSubstitution_iterate_trans
        (compactArithmeticTermTokens witness) hfirst hright
      change
        ((compactFormulaSubstitutionStep
            (compactArithmeticTermTokens witness))^[
              compactFormulaTaskSteps (left ⋎ right)])
            ((compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
              compactFormulaTask (1 + depth) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ compactArithmeticFormulaTokens
            (compactSubstituteFormulaAlong witness depth (left ⋎ right) rfl))
      simpa [compactFormulaTaskSteps, compactSubstituteFormulaAlong,
        compactArithmeticFormulaTokens,
        LogicalConnective.HomClass.map_or, List.append_assoc] using hrun
  | @hall sourceArity body ih =>
      intro depth harity suffix tasks output
      cases harity
      have hone :
          ((compactFormulaSubstitutionStep
              (compactArithmeticTermTokens witness))^[1])
              ((compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
                compactFormulaTask (1 + depth) :: tasks, none), output) =
            ((compactArithmeticFormulaTokens body ++ suffix,
              compactFormulaTask ((1 + depth) + 1) :: tasks, none),
              output ++ [6]) := by
        simpa [Function.iterate_one] using
          compactFormulaSubstitutionStep_formula_all body
            (compactArithmeticTermTokens witness) suffix output tasks
      have hbody := ih (depth + 1) rfl suffix tasks (output ++ [6])
      have hrun := compactFormulaSubstitution_iterate_trans
        (compactArithmeticTermTokens witness) hone hbody
      change
        ((compactFormulaSubstitutionStep
            (compactArithmeticTermTokens witness))^[
              compactFormulaTaskSteps (∀⁰ body)])
            ((compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
              compactFormulaTask (1 + depth) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ compactArithmeticFormulaTokens
            (compactSubstituteFormulaAlong witness depth (∀⁰ body) rfl))
      simpa [compactFormulaTaskSteps, compactSubstituteFormulaAlong,
        compactArithmeticFormulaTokens, Rewriting.app_all, Rew.qpow,
        List.append_assoc] using hrun
  | @hexs sourceArity body ih =>
      intro depth harity suffix tasks output
      cases harity
      have hone :
          ((compactFormulaSubstitutionStep
              (compactArithmeticTermTokens witness))^[1])
              ((compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
                compactFormulaTask (1 + depth) :: tasks, none), output) =
            ((compactArithmeticFormulaTokens body ++ suffix,
              compactFormulaTask ((1 + depth) + 1) :: tasks, none),
              output ++ [7]) := by
        simpa [Function.iterate_one] using
          compactFormulaSubstitutionStep_formula_exs body
            (compactArithmeticTermTokens witness) suffix output tasks
      have hbody := ih (depth + 1) rfl suffix tasks (output ++ [7])
      have hrun := compactFormulaSubstitution_iterate_trans
        (compactArithmeticTermTokens witness) hone hbody
      change
        ((compactFormulaSubstitutionStep
            (compactArithmeticTermTokens witness))^[
              compactFormulaTaskSteps (∃⁰ body)])
            ((compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
              compactFormulaTask (1 + depth) :: tasks, none), output) =
          ((suffix, tasks, none), output ++ compactArithmeticFormulaTokens
            (compactSubstituteFormulaAlong witness depth (∃⁰ body) rfl))
      simpa [compactFormulaTaskSteps, compactSubstituteFormulaAlong,
        compactArithmeticFormulaTokens, Rewriting.app_exs, Rew.qpow,
        List.append_assoc] using hrun

theorem compactFormulaSubstitutionFormulaTask_execute
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    ((compactFormulaSubstitutionStep
        (compactArithmeticTermTokens witness))^[compactFormulaTaskSteps formula])
        ((compactArithmeticFormulaTokens formula ++ suffix,
          compactFormulaTask 1 :: tasks, none), output) =
      ((suffix, tasks, none), output ++ compactArithmeticFormulaTokens
        (Rewriting.app (Rew.subst ![witness]) formula)) := by
  simpa [compactSubstituteFormulaAlong, Rew.qpow] using
    (compactFormulaSubstitutionFormulaTask_execute_along
      witness formula 0 rfl suffix tasks output)

theorem compactFormulaSubstitutionTokenTransform_canonical_append
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (suffix : List Nat) :
    compactFormulaSubstitutionTokenTransform 1
        (compactArithmeticTermTokens witness,
          compactArithmeticFormulaTokens formula ++ suffix) =
      some (compactArithmeticFormulaTokens
        (Rewriting.app (Rew.subst ![witness]) formula), suffix) := by
  let witnessTokens := compactArithmeticTermTokens witness
  let tokens := compactArithmeticFormulaTokens formula ++ suffix
  let substitutedTokens := compactArithmeticFormulaTokens
    (Rewriting.app (Rew.subst ![witness]) formula)
  let used := compactFormulaTaskSteps formula + 1
  have htask := compactFormulaSubstitutionFormulaTask_execute
    witness formula suffix [] []
  have hfinish :
      ((compactFormulaSubstitutionStep witnessTokens)^[used])
          ((tokens, [compactFormulaTask 1], none), []) =
        ((suffix, [], some (some suffix)), substitutedTokens) := by
    apply compactFormulaSubstitution_iterate_trans witnessTokens htask
    simp [Function.iterate_one, witnessTokens, substitutedTokens]
  have hformula := compactFormulaTaskSteps_le_tokenLength formula
  have hinputLength :
      (compactArithmeticFormulaTokens formula).length <= tokens.length := by
    simp [tokens]
  have hfuelLength := compactSyntaxRunFuelBound_length_add_one tokens
  have hused : used <= compactSyntaxRunFuelBound tokens := by
    omega
  obtain ⟨extra, hfuel⟩ := exists_add_of_le hused
  have hrun :
      ((compactFormulaSubstitutionStep witnessTokens)^[
          compactSyntaxRunFuelBound tokens])
          ((tokens, [compactFormulaTask 1], none), []) =
        ((suffix, [], some (some suffix)), substitutedTokens) := by
    rw [hfuel]
    exact compactFormulaSubstitution_iterate_trans witnessTokens hfinish
      (compactFormulaSubstitutionStep_iterate_done witnessTokens extra suffix []
        (some suffix) substitutedTokens)
  simp [compactFormulaSubstitutionTokenTransform, compactFormulaSubstitutionRun,
    compactFormulaSubstitutionInitialState, compactFormulaParserInitialState,
    compactFormulaSubstitutionStateOutput, witnessTokens, tokens,
    substitutedTokens, hrun]

#print axioms compactSubstituteConsumedTermHeader_primrec
#print axioms compactFormulaSubstitutionStep_primrec
#print axioms compactFormulaSubstitutionRun_primrec
#print axioms compactFormulaSubstitutionTokenTransform_primrec
#print axioms compactSubstitutionBVarResult_eq_qpow
#print axioms compactFormulaSubstitutionTermTask_execute
#print axioms compactFormulaSubstitutionTermList_execute
#print axioms compactFormulaSubstitutionFormulaTask_execute
#print axioms compactFormulaSubstitutionTokenTransform_canonical_append

end FoundationCompactNumericFormulaSubstitution
