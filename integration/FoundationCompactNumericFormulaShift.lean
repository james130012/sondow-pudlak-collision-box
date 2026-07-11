import integration.FoundationCompactNumericFormulaConstructors

/-!
# Pure numeric formula shift

The machine reuses the checked numeric syntax-task stack.  It copies every
formula header and every bound-variable/function header verbatim, while a
free-variable header `[1, index]` becomes `[1, index + 1]`.  Its runtime state
contains only naturals and lists of naturals; typed syntax is used solely in
the correctness theorem.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericFormulaShift

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser

abbrev CompactFormulaShiftState :=
  CompactSyntaxParserState × List Nat

def compactShiftConsumedTermHeader
    (tokens : List Nat) : List Nat :=
  if compactTokenAt 0 tokens = 1 then
    [1, compactTokenAt 1 tokens + 1]
  else
    tokens

theorem compactShiftConsumedTermHeader_primrec :
    Primrec compactShiftConsumedTermHeader := by
  have htag : Primrec
      (fun tokens : List Nat => compactTokenAt 0 tokens) :=
    compactTokenAt_primrec.comp (Primrec.const 0) Primrec.id
  have hindex : Primrec
      (fun tokens : List Nat => compactTokenAt 1 tokens) :=
    compactTokenAt_primrec.comp (Primrec.const 1) Primrec.id
  have hisFree : PrimrecPred
      (fun tokens : List Nat => compactTokenAt 0 tokens = 1) :=
    Primrec.eq.comp htag (Primrec.const 1)
  have htail : Primrec
      (fun tokens : List Nat => [compactTokenAt 1 tokens + 1]) :=
    Primrec.list_cons.comp (Primrec.succ.comp hindex) (Primrec.const [])
  have hshifted : Primrec
      (fun tokens : List Nat => [1, compactTokenAt 1 tokens + 1]) :=
    Primrec.list_cons.comp (Primrec.const 1) htail
  exact
    (Primrec.ite hisFree hshifted Primrec.id).of_eq fun tokens => by
      simp [compactShiftConsumedTermHeader]

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

def compactFormulaShiftEmission
    (taskKind : Nat) (consumed : List Nat) : List Nat :=
  if taskKind = 0 then
    compactShiftConsumedTermHeader consumed
  else
    consumed

theorem compactFormulaShiftEmission_primrec :
    Primrec₂ compactFormulaShiftEmission := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  have hterm : PrimrecPred (fun input : Input => input.1 = 0) :=
    Primrec.eq.comp Primrec.fst (Primrec.const 0)
  have htransformed : Primrec
      (fun input : Input =>
        compactShiftConsumedTermHeader input.2) :=
    compactShiftConsumedTermHeader_primrec.comp Primrec.snd
  exact
    (Primrec.ite hterm
      htransformed Primrec.snd).of_eq fun input => by
        simp only [compactFormulaShiftEmission]

def compactFormulaShiftStep
    (state : CompactFormulaShiftState) :
    CompactFormulaShiftState :=
  let parserState := state.1
  let nextParserState := compactSyntaxParserStep parserState
  let consumed := consumedTokenPrefix parserState.1 nextParserState.1
  let emitted := compactFormulaShiftEmission
    (compactSyntaxCurrentTaskKind parserState) consumed
  (nextParserState, state.2 ++ emitted)

theorem compactFormulaShiftStep_primrec :
    Primrec compactFormulaShiftStep := by
  have hparser : Primrec
      (fun state : CompactFormulaShiftState => state.1) :=
    Primrec.fst
  have hnext : Primrec
      (fun state : CompactFormulaShiftState =>
        compactSyntaxParserStep state.1) :=
    compactSyntaxParserStep_primrec.comp hparser
  have holdTokens : Primrec
      (fun state : CompactFormulaShiftState => state.1.1) :=
    Primrec.fst.comp hparser
  have hnextTokens : Primrec
      (fun state : CompactFormulaShiftState =>
        (compactSyntaxParserStep state.1).1) :=
    Primrec.fst.comp hnext
  have hconsumed : Primrec
      (fun state : CompactFormulaShiftState =>
        consumedTokenPrefix state.1.1
          (compactSyntaxParserStep state.1).1) :=
    consumedTokenPrefix_primrec.comp holdTokens hnextTokens
  have hkind : Primrec
      (fun state : CompactFormulaShiftState =>
        compactSyntaxCurrentTaskKind state.1) :=
    compactSyntaxCurrentTaskKind_primrec.comp hparser
  have hemitted : Primrec
      (fun state : CompactFormulaShiftState =>
        compactFormulaShiftEmission
          (compactSyntaxCurrentTaskKind state.1)
          (consumedTokenPrefix state.1.1
            (compactSyntaxParserStep state.1).1)) :=
    compactFormulaShiftEmission_primrec.comp hkind hconsumed
  have houtput : Primrec
      (fun state : CompactFormulaShiftState => state.2) :=
    Primrec.snd
  have hnextOutput : Primrec
      (fun state : CompactFormulaShiftState =>
        state.2 ++ compactFormulaShiftEmission
          (compactSyntaxCurrentTaskKind state.1)
          (consumedTokenPrefix state.1.1
            (compactSyntaxParserStep state.1).1)) :=
    Primrec.list_append.comp houtput hemitted
  exact
    (Primrec.pair hnext hnextOutput).of_eq fun state => by rfl

def compactFormulaShiftInitialState
    (binderArity : Nat) (tokens : List Nat) :
    CompactFormulaShiftState :=
  (compactFormulaParserInitialState binderArity tokens, [])

theorem compactFormulaShiftInitialState_primrec :
    Primrec₂ compactFormulaShiftInitialState := by
  exact Primrec₂.pair.comp₂
    compactFormulaParserInitialState_primrec
    (Primrec₂.const [])

def compactFormulaShiftRun
    (binderArity : Nat) (tokens : List Nat) :
    CompactFormulaShiftState :=
  (compactFormulaShiftStep^[compactSyntaxRunFuelBound tokens])
    (compactFormulaShiftInitialState binderArity tokens)

theorem compactFormulaShiftRun_primrec :
    Primrec₂ compactFormulaShiftRun := by
  apply Primrec₂.mk
  have hfuel : Primrec
      (fun input : Nat × List Nat =>
        compactSyntaxRunFuelBound input.2) :=
    compactSyntaxRunFuelBound_primrec.comp Primrec.snd
  have hinitial : Primrec
      (fun input : Nat × List Nat =>
        compactFormulaShiftInitialState input.1 input.2) :=
    compactFormulaShiftInitialState_primrec
  have hstep : Primrec₂
      (fun (_input : Nat × List Nat)
          (state : CompactFormulaShiftState) =>
        compactFormulaShiftStep state) :=
    (compactFormulaShiftStep_primrec.comp Primrec.snd).to₂
  exact
    (Primrec.nat_iterate hfuel hinitial hstep).of_eq
      fun input => by rfl

def compactFormulaShiftStateOutput
    (state : CompactFormulaShiftState) :
    Option (List Nat × List Nat) :=
  state.1.2.2.bind fun result =>
    result.map fun suffix => (state.2, suffix)

theorem compactFormulaShiftStateOutput_primrec :
    Primrec compactFormulaShiftStateOutput := by
  have hstatus : Primrec
      (fun state : CompactFormulaShiftState => state.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hinner : Primrec₂
      (fun (state : CompactFormulaShiftState)
          (result : Option (List Nat)) =>
        result.map fun suffix => (state.2, suffix)) := by
    apply Primrec₂.mk
    let Input := CompactFormulaShiftState × Option (List Nat)
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

def compactFormulaShiftTokenTransform
    (binderArity : Nat) (tokens : List Nat) :
    Option (List Nat × List Nat) :=
  compactFormulaShiftStateOutput
    (compactFormulaShiftRun binderArity tokens)

theorem compactFormulaShiftTokenTransform_primrec :
    Primrec₂ compactFormulaShiftTokenTransform := by
  exact compactFormulaShiftStateOutput_primrec.comp₂
    compactFormulaShiftRun_primrec

/-! ## Exact task execution -/

theorem compactFormulaShift_iterate_trans
    {start middle finish : CompactFormulaShiftState}
    {firstSteps secondSteps : Nat}
    (hfirst : (compactFormulaShiftStep^[firstSteps]) start = middle)
    (hsecond : (compactFormulaShiftStep^[secondSteps]) middle = finish) :
    (compactFormulaShiftStep^[firstSteps + secondSteps]) start = finish := by
  rw [Nat.add_comm, Function.iterate_add_apply, hfirst, hsecond]

theorem compactFormulaShiftStep_of_transition
    {parserState nextParserState : CompactSyntaxParserState}
    {consumed : List Nat} (output : List Nat)
    (hparser : compactSyntaxParserStep parserState = nextParserState)
    (hconsumed : consumedTokenPrefix parserState.1 nextParserState.1 =
      consumed) :
    compactFormulaShiftStep (parserState, output) =
      (nextParserState,
        output ++ compactFormulaShiftEmission
          (compactSyntaxCurrentTaskKind parserState) consumed) := by
  simp [compactFormulaShiftStep, hparser, hconsumed]

@[simp] theorem compactFormulaShiftStep_done
    (tokens : List Nat) (tasks : List CompactSyntaxTask)
    (result : Option (List Nat)) (output : List Nat) :
    compactFormulaShiftStep
        ((tokens, tasks, some result), output) =
      ((tokens, tasks, some result), output) := by
  refine (compactFormulaShiftStep_of_transition output
    (consumed := [])
    (compactSyntaxParserStep_done tokens tasks result) ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactFormulaShiftEmission,
      compactShiftConsumedTermHeader, compactTokenAt]

theorem compactFormulaShiftStep_iterate_done
    (fuel : Nat) (tokens : List Nat) (tasks : List CompactSyntaxTask)
    (result : Option (List Nat)) (output : List Nat) :
    (compactFormulaShiftStep^[fuel])
        ((tokens, tasks, some result), output) =
      ((tokens, tasks, some result), output) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply,
        compactFormulaShiftStep_done, ih]

@[simp] theorem compactFormulaShiftStep_empty
    (tokens output : List Nat) :
    compactFormulaShiftStep ((tokens, [], none), output) =
      ((tokens, [], some (some tokens)), output) := by
  refine (compactFormulaShiftStep_of_transition output
    (consumed := []) (compactSyntaxParserStep_empty tokens) ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTaskKind,
      compactFormulaShiftEmission]

@[simp] theorem compactFormulaShiftStep_repeat_zero
    (binderArity : Nat) (tokens output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaShiftStep
        ((tokens, compactRepeatTermTask binderArity 0 :: tasks, none),
          output) =
      ((tokens, tasks, none), output) := by
  have hparser : compactSyntaxParserStep
      (tokens, compactRepeatTermTask binderArity 0 :: tasks, none) =
      (tokens, tasks, none) := by
    simpa [compactSyntaxContinue] using
      (compactSyntaxParserStep_repeat_zero binderArity tokens tasks)
  refine (compactFormulaShiftStep_of_transition output
    (consumed := []) hparser ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTaskKind, compactRepeatTermTask,
      compactFormulaShiftEmission]

@[simp] theorem compactFormulaShiftStep_repeat_succ
    (binderArity count : Nat) (tokens output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaShiftStep
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
  refine (compactFormulaShiftStep_of_transition output
    (consumed := []) hparser ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTaskKind, compactRepeatTermTask,
      compactFormulaShiftEmission]

@[simp] theorem compactFormulaShiftStep_term_bvar
    {binderArity : Nat} (index : Fin binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaShiftStep
        ((compactArithmeticTermTokens (#index) ++ suffix,
          compactTermTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++ compactArithmeticTermTokens (#index)) := by
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
  refine (compactFormulaShiftStep_of_transition output hparser
    hconsumed).trans ?_
  rw [htokens]
  simp [compactSyntaxCurrentTaskKind, compactTermTask,
    compactFormulaShiftEmission, compactShiftConsumedTermHeader,
    compactTokenAt]

@[simp] theorem compactFormulaShiftStep_term_fvar
    {binderArity : Nat} (freeIndex : Nat)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaShiftStep
        ((compactArithmeticTermTokens
            (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) ++
              suffix,
          compactTermTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++ compactArithmeticTermTokens
          (&(freeIndex + 1) :
            LO.FirstOrder.ArithmeticSemiterm Nat binderArity)) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticTermTokens
          (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) ++
            suffix,
        compactTermTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
    rw [compactSyntaxParserStep_term]
    exact compactTermTokenStep_fvar freeIndex suffix tasks
  refine (compactFormulaShiftStep_of_transition output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactTermTask,
    compactFormulaShiftEmission, compactShiftConsumedTermHeader,
    compactArithmeticTermTokens, compactTokenAt]

@[simp] theorem compactFormulaShiftStep_term_func
    {binderArity functionArity : Nat}
    (functionSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Func functionArity)
    (arguments : Fin functionArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaShiftStep
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
  refine (compactFormulaShiftStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactTermTask,
    compactFormulaShiftEmission, compactShiftConsumedTermHeader,
    compactTokenAt]

@[simp] theorem compactFormulaShiftStep_formula_rel
    {binderArity relationArity : Nat}
    (relationSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Rel relationArity)
    (arguments : Fin relationArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaShiftStep
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
  refine (compactFormulaShiftStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaShiftEmission, compactShiftConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaShiftStep_formula_nrel
    {binderArity relationArity : Nat}
    (relationSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Rel relationArity)
    (arguments : Fin relationArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaShiftStep
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
  refine (compactFormulaShiftStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaShiftEmission, compactShiftConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaShiftStep_formula_verum
    {binderArity : Nat} (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaShiftStep
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
  refine (compactFormulaShiftStep_of_transition output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaShiftEmission, compactShiftConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaShiftStep_formula_falsum
    {binderArity : Nat} (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaShiftStep
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
  refine (compactFormulaShiftStep_of_transition output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaShiftEmission, compactShiftConsumedTermHeader,
    compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaShiftStep_formula_and
    {binderArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaShiftStep
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
  refine (compactFormulaShiftStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaShiftEmission, compactShiftConsumedTermHeader]

@[simp] theorem compactFormulaShiftStep_formula_or
    {binderArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaShiftStep
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
  refine (compactFormulaShiftStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaShiftEmission, compactShiftConsumedTermHeader]

@[simp] theorem compactFormulaShiftStep_formula_all
    {binderArity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (binderArity + 1))
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaShiftStep
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
  refine (compactFormulaShiftStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaShiftEmission, compactShiftConsumedTermHeader]

@[simp] theorem compactFormulaShiftStep_formula_exs
    {binderArity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (binderArity + 1))
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaShiftStep
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
  refine (compactFormulaShiftStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaShiftEmission, compactShiftConsumedTermHeader]

def compactShiftedTermListTokens {binderArity : Nat}
    (terms : List
      (LO.FirstOrder.ArithmeticSemiterm Nat binderArity)) : List Nat :=
  (terms.map fun term =>
    compactArithmeticTermTokens (Rew.shift term)).flatten

theorem compactFormulaShiftTermTask_execute
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    (compactFormulaShiftStep^[compactTermTaskSteps term])
        ((compactArithmeticTermTokens term ++ suffix,
          compactTermTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++ compactArithmeticTermTokens (Rew.shift term)) := by
  induction term generalizing suffix tasks output with
  | bvar index =>
      simp [compactTermTaskSteps, Function.iterate_one]
  | fvar freeIndex =>
      simp [compactTermTaskSteps, Function.iterate_one]
  | @func functionArity functionSymbol arguments ih =>
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat binderArity) :=
        List.ofFn arguments
      have hmembers : ∀ member ∈ terms,
          ∀ (memberSuffix : List Nat)
            (memberTasks : List CompactSyntaxTask)
            (memberOutput : List Nat),
          (compactFormulaShiftStep^[compactTermTaskSteps member])
              ((compactArithmeticTermTokens member ++ memberSuffix,
                compactTermTask binderArity :: memberTasks, none),
                memberOutput) =
            ((memberSuffix, memberTasks, none),
              memberOutput ++
                compactArithmeticTermTokens (Rew.shift member)) := by
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
            (compactFormulaShiftStep^[compactTermTaskSteps member])
                ((compactArithmeticTermTokens member ++ memberSuffix,
                  compactTermTask binderArity :: memberTasks, none),
                  memberOutput) =
              ((memberSuffix, memberTasks, none),
                memberOutput ++
                  compactArithmeticTermTokens (Rew.shift member))) ->
          ∀ (repeatSuffix : List Nat)
            (repeatTasks : List CompactSyntaxTask)
            (repeatOutput : List Nat),
          (compactFormulaShiftStep^[
              compactTermListRepeatSteps termList])
              ((compactTermListTokens termList ++ repeatSuffix,
                compactRepeatTermTask binderArity termList.length ::
                  repeatTasks, none), repeatOutput) =
            ((repeatSuffix, repeatTasks, none),
              repeatOutput ++ compactShiftedTermListTokens termList) := by
        intro termList hall repeatSuffix repeatTasks repeatOutput
        induction termList generalizing repeatOutput with
        | nil =>
            simp [compactTermListRepeatSteps, compactTermListTokens,
              compactShiftedTermListTokens, Function.iterate_one]
        | cons head tail ihTail =>
            have hhead := hall head (by simp)
            have htailMembers : ∀ member ∈ tail,
                ∀ (memberSuffix : List Nat)
                  (memberTasks : List CompactSyntaxTask)
                  (memberOutput : List Nat),
                (compactFormulaShiftStep^[compactTermTaskSteps member])
                    ((compactArithmeticTermTokens member ++ memberSuffix,
                      compactTermTask binderArity :: memberTasks, none),
                      memberOutput) =
                  ((memberSuffix, memberTasks, none),
                    memberOutput ++
                      compactArithmeticTermTokens (Rew.shift member)) := by
              intro member hmember
              exact hall member (by simp [hmember])
            have hone :
                (compactFormulaShiftStep^[1])
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
                compactArithmeticTermTokens (Rew.shift head))
            have hfirst := compactFormulaShift_iterate_trans
              hone hheadRun
            have hallRun := compactFormulaShift_iterate_trans
              hfirst htailRun
            simpa [compactTermListRepeatSteps, compactTermListTokens,
              compactShiftedTermListTokens,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              List.append_assoc] using hallRun
      have hfirst :
          (compactFormulaShiftStep^[1])
              ((compactArithmeticTermTokens
                    (Semiterm.func functionSymbol arguments) ++ suffix,
                compactTermTask binderArity :: tasks, none), output) =
            ((compactTermListTokens terms ++ suffix,
              compactRepeatTermTask binderArity terms.length :: tasks,
              none),
              output ++ [2, functionArity,
                Encodable.encode functionSymbol]) := by
        have htermsTokens : compactTermListTokens terms =
            (List.ofFn fun index =>
              compactArithmeticTermTokens (arguments index)).flatten := by
          exact compactTermListTokens_ofFn arguments
        rw [htermsTokens]
        simpa only [Function.iterate_one, terms, List.length_ofFn] using
          compactFormulaShiftStep_term_func functionSymbol arguments
            suffix output tasks
      have hrepeatRun := hrepeat terms hmembers suffix tasks
        (output ++ [2, functionArity, Encodable.encode functionSymbol])
      have hrun := compactFormulaShift_iterate_trans hfirst hrepeatRun
      have hsteps :
          compactTermTaskSteps
              (Semiterm.func functionSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactTermTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have hshiftedTokens : compactShiftedTermListTokens terms =
          (List.ofFn fun index => compactArithmeticTermTokens
            (Rew.shift (arguments index))).flatten := by
        simp only [compactShiftedTermListTokens, terms, List.map_ofFn,
          Function.comp_def]
      rw [hshiftedTokens] at hrun
      simpa [compactArithmeticTermTokens, compactShiftedTermListTokens,
        Rew.func, Function.comp_def, terms, List.append_assoc] using hrun

theorem compactFormulaShiftTermList_execute
    {binderArity : Nat}
    (terms : List
      (LO.FirstOrder.ArithmeticSemiterm Nat binderArity))
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    (compactFormulaShiftStep^[compactTermListRepeatSteps terms])
        ((compactTermListTokens terms ++ suffix,
          compactRepeatTermTask binderArity terms.length :: tasks, none),
          output) =
      ((suffix, tasks, none),
        output ++ compactShiftedTermListTokens terms) := by
  induction terms generalizing output with
  | nil =>
      simp [compactTermListRepeatSteps, compactTermListTokens,
        compactShiftedTermListTokens, Function.iterate_one]
  | cons head tail ih =>
      have hone :
          (compactFormulaShiftStep^[1])
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
      have hhead := compactFormulaShiftTermTask_execute head
        (compactTermListTokens tail ++ suffix)
        (compactRepeatTermTask binderArity tail.length :: tasks) output
      have hfirst := compactFormulaShift_iterate_trans hone hhead
      have htail := ih
        (output ++ compactArithmeticTermTokens (Rew.shift head))
      have hall := compactFormulaShift_iterate_trans hfirst htail
      simpa [compactTermListRepeatSteps, compactTermListTokens,
        compactShiftedTermListTokens,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using hall

theorem compactFormulaShiftFormulaTask_execute
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    (compactFormulaShiftStep^[compactFormulaTaskSteps formula])
        ((compactArithmeticFormulaTokens formula ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++
          compactArithmeticFormulaTokens (Rewriting.shift formula)) := by
  revert suffix tasks output
  let P : (arity : Nat) ->
      LO.FirstOrder.ArithmeticSemiformula Nat arity -> Prop :=
    fun arity formula =>
      ∀ (suffix : List Nat) (tasks : List CompactSyntaxTask)
        (output : List Nat),
        (compactFormulaShiftStep^[compactFormulaTaskSteps formula])
            ((compactArithmeticFormulaTokens formula ++ suffix,
              compactFormulaTask arity :: tasks, none), output) =
          ((suffix, tasks, none),
            output ++
              compactArithmeticFormulaTokens (Rewriting.shift formula))
  change P binderArity formula
  induction formula with
  | @rel formulaArity relationArity relationSymbol arguments =>
      intro suffix tasks output
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat formulaArity) :=
        List.ofFn arguments
      have hfirst :
          (compactFormulaShiftStep^[1])
              ((compactArithmeticFormulaTokens
                    (Semiformula.rel relationSymbol arguments) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none), output) =
            ((compactTermListTokens terms ++ suffix,
              compactRepeatTermTask formulaArity terms.length :: tasks,
              none),
              output ++ [0, relationArity,
                Encodable.encode relationSymbol]) := by
        have htermsTokens : compactTermListTokens terms =
            (List.ofFn fun index =>
              compactArithmeticTermTokens (arguments index)).flatten :=
          compactTermListTokens_ofFn arguments
        rw [htermsTokens]
        simpa only [Function.iterate_one, terms, List.length_ofFn] using
          compactFormulaShiftStep_formula_rel relationSymbol arguments
            suffix output tasks
      have hterms := compactFormulaShiftTermList_execute terms suffix tasks
        (output ++ [0, relationArity, Encodable.encode relationSymbol])
      have hrun := compactFormulaShift_iterate_trans hfirst hterms
      have hsteps :
          compactFormulaTaskSteps
              (Semiformula.rel relationSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactFormulaTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have hshiftedTokens : compactShiftedTermListTokens terms =
          (List.ofFn fun index => compactArithmeticTermTokens
            (Rew.shift (arguments index))).flatten := by
        simp only [compactShiftedTermListTokens, terms, List.map_ofFn,
          Function.comp_def]
      rw [hshiftedTokens] at hrun
      simpa [compactArithmeticFormulaTokens, compactShiftedTermListTokens,
        Semiformula.rew_rel, Function.comp_def, terms,
        List.append_assoc] using hrun
  | @nrel formulaArity relationArity relationSymbol arguments =>
      intro suffix tasks output
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat formulaArity) :=
        List.ofFn arguments
      have hfirst :
          (compactFormulaShiftStep^[1])
              ((compactArithmeticFormulaTokens
                    (Semiformula.nrel relationSymbol arguments) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none), output) =
            ((compactTermListTokens terms ++ suffix,
              compactRepeatTermTask formulaArity terms.length :: tasks,
              none),
              output ++ [1, relationArity,
                Encodable.encode relationSymbol]) := by
        have htermsTokens : compactTermListTokens terms =
            (List.ofFn fun index =>
              compactArithmeticTermTokens (arguments index)).flatten :=
          compactTermListTokens_ofFn arguments
        rw [htermsTokens]
        simpa only [Function.iterate_one, terms, List.length_ofFn] using
          compactFormulaShiftStep_formula_nrel relationSymbol arguments
            suffix output tasks
      have hterms := compactFormulaShiftTermList_execute terms suffix tasks
        (output ++ [1, relationArity, Encodable.encode relationSymbol])
      have hrun := compactFormulaShift_iterate_trans hfirst hterms
      have hsteps :
          compactFormulaTaskSteps
              (Semiformula.nrel relationSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactFormulaTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have hshiftedTokens : compactShiftedTermListTokens terms =
          (List.ofFn fun index => compactArithmeticTermTokens
            (Rew.shift (arguments index))).flatten := by
        simp only [compactShiftedTermListTokens, terms, List.map_ofFn,
          Function.comp_def]
      rw [hshiftedTokens] at hrun
      simpa [compactArithmeticFormulaTokens, compactShiftedTermListTokens,
        Semiformula.rew_nrel, Function.comp_def, terms,
        List.append_assoc] using hrun
  | @verum formulaArity =>
      intro suffix tasks output
      change
        (compactFormulaShiftStep^[1])
            ((compactArithmeticFormulaTokens
                (⊤ : LO.FirstOrder.ArithmeticSemiformula Nat formulaArity) ++
              suffix,
              compactFormulaTask formulaArity :: tasks, none), output) =
          ((suffix, tasks, none), output ++ [2])
      simpa only [Function.iterate_one] using
          (compactFormulaShiftStep_formula_verum
            (binderArity := formulaArity) suffix output tasks)
  | @falsum formulaArity =>
      intro suffix tasks output
      change
        (compactFormulaShiftStep^[1])
            ((compactArithmeticFormulaTokens
                (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat formulaArity) ++
              suffix,
              compactFormulaTask formulaArity :: tasks, none), output) =
          ((suffix, tasks, none), output ++ [3])
      simpa only [Function.iterate_one] using
          (compactFormulaShiftStep_formula_falsum
            (binderArity := formulaArity) suffix output tasks)
  | @and formulaArity left right ihLeft ihRight =>
      intro suffix tasks output
      have hone :
          (compactFormulaShiftStep^[1])
              ((compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none), output) =
            ((compactArithmeticFormulaTokens left ++
                (compactArithmeticFormulaTokens right ++ suffix),
              compactFormulaTask formulaArity ::
                compactFormulaTask formulaArity :: tasks,
              none), output ++ [4]) := by
        simpa [Function.iterate_one, List.append_assoc] using
          compactFormulaShiftStep_formula_and left right suffix output tasks
      have hleft := ihLeft
        (compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask formulaArity :: tasks) (output ++ [4])
      have hright := ihRight suffix tasks
        (output ++ [4] ++
          compactArithmeticFormulaTokens (Rewriting.shift left))
      have hfirst := compactFormulaShift_iterate_trans hone hleft
      have hrun := compactFormulaShift_iterate_trans hfirst hright
      change
        (compactFormulaShiftStep^[compactFormulaTaskSteps (left ⋏ right)])
            ((compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none), output) =
          ((suffix, tasks, none),
            output ++ compactArithmeticFormulaTokens
              (Rewriting.shift (left ⋏ right)))
      simpa [compactFormulaTaskSteps, compactArithmeticFormulaTokens,
        LogicalConnective.HomClass.map_and, List.append_assoc] using hrun
  | @or formulaArity left right ihLeft ihRight =>
      intro suffix tasks output
      have hone :
          (compactFormulaShiftStep^[1])
              ((compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none), output) =
            ((compactArithmeticFormulaTokens left ++
                (compactArithmeticFormulaTokens right ++ suffix),
              compactFormulaTask formulaArity ::
                compactFormulaTask formulaArity :: tasks,
              none), output ++ [5]) := by
        simpa [Function.iterate_one, List.append_assoc] using
          compactFormulaShiftStep_formula_or left right suffix output tasks
      have hleft := ihLeft
        (compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask formulaArity :: tasks) (output ++ [5])
      have hright := ihRight suffix tasks
        (output ++ [5] ++
          compactArithmeticFormulaTokens (Rewriting.shift left))
      have hfirst := compactFormulaShift_iterate_trans hone hleft
      have hrun := compactFormulaShift_iterate_trans hfirst hright
      change
        (compactFormulaShiftStep^[compactFormulaTaskSteps (left ⋎ right)])
            ((compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none), output) =
          ((suffix, tasks, none),
            output ++ compactArithmeticFormulaTokens
              (Rewriting.shift (left ⋎ right)))
      simpa [compactFormulaTaskSteps, compactArithmeticFormulaTokens,
        LogicalConnective.HomClass.map_or, List.append_assoc] using hrun
  | @all formulaArity body ih =>
      intro suffix tasks output
      have hone :
          (compactFormulaShiftStep^[1])
              ((compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none), output) =
            ((compactArithmeticFormulaTokens body ++ suffix,
              compactFormulaTask (formulaArity + 1) :: tasks, none),
              output ++ [6]) := by
        simpa [Function.iterate_one] using
          compactFormulaShiftStep_formula_all body suffix output tasks
      have hbody := ih suffix tasks (output ++ [6])
      have hrun := compactFormulaShift_iterate_trans hone hbody
      change
        (compactFormulaShiftStep^[compactFormulaTaskSteps (∀⁰ body)])
            ((compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none), output) =
          ((suffix, tasks, none),
            output ++ compactArithmeticFormulaTokens
              (Rewriting.shift (∀⁰ body)))
      simpa [compactFormulaTaskSteps, compactArithmeticFormulaTokens,
        Rewriting.app_all, Rew.q_shift, List.append_assoc] using hrun
  | @exs formulaArity body ih =>
      intro suffix tasks output
      have hone :
          (compactFormulaShiftStep^[1])
              ((compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none), output) =
            ((compactArithmeticFormulaTokens body ++ suffix,
              compactFormulaTask (formulaArity + 1) :: tasks, none),
              output ++ [7]) := by
        simpa [Function.iterate_one] using
          compactFormulaShiftStep_formula_exs body suffix output tasks
      have hbody := ih suffix tasks (output ++ [7])
      have hrun := compactFormulaShift_iterate_trans hone hbody
      change
        (compactFormulaShiftStep^[compactFormulaTaskSteps (∃⁰ body)])
            ((compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none), output) =
          ((suffix, tasks, none),
            output ++ compactArithmeticFormulaTokens
              (Rewriting.shift (∃⁰ body)))
      simpa [compactFormulaTaskSteps, compactArithmeticFormulaTokens,
        Rewriting.app_exs, Rew.q_shift, List.append_assoc] using hrun

theorem compactFormulaShiftTokenTransform_canonical_append
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix : List Nat) :
    compactFormulaShiftTokenTransform binderArity
        (compactArithmeticFormulaTokens formula ++ suffix) =
      some (compactArithmeticFormulaTokens (Rewriting.shift formula),
        suffix) := by
  let tokens := compactArithmeticFormulaTokens formula ++ suffix
  let shiftedTokens := compactArithmeticFormulaTokens
    (Rewriting.shift formula)
  let used := compactFormulaTaskSteps formula + 1
  have htask := compactFormulaShiftFormulaTask_execute formula suffix [] []
  have hfinish :
      (compactFormulaShiftStep^[used])
          ((tokens, [compactFormulaTask binderArity], none), []) =
        ((suffix, [], some (some suffix)), shiftedTokens) := by
    apply compactFormulaShift_iterate_trans htask
    simp [Function.iterate_one, shiftedTokens]
  have hformula := compactFormulaTaskSteps_le_tokenLength formula
  have hinputLength :
      (compactArithmeticFormulaTokens formula).length <= tokens.length := by
    simp [tokens]
  have hfuelLength := compactSyntaxRunFuelBound_length_add_one tokens
  have hused : used <= compactSyntaxRunFuelBound tokens := by
    omega
  obtain ⟨extra, hfuel⟩ := exists_add_of_le hused
  have hrun :
      (compactFormulaShiftStep^[compactSyntaxRunFuelBound tokens])
          ((tokens, [compactFormulaTask binderArity], none), []) =
        ((suffix, [], some (some suffix)), shiftedTokens) := by
    rw [hfuel]
    exact compactFormulaShift_iterate_trans hfinish
      (compactFormulaShiftStep_iterate_done extra suffix []
        (some suffix) shiftedTokens)
  simp [compactFormulaShiftTokenTransform, compactFormulaShiftRun,
    compactFormulaShiftInitialState, compactFormulaParserInitialState,
    compactFormulaShiftStateOutput, tokens, shiftedTokens, hrun]

#print axioms compactShiftConsumedTermHeader_primrec
#print axioms compactSyntaxCurrentTaskKind_primrec
#print axioms compactFormulaShiftEmission_primrec
#print axioms compactFormulaShiftStep_primrec
#print axioms compactFormulaShiftRun_primrec
#print axioms compactFormulaShiftTokenTransform_primrec
#print axioms compactFormulaShiftStep_term_func
#print axioms compactFormulaShiftStep_formula_rel
#print axioms compactFormulaShiftStep_formula_and
#print axioms compactFormulaShiftTermTask_execute
#print axioms compactFormulaShiftTermList_execute
#print axioms compactFormulaShiftFormulaTask_execute
#print axioms compactFormulaShiftTokenTransform_canonical_append

end FoundationCompactNumericFormulaShift
