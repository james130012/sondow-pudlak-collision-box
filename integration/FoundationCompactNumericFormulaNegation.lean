import integration.FoundationCompactNumericFormulaConstructors

/-!
# Pure numeric formula negation

The machine reuses the checked numeric syntax-task stack.  It copies every
consumed term header verbatim and applies the De Morgan tag involution only to
headers consumed by formula tasks.  Its runtime state contains only naturals
and lists of naturals; typed syntax is used solely in the correctness theorem.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericFormulaNegation

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser

abbrev CompactFormulaNegationState :=
  CompactSyntaxParserState × List Nat

def compactNegationFormulaTag (tag : Nat) : Nat :=
  if tag = 0 then 1
  else if tag = 1 then 0
  else if tag = 2 then 3
  else if tag = 3 then 2
  else if tag = 4 then 5
  else if tag = 5 then 4
  else if tag = 6 then 7
  else if tag = 7 then 6
  else tag

theorem compactNegationFormulaTag_primrec :
    Primrec compactNegationFormulaTag := by
  have heq (value : Nat) : PrimrecPred (fun tag : Nat => tag = value) :=
    Primrec.eq.comp Primrec.id (Primrec.const value)
  exact
    (Primrec.ite (heq 0) (Primrec.const 1)
      (Primrec.ite (heq 1) (Primrec.const 0)
        (Primrec.ite (heq 2) (Primrec.const 3)
          (Primrec.ite (heq 3) (Primrec.const 2)
            (Primrec.ite (heq 4) (Primrec.const 5)
              (Primrec.ite (heq 5) (Primrec.const 4)
                (Primrec.ite (heq 6) (Primrec.const 7)
                  (Primrec.ite (heq 7) (Primrec.const 6)
                    Primrec.id)))))))).of_eq fun tag => by
                      simp [compactNegationFormulaTag]

def compactNegateConsumedFormulaHeader
    (tokens : List Nat) : List Nat :=
  match tokens with
  | [] => []
  | tag :: tail => compactNegationFormulaTag tag :: tail

theorem compactNegateConsumedFormulaHeader_primrec :
    Primrec compactNegateConsumedFormulaHeader := by
  have hcons : Primrec₂
      (fun (_tokens : List Nat) (headTail : Nat × List Nat) =>
        compactNegationFormulaTag headTail.1 :: headTail.2) :=
    Primrec.list_cons.comp₂
      (compactNegationFormulaTag_primrec.comp₂
        (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_casesOn Primrec.id (Primrec.const []) hcons).of_eq
      fun tokens => by cases tokens <;> rfl

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

def compactFormulaNegationEmission
    (taskKind : Nat) (consumed : List Nat) : List Nat :=
  if taskKind = 1 then
    compactNegateConsumedFormulaHeader consumed
  else
    consumed

theorem compactFormulaNegationEmission_primrec :
    Primrec₂ compactFormulaNegationEmission := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  have hformula : PrimrecPred (fun input : Input => input.1 = 1) :=
    Primrec.eq.comp Primrec.fst (Primrec.const 1)
  have htransformed : Primrec
      (fun input : Input =>
        compactNegateConsumedFormulaHeader input.2) :=
    compactNegateConsumedFormulaHeader_primrec.comp Primrec.snd
  exact
    (Primrec.ite hformula
      htransformed Primrec.snd).of_eq fun input => by
        simp only [compactFormulaNegationEmission]

def compactFormulaNegationStep
    (state : CompactFormulaNegationState) :
    CompactFormulaNegationState :=
  let parserState := state.1
  let nextParserState := compactSyntaxParserStep parserState
  let consumed := consumedTokenPrefix parserState.1 nextParserState.1
  let emitted := compactFormulaNegationEmission
    (compactSyntaxCurrentTaskKind parserState) consumed
  (nextParserState, state.2 ++ emitted)

theorem compactFormulaNegationStep_primrec :
    Primrec compactFormulaNegationStep := by
  have hparser : Primrec
      (fun state : CompactFormulaNegationState => state.1) :=
    Primrec.fst
  have hnext : Primrec
      (fun state : CompactFormulaNegationState =>
        compactSyntaxParserStep state.1) :=
    compactSyntaxParserStep_primrec.comp hparser
  have holdTokens : Primrec
      (fun state : CompactFormulaNegationState => state.1.1) :=
    Primrec.fst.comp hparser
  have hnextTokens : Primrec
      (fun state : CompactFormulaNegationState =>
        (compactSyntaxParserStep state.1).1) :=
    Primrec.fst.comp hnext
  have hconsumed : Primrec
      (fun state : CompactFormulaNegationState =>
        consumedTokenPrefix state.1.1
          (compactSyntaxParserStep state.1).1) :=
    consumedTokenPrefix_primrec.comp holdTokens hnextTokens
  have hkind : Primrec
      (fun state : CompactFormulaNegationState =>
        compactSyntaxCurrentTaskKind state.1) :=
    compactSyntaxCurrentTaskKind_primrec.comp hparser
  have hemitted : Primrec
      (fun state : CompactFormulaNegationState =>
        compactFormulaNegationEmission
          (compactSyntaxCurrentTaskKind state.1)
          (consumedTokenPrefix state.1.1
            (compactSyntaxParserStep state.1).1)) :=
    compactFormulaNegationEmission_primrec.comp hkind hconsumed
  have houtput : Primrec
      (fun state : CompactFormulaNegationState => state.2) :=
    Primrec.snd
  have hnextOutput : Primrec
      (fun state : CompactFormulaNegationState =>
        state.2 ++ compactFormulaNegationEmission
          (compactSyntaxCurrentTaskKind state.1)
          (consumedTokenPrefix state.1.1
            (compactSyntaxParserStep state.1).1)) :=
    Primrec.list_append.comp houtput hemitted
  exact
    (Primrec.pair hnext hnextOutput).of_eq fun state => by rfl

def compactFormulaNegationInitialState
    (binderArity : Nat) (tokens : List Nat) :
    CompactFormulaNegationState :=
  (compactFormulaParserInitialState binderArity tokens, [])

theorem compactFormulaNegationInitialState_primrec :
    Primrec₂ compactFormulaNegationInitialState := by
  exact Primrec₂.pair.comp₂
    compactFormulaParserInitialState_primrec
    (Primrec₂.const [])

def compactFormulaNegationRun
    (binderArity : Nat) (tokens : List Nat) :
    CompactFormulaNegationState :=
  (compactFormulaNegationStep^[compactSyntaxRunFuelBound tokens])
    (compactFormulaNegationInitialState binderArity tokens)

theorem compactFormulaNegationRun_primrec :
    Primrec₂ compactFormulaNegationRun := by
  apply Primrec₂.mk
  have hfuel : Primrec
      (fun input : Nat × List Nat =>
        compactSyntaxRunFuelBound input.2) :=
    compactSyntaxRunFuelBound_primrec.comp Primrec.snd
  have hinitial : Primrec
      (fun input : Nat × List Nat =>
        compactFormulaNegationInitialState input.1 input.2) :=
    compactFormulaNegationInitialState_primrec
  have hstep : Primrec₂
      (fun (_input : Nat × List Nat)
          (state : CompactFormulaNegationState) =>
        compactFormulaNegationStep state) :=
    (compactFormulaNegationStep_primrec.comp Primrec.snd).to₂
  exact
    (Primrec.nat_iterate hfuel hinitial hstep).of_eq
      fun input => by rfl

def compactFormulaNegationStateOutput
    (state : CompactFormulaNegationState) :
    Option (List Nat × List Nat) :=
  state.1.2.2.bind fun result =>
    result.map fun suffix => (state.2, suffix)

theorem compactFormulaNegationStateOutput_primrec :
    Primrec compactFormulaNegationStateOutput := by
  have hstatus : Primrec
      (fun state : CompactFormulaNegationState => state.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hinner : Primrec₂
      (fun (state : CompactFormulaNegationState)
          (result : Option (List Nat)) =>
        result.map fun suffix => (state.2, suffix)) := by
    apply Primrec₂.mk
    let Input := CompactFormulaNegationState × Option (List Nat)
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

def compactFormulaNegationTokenTransform
    (binderArity : Nat) (tokens : List Nat) :
    Option (List Nat × List Nat) :=
  compactFormulaNegationStateOutput
    (compactFormulaNegationRun binderArity tokens)

theorem compactFormulaNegationTokenTransform_primrec :
    Primrec₂ compactFormulaNegationTokenTransform := by
  exact compactFormulaNegationStateOutput_primrec.comp₂
    compactFormulaNegationRun_primrec

/-! ## Exact task execution -/

theorem compactFormulaNegation_iterate_trans
    {start middle finish : CompactFormulaNegationState}
    {firstSteps secondSteps : Nat}
    (hfirst : (compactFormulaNegationStep^[firstSteps]) start = middle)
    (hsecond : (compactFormulaNegationStep^[secondSteps]) middle = finish) :
    (compactFormulaNegationStep^[firstSteps + secondSteps]) start = finish := by
  rw [Nat.add_comm, Function.iterate_add_apply, hfirst, hsecond]

theorem compactFormulaNegationStep_of_transition
    {parserState nextParserState : CompactSyntaxParserState}
    {consumed : List Nat} (output : List Nat)
    (hparser : compactSyntaxParserStep parserState = nextParserState)
    (hconsumed : consumedTokenPrefix parserState.1 nextParserState.1 =
      consumed) :
    compactFormulaNegationStep (parserState, output) =
      (nextParserState,
        output ++ compactFormulaNegationEmission
          (compactSyntaxCurrentTaskKind parserState) consumed) := by
  simp [compactFormulaNegationStep, hparser, hconsumed]

@[simp] theorem compactFormulaNegationStep_done
    (tokens : List Nat) (tasks : List CompactSyntaxTask)
    (result : Option (List Nat)) (output : List Nat) :
    compactFormulaNegationStep
        ((tokens, tasks, some result), output) =
      ((tokens, tasks, some result), output) := by
  refine (compactFormulaNegationStep_of_transition output
    (consumed := [])
    (compactSyntaxParserStep_done tokens tasks result) ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactFormulaNegationEmission,
      compactNegateConsumedFormulaHeader]

theorem compactFormulaNegationStep_iterate_done
    (fuel : Nat) (tokens : List Nat) (tasks : List CompactSyntaxTask)
    (result : Option (List Nat)) (output : List Nat) :
    (compactFormulaNegationStep^[fuel])
        ((tokens, tasks, some result), output) =
      ((tokens, tasks, some result), output) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply,
        compactFormulaNegationStep_done, ih]

@[simp] theorem compactFormulaNegationStep_empty
    (tokens output : List Nat) :
    compactFormulaNegationStep ((tokens, [], none), output) =
      ((tokens, [], some (some tokens)), output) := by
  refine (compactFormulaNegationStep_of_transition output
    (consumed := []) (compactSyntaxParserStep_empty tokens) ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTaskKind,
      compactFormulaNegationEmission]

@[simp] theorem compactFormulaNegationStep_repeat_zero
    (binderArity : Nat) (tokens output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaNegationStep
        ((tokens, compactRepeatTermTask binderArity 0 :: tasks, none),
          output) =
      ((tokens, tasks, none), output) := by
  have hparser : compactSyntaxParserStep
      (tokens, compactRepeatTermTask binderArity 0 :: tasks, none) =
      (tokens, tasks, none) := by
    simpa [compactSyntaxContinue] using
      (compactSyntaxParserStep_repeat_zero binderArity tokens tasks)
  refine (compactFormulaNegationStep_of_transition output
    (consumed := []) hparser ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTaskKind, compactRepeatTermTask,
      compactFormulaNegationEmission]

@[simp] theorem compactFormulaNegationStep_repeat_succ
    (binderArity count : Nat) (tokens output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaNegationStep
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
  refine (compactFormulaNegationStep_of_transition output
    (consumed := []) hparser ?_).trans ?_
  · simp [consumedTokenPrefix]
  · simp [compactSyntaxCurrentTaskKind, compactRepeatTermTask,
      compactFormulaNegationEmission]

@[simp] theorem compactFormulaNegationStep_term_bvar
    {binderArity : Nat} (index : Fin binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaNegationStep
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
  refine (compactFormulaNegationStep_of_transition output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactTermTask,
    compactFormulaNegationEmission]

@[simp] theorem compactFormulaNegationStep_term_fvar
    {binderArity : Nat} (freeIndex : Nat)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaNegationStep
        ((compactArithmeticTermTokens
            (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) ++
              suffix,
          compactTermTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++ compactArithmeticTermTokens
          (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat binderArity)) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticTermTokens
          (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) ++
            suffix,
        compactTermTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
    rw [compactSyntaxParserStep_term]
    exact compactTermTokenStep_fvar freeIndex suffix tasks
  refine (compactFormulaNegationStep_of_transition output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactTermTask,
    compactFormulaNegationEmission]

@[simp] theorem compactFormulaNegationStep_term_func
    {binderArity functionArity : Nat}
    (functionSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Func functionArity)
    (arguments : Fin functionArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaNegationStep
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
  refine (compactFormulaNegationStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactTermTask,
    compactFormulaNegationEmission]

@[simp] theorem compactFormulaNegationStep_formula_rel
    {binderArity relationArity : Nat}
    (relationSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Rel relationArity)
    (arguments : Fin relationArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaNegationStep
        ((compactArithmeticFormulaTokens
              (Semiformula.rel relationSymbol arguments) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      (((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix,
        compactRepeatTermTask binderArity relationArity :: tasks, none),
        output ++ [1, relationArity, Encodable.encode relationSymbol]) := by
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
  refine (compactFormulaNegationStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaNegationEmission, compactNegateConsumedFormulaHeader,
    compactNegationFormulaTag, compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaNegationStep_formula_nrel
    {binderArity relationArity : Nat}
    (relationSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Rel relationArity)
    (arguments : Fin relationArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaNegationStep
        ((compactArithmeticFormulaTokens
              (Semiformula.nrel relationSymbol arguments) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      (((List.ofFn fun index =>
          compactArithmeticTermTokens (arguments index)).flatten ++ suffix,
        compactRepeatTermTask binderArity relationArity :: tasks, none),
        output ++ [0, relationArity, Encodable.encode relationSymbol]) := by
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
  refine (compactFormulaNegationStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaNegationEmission, compactNegateConsumedFormulaHeader,
    compactNegationFormulaTag, compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaNegationStep_formula_verum
    {binderArity : Nat} (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaNegationStep
        ((compactArithmeticFormulaTokens
              (⊤ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none), output ++ [3]) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticFormulaTokens
          (⊤ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) ++ suffix,
        compactFormulaTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
    rw [compactSyntaxParserStep_formula]
    exact compactFormulaTokenStep_verum suffix tasks
  refine (compactFormulaNegationStep_of_transition output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaNegationEmission, compactNegateConsumedFormulaHeader,
    compactNegationFormulaTag, compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaNegationStep_formula_falsum
    {binderArity : Nat} (suffix output : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactFormulaNegationStep
        ((compactArithmeticFormulaTokens
              (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none), output ++ [2]) := by
  have hparser : compactSyntaxParserStep
      (compactArithmeticFormulaTokens
          (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) ++ suffix,
        compactFormulaTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
    rw [compactSyntaxParserStep_formula]
    exact compactFormulaTokenStep_falsum suffix tasks
  refine (compactFormulaNegationStep_of_transition output hparser
    (consumedTokenPrefix_append _ _)).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaNegationEmission, compactNegateConsumedFormulaHeader,
    compactNegationFormulaTag, compactArithmeticFormulaTokens]

@[simp] theorem compactFormulaNegationStep_formula_and
    {binderArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaNegationStep
        ((compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((compactArithmeticFormulaTokens left ++
          compactArithmeticFormulaTokens right ++ suffix,
        compactFormulaTask binderArity ::
          compactFormulaTask binderArity :: tasks, none),
        output ++ [5]) := by
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
  refine (compactFormulaNegationStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaNegationEmission, compactNegateConsumedFormulaHeader,
    compactNegationFormulaTag]

@[simp] theorem compactFormulaNegationStep_formula_or
    {binderArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaNegationStep
        ((compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((compactArithmeticFormulaTokens left ++
          compactArithmeticFormulaTokens right ++ suffix,
        compactFormulaTask binderArity ::
          compactFormulaTask binderArity :: tasks, none),
        output ++ [4]) := by
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
  refine (compactFormulaNegationStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaNegationEmission, compactNegateConsumedFormulaHeader,
    compactNegationFormulaTag]

@[simp] theorem compactFormulaNegationStep_formula_all
    {binderArity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (binderArity + 1))
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaNegationStep
        ((compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((compactArithmeticFormulaTokens body ++ suffix,
        compactFormulaTask (binderArity + 1) :: tasks, none),
        output ++ [7]) := by
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
  refine (compactFormulaNegationStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaNegationEmission, compactNegateConsumedFormulaHeader,
    compactNegationFormulaTag]

@[simp] theorem compactFormulaNegationStep_formula_exs
    {binderArity : Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat (binderArity + 1))
    (suffix output : List Nat) (tasks : List CompactSyntaxTask) :
    compactFormulaNegationStep
        ((compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((compactArithmeticFormulaTokens body ++ suffix,
        compactFormulaTask (binderArity + 1) :: tasks, none),
        output ++ [6]) := by
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
  refine (compactFormulaNegationStep_of_transition output hparser
    hconsumed).trans ?_
  simp [compactSyntaxCurrentTaskKind, compactFormulaTask,
    compactFormulaNegationEmission, compactNegateConsumedFormulaHeader,
    compactNegationFormulaTag]

theorem compactFormulaNegationTermTask_execute
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    (compactFormulaNegationStep^[compactTermTaskSteps term])
        ((compactArithmeticTermTokens term ++ suffix,
          compactTermTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++ compactArithmeticTermTokens term) := by
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
          (compactFormulaNegationStep^[compactTermTaskSteps member])
              ((compactArithmeticTermTokens member ++ memberSuffix,
                compactTermTask binderArity :: memberTasks, none),
                memberOutput) =
            ((memberSuffix, memberTasks, none),
              memberOutput ++ compactArithmeticTermTokens member) := by
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
            (compactFormulaNegationStep^[compactTermTaskSteps member])
                ((compactArithmeticTermTokens member ++ memberSuffix,
                  compactTermTask binderArity :: memberTasks, none),
                  memberOutput) =
              ((memberSuffix, memberTasks, none),
                memberOutput ++ compactArithmeticTermTokens member)) ->
          ∀ (repeatSuffix : List Nat)
            (repeatTasks : List CompactSyntaxTask)
            (repeatOutput : List Nat),
          (compactFormulaNegationStep^[
              compactTermListRepeatSteps termList])
              ((compactTermListTokens termList ++ repeatSuffix,
                compactRepeatTermTask binderArity termList.length ::
                  repeatTasks, none), repeatOutput) =
            ((repeatSuffix, repeatTasks, none),
              repeatOutput ++ compactTermListTokens termList) := by
        intro termList hall repeatSuffix repeatTasks repeatOutput
        induction termList generalizing repeatOutput with
        | nil =>
            simp [compactTermListRepeatSteps, compactTermListTokens,
              Function.iterate_one]
        | cons head tail ihTail =>
            have hhead := hall head (by simp)
            have htailMembers : ∀ member ∈ tail,
                ∀ (memberSuffix : List Nat)
                  (memberTasks : List CompactSyntaxTask)
                  (memberOutput : List Nat),
                (compactFormulaNegationStep^[compactTermTaskSteps member])
                    ((compactArithmeticTermTokens member ++ memberSuffix,
                      compactTermTask binderArity :: memberTasks, none),
                      memberOutput) =
                  ((memberSuffix, memberTasks, none),
                    memberOutput ++ compactArithmeticTermTokens member) := by
              intro member hmember
              exact hall member (by simp [hmember])
            have hone :
                (compactFormulaNegationStep^[1])
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
              (repeatOutput ++ compactArithmeticTermTokens head)
            have hfirst := compactFormulaNegation_iterate_trans
              hone hheadRun
            have hallRun := compactFormulaNegation_iterate_trans
              hfirst htailRun
            simpa [compactTermListRepeatSteps, compactTermListTokens,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              List.append_assoc] using hallRun
      have hfirst :
          (compactFormulaNegationStep^[1])
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
          compactFormulaNegationStep_term_func functionSymbol arguments
            suffix output tasks
      have hrepeatRun := hrepeat terms hmembers suffix tasks
        (output ++ [2, functionArity, Encodable.encode functionSymbol])
      have hrun := compactFormulaNegation_iterate_trans hfirst hrepeatRun
      have hsteps :
          compactTermTaskSteps
              (Semiterm.func functionSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactTermTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have htermsTokens : compactTermListTokens terms =
          (List.ofFn fun index =>
            compactArithmeticTermTokens (arguments index)).flatten := by
        exact compactTermListTokens_ofFn arguments
      rw [htermsTokens] at hrun
      simpa [compactArithmeticTermTokens, List.append_assoc] using hrun

theorem compactFormulaNegationTermList_execute
    {binderArity : Nat}
    (terms : List
      (LO.FirstOrder.ArithmeticSemiterm Nat binderArity))
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    (compactFormulaNegationStep^[compactTermListRepeatSteps terms])
        ((compactTermListTokens terms ++ suffix,
          compactRepeatTermTask binderArity terms.length :: tasks, none),
          output) =
      ((suffix, tasks, none), output ++ compactTermListTokens terms) := by
  induction terms generalizing output with
  | nil =>
      simp [compactTermListRepeatSteps, compactTermListTokens,
        Function.iterate_one]
  | cons head tail ih =>
      have hone :
          (compactFormulaNegationStep^[1])
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
      have hhead := compactFormulaNegationTermTask_execute head
        (compactTermListTokens tail ++ suffix)
        (compactRepeatTermTask binderArity tail.length :: tasks) output
      have hfirst := compactFormulaNegation_iterate_trans hone hhead
      have htail := ih (output ++ compactArithmeticTermTokens head)
      have hall := compactFormulaNegation_iterate_trans hfirst htail
      simpa [compactTermListRepeatSteps, compactTermListTokens,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using hall

theorem compactFormulaNegationFormulaTask_execute
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix : List Nat) (tasks : List CompactSyntaxTask)
    (output : List Nat) :
    (compactFormulaNegationStep^[compactFormulaTaskSteps formula])
        ((compactArithmeticFormulaTokens formula ++ suffix,
          compactFormulaTask binderArity :: tasks, none), output) =
      ((suffix, tasks, none),
        output ++ compactArithmeticFormulaTokens (∼formula)) := by
  revert suffix tasks output
  let P : (arity : Nat) ->
      LO.FirstOrder.ArithmeticSemiformula Nat arity -> Prop :=
    fun arity formula =>
      ∀ (suffix : List Nat) (tasks : List CompactSyntaxTask)
        (output : List Nat),
        (compactFormulaNegationStep^[compactFormulaTaskSteps formula])
            ((compactArithmeticFormulaTokens formula ++ suffix,
              compactFormulaTask arity :: tasks, none), output) =
          ((suffix, tasks, none),
            output ++ compactArithmeticFormulaTokens (∼formula))
  change P binderArity formula
  induction formula with
  | @rel formulaArity relationArity relationSymbol arguments =>
      intro suffix tasks output
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat formulaArity) :=
        List.ofFn arguments
      have hfirst :
          (compactFormulaNegationStep^[1])
              ((compactArithmeticFormulaTokens
                    (Semiformula.rel relationSymbol arguments) ++ suffix,
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
          compactFormulaNegationStep_formula_rel relationSymbol arguments
            suffix output tasks
      have hterms := compactFormulaNegationTermList_execute terms suffix tasks
        (output ++ [1, relationArity, Encodable.encode relationSymbol])
      have hrun := compactFormulaNegation_iterate_trans hfirst hterms
      have hsteps :
          compactFormulaTaskSteps
              (Semiformula.rel relationSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactFormulaTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have htermsTokens : compactTermListTokens terms =
          (List.ofFn fun index =>
            compactArithmeticTermTokens (arguments index)).flatten :=
        compactTermListTokens_ofFn arguments
      rw [htermsTokens] at hrun
      simpa [compactArithmeticFormulaTokens, List.append_assoc] using hrun
  | @nrel formulaArity relationArity relationSymbol arguments =>
      intro suffix tasks output
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat formulaArity) :=
        List.ofFn arguments
      have hfirst :
          (compactFormulaNegationStep^[1])
              ((compactArithmeticFormulaTokens
                    (Semiformula.nrel relationSymbol arguments) ++ suffix,
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
          compactFormulaNegationStep_formula_nrel relationSymbol arguments
            suffix output tasks
      have hterms := compactFormulaNegationTermList_execute terms suffix tasks
        (output ++ [0, relationArity, Encodable.encode relationSymbol])
      have hrun := compactFormulaNegation_iterate_trans hfirst hterms
      have hsteps :
          compactFormulaTaskSteps
              (Semiformula.nrel relationSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactFormulaTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      have htermsTokens : compactTermListTokens terms =
          (List.ofFn fun index =>
            compactArithmeticTermTokens (arguments index)).flatten := by
        exact compactTermListTokens_ofFn arguments
      rw [htermsTokens] at hrun
      simpa [compactArithmeticFormulaTokens, List.append_assoc] using hrun
  | @verum formulaArity =>
      intro suffix tasks output
      simpa only [compactFormulaTaskSteps, Function.iterate_one,
        compactArithmeticFormulaTokens, Semiformula.neg_eq,
        Semiformula.neg] using
          (compactFormulaNegationStep_formula_verum
            (binderArity := formulaArity) suffix output tasks)
  | @falsum formulaArity =>
      intro suffix tasks output
      simpa only [compactFormulaTaskSteps, Function.iterate_one,
        compactArithmeticFormulaTokens, Semiformula.neg_eq,
        Semiformula.neg] using
          (compactFormulaNegationStep_formula_falsum
            (binderArity := formulaArity) suffix output tasks)
  | @and formulaArity left right ihLeft ihRight =>
      intro suffix tasks output
      have hone :
          (compactFormulaNegationStep^[1])
              ((compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none), output) =
            ((compactArithmeticFormulaTokens left ++
                (compactArithmeticFormulaTokens right ++ suffix),
              compactFormulaTask formulaArity ::
                compactFormulaTask formulaArity :: tasks,
              none), output ++ [5]) := by
        simpa [Function.iterate_one, List.append_assoc] using
          compactFormulaNegationStep_formula_and left right suffix output tasks
      have hleft := ihLeft
        (compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask formulaArity :: tasks) (output ++ [5])
      have hright := ihRight suffix tasks
        (output ++ [5] ++ compactArithmeticFormulaTokens (∼left))
      have hfirst := compactFormulaNegation_iterate_trans hone hleft
      have hrun := compactFormulaNegation_iterate_trans hfirst hright
      change
        (compactFormulaNegationStep^[compactFormulaTaskSteps (left ⋏ right)])
            ((compactArithmeticFormulaTokens (left ⋏ right) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none), output) =
          ((suffix, tasks, none),
            output ++ compactArithmeticFormulaTokens (∼(left ⋏ right)))
      simpa [compactFormulaTaskSteps, compactArithmeticFormulaTokens,
        List.append_assoc] using hrun
  | @or formulaArity left right ihLeft ihRight =>
      intro suffix tasks output
      have hone :
          (compactFormulaNegationStep^[1])
              ((compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none), output) =
            ((compactArithmeticFormulaTokens left ++
                (compactArithmeticFormulaTokens right ++ suffix),
              compactFormulaTask formulaArity ::
                compactFormulaTask formulaArity :: tasks,
              none), output ++ [4]) := by
        simpa [Function.iterate_one, List.append_assoc] using
          compactFormulaNegationStep_formula_or left right suffix output tasks
      have hleft := ihLeft
        (compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask formulaArity :: tasks) (output ++ [4])
      have hright := ihRight suffix tasks
        (output ++ [4] ++ compactArithmeticFormulaTokens (∼left))
      have hfirst := compactFormulaNegation_iterate_trans hone hleft
      have hrun := compactFormulaNegation_iterate_trans hfirst hright
      change
        (compactFormulaNegationStep^[compactFormulaTaskSteps (left ⋎ right)])
            ((compactArithmeticFormulaTokens (left ⋎ right) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none), output) =
          ((suffix, tasks, none),
            output ++ compactArithmeticFormulaTokens (∼(left ⋎ right)))
      simpa [compactFormulaTaskSteps, compactArithmeticFormulaTokens,
        List.append_assoc] using hrun
  | @all formulaArity body ih =>
      intro suffix tasks output
      have hone :
          (compactFormulaNegationStep^[1])
              ((compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none), output) =
            ((compactArithmeticFormulaTokens body ++ suffix,
              compactFormulaTask (formulaArity + 1) :: tasks, none),
              output ++ [7]) := by
        simpa [Function.iterate_one] using
          compactFormulaNegationStep_formula_all body suffix output tasks
      have hbody := ih suffix tasks (output ++ [7])
      have hrun := compactFormulaNegation_iterate_trans hone hbody
      change
        (compactFormulaNegationStep^[compactFormulaTaskSteps (∀⁰ body)])
            ((compactArithmeticFormulaTokens (∀⁰ body) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none), output) =
          ((suffix, tasks, none),
            output ++ compactArithmeticFormulaTokens (∼(∀⁰ body)))
      simpa [compactFormulaTaskSteps, compactArithmeticFormulaTokens,
        List.append_assoc] using hrun
  | @exs formulaArity body ih =>
      intro suffix tasks output
      have hone :
          (compactFormulaNegationStep^[1])
              ((compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none), output) =
            ((compactArithmeticFormulaTokens body ++ suffix,
              compactFormulaTask (formulaArity + 1) :: tasks, none),
              output ++ [6]) := by
        simpa [Function.iterate_one] using
          compactFormulaNegationStep_formula_exs body suffix output tasks
      have hbody := ih suffix tasks (output ++ [6])
      have hrun := compactFormulaNegation_iterate_trans hone hbody
      change
        (compactFormulaNegationStep^[compactFormulaTaskSteps (∃⁰ body)])
            ((compactArithmeticFormulaTokens (∃⁰ body) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none), output) =
          ((suffix, tasks, none),
            output ++ compactArithmeticFormulaTokens (∼(∃⁰ body)))
      simpa [compactFormulaTaskSteps, compactArithmeticFormulaTokens,
        List.append_assoc] using hrun

theorem compactFormulaNegationTokenTransform_canonical_append
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (suffix : List Nat) :
    compactFormulaNegationTokenTransform binderArity
        (compactArithmeticFormulaTokens formula ++ suffix) =
      some (compactArithmeticFormulaTokens (∼formula), suffix) := by
  let tokens := compactArithmeticFormulaTokens formula ++ suffix
  let negatedTokens := compactArithmeticFormulaTokens (∼formula)
  let used := compactFormulaTaskSteps formula + 1
  have htask := compactFormulaNegationFormulaTask_execute formula suffix [] []
  have hfinish :
      (compactFormulaNegationStep^[used])
          ((tokens, [compactFormulaTask binderArity], none), []) =
        ((suffix, [], some (some suffix)), negatedTokens) := by
    apply compactFormulaNegation_iterate_trans htask
    simp [Function.iterate_one, negatedTokens]
  have hformula := compactFormulaTaskSteps_le_tokenLength formula
  have hinputLength :
      (compactArithmeticFormulaTokens formula).length <= tokens.length := by
    simp [tokens]
  have hfuelLength := compactSyntaxRunFuelBound_length_add_one tokens
  have hused : used <= compactSyntaxRunFuelBound tokens := by
    omega
  obtain ⟨extra, hfuel⟩ := exists_add_of_le hused
  have hrun :
      (compactFormulaNegationStep^[compactSyntaxRunFuelBound tokens])
          ((tokens, [compactFormulaTask binderArity], none), []) =
        ((suffix, [], some (some suffix)), negatedTokens) := by
    rw [hfuel]
    exact compactFormulaNegation_iterate_trans hfinish
      (compactFormulaNegationStep_iterate_done extra suffix []
        (some suffix) negatedTokens)
  simp [compactFormulaNegationTokenTransform, compactFormulaNegationRun,
    compactFormulaNegationInitialState, compactFormulaParserInitialState,
    compactFormulaNegationStateOutput, tokens, negatedTokens, hrun]

#print axioms compactNegationFormulaTag_primrec
#print axioms compactNegateConsumedFormulaHeader_primrec
#print axioms compactSyntaxCurrentTaskKind_primrec
#print axioms compactFormulaNegationEmission_primrec
#print axioms compactFormulaNegationStep_primrec
#print axioms compactFormulaNegationRun_primrec
#print axioms compactFormulaNegationTokenTransform_primrec
#print axioms compactFormulaNegationStep_term_func
#print axioms compactFormulaNegationStep_formula_rel
#print axioms compactFormulaNegationStep_formula_and
#print axioms compactFormulaNegationTermTask_execute
#print axioms compactFormulaNegationTermList_execute
#print axioms compactFormulaNegationFormulaTask_execute
#print axioms compactFormulaNegationTokenTransform_canonical_append

end FoundationCompactNumericFormulaNegation
