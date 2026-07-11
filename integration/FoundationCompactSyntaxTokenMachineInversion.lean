import integration.FoundationCompactSyntaxTokenMachine

/-!
# Exact inversion for the numeric compact-syntax parser

The numeric parser stores only natural-number tokens.  This file gives its
states a typed semantics and proves the backward invariant needed to rule out
successful malformed token trees.  No raw Goedel code is reconstructed.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationCompactSyntaxTokenMachineInversion

open FoundationCompactArithmeticSymbolCode
open FoundationCompactSyntaxTokenMachine

inductive CompactSyntaxTasksRealize :
    List CompactSyntaxTask -> List Nat -> List Nat -> Prop
  | nil (suffix : List Nat) :
      CompactSyntaxTasksRealize [] suffix suffix
  | term {binderArity taskPayload : Nat}
      (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
      {middle suffix : List Nat} {tasks : List CompactSyntaxTask}
      (rest : CompactSyntaxTasksRealize tasks middle suffix) :
      CompactSyntaxTasksRealize
        ((0, binderArity, taskPayload) :: tasks)
        (compactArithmeticTermTokens term ++ middle) suffix
  | formula {binderArity taskPayload : Nat}
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
      {middle suffix : List Nat} {tasks : List CompactSyntaxTask}
      (rest : CompactSyntaxTasksRealize tasks middle suffix) :
      CompactSyntaxTasksRealize
        ((1, binderArity, taskPayload) :: tasks)
        (compactArithmeticFormulaTokens formula ++ middle) suffix
  | repeatTerm {binderArity count : Nat}
      (terms : Fin count ->
        LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
      {middle suffix : List Nat} {tasks : List CompactSyntaxTask}
      (rest : CompactSyntaxTasksRealize tasks middle suffix) :
      CompactSyntaxTasksRealize
        (compactRepeatTermTask binderArity count :: tasks)
        ((List.ofFn fun index =>
          compactArithmeticTermTokens (terms index)).flatten ++ middle)
        suffix

def CompactSyntaxStateRealizes
    (state : CompactSyntaxParserState) (suffix : List Nat) : Prop :=
  match state.2.2 with
  | none => CompactSyntaxTasksRealize state.2.1 state.1 suffix
  | some none => False
  | some (some output) => output = suffix

@[simp] theorem compactSyntaxStateRealizes_running
    (tokens suffix : List Nat) (tasks : List CompactSyntaxTask) :
    CompactSyntaxStateRealizes (tokens, tasks, none) suffix <->
      CompactSyntaxTasksRealize tasks tokens suffix := by
  rfl

@[simp] theorem compactSyntaxStateRealizes_failure
    (tokens suffix : List Nat) (tasks : List CompactSyntaxTask) :
    ¬ CompactSyntaxStateRealizes
      (tokens, tasks, some none) suffix := by
  exact fun h => h

@[simp] theorem compactSyntaxStateRealizes_success
    (tokens output suffix : List Nat) (tasks : List CompactSyntaxTask) :
    CompactSyntaxStateRealizes
        (tokens, tasks, some (some output)) suffix <->
      output = suffix := by
  rfl

@[simp] theorem compactSyntaxStateRealizes_continue
    (tokens suffix : List Nat) (tasks : List CompactSyntaxTask) :
    CompactSyntaxStateRealizes
        (compactSyntaxContinue tokens tasks) suffix <->
      CompactSyntaxTasksRealize tasks tokens suffix := by
  rfl

@[simp] theorem compactSyntaxStateRealizes_failedState
    (tokens suffix : List Nat) (tasks : List CompactSyntaxTask) :
    ¬ CompactSyntaxStateRealizes
      (compactSyntaxFailure tokens tasks) suffix := by
  exact fun h => h

theorem arithmeticFuncCodeValid_exists_symbol
    {arity code : Nat} (hvalid : ArithmeticFuncCodeValid arity code) :
    exists symbol : (ℒₒᵣ : LO.FirstOrder.Language).Func arity,
      Encodable.encode symbol = code := by
  have hne :
      (Encodable.decode₂ _ code :
        Option ((ℒₒᵣ : LO.FirstOrder.Language).Func arity)) ≠ none :=
    (arithmeticFuncCodeValid_iff_decode₂_ne_none arity code).1 hvalid
  cases hdecode :
      (Encodable.decode₂ _ code :
        Option ((ℒₒᵣ : LO.FirstOrder.Language).Func arity)) with
  | none => exact False.elim (hne hdecode)
  | some symbol =>
      exact ⟨symbol, Encodable.decode₂_eq_some.mp hdecode⟩

theorem arithmeticRelCodeValid_exists_symbol
    {arity code : Nat} (hvalid : ArithmeticRelCodeValid arity code) :
    exists symbol : (ℒₒᵣ : LO.FirstOrder.Language).Rel arity,
      Encodable.encode symbol = code := by
  have hne :
      (Encodable.decode₂ _ code :
        Option ((ℒₒᵣ : LO.FirstOrder.Language).Rel arity)) ≠ none :=
    (arithmeticRelCodeValid_iff_decode₂_ne_none arity code).1 hvalid
  cases hdecode :
      (Encodable.decode₂ _ code :
        Option ((ℒₒᵣ : LO.FirstOrder.Language).Rel arity)) with
  | none => exact False.elim (hne hdecode)
  | some symbol =>
      exact ⟨symbol, Encodable.decode₂_eq_some.mp hdecode⟩

theorem compactTermTokenStep_realizes_backward
    (binderArity taskPayload : Nat) (tokens suffix : List Nat)
    (tasks : List CompactSyntaxTask)
    (hnext : CompactSyntaxStateRealizes
      (compactTermTokenStep (binderArity, tokens, tasks)) suffix) :
    CompactSyntaxTasksRealize
      ((0, binderArity, taskPayload) :: tasks) tokens suffix := by
  cases tokens with
  | nil =>
      exfalso
      simpa [compactTermTokenStep, compactTokenAt, compactSyntaxFailure,
        CompactSyntaxStateRealizes] using hnext
  | cons tag tail =>
      cases tail with
      | nil =>
          exfalso
          simpa [compactTermTokenStep, compactTokenAt,
            compactSyntaxFailure, CompactSyntaxStateRealizes] using hnext
      | cons argument rest =>
          by_cases htagZero : tag = 0
          · subst tag
            by_cases hbound : argument < binderArity
            · have hrest :
                  CompactSyntaxTasksRealize tasks rest suffix := by
                simpa [compactTermTokenStep, compactTokenAt, hbound,
                  compactSyntaxContinue, CompactSyntaxStateRealizes]
                  using hnext
              simpa [compactArithmeticTermTokens] using
                CompactSyntaxTasksRealize.term
                  (taskPayload := taskPayload)
                  (#(Fin.mk argument hbound) :
                    LO.FirstOrder.ArithmeticSemiterm Nat binderArity) hrest
            · exfalso
              simpa [compactTermTokenStep, compactTokenAt, hbound,
                compactSyntaxFailure, CompactSyntaxStateRealizes] using hnext
          · by_cases htagOne : tag = 1
            · subst tag
              have hrest :
                  CompactSyntaxTasksRealize tasks rest suffix := by
                simpa [compactTermTokenStep, compactTokenAt,
                  compactSyntaxContinue, CompactSyntaxStateRealizes]
                  using hnext
              simpa [compactArithmeticTermTokens] using
                CompactSyntaxTasksRealize.term
                  (taskPayload := taskPayload)
                  (&argument :
                    LO.FirstOrder.ArithmeticSemiterm Nat binderArity) hrest
            · by_cases htagTwo : tag = 2
              · subst tag
                cases rest with
                | nil =>
                    exfalso
                    simpa [compactTermTokenStep, compactTokenAt,
                      compactSyntaxFailure, CompactSyntaxStateRealizes]
                      using hnext
                | cons functionCode body =>
                    by_cases hvalid :
                        ArithmeticFuncCodeValid argument functionCode
                    · have hrepeat : CompactSyntaxTasksRealize
                          (compactRepeatTermTask binderArity argument :: tasks)
                          body suffix := by
                        simpa [compactTermTokenStep, compactTokenAt, hvalid,
                          compactSyntaxContinue, CompactSyntaxStateRealizes]
                          using hnext
                      cases hrepeat with
                      | repeatTerm arguments restRealizes =>
                          obtain ⟨functionSymbol, hcode⟩ :=
                            arithmeticFuncCodeValid_exists_symbol hvalid
                          subst functionCode
                          simpa [compactArithmeticTermTokens,
                            List.append_assoc] using
                            CompactSyntaxTasksRealize.term
                              (taskPayload := taskPayload)
                              (Semiterm.func functionSymbol arguments)
                              restRealizes
                    · exfalso
                      simpa [compactTermTokenStep, compactTokenAt, hvalid,
                        compactSyntaxFailure, CompactSyntaxStateRealizes]
                        using hnext
              · exfalso
                simpa [compactTermTokenStep, compactTokenAt, htagZero,
                  htagOne, htagTwo, compactSyntaxFailure,
                  CompactSyntaxStateRealizes] using hnext

theorem compactFormulaTokenStep_realizes_backward
    (binderArity taskPayload : Nat) (tokens suffix : List Nat)
    (tasks : List CompactSyntaxTask)
    (hnext : CompactSyntaxStateRealizes
      (compactFormulaTokenStep (binderArity, tokens, tasks)) suffix) :
    CompactSyntaxTasksRealize
      ((1, binderArity, taskPayload) :: tasks) tokens suffix := by
  cases tokens with
  | nil =>
      exfalso
      simpa [compactFormulaTokenStep, compactTokenAt,
        compactSyntaxFailure, CompactSyntaxStateRealizes] using hnext
  | cons tag tail =>
      by_cases htagZero : tag = 0
      · subst tag
        cases tail with
        | nil =>
            exfalso
            simpa [compactFormulaTokenStep, compactTokenAt,
              compactSyntaxFailure, CompactSyntaxStateRealizes] using hnext
        | cons relationArity tail =>
            cases tail with
            | nil =>
                exfalso
                simpa [compactFormulaTokenStep, compactTokenAt,
                  compactSyntaxFailure, CompactSyntaxStateRealizes]
                  using hnext
            | cons relationCode body =>
                by_cases hvalid :
                    ArithmeticRelCodeValid relationArity relationCode
                · have hrepeat : CompactSyntaxTasksRealize
                      (compactRepeatTermTask binderArity relationArity ::
                        tasks) body suffix := by
                    simpa [compactFormulaTokenStep, compactTokenAt, hvalid,
                      compactSyntaxContinue, CompactSyntaxStateRealizes]
                      using hnext
                  cases hrepeat with
                  | repeatTerm arguments restRealizes =>
                      obtain ⟨relationSymbol, hcode⟩ :=
                        arithmeticRelCodeValid_exists_symbol hvalid
                      subst relationCode
                      simpa [compactArithmeticFormulaTokens,
                        List.append_assoc] using
                        CompactSyntaxTasksRealize.formula
                          (taskPayload := taskPayload)
                          (Semiformula.rel relationSymbol arguments)
                          restRealizes
                · exfalso
                  simpa [compactFormulaTokenStep, compactTokenAt, hvalid,
                    compactSyntaxFailure, CompactSyntaxStateRealizes]
                    using hnext
      · by_cases htagOne : tag = 1
        · subst tag
          cases tail with
          | nil =>
              exfalso
              simpa [compactFormulaTokenStep, compactTokenAt,
                compactSyntaxFailure, CompactSyntaxStateRealizes] using hnext
          | cons relationArity tail =>
              cases tail with
              | nil =>
                  exfalso
                  simpa [compactFormulaTokenStep, compactTokenAt,
                    compactSyntaxFailure, CompactSyntaxStateRealizes]
                    using hnext
              | cons relationCode body =>
                  by_cases hvalid :
                      ArithmeticRelCodeValid relationArity relationCode
                  · have hrepeat : CompactSyntaxTasksRealize
                        (compactRepeatTermTask binderArity relationArity ::
                          tasks) body suffix := by
                      simpa [compactFormulaTokenStep, compactTokenAt, hvalid,
                        compactSyntaxContinue, CompactSyntaxStateRealizes]
                        using hnext
                    cases hrepeat with
                    | repeatTerm arguments restRealizes =>
                        obtain ⟨relationSymbol, hcode⟩ :=
                          arithmeticRelCodeValid_exists_symbol hvalid
                        subst relationCode
                        simpa [compactArithmeticFormulaTokens,
                          List.append_assoc] using
                          CompactSyntaxTasksRealize.formula
                            (taskPayload := taskPayload)
                            (Semiformula.nrel relationSymbol arguments)
                            restRealizes
                  · exfalso
                    simpa [compactFormulaTokenStep, compactTokenAt, hvalid,
                      compactSyntaxFailure, CompactSyntaxStateRealizes]
                      using hnext
        · by_cases htagTwo : tag = 2
          · subst tag
            have hrest : CompactSyntaxTasksRealize tasks tail suffix := by
              simpa [compactFormulaTokenStep, compactTokenAt,
                compactSyntaxContinue, CompactSyntaxStateRealizes]
                using hnext
            simpa [compactArithmeticFormulaTokens] using
              CompactSyntaxTasksRealize.formula
                (taskPayload := taskPayload)
                (⊤ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
                hrest
          · by_cases htagThree : tag = 3
            · subst tag
              have hrest : CompactSyntaxTasksRealize tasks tail suffix := by
                simpa [compactFormulaTokenStep, compactTokenAt,
                  compactSyntaxContinue, CompactSyntaxStateRealizes]
                  using hnext
              simpa [compactArithmeticFormulaTokens] using
                CompactSyntaxTasksRealize.formula
                  (taskPayload := taskPayload)
                  (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
                  hrest
            · by_cases htagFour : tag = 4
              · subst tag
                have hchildren : CompactSyntaxTasksRealize
                    (compactFormulaTask binderArity ::
                      compactFormulaTask binderArity :: tasks)
                    tail suffix := by
                  simpa [compactFormulaTokenStep, compactTokenAt,
                    compactSyntaxContinue, CompactSyntaxStateRealizes]
                    using hnext
                cases hchildren with
                | formula left hright =>
                    cases hright with
                    | formula right restRealizes =>
                        simpa [compactArithmeticFormulaTokens,
                          List.append_assoc] using
                          CompactSyntaxTasksRealize.formula
                            (taskPayload := taskPayload)
                            (left ⋏ right) restRealizes
              · by_cases htagFive : tag = 5
                · subst tag
                  have hchildren : CompactSyntaxTasksRealize
                      (compactFormulaTask binderArity ::
                        compactFormulaTask binderArity :: tasks)
                      tail suffix := by
                    simpa [compactFormulaTokenStep, compactTokenAt,
                      compactSyntaxContinue, CompactSyntaxStateRealizes]
                      using hnext
                  cases hchildren with
                  | formula left hright =>
                      cases hright with
                      | formula right restRealizes =>
                          simpa [compactArithmeticFormulaTokens,
                            List.append_assoc] using
                            CompactSyntaxTasksRealize.formula
                              (taskPayload := taskPayload)
                              (left ⋎ right) restRealizes
                · by_cases htagSix : tag = 6
                  · subst tag
                    have hbody : CompactSyntaxTasksRealize
                        (compactFormulaTask (binderArity + 1) :: tasks)
                        tail suffix := by
                      simpa [compactFormulaTokenStep, compactTokenAt,
                        compactSyntaxContinue, CompactSyntaxStateRealizes]
                        using hnext
                    cases hbody with
                    | formula body restRealizes =>
                        simpa [compactArithmeticFormulaTokens] using
                          CompactSyntaxTasksRealize.formula
                            (taskPayload := taskPayload)
                            (∀⁰ body) restRealizes
                  · by_cases htagSeven : tag = 7
                    · subst tag
                      have hbody : CompactSyntaxTasksRealize
                          (compactFormulaTask (binderArity + 1) :: tasks)
                          tail suffix := by
                        simpa [compactFormulaTokenStep, compactTokenAt,
                          compactSyntaxContinue, CompactSyntaxStateRealizes]
                          using hnext
                      cases hbody with
                      | formula body restRealizes =>
                          simpa [compactArithmeticFormulaTokens] using
                            CompactSyntaxTasksRealize.formula
                              (taskPayload := taskPayload)
                              (∃⁰ body) restRealizes
                    · exfalso
                      simpa [compactFormulaTokenStep, compactTokenAt,
                        htagZero, htagOne, htagTwo, htagThree, htagFour,
                        htagFive, htagSix, htagSeven, compactSyntaxFailure,
                        CompactSyntaxStateRealizes] using hnext

theorem compactRepeatTermTokenStep_realizes_backward
    (task : CompactSyntaxTask) (tokens suffix : List Nat)
    (tasks : List CompactSyntaxTask)
    (hkind : task.1 = 2)
    (hnext : CompactSyntaxStateRealizes
      (compactRepeatTermTokenStep (task, tokens, tasks)) suffix) :
    CompactSyntaxTasksRealize (task :: tasks) tokens suffix := by
  rcases task with ⟨kind, binderArity, count⟩
  simp only at hkind
  subst kind
  cases count with
  | zero =>
      have hrest : CompactSyntaxTasksRealize tasks tokens suffix := by
        simpa [compactRepeatTermTokenStep, compactSyntaxContinue,
          CompactSyntaxStateRealizes]
          using hnext
      simpa [compactRepeatTermTask] using
        CompactSyntaxTasksRealize.repeatTerm
          (fun index : Fin 0 => Fin.elim0 index) hrest
  | succ count =>
      have hchildren : CompactSyntaxTasksRealize
          (compactTermTask binderArity ::
            compactRepeatTermTask binderArity count :: tasks)
          tokens suffix := by
        simpa [compactRepeatTermTokenStep, compactRepeatTermTask,
          compactSyntaxContinue, CompactSyntaxStateRealizes] using hnext
      cases hchildren with
      | term head htail =>
          cases htail with
          | repeatTerm tail rest =>
              let terms : Fin (count + 1) ->
                  LO.FirstOrder.ArithmeticSemiterm Nat binderArity :=
                Fin.cons head tail
              have htokens :
                  (List.ofFn fun index =>
                    compactArithmeticTermTokens (terms index)).flatten =
                    compactArithmeticTermTokens head ++
                      (List.ofFn fun index =>
                        compactArithmeticTermTokens (tail index)).flatten := by
                simp [terms]
              have hreal :=
                CompactSyntaxTasksRealize.repeatTerm terms rest
              rw [htokens] at hreal
              simpa [compactRepeatTermTask, List.append_assoc] using hreal

theorem compactSyntaxTaskTokenStep_realizes_backward
    (task : CompactSyntaxTask) (tokens suffix : List Nat)
    (tasks : List CompactSyntaxTask)
    (hnext : CompactSyntaxStateRealizes
      (compactSyntaxTaskTokenStep (task, tokens, tasks)) suffix) :
    CompactSyntaxTasksRealize (task :: tasks) tokens suffix := by
  rcases task with ⟨kind, binderArity, count⟩
  by_cases hzero : kind = 0
  · subst kind
    simpa [compactSyntaxTaskTokenStep] using
      compactTermTokenStep_realizes_backward
        binderArity count tokens suffix tasks hnext
  · by_cases hone : kind = 1
    · subst kind
      simpa [compactSyntaxTaskTokenStep] using
        compactFormulaTokenStep_realizes_backward
          binderArity count tokens suffix tasks hnext
    · by_cases htwo : kind = 2
      · subst kind
        exact compactRepeatTermTokenStep_realizes_backward
          (2, binderArity, count) tokens suffix tasks (by rfl) <| by
            simpa [compactSyntaxTaskTokenStep] using hnext
      · exfalso
        simpa [compactSyntaxTaskTokenStep, hzero, hone, htwo] using hnext

theorem compactSyntaxParserStep_realizes_backward
    (state : CompactSyntaxParserState) (suffix : List Nat)
    (hnext : CompactSyntaxStateRealizes
      (compactSyntaxParserStep state) suffix) :
    CompactSyntaxStateRealizes state suffix := by
  rcases state with ⟨tokens, tasks, status⟩
  cases status with
  | some result =>
      simpa [compactSyntaxParserStep, CompactSyntaxStateRealizes] using hnext
  | none =>
      cases tasks with
      | nil =>
          have htokens : tokens = suffix := by
            simpa [compactSyntaxParserStep, compactSyntaxRunningStep,
              CompactSyntaxStateRealizes] using hnext
          subst tokens
          exact CompactSyntaxTasksRealize.nil suffix
      | cons task tasks =>
          simpa [compactSyntaxParserStep, compactSyntaxRunningStep,
            CompactSyntaxStateRealizes] using
            compactSyntaxTaskTokenStep_realizes_backward
              task tokens suffix tasks <| by
                simpa [compactSyntaxParserStep, compactSyntaxRunningStep]
                  using hnext

theorem compactSyntaxParser_iterate_realizes_backward
    (fuel : Nat) (state : CompactSyntaxParserState) (suffix : List Nat)
    (hfinal : CompactSyntaxStateRealizes
      ((compactSyntaxParserStep^[fuel]) state) suffix) :
    CompactSyntaxStateRealizes state suffix := by
  induction fuel generalizing state with
  | zero => exact hfinal
  | succ fuel ih =>
      rw [Function.iterate_succ_apply] at hfinal
      exact compactSyntaxParserStep_realizes_backward state suffix
        (ih (compactSyntaxParserStep state) hfinal)

theorem compactSyntaxParserStateOutput_realizes
    (state : CompactSyntaxParserState) (suffix : List Nat)
    (houtput : compactSyntaxParserStateOutput state = some suffix) :
    CompactSyntaxStateRealizes state suffix := by
  rcases state with ⟨tokens, tasks, status⟩
  cases status with
  | none => simp [compactSyntaxParserStateOutput] at houtput
  | some result =>
      cases result with
      | none => simp [compactSyntaxParserStateOutput] at houtput
      | some output =>
          simpa [compactSyntaxParserStateOutput,
            CompactSyntaxStateRealizes] using houtput

theorem compactTermTokenParser_success_iff
    (binderArity : Nat) (tokens suffix : List Nat) :
    compactTermTokenParser binderArity tokens = some suffix <->
      exists term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity,
        tokens = compactArithmeticTermTokens term ++ suffix := by
  constructor
  · intro hparser
    have hfinal := compactSyntaxParserStateOutput_realizes
      (compactTermTokenParserRun binderArity tokens) suffix hparser
    have hinitial := compactSyntaxParser_iterate_realizes_backward
      (compactSyntaxRunFuelBound tokens)
      (compactTermParserInitialState binderArity tokens) suffix hfinal
    change CompactSyntaxTasksRealize
      [compactTermTask binderArity] tokens suffix at hinitial
    cases hinitial with
    | term term rest =>
        cases rest
        exact ⟨term, rfl⟩
  · rintro ⟨term, rfl⟩
    exact compactTermTokenParser_canonical_append term suffix

theorem compactFormulaTokenParser_success_iff
    (binderArity : Nat) (tokens suffix : List Nat) :
    compactFormulaTokenParser binderArity tokens = some suffix <->
      exists formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity,
        tokens = compactArithmeticFormulaTokens formula ++ suffix := by
  constructor
  · intro hparser
    have hfinal := compactSyntaxParserStateOutput_realizes
      (compactFormulaTokenParserRun binderArity tokens) suffix hparser
    have hinitial := compactSyntaxParser_iterate_realizes_backward
      (compactSyntaxRunFuelBound tokens)
      (compactFormulaParserInitialState binderArity tokens) suffix hfinal
    change CompactSyntaxTasksRealize
      [compactFormulaTask binderArity] tokens suffix at hinitial
    cases hinitial with
    | formula formula rest =>
        cases rest
        exact ⟨formula, rfl⟩
  · rintro ⟨formula, rfl⟩
    exact compactFormulaTokenParser_canonical_append formula suffix

#print axioms compactTermTokenParser_success_iff
#print axioms compactFormulaTokenParser_success_iff

end FoundationCompactSyntaxTokenMachineInversion
