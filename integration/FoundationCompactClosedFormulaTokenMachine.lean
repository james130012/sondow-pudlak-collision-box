import integration.FoundationCompactSyntaxTokenMachineInversion

/-!
# Numeric closed-formula token machine

The ordinary syntax parser accepts propositions with free variables.  A PA
axiom leaf, however, stores a sentence.  This machine follows the same compact
grammar while rejecting the free-variable term constructor in every term
position.  Its state remains a list of natural tokens and a bounded task stack.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationCompactClosedFormulaTokenMachine

open FoundationCompactArithmeticSymbolCode
open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTokenMachineInversion

def compactClosedTermTokenStep
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
      compactSyntaxFailure tokens tasks
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

def compactClosedSyntaxTaskTokenStep
    (input : CompactTaskBranchInput) : CompactSyntaxParserState :=
  let kind := input.1.1
  let binderArity := input.1.2.1
  let tokens := input.2.1
  let tasks := input.2.2
  if kind = 0 then
    compactClosedTermTokenStep (binderArity, tokens, tasks)
  else if kind = 1 then
    compactFormulaTokenStep (binderArity, tokens, tasks)
  else if kind = 2 then
    compactRepeatTermTokenStep input
  else
    compactSyntaxFailure tokens tasks

def compactClosedSyntaxRunningStep
    (state : CompactSyntaxParserState) : CompactSyntaxParserState :=
  match state.2.1 with
  | [] => (state.1, [], some (some state.1))
  | task :: tasks =>
      compactClosedSyntaxTaskTokenStep (task, state.1, tasks)

def compactClosedSyntaxParserStep
    (state : CompactSyntaxParserState) : CompactSyntaxParserState :=
  if state.2.2.isSome then state else compactClosedSyntaxRunningStep state

def compactClosedFormulaTokenParserRun
    (binderArity : Nat) (tokens : List Nat) : CompactSyntaxParserState :=
  (compactClosedSyntaxParserStep^[compactSyntaxRunFuelBound tokens])
    (compactFormulaParserInitialState binderArity tokens)

def compactClosedFormulaTokenParser
    (binderArity : Nat) (tokens : List Nat) : Option (List Nat) :=
  compactSyntaxParserStateOutput
    (compactClosedFormulaTokenParserRun binderArity tokens)

theorem compactClosedTermTokenStep_primrec :
    Primrec compactClosedTermTokenStep := by
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
  have hbvarSuccess : Primrec
      (fun input : CompactTermBranchInput =>
        compactSyntaxContinue (input.2.1.drop 2) input.2.2) :=
    compactSyntaxContinue_primrec.comp hdropTwo htasks
  have hrepeat : Primrec
      (fun input : CompactTermBranchInput =>
        compactRepeatTermTask input.1
          (compactTokenAt 1 input.2.1)) :=
    compactRepeatTermTask_primrec.comp harity hargument
  have hfunctionTasks : Primrec
      (fun input : CompactTermBranchInput =>
        compactRepeatTermTask input.1
          (compactTokenAt 1 input.2.1) :: input.2.2) :=
    Primrec.list_cons.comp hrepeat htasks
  have hfunctionSuccess : Primrec
      (fun input : CompactTermBranchInput =>
        compactSyntaxContinue (input.2.1.drop 3)
          (compactRepeatTermTask input.1
            (compactTokenAt 1 input.2.1) :: input.2.2)) :=
    compactSyntaxContinue_primrec.comp hdropThree hfunctionTasks
  exact
    (Primrec.ite htwo
      (Primrec.ite htagZero
        (Primrec.ite hbvar hbvarSuccess hfailure)
        (Primrec.ite htagOne hfailure
          (Primrec.ite htagTwo
            (Primrec.ite hthree
              (Primrec.ite hfunction hfunctionSuccess hfailure)
              hfailure)
            hfailure)))
      hfailure).of_eq fun input => by
        simp only [compactClosedTermTokenStep]

theorem compactClosedSyntaxTaskTokenStep_primrec :
    Primrec compactClosedSyntaxTaskTokenStep := by
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
        compactClosedTermTokenStep
          (input.1.2.1, input.2.1, input.2.2)) :=
    compactClosedTermTokenStep_primrec.comp hbranchInput
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
            simp only [compactClosedSyntaxTaskTokenStep]

theorem compactClosedSyntaxRunningStep_primrec :
    Primrec compactClosedSyntaxRunningStep := by
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
      (fun state : CompactSyntaxParserState => some (some state.1)) :=
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
        compactClosedSyntaxTaskTokenStep
          (state.2.1.head?.getD (compactTermTask 0),
            state.1, state.2.1.tail)) :=
    compactClosedSyntaxTaskTokenStep_primrec.comp hinput
  exact
    (Primrec.ite hempty hsuccess hbranch).of_eq fun state => by
      cases htasksValue : state.2.1 <;>
        simp [compactClosedSyntaxRunningStep, htasksValue]

theorem compactClosedSyntaxParserStep_primrec :
    Primrec compactClosedSyntaxParserStep := by
  have hstatus : Primrec
      (fun state : CompactSyntaxParserState => state.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hdone : Primrec
      (fun state : CompactSyntaxParserState => state.2.2.isSome) :=
    Primrec.option_isSome.comp hstatus
  exact
    (Primrec.cond hdone Primrec.id
      compactClosedSyntaxRunningStep_primrec).of_eq fun state => by
        cases hstatusValue : state.2.2 <;>
          simp [compactClosedSyntaxParserStep, hstatusValue]

theorem compactClosedFormulaTokenParserRun_primrec :
    Primrec₂ compactClosedFormulaTokenParserRun := by
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
        compactClosedSyntaxParserStep state) :=
    (compactClosedSyntaxParserStep_primrec.comp Primrec.snd).to₂
  exact
    (Primrec.nat_iterate hfuel hinitial hstep).of_eq
      fun input => by rfl

theorem compactClosedFormulaTokenParser_primrec :
    Primrec₂ compactClosedFormulaTokenParser := by
  exact
    (compactSyntaxParserStateOutput_primrec.comp₂
      compactClosedFormulaTokenParserRun_primrec).of_eq
      fun binderArity tokens => by rfl

inductive CompactClosedSyntaxTasksRealize :
    List CompactSyntaxTask -> List Nat -> List Nat -> Prop
  | nil (suffix : List Nat) :
      CompactClosedSyntaxTasksRealize [] suffix suffix
  | term {binderArity taskPayload : Nat}
      (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
      (closed : term.freeVariables = ∅)
      {middle suffix : List Nat} {tasks : List CompactSyntaxTask}
      (rest : CompactClosedSyntaxTasksRealize tasks middle suffix) :
      CompactClosedSyntaxTasksRealize
        ((0, binderArity, taskPayload) :: tasks)
        (compactArithmeticTermTokens term ++ middle) suffix
  | formula {binderArity taskPayload : Nat}
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
      (closed : formula.freeVariables = ∅)
      {middle suffix : List Nat} {tasks : List CompactSyntaxTask}
      (rest : CompactClosedSyntaxTasksRealize tasks middle suffix) :
      CompactClosedSyntaxTasksRealize
        ((1, binderArity, taskPayload) :: tasks)
        (compactArithmeticFormulaTokens formula ++ middle) suffix
  | repeatTerm {binderArity count : Nat}
      (terms : Fin count ->
        LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
      (closed : ∀ index, (terms index).freeVariables = ∅)
      {middle suffix : List Nat} {tasks : List CompactSyntaxTask}
      (rest : CompactClosedSyntaxTasksRealize tasks middle suffix) :
      CompactClosedSyntaxTasksRealize
        (compactRepeatTermTask binderArity count :: tasks)
        ((List.ofFn fun index =>
          compactArithmeticTermTokens (terms index)).flatten ++ middle)
        suffix

def CompactClosedSyntaxStateRealizes
    (state : CompactSyntaxParserState) (suffix : List Nat) : Prop :=
  match state.2.2 with
  | none => CompactClosedSyntaxTasksRealize state.2.1 state.1 suffix
  | some none => False
  | some (some output) => output = suffix

@[simp] theorem compactClosedSyntaxStateRealizes_continue
    (tokens suffix : List Nat) (tasks : List CompactSyntaxTask) :
    CompactClosedSyntaxStateRealizes
        (compactSyntaxContinue tokens tasks) suffix <->
      CompactClosedSyntaxTasksRealize tasks tokens suffix := by
  rfl

@[simp] theorem compactClosedSyntaxStateRealizes_failure
    (tokens suffix : List Nat) (tasks : List CompactSyntaxTask) :
    ¬ CompactClosedSyntaxStateRealizes
      (compactSyntaxFailure tokens tasks) suffix := by
  exact fun h => h

theorem compactClosedTermTokenStep_realizes_backward
    (binderArity taskPayload : Nat) (tokens suffix : List Nat)
    (tasks : List CompactSyntaxTask)
    (hnext : CompactClosedSyntaxStateRealizes
      (compactClosedTermTokenStep (binderArity, tokens, tasks)) suffix) :
    CompactClosedSyntaxTasksRealize
      ((0, binderArity, taskPayload) :: tasks) tokens suffix := by
  cases tokens with
  | nil =>
      exfalso
      simpa [compactClosedTermTokenStep, compactTokenAt,
        compactSyntaxFailure, CompactClosedSyntaxStateRealizes] using hnext
  | cons tag tail =>
      cases tail with
      | nil =>
          exfalso
          simpa [compactClosedTermTokenStep, compactTokenAt,
            compactSyntaxFailure, CompactClosedSyntaxStateRealizes]
            using hnext
      | cons argument rest =>
          by_cases htagZero : tag = 0
          · subst tag
            by_cases hbound : argument < binderArity
            · have hrest :
                  CompactClosedSyntaxTasksRealize tasks rest suffix := by
                simpa [compactClosedTermTokenStep, compactTokenAt, hbound,
                  compactSyntaxContinue, CompactClosedSyntaxStateRealizes]
                  using hnext
              simpa [compactArithmeticTermTokens] using
                CompactClosedSyntaxTasksRealize.term
                  (taskPayload := taskPayload)
                  (#(Fin.mk argument hbound) :
                    LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
                  (by simp) hrest
            · exfalso
              simpa [compactClosedTermTokenStep, compactTokenAt, hbound,
                compactSyntaxFailure, CompactClosedSyntaxStateRealizes]
                using hnext
          · by_cases htagOne : tag = 1
            · exfalso
              simpa [compactClosedTermTokenStep, compactTokenAt, htagZero,
                htagOne, compactSyntaxFailure,
                CompactClosedSyntaxStateRealizes] using hnext
            · by_cases htagTwo : tag = 2
              · subst tag
                cases rest with
                | nil =>
                    exfalso
                    simpa [compactClosedTermTokenStep, compactTokenAt,
                      compactSyntaxFailure, CompactClosedSyntaxStateRealizes]
                      using hnext
                | cons functionCode body =>
                    by_cases hvalid :
                        ArithmeticFuncCodeValid argument functionCode
                    · have hrepeat : CompactClosedSyntaxTasksRealize
                          (compactRepeatTermTask binderArity argument :: tasks)
                          body suffix := by
                        simpa [compactClosedTermTokenStep, compactTokenAt,
                          hvalid, compactSyntaxContinue,
                          CompactClosedSyntaxStateRealizes] using hnext
                      cases hrepeat with
                      | repeatTerm arguments harguments restRealizes =>
                          obtain ⟨functionSymbol, hcode⟩ :=
                            arithmeticFuncCodeValid_exists_symbol hvalid
                          subst functionCode
                          have hclosed :
                              (Semiterm.func functionSymbol arguments :
                                LO.FirstOrder.ArithmeticSemiterm Nat
                                  binderArity).freeVariables = ∅ := by
                            simp [Semiterm.freeVariables_func,
                              Finset.biUnion_eq_empty, harguments]
                          simpa [compactArithmeticTermTokens,
                            List.append_assoc] using
                            CompactClosedSyntaxTasksRealize.term
                              (taskPayload := taskPayload)
                              (Semiterm.func functionSymbol arguments)
                              hclosed restRealizes
                    · exfalso
                      simpa [compactClosedTermTokenStep, compactTokenAt,
                        hvalid, compactSyntaxFailure,
                        CompactClosedSyntaxStateRealizes] using hnext
              · exfalso
                simpa [compactClosedTermTokenStep, compactTokenAt, htagZero,
                  htagOne, htagTwo, compactSyntaxFailure,
                  CompactClosedSyntaxStateRealizes] using hnext

theorem compactClosedFormulaTokenStep_realizes_backward
    (binderArity taskPayload : Nat) (tokens suffix : List Nat)
    (tasks : List CompactSyntaxTask)
    (hnext : CompactClosedSyntaxStateRealizes
      (compactFormulaTokenStep (binderArity, tokens, tasks)) suffix) :
    CompactClosedSyntaxTasksRealize
      ((1, binderArity, taskPayload) :: tasks) tokens suffix := by
  cases tokens with
  | nil =>
      exfalso
      simpa [compactFormulaTokenStep, compactTokenAt,
        compactSyntaxFailure, CompactClosedSyntaxStateRealizes] using hnext
  | cons tag tail =>
      by_cases htagZero : tag = 0
      · subst tag
        cases tail with
        | nil =>
            exfalso
            simpa [compactFormulaTokenStep, compactTokenAt,
              compactSyntaxFailure, CompactClosedSyntaxStateRealizes]
              using hnext
        | cons relationArity tail =>
            cases tail with
            | nil =>
                exfalso
                simpa [compactFormulaTokenStep, compactTokenAt,
                  compactSyntaxFailure, CompactClosedSyntaxStateRealizes]
                  using hnext
            | cons relationCode body =>
                by_cases hvalid :
                    ArithmeticRelCodeValid relationArity relationCode
                · have hrepeat : CompactClosedSyntaxTasksRealize
                      (compactRepeatTermTask binderArity relationArity ::
                        tasks) body suffix := by
                    simpa [compactFormulaTokenStep, compactTokenAt, hvalid,
                      compactSyntaxContinue, CompactClosedSyntaxStateRealizes]
                      using hnext
                  cases hrepeat with
                  | repeatTerm arguments harguments restRealizes =>
                      obtain ⟨relationSymbol, hcode⟩ :=
                        arithmeticRelCodeValid_exists_symbol hvalid
                      subst relationCode
                      have hclosed :
                          (Semiformula.rel relationSymbol arguments :
                            LO.FirstOrder.ArithmeticSemiformula Nat
                              binderArity).freeVariables = ∅ := by
                        simp [Semiformula.freeVariables_rel,
                          Finset.biUnion_eq_empty, harguments]
                      simpa [compactArithmeticFormulaTokens,
                        List.append_assoc] using
                        CompactClosedSyntaxTasksRealize.formula
                          (taskPayload := taskPayload)
                          (Semiformula.rel relationSymbol arguments)
                          hclosed restRealizes
                · exfalso
                  simpa [compactFormulaTokenStep, compactTokenAt, hvalid,
                    compactSyntaxFailure, CompactClosedSyntaxStateRealizes]
                    using hnext
      · by_cases htagOne : tag = 1
        · subst tag
          cases tail with
          | nil =>
              exfalso
              simpa [compactFormulaTokenStep, compactTokenAt,
                compactSyntaxFailure, CompactClosedSyntaxStateRealizes]
                using hnext
          | cons relationArity tail =>
              cases tail with
              | nil =>
                  exfalso
                  simpa [compactFormulaTokenStep, compactTokenAt,
                    compactSyntaxFailure, CompactClosedSyntaxStateRealizes]
                    using hnext
              | cons relationCode body =>
                  by_cases hvalid :
                      ArithmeticRelCodeValid relationArity relationCode
                  · have hrepeat : CompactClosedSyntaxTasksRealize
                        (compactRepeatTermTask binderArity relationArity ::
                          tasks) body suffix := by
                      simpa [compactFormulaTokenStep, compactTokenAt, hvalid,
                        compactSyntaxContinue,
                        CompactClosedSyntaxStateRealizes] using hnext
                    cases hrepeat with
                    | repeatTerm arguments harguments restRealizes =>
                        obtain ⟨relationSymbol, hcode⟩ :=
                          arithmeticRelCodeValid_exists_symbol hvalid
                        subst relationCode
                        have hclosed :
                            (Semiformula.nrel relationSymbol arguments :
                              LO.FirstOrder.ArithmeticSemiformula Nat
                                binderArity).freeVariables = ∅ := by
                          simp [Semiformula.freeVariables_nrel,
                            Finset.biUnion_eq_empty, harguments]
                        simpa [compactArithmeticFormulaTokens,
                          List.append_assoc] using
                          CompactClosedSyntaxTasksRealize.formula
                            (taskPayload := taskPayload)
                            (Semiformula.nrel relationSymbol arguments)
                            hclosed restRealizes
                  · exfalso
                    simpa [compactFormulaTokenStep, compactTokenAt, hvalid,
                      compactSyntaxFailure, CompactClosedSyntaxStateRealizes]
                      using hnext
        · by_cases htagTwo : tag = 2
          · subst tag
            have hrest :
                CompactClosedSyntaxTasksRealize tasks tail suffix := by
              simpa [compactFormulaTokenStep, compactTokenAt,
                compactSyntaxContinue, CompactClosedSyntaxStateRealizes]
                using hnext
            simpa [compactArithmeticFormulaTokens] using
              CompactClosedSyntaxTasksRealize.formula
                (taskPayload := taskPayload)
                (⊤ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
                (by simp) hrest
          · by_cases htagThree : tag = 3
            · subst tag
              have hrest :
                  CompactClosedSyntaxTasksRealize tasks tail suffix := by
                simpa [compactFormulaTokenStep, compactTokenAt,
                  compactSyntaxContinue, CompactClosedSyntaxStateRealizes]
                  using hnext
              simpa [compactArithmeticFormulaTokens] using
                CompactClosedSyntaxTasksRealize.formula
                  (taskPayload := taskPayload)
                  (⊥ : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
                  (by simp) hrest
            · by_cases htagFour : tag = 4
              · subst tag
                have hchildren : CompactClosedSyntaxTasksRealize
                    (compactFormulaTask binderArity ::
                      compactFormulaTask binderArity :: tasks)
                    tail suffix := by
                  simpa [compactFormulaTokenStep, compactTokenAt,
                    compactSyntaxContinue, CompactClosedSyntaxStateRealizes]
                    using hnext
                cases hchildren with
                | formula left hleft hright =>
                    cases hright with
                    | formula right hrightClosed restRealizes =>
                        have hclosed : (left ⋏ right).freeVariables = ∅ := by
                          simp [hleft, hrightClosed]
                        simpa [compactArithmeticFormulaTokens,
                          List.append_assoc] using
                          CompactClosedSyntaxTasksRealize.formula
                            (taskPayload := taskPayload)
                            (left ⋏ right) hclosed restRealizes
              · by_cases htagFive : tag = 5
                · subst tag
                  have hchildren : CompactClosedSyntaxTasksRealize
                      (compactFormulaTask binderArity ::
                        compactFormulaTask binderArity :: tasks)
                      tail suffix := by
                    simpa [compactFormulaTokenStep, compactTokenAt,
                      compactSyntaxContinue,
                      CompactClosedSyntaxStateRealizes] using hnext
                  cases hchildren with
                  | formula left hleft hright =>
                      cases hright with
                      | formula right hrightClosed restRealizes =>
                          have hclosed : (left ⋎ right).freeVariables = ∅ := by
                            simp [hleft, hrightClosed]
                          simpa [compactArithmeticFormulaTokens,
                            List.append_assoc] using
                            CompactClosedSyntaxTasksRealize.formula
                              (taskPayload := taskPayload)
                              (left ⋎ right) hclosed restRealizes
                · by_cases htagSix : tag = 6
                  · subst tag
                    have hbody : CompactClosedSyntaxTasksRealize
                        (compactFormulaTask (binderArity + 1) :: tasks)
                        tail suffix := by
                      simpa [compactFormulaTokenStep, compactTokenAt,
                        compactSyntaxContinue,
                        CompactClosedSyntaxStateRealizes] using hnext
                    cases hbody with
                    | formula body hbodyClosed restRealizes =>
                        have hclosed : (∀⁰ body).freeVariables = ∅ := by
                          simpa using hbodyClosed
                        simpa [compactArithmeticFormulaTokens] using
                          CompactClosedSyntaxTasksRealize.formula
                            (taskPayload := taskPayload)
                            (∀⁰ body) hclosed restRealizes
                  · by_cases htagSeven : tag = 7
                    · subst tag
                      have hbody : CompactClosedSyntaxTasksRealize
                          (compactFormulaTask (binderArity + 1) :: tasks)
                          tail suffix := by
                        simpa [compactFormulaTokenStep, compactTokenAt,
                          compactSyntaxContinue,
                          CompactClosedSyntaxStateRealizes] using hnext
                      cases hbody with
                      | formula body hbodyClosed restRealizes =>
                          have hclosed : (∃⁰ body).freeVariables = ∅ := by
                            simpa using hbodyClosed
                          simpa [compactArithmeticFormulaTokens] using
                            CompactClosedSyntaxTasksRealize.formula
                              (taskPayload := taskPayload)
                              (∃⁰ body) hclosed restRealizes
                    · exfalso
                      simpa [compactFormulaTokenStep, compactTokenAt,
                        htagZero, htagOne, htagTwo, htagThree, htagFour,
                        htagFive, htagSix, htagSeven, compactSyntaxFailure,
                        CompactClosedSyntaxStateRealizes] using hnext

theorem compactClosedRepeatTermTokenStep_realizes_backward
    (task : CompactSyntaxTask) (tokens suffix : List Nat)
    (tasks : List CompactSyntaxTask)
    (hkind : task.1 = 2)
    (hnext : CompactClosedSyntaxStateRealizes
      (compactRepeatTermTokenStep (task, tokens, tasks)) suffix) :
    CompactClosedSyntaxTasksRealize (task :: tasks) tokens suffix := by
  rcases task with ⟨kind, binderArity, count⟩
  simp only at hkind
  subst kind
  cases count with
  | zero =>
      have hrest :
          CompactClosedSyntaxTasksRealize tasks tokens suffix := by
        simpa [compactRepeatTermTokenStep, compactSyntaxContinue,
          CompactClosedSyntaxStateRealizes] using hnext
      simpa [compactRepeatTermTask] using
        CompactClosedSyntaxTasksRealize.repeatTerm
          (fun index : Fin 0 => Fin.elim0 index)
          (fun index : Fin 0 => Fin.elim0 index) hrest
  | succ count =>
      have hchildren : CompactClosedSyntaxTasksRealize
          (compactTermTask binderArity ::
            compactRepeatTermTask binderArity count :: tasks)
          tokens suffix := by
        simpa [compactRepeatTermTokenStep, compactRepeatTermTask,
          compactSyntaxContinue, CompactClosedSyntaxStateRealizes]
          using hnext
      cases hchildren with
      | term head hheadClosed htail =>
          cases htail with
          | repeatTerm tail htailClosed rest =>
              let terms : Fin (count + 1) ->
                  LO.FirstOrder.ArithmeticSemiterm Nat binderArity :=
                Fin.cons head tail
              have hclosed : ∀ index, (terms index).freeVariables = ∅ := by
                intro index
                refine Fin.cases hheadClosed ?_ index
                intro tailIndex
                exact htailClosed tailIndex
              have htokens :
                  (List.ofFn fun index =>
                    compactArithmeticTermTokens (terms index)).flatten =
                    compactArithmeticTermTokens head ++
                      (List.ofFn fun index =>
                        compactArithmeticTermTokens (tail index)).flatten := by
                simp [terms]
              have hreal :=
                CompactClosedSyntaxTasksRealize.repeatTerm
                  terms hclosed rest
              rw [htokens] at hreal
              simpa [compactRepeatTermTask, List.append_assoc] using hreal

theorem compactClosedSyntaxTaskTokenStep_realizes_backward
    (task : CompactSyntaxTask) (tokens suffix : List Nat)
    (tasks : List CompactSyntaxTask)
    (hnext : CompactClosedSyntaxStateRealizes
      (compactClosedSyntaxTaskTokenStep (task, tokens, tasks)) suffix) :
    CompactClosedSyntaxTasksRealize (task :: tasks) tokens suffix := by
  rcases task with ⟨kind, binderArity, count⟩
  by_cases hzero : kind = 0
  · subst kind
    simpa [compactClosedSyntaxTaskTokenStep] using
      compactClosedTermTokenStep_realizes_backward
        binderArity count tokens suffix tasks hnext
  · by_cases hone : kind = 1
    · subst kind
      simpa [compactClosedSyntaxTaskTokenStep] using
        compactClosedFormulaTokenStep_realizes_backward
          binderArity count tokens suffix tasks hnext
    · by_cases htwo : kind = 2
      · subst kind
        exact compactClosedRepeatTermTokenStep_realizes_backward
          (2, binderArity, count) tokens suffix tasks (by rfl) <| by
            simpa [compactClosedSyntaxTaskTokenStep] using hnext
      · exfalso
        simpa [compactClosedSyntaxTaskTokenStep, hzero, hone, htwo,
          compactSyntaxFailure, CompactClosedSyntaxStateRealizes] using hnext

theorem compactClosedSyntaxParserStep_realizes_backward
    (state : CompactSyntaxParserState) (suffix : List Nat)
    (hnext : CompactClosedSyntaxStateRealizes
      (compactClosedSyntaxParserStep state) suffix) :
    CompactClosedSyntaxStateRealizes state suffix := by
  rcases state with ⟨tokens, tasks, status⟩
  cases status with
  | some result =>
      simpa [compactClosedSyntaxParserStep,
        CompactClosedSyntaxStateRealizes] using hnext
  | none =>
      cases tasks with
      | nil =>
          have htokens : tokens = suffix := by
            simpa [compactClosedSyntaxParserStep,
              compactClosedSyntaxRunningStep,
              CompactClosedSyntaxStateRealizes] using hnext
          subst tokens
          exact CompactClosedSyntaxTasksRealize.nil suffix
      | cons task tasks =>
          change CompactClosedSyntaxTasksRealize
            (task :: tasks) tokens suffix
          exact compactClosedSyntaxTaskTokenStep_realizes_backward
            task tokens suffix tasks <| by
              simpa [compactClosedSyntaxParserStep,
                compactClosedSyntaxRunningStep] using hnext

theorem compactClosedSyntaxParser_iterate_realizes_backward
    (fuel : Nat) (state : CompactSyntaxParserState) (suffix : List Nat)
    (hfinal : CompactClosedSyntaxStateRealizes
      ((compactClosedSyntaxParserStep^[fuel]) state) suffix) :
    CompactClosedSyntaxStateRealizes state suffix := by
  induction fuel generalizing state with
  | zero => exact hfinal
  | succ fuel ih =>
      rw [Function.iterate_succ_apply] at hfinal
      exact compactClosedSyntaxParserStep_realizes_backward state suffix
        (ih (compactClosedSyntaxParserStep state) hfinal)

theorem compactClosedSyntaxParserStateOutput_realizes
    (state : CompactSyntaxParserState) (suffix : List Nat)
    (houtput : compactSyntaxParserStateOutput state = some suffix) :
    CompactClosedSyntaxStateRealizes state suffix := by
  rcases state with ⟨tokens, tasks, status⟩
  cases status with
  | none => simp [compactSyntaxParserStateOutput] at houtput
  | some result =>
      cases result with
      | none => simp [compactSyntaxParserStateOutput] at houtput
      | some output =>
          simpa [compactSyntaxParserStateOutput,
            CompactClosedSyntaxStateRealizes] using houtput

theorem compactClosedFormulaTokenParser_success
    (binderArity : Nat) (tokens suffix : List Nat)
    (hparser : compactClosedFormulaTokenParser binderArity tokens =
      some suffix) :
    exists formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity,
      formula.freeVariables = ∅ ∧
        tokens = compactArithmeticFormulaTokens formula ++ suffix := by
  have hfinal := compactClosedSyntaxParserStateOutput_realizes
    (compactClosedFormulaTokenParserRun binderArity tokens) suffix hparser
  have hinitial := compactClosedSyntaxParser_iterate_realizes_backward
    (compactSyntaxRunFuelBound tokens)
    (compactFormulaParserInitialState binderArity tokens) suffix hfinal
  change CompactClosedSyntaxTasksRealize
    [compactFormulaTask binderArity] tokens suffix at hinitial
  cases hinitial with
  | formula formula hclosed rest =>
      cases rest
      exact ⟨formula, hclosed, rfl⟩

@[simp] theorem compactClosedSyntaxParserStep_term
    (binderArity : Nat) (tokens : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactClosedSyntaxParserStep
        (tokens, compactTermTask binderArity :: tasks, none) =
      compactClosedTermTokenStep (binderArity, tokens, tasks) := by
  simp [compactClosedSyntaxParserStep, compactClosedSyntaxRunningStep,
    compactClosedSyntaxTaskTokenStep, compactTermTask]

@[simp] theorem compactClosedSyntaxParserStep_formula
    (binderArity : Nat) (tokens : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactClosedSyntaxParserStep
        (tokens, compactFormulaTask binderArity :: tasks, none) =
      compactFormulaTokenStep (binderArity, tokens, tasks) := by
  simp [compactClosedSyntaxParserStep, compactClosedSyntaxRunningStep,
    compactClosedSyntaxTaskTokenStep, compactFormulaTask]

@[simp] theorem compactClosedSyntaxParserStep_repeat_zero
    (binderArity : Nat) (tokens : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactClosedSyntaxParserStep
        (tokens, compactRepeatTermTask binderArity 0 :: tasks, none) =
      compactSyntaxContinue tokens tasks := by
  simp [compactClosedSyntaxParserStep, compactClosedSyntaxRunningStep,
    compactClosedSyntaxTaskTokenStep, compactRepeatTermTokenStep,
    compactRepeatTermTask]

@[simp] theorem compactClosedSyntaxParserStep_repeat_succ
    (binderArity count : Nat) (tokens : List Nat)
    (tasks : List CompactSyntaxTask) :
    compactClosedSyntaxParserStep
        (tokens, compactRepeatTermTask binderArity (count + 1) :: tasks,
          none) =
      compactSyntaxContinue tokens
        (compactTermTask binderArity ::
          compactRepeatTermTask binderArity count :: tasks) := by
  simp [compactClosedSyntaxParserStep, compactClosedSyntaxRunningStep,
    compactClosedSyntaxTaskTokenStep, compactRepeatTermTokenStep,
    compactRepeatTermTask]

theorem compactClosedSyntaxParser_iterate_trans
    {start middle finish : CompactSyntaxParserState}
    {firstSteps secondSteps : Nat}
    (hfirst : (compactClosedSyntaxParserStep^[firstSteps]) start = middle)
    (hsecond : (compactClosedSyntaxParserStep^[secondSteps]) middle = finish) :
    (compactClosedSyntaxParserStep^[firstSteps + secondSteps]) start =
      finish := by
  rw [Nat.add_comm, Function.iterate_add_apply, hfirst, hsecond]

theorem compactClosedTermTask_execute
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
    (hclosed : term.freeVariables = ∅)
    (suffix : List Nat) (tasks : List CompactSyntaxTask) :
    (compactClosedSyntaxParserStep^[compactTermTaskSteps term])
        (compactArithmeticTermTokens term ++ suffix,
          compactTermTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
  induction term generalizing suffix tasks with
  | bvar index =>
      simp [compactTermTaskSteps, compactClosedTermTokenStep,
        compactArithmeticTermTokens, compactTokenAt, index.isLt,
        compactSyntaxContinue]
  | fvar freeIndex =>
      simp at hclosed
  | @func functionArity functionSymbol arguments ih =>
      have harguments : ∀ index,
          (arguments index).freeVariables = ∅ := by
        simpa [Semiterm.freeVariables_func,
          Finset.biUnion_eq_empty] using hclosed
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat binderArity) :=
        List.ofFn arguments
      have hmembers : ∀ member ∈ terms,
          member.freeVariables = ∅ ∧
          ∀ (memberSuffix : List Nat)
            (memberTasks : List CompactSyntaxTask),
          (compactClosedSyntaxParserStep^[compactTermTaskSteps member])
              (compactArithmeticTermTokens member ++ memberSuffix,
                compactTermTask binderArity :: memberTasks, none) =
            (memberSuffix, memberTasks, none) := by
        intro member hmember
        rw [List.mem_ofFn] at hmember
        rcases hmember with ⟨index, rfl⟩
        exact ⟨harguments index,
          ih index (harguments index)⟩
      have hrepeat : ∀ (termList : List
          (LO.FirstOrder.ArithmeticSemiterm Nat binderArity)),
          (∀ member ∈ termList,
            member.freeVariables = ∅ ∧
            ∀ (memberSuffix : List Nat)
              (memberTasks : List CompactSyntaxTask),
            (compactClosedSyntaxParserStep^[compactTermTaskSteps member])
                (compactArithmeticTermTokens member ++ memberSuffix,
                  compactTermTask binderArity :: memberTasks, none) =
              (memberSuffix, memberTasks, none)) ->
          (compactClosedSyntaxParserStep^[
              compactTermListRepeatSteps termList])
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
            have hhead := (hall head (by simp)).2
            have htailMembers : ∀ member ∈ tail,
                member.freeVariables = ∅ ∧
                ∀ (memberSuffix : List Nat)
                  (memberTasks : List CompactSyntaxTask),
                (compactClosedSyntaxParserStep^[
                    compactTermTaskSteps member])
                    (compactArithmeticTermTokens member ++ memberSuffix,
                      compactTermTask binderArity :: memberTasks, none) =
                  (memberSuffix, memberTasks, none) := by
              intro member hmember
              exact hall member (by simp [hmember])
            have hone :
                (compactClosedSyntaxParserStep^[1])
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
            have hfirst :=
              compactClosedSyntaxParser_iterate_trans hone hheadRun
            have hallRun :=
              compactClosedSyntaxParser_iterate_trans hfirst htailRun
            simpa [compactTermListRepeatSteps, compactTermListTokens,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              List.append_assoc] using hallRun
      have hfirst :
          (compactClosedSyntaxParserStep^[1])
              (compactArithmeticTermTokens
                    (Semiterm.func functionSymbol arguments) ++ suffix,
                compactTermTask binderArity :: tasks, none) =
            (compactTermListTokens terms ++ suffix,
              compactRepeatTermTask binderArity terms.length :: tasks,
              none) := by
        have hvalid := arithmeticFuncCodeValid_encode functionSymbol
        simp [Function.iterate_one, compactArithmeticTermTokens,
          compactClosedTermTokenStep, compactTokenAt, hvalid,
          compactSyntaxContinue, terms, compactTermListTokens,
          List.ofFn_comp', List.append_assoc]
        exact (compactTermListTokens_ofFn arguments).symm
      have hrepeatRun := hrepeat terms hmembers
      have hrun :=
        compactClosedSyntaxParser_iterate_trans hfirst hrepeatRun
      have hsteps :
          compactTermTaskSteps
              (Semiterm.func functionSymbol arguments) =
            1 + compactTermListRepeatSteps terms := by
        simp [compactTermTaskSteps, compactTermListRepeatSteps, terms,
          Function.comp_def]
        omega
      rw [hsteps]
      exact hrun

theorem compactClosedTermList_execute
    {binderArity : Nat}
    (terms : List
      (LO.FirstOrder.ArithmeticSemiterm Nat binderArity))
    (hclosed : ∀ term ∈ terms, term.freeVariables = ∅)
    (suffix : List Nat) (tasks : List CompactSyntaxTask) :
    (compactClosedSyntaxParserStep^[compactTermListRepeatSteps terms])
        (compactTermListTokens terms ++ suffix,
          compactRepeatTermTask binderArity terms.length :: tasks, none) =
      (suffix, tasks, none) := by
  induction terms with
  | nil =>
      simp [compactTermListRepeatSteps, compactTermListTokens,
        Function.iterate_one, compactSyntaxContinue]
  | cons head tail ih =>
      have hheadClosed : head.freeVariables = ∅ := hclosed head (by simp)
      have htailClosed : ∀ term ∈ tail, term.freeVariables = ∅ := by
        intro term hterm
        exact hclosed term (by simp [hterm])
      have hone :
          (compactClosedSyntaxParserStep^[1])
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
      have hhead := compactClosedTermTask_execute head hheadClosed
        (compactTermListTokens tail ++ suffix)
        (compactRepeatTermTask binderArity tail.length :: tasks)
      have hfirst :=
        compactClosedSyntaxParser_iterate_trans hone hhead
      have htail := ih htailClosed
      have hall :=
        compactClosedSyntaxParser_iterate_trans hfirst htail
      simpa [compactTermListRepeatSteps, compactTermListTokens,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using hall

theorem compactClosedFormulaTask_execute
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (hclosed : formula.freeVariables = ∅)
    (suffix : List Nat) (tasks : List CompactSyntaxTask) :
    (compactClosedSyntaxParserStep^[compactFormulaTaskSteps formula])
        (compactArithmeticFormulaTokens formula ++ suffix,
          compactFormulaTask binderArity :: tasks, none) =
      (suffix, tasks, none) := by
  induction formula generalizing suffix tasks with
  | @rel formulaArity relationArity relationSymbol arguments =>
      have harguments : ∀ index,
          (arguments index).freeVariables = ∅ := by
        simpa [Semiformula.freeVariables_rel,
          Finset.biUnion_eq_empty] using hclosed
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat formulaArity) :=
        List.ofFn arguments
      have htermsClosed : ∀ term ∈ terms,
          term.freeVariables = ∅ := by
        intro term hterm
        rw [List.mem_ofFn] at hterm
        rcases hterm with ⟨index, rfl⟩
        exact harguments index
      have hfirst :
          (compactClosedSyntaxParserStep^[1])
              (compactArithmeticFormulaTokens
                    (Semiformula.rel relationSymbol arguments) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none) =
            (compactTermListTokens terms ++ suffix,
              compactRepeatTermTask formulaArity terms.length :: tasks,
              none) := by
        simp [Function.iterate_one, terms, compactTermListTokens,
          List.ofFn_comp', List.append_assoc, compactSyntaxContinue]
        exact (compactTermListTokens_ofFn arguments).symm
      have hterms := compactClosedTermList_execute terms htermsClosed
        suffix tasks
      have hrun :=
        compactClosedSyntaxParser_iterate_trans hfirst hterms
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
      have harguments : ∀ index,
          (arguments index).freeVariables = ∅ := by
        simpa [Semiformula.freeVariables_nrel,
          Finset.biUnion_eq_empty] using hclosed
      let terms : List
          (LO.FirstOrder.ArithmeticSemiterm Nat formulaArity) :=
        List.ofFn arguments
      have htermsClosed : ∀ term ∈ terms,
          term.freeVariables = ∅ := by
        intro term hterm
        rw [List.mem_ofFn] at hterm
        rcases hterm with ⟨index, rfl⟩
        exact harguments index
      have hfirst :
          (compactClosedSyntaxParserStep^[1])
              (compactArithmeticFormulaTokens
                    (Semiformula.nrel relationSymbol arguments) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none) =
            (compactTermListTokens terms ++ suffix,
              compactRepeatTermTask formulaArity terms.length :: tasks,
              none) := by
        simp [Function.iterate_one, terms, compactTermListTokens,
          List.ofFn_comp', List.append_assoc, compactSyntaxContinue]
        exact (compactTermListTokens_ofFn arguments).symm
      have hterms := compactClosedTermList_execute terms htermsClosed
        suffix tasks
      have hrun :=
        compactClosedSyntaxParser_iterate_trans hfirst hterms
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
      simp [compactFormulaTaskSteps, Function.iterate_one,
        compactArithmeticFormulaTokens, compactFormulaTokenStep,
        compactTokenAt, compactSyntaxContinue]
  | @falsum formulaArity =>
      simp [compactFormulaTaskSteps, Function.iterate_one,
        compactArithmeticFormulaTokens, compactFormulaTokenStep,
        compactTokenAt, compactSyntaxContinue]
  | @and formulaArity left right ihLeft ihRight =>
      have hand : Semiformula.and left right = left ⋏ right := rfl
      change left.freeVariables ∪ right.freeVariables = ∅ at hclosed
      have hparts :
          left.freeVariables = ∅ ∧ right.freeVariables = ∅ := by
        simpa using hclosed
      have hone :
          (compactClosedSyntaxParserStep^[1])
              (compactArithmeticFormulaTokens
                    (Semiformula.and left right) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none) =
            (compactArithmeticFormulaTokens left ++
                (compactArithmeticFormulaTokens right ++ suffix),
              compactFormulaTask formulaArity ::
                compactFormulaTask formulaArity :: tasks,
              none) := by
        rw [Function.iterate_one, compactClosedSyntaxParserStep_formula,
          hand]
        simpa [compactSyntaxContinue, List.append_assoc] using
          compactFormulaTokenStep_and left right suffix tasks
      have hleft := ihLeft hparts.1
        (compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask formulaArity :: tasks)
      have hright := ihRight hparts.2 suffix tasks
      have hfirst :=
        compactClosedSyntaxParser_iterate_trans hone hleft
      have hrun :=
        compactClosedSyntaxParser_iterate_trans hfirst hright
      change
        (compactClosedSyntaxParserStep^[
            compactFormulaTaskSteps (Semiformula.and left right)])
            (compactArithmeticFormulaTokens (Semiformula.and left right) ++
                suffix,
              compactFormulaTask formulaArity :: tasks, none) =
          (suffix, tasks, none)
      simpa only [compactFormulaTaskSteps] using hrun
  | @or formulaArity left right ihLeft ihRight =>
      have hor : Semiformula.or left right = left ⋎ right := rfl
      change left.freeVariables ∪ right.freeVariables = ∅ at hclosed
      have hparts :
          left.freeVariables = ∅ ∧ right.freeVariables = ∅ := by
        simpa using hclosed
      have hone :
          (compactClosedSyntaxParserStep^[1])
              (compactArithmeticFormulaTokens
                    (Semiformula.or left right) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none) =
            (compactArithmeticFormulaTokens left ++
                (compactArithmeticFormulaTokens right ++ suffix),
              compactFormulaTask formulaArity ::
                compactFormulaTask formulaArity :: tasks,
              none) := by
        rw [Function.iterate_one, compactClosedSyntaxParserStep_formula,
          hor]
        simpa [compactSyntaxContinue, List.append_assoc] using
          compactFormulaTokenStep_or left right suffix tasks
      have hleft := ihLeft hparts.1
        (compactArithmeticFormulaTokens right ++ suffix)
        (compactFormulaTask formulaArity :: tasks)
      have hright := ihRight hparts.2 suffix tasks
      have hfirst :=
        compactClosedSyntaxParser_iterate_trans hone hleft
      have hrun :=
        compactClosedSyntaxParser_iterate_trans hfirst hright
      change
        (compactClosedSyntaxParserStep^[
            compactFormulaTaskSteps (Semiformula.or left right)])
            (compactArithmeticFormulaTokens (Semiformula.or left right) ++
                suffix,
              compactFormulaTask formulaArity :: tasks, none) =
          (suffix, tasks, none)
      simpa only [compactFormulaTaskSteps] using hrun
  | @all formulaArity body ih =>
      have hall : Semiformula.all body = ∀⁰ body := rfl
      change body.freeVariables = ∅ at hclosed
      have hbodyClosed : body.freeVariables = ∅ := by
        exact hclosed
      have hone :
          (compactClosedSyntaxParserStep^[1])
              (compactArithmeticFormulaTokens
                    (Semiformula.all body) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none) =
            (compactArithmeticFormulaTokens body ++ suffix,
              compactFormulaTask (formulaArity + 1) :: tasks, none) := by
        rw [Function.iterate_one, compactClosedSyntaxParserStep_formula,
          hall]
        exact compactFormulaTokenStep_all body suffix tasks
      have hbody := ih hbodyClosed suffix tasks
      have hrun :=
        compactClosedSyntaxParser_iterate_trans hone hbody
      change
        (compactClosedSyntaxParserStep^[
            compactFormulaTaskSteps (Semiformula.all body)])
            (compactArithmeticFormulaTokens (Semiformula.all body) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none) =
          (suffix, tasks, none)
      simpa only [compactFormulaTaskSteps] using hrun
  | @exs formulaArity body ih =>
      have hexs : Semiformula.exs body = ∃⁰ body := rfl
      change body.freeVariables = ∅ at hclosed
      have hbodyClosed : body.freeVariables = ∅ := by
        exact hclosed
      have hone :
          (compactClosedSyntaxParserStep^[1])
              (compactArithmeticFormulaTokens
                    (Semiformula.exs body) ++ suffix,
                compactFormulaTask formulaArity :: tasks, none) =
            (compactArithmeticFormulaTokens body ++ suffix,
              compactFormulaTask (formulaArity + 1) :: tasks, none) := by
        rw [Function.iterate_one, compactClosedSyntaxParserStep_formula,
          hexs]
        exact compactFormulaTokenStep_exs body suffix tasks
      have hbody := ih hbodyClosed suffix tasks
      have hrun :=
        compactClosedSyntaxParser_iterate_trans hone hbody
      change
        (compactClosedSyntaxParserStep^[
            compactFormulaTaskSteps (Semiformula.exs body)])
            (compactArithmeticFormulaTokens (Semiformula.exs body) ++ suffix,
              compactFormulaTask formulaArity :: tasks, none) =
          (suffix, tasks, none)
      simpa only [compactFormulaTaskSteps] using hrun

theorem compactClosedSyntaxParserStep_done
    (tokens : List Nat) (tasks : List CompactSyntaxTask)
    (result : Option (List Nat)) :
    compactClosedSyntaxParserStep (tokens, tasks, some result) =
      (tokens, tasks, some result) := by
  simp [compactClosedSyntaxParserStep]

theorem compactClosedSyntaxParserStep_iterate_done
    (fuel : Nat) (tokens : List Nat) (tasks : List CompactSyntaxTask)
    (result : Option (List Nat)) :
    (compactClosedSyntaxParserStep^[fuel])
        (tokens, tasks, some result) =
      (tokens, tasks, some result) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply,
        compactClosedSyntaxParserStep_done, ih]

theorem compactClosedFormulaTokenParser_canonical_append
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
    (hclosed : formula.freeVariables = ∅)
    (suffix : List Nat) :
    compactClosedFormulaTokenParser binderArity
        (compactArithmeticFormulaTokens formula ++ suffix) =
      some suffix := by
  let tokens := compactArithmeticFormulaTokens formula ++ suffix
  let used := compactFormulaTaskSteps formula + 1
  have htask :=
    compactClosedFormulaTask_execute formula hclosed suffix []
  have hfinish :
      (compactClosedSyntaxParserStep^[used])
          (tokens, [compactFormulaTask binderArity], none) =
        (suffix, [], some (some suffix)) := by
    apply compactClosedSyntaxParser_iterate_trans htask
    simp [Function.iterate_one, compactClosedSyntaxParserStep,
      compactClosedSyntaxRunningStep]
  have hformula := compactFormulaTaskSteps_le_tokenLength formula
  have hinputLength :
      (compactArithmeticFormulaTokens formula).length <= tokens.length := by
    simp [tokens]
  have hfuelLength := compactSyntaxRunFuelBound_length_add_one tokens
  have hused : used <= compactSyntaxRunFuelBound tokens := by
    omega
  obtain ⟨extra, hfuel⟩ := exists_add_of_le hused
  have hrun :
      (compactClosedSyntaxParserStep^[compactSyntaxRunFuelBound tokens])
          (tokens, [compactFormulaTask binderArity], none) =
        (suffix, [], some (some suffix)) := by
    rw [hfuel]
    exact compactClosedSyntaxParser_iterate_trans hfinish
      (compactClosedSyntaxParserStep_iterate_done
        extra suffix [] (some suffix))
  simp [compactClosedFormulaTokenParser,
    compactClosedFormulaTokenParserRun,
    compactFormulaParserInitialState,
    compactSyntaxParserStateOutput, tokens, hrun]

theorem compactClosedFormulaTokenParser_success_iff
    (binderArity : Nat) (tokens suffix : List Nat) :
    compactClosedFormulaTokenParser binderArity tokens = some suffix <->
      exists formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity,
        formula.freeVariables = ∅ ∧
          tokens = compactArithmeticFormulaTokens formula ++ suffix := by
  constructor
  · exact compactClosedFormulaTokenParser_success
      binderArity tokens suffix
  · rintro ⟨formula, hclosed, rfl⟩
    exact compactClosedFormulaTokenParser_canonical_append
      formula hclosed suffix

theorem compactClosedFormulaTokenParser_sentence_append
    (sentence : LO.FirstOrder.ArithmeticSentence) (suffix : List Nat) :
    compactClosedFormulaTokenParser 0
        (compactArithmeticFormulaTokens
          (Rewriting.emb sentence :
            LO.FirstOrder.ArithmeticProposition) ++ suffix) =
      some suffix := by
  apply compactClosedFormulaTokenParser_canonical_append
  simp

#print axioms compactClosedTermTokenStep_primrec
#print axioms compactClosedSyntaxParserStep_primrec
#print axioms compactClosedFormulaTokenParser_primrec
#print axioms compactClosedFormulaTokenParser_success_iff
#print axioms compactClosedFormulaTokenParser_sentence_append

end FoundationCompactClosedFormulaTokenMachine
