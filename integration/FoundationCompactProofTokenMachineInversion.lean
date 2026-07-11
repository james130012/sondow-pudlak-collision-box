import integration.FoundationCompactProofTokenMachine

/-!
# Exact inversion for the numeric listed-proof parser

Successful numeric parsing is interpreted by a typed task-stack invariant.
The axiom branch uses the closed-formula machine, so every recovered axiom
leaf contains an actual arithmetic sentence.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationCompactProofTokenMachineInversion

open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTokenMachineInversion
open FoundationCompactClosedFormulaTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactProofTokenMachine

inductive CompactProofTasksRealize :
    List CompactProofParserTask -> List Nat -> List Nat -> Prop
  | nil (suffix : List Nat) :
      CompactProofTasksRealize [] suffix suffix
  | proof {taskAux taskPayload : Nat}
      (tree : ListedCheckedPAProofTree)
      {middle suffix : List Nat} {tasks : List CompactProofParserTask}
      (rest : CompactProofTasksRealize tasks middle suffix) :
      CompactProofTasksRealize
        ((3, taskAux, taskPayload) :: tasks)
        (compactListedProofTokens tree ++ middle) suffix
  | formula {binderArity taskPayload : Nat}
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
      {middle suffix : List Nat} {tasks : List CompactProofParserTask}
      (rest : CompactProofTasksRealize tasks middle suffix) :
      CompactProofTasksRealize
        ((4, binderArity, taskPayload) :: tasks)
        (compactArithmeticFormulaTokens formula ++ middle) suffix
  | term {binderArity taskPayload : Nat}
      (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity)
      {middle suffix : List Nat} {tasks : List CompactProofParserTask}
      (rest : CompactProofTasksRealize tasks middle suffix) :
      CompactProofTasksRealize
        ((5, binderArity, taskPayload) :: tasks)
        (compactArithmeticTermTokens term ++ middle) suffix
  | repeatFormula {taskAux count : Nat}
      (formulas : List LO.FirstOrder.ArithmeticProposition)
      (length_eq : formulas.length = count)
      {middle suffix : List Nat} {tasks : List CompactProofParserTask}
      (rest : CompactProofTasksRealize tasks middle suffix) :
      CompactProofTasksRealize
        ((6, taskAux, count) :: tasks)
        (formulas.flatMap compactArithmeticFormulaTokens ++ middle) suffix
  | sequent {taskAux taskPayload : Nat}
      (Gamma : List LO.FirstOrder.ArithmeticProposition)
      {middle suffix : List Nat} {tasks : List CompactProofParserTask}
      (rest : CompactProofTasksRealize tasks middle suffix) :
      CompactProofTasksRealize
        ((7, taskAux, taskPayload) :: tasks)
        (compactSequentListTokens Gamma ++ middle) suffix
  | closedFormula {binderArity taskPayload : Nat}
      (sentence : LO.FirstOrder.ArithmeticSemisentence binderArity)
      {middle suffix : List Nat} {tasks : List CompactProofParserTask}
      (rest : CompactProofTasksRealize tasks middle suffix) :
      CompactProofTasksRealize
        ((8, binderArity, taskPayload) :: tasks)
        (compactArithmeticFormulaTokens
          (Rewriting.emb sentence :
            LO.FirstOrder.ArithmeticSemiformula Nat binderArity) ++ middle)
        suffix

def CompactProofStateRealizes
    (state : CompactProofParserState) (suffix : List Nat) : Prop :=
  match state.2.2 with
  | none => CompactProofTasksRealize state.2.1 state.1 suffix
  | some none => False
  | some (some output) => output = suffix

@[simp] theorem compactProofStateRealizes_continue
    (tokens suffix : List Nat) (tasks : List CompactProofParserTask) :
    CompactProofStateRealizes
        (compactSyntaxContinue tokens tasks) suffix <->
      CompactProofTasksRealize tasks tokens suffix := by
  rfl

@[simp] theorem compactProofStateRealizes_failure
    (tokens suffix : List Nat) (tasks : List CompactProofParserTask) :
    ¬ CompactProofStateRealizes
      (compactSyntaxFailure tokens tasks) suffix := by
  exact fun h => h

theorem compactProofFormulaTokenStep_realizes_backward
    (binderArity taskPayload : Nat) (tokens suffix : List Nat)
    (tasks : List CompactProofParserTask)
    (hnext : CompactProofStateRealizes
      (compactProofFormulaTokenStep (binderArity, tokens, tasks)) suffix) :
    CompactProofTasksRealize
      ((4, binderArity, taskPayload) :: tasks) tokens suffix := by
  cases hparse : compactFormulaTokenParser binderArity tokens with
  | none =>
      exfalso
      simpa [compactProofFormulaTokenStep, hparse,
        compactSyntaxFailure, CompactProofStateRealizes] using hnext
  | some middle =>
      have hrest : CompactProofTasksRealize tasks middle suffix := by
        simpa [compactProofFormulaTokenStep, hparse,
          compactSyntaxContinue, CompactProofStateRealizes] using hnext
      obtain ⟨formula, htokens⟩ :=
        (compactFormulaTokenParser_success_iff
          binderArity tokens middle).1 hparse
      subst tokens
      exact CompactProofTasksRealize.formula
        (taskPayload := taskPayload) formula hrest

theorem compactProofTermTokenStep_realizes_backward
    (binderArity taskPayload : Nat) (tokens suffix : List Nat)
    (tasks : List CompactProofParserTask)
    (hnext : CompactProofStateRealizes
      (compactProofTermTokenStep (binderArity, tokens, tasks)) suffix) :
    CompactProofTasksRealize
      ((5, binderArity, taskPayload) :: tasks) tokens suffix := by
  cases hparse : compactTermTokenParser binderArity tokens with
  | none =>
      exfalso
      simpa [compactProofTermTokenStep, hparse,
        compactSyntaxFailure, CompactProofStateRealizes] using hnext
  | some middle =>
      have hrest : CompactProofTasksRealize tasks middle suffix := by
        simpa [compactProofTermTokenStep, hparse,
          compactSyntaxContinue, CompactProofStateRealizes] using hnext
      obtain ⟨term, htokens⟩ :=
        (compactTermTokenParser_success_iff
          binderArity tokens middle).1 hparse
      subst tokens
      exact CompactProofTasksRealize.term
        (taskPayload := taskPayload) term hrest

theorem compactProofClosedFormulaTokenStep_realizes_backward
    (binderArity taskPayload : Nat) (tokens suffix : List Nat)
    (tasks : List CompactProofParserTask)
    (hnext : CompactProofStateRealizes
      (compactProofClosedFormulaTokenStep
        (binderArity, tokens, tasks)) suffix) :
    CompactProofTasksRealize
      ((8, binderArity, taskPayload) :: tasks) tokens suffix := by
  cases hparse : compactClosedFormulaTokenParser binderArity tokens with
  | none =>
      exfalso
      simpa [compactProofClosedFormulaTokenStep, hparse,
        compactSyntaxFailure, CompactProofStateRealizes] using hnext
  | some middle =>
      have hrest : CompactProofTasksRealize tasks middle suffix := by
        simpa [compactProofClosedFormulaTokenStep, hparse,
          compactSyntaxContinue, CompactProofStateRealizes] using hnext
      obtain ⟨formula, hclosed, htokens⟩ :=
        (compactClosedFormulaTokenParser_success_iff
          binderArity tokens middle).1 hparse
      let sentence : LO.FirstOrder.ArithmeticSemisentence binderArity :=
        formula.toEmpty hclosed
      have hemb :
          (Rewriting.emb sentence :
            LO.FirstOrder.ArithmeticSemiformula Nat binderArity) =
            formula := by
        simp [sentence]
      subst tokens
      rw [← hemb]
      exact CompactProofTasksRealize.closedFormula
        (taskPayload := taskPayload) sentence hrest

theorem compactProofRepeatFormulaTokenStep_realizes_backward
    (task : CompactProofParserTask) (tokens suffix : List Nat)
    (tasks : List CompactProofParserTask)
    (hkind : task.1 = 6)
    (hnext : CompactProofStateRealizes
      (compactProofRepeatFormulaTokenStep (task, tokens, tasks)) suffix) :
    CompactProofTasksRealize (task :: tasks) tokens suffix := by
  rcases task with ⟨kind, taskAux, count⟩
  simp only at hkind
  subst kind
  cases count with
  | zero =>
      have hrest : CompactProofTasksRealize tasks tokens suffix := by
        simpa [compactProofRepeatFormulaTokenStep, compactSyntaxContinue,
          CompactProofStateRealizes] using hnext
      exact CompactProofTasksRealize.repeatFormula
        (taskAux := taskAux) [] (by rfl) hrest
  | succ count =>
      have hchildren : CompactProofTasksRealize
          (compactProofFormulaTask 0 ::
            compactProofRepeatFormulaTask count :: tasks)
          tokens suffix := by
        simpa [compactProofRepeatFormulaTokenStep,
          compactProofRepeatFormulaTask, compactSyntaxContinue,
          CompactProofStateRealizes] using hnext
      cases hchildren with
      | formula head htail =>
          cases htail with
          | repeatFormula tail hlength rest =>
              have hnewLength : (head :: tail).length = count + 1 := by
                simp [hlength]
              simpa [List.append_assoc] using
                CompactProofTasksRealize.repeatFormula
                  (taskAux := taskAux) (head :: tail) hnewLength rest

theorem compactProofSequentTokenStep_realizes_backward
    (taskAux taskPayload : Nat) (tokens suffix : List Nat)
    (tasks : List CompactProofParserTask)
    (hnext : CompactProofStateRealizes
      (compactProofSequentTokenStep tokens tasks) suffix) :
    CompactProofTasksRealize
      ((7, taskAux, taskPayload) :: tasks) tokens suffix := by
  cases tokens with
  | nil =>
      exfalso
      simpa [compactProofSequentTokenStep, compactSyntaxFailure,
        CompactProofStateRealizes] using hnext
  | cons count body =>
      have hrepeat : CompactProofTasksRealize
          (compactProofRepeatFormulaTask count :: tasks) body suffix := by
        simpa [compactProofSequentTokenStep, compactSyntaxContinue,
          CompactProofStateRealizes] using hnext
      cases hrepeat with
      | repeatFormula Gamma hlength rest =>
          have hcount : Gamma.length = count := hlength
          subst count
          simpa [compactSequentListTokens, List.append_assoc] using
            CompactProofTasksRealize.sequent
              (taskAux := taskAux) (taskPayload := taskPayload)
              Gamma rest

theorem compactProofNodeTokenStep_realizes_backward
    (taskAux taskPayload : Nat) (tokens suffix : List Nat)
    (tasks : List CompactProofParserTask)
    (hnext : CompactProofStateRealizes
      (compactProofNodeTokenStep tokens tasks) suffix) :
    CompactProofTasksRealize
      ((3, taskAux, taskPayload) :: tasks) tokens suffix := by
  cases tokens with
  | nil =>
      exfalso
      simpa [compactProofNodeTokenStep, compactSyntaxFailure,
        CompactProofStateRealizes] using hnext
  | cons tag body =>
      by_cases h0 : tag = 0
      · subst tag
        have hfields : CompactProofTasksRealize
            (compactProofSequentTask :: compactProofFormulaTask 0 :: tasks)
            body suffix := by
          simpa [compactProofNodeTokenStep, compactSyntaxContinue,
            CompactProofStateRealizes] using hnext
        cases hfields with
        | sequent Gamma hformula =>
            cases hformula with
            | formula formula rest =>
                simpa [compactListedProofTokens, List.append_assoc] using
                  CompactProofTasksRealize.proof
                    (taskAux := taskAux) (taskPayload := taskPayload)
                    (.closed Gamma formula) rest
      · by_cases h1 : tag = 1
        · subst tag
          have hfields : CompactProofTasksRealize
              (compactProofSequentTask ::
                compactProofClosedFormulaTask 0 :: tasks)
              body suffix := by
            simpa [compactProofNodeTokenStep, compactSyntaxContinue,
              CompactProofStateRealizes] using hnext
          cases hfields with
          | sequent Gamma hsentence =>
              cases hsentence with
              | closedFormula sentence rest =>
                  simpa [compactListedProofTokens, List.append_assoc] using
                    CompactProofTasksRealize.proof
                      (taskAux := taskAux) (taskPayload := taskPayload)
                      (.axm Gamma sentence) rest
        · by_cases h2 : tag = 2
          · subst tag
            have hfields : CompactProofTasksRealize
                (compactProofSequentTask :: tasks) body suffix := by
              simpa [compactProofNodeTokenStep, compactSyntaxContinue,
                CompactProofStateRealizes] using hnext
            cases hfields with
            | sequent Gamma rest =>
                simpa [compactListedProofTokens] using
                  CompactProofTasksRealize.proof
                    (taskAux := taskAux) (taskPayload := taskPayload)
                    (.verum Gamma) rest
          · by_cases h3 : tag = 3
            · subst tag
              have hfields : CompactProofTasksRealize
                  (compactProofSequentTask :: compactProofFormulaTask 0 ::
                    compactProofFormulaTask 0 :: compactProofTask ::
                    compactProofTask :: tasks) body suffix := by
                simpa [compactProofNodeTokenStep, compactSyntaxContinue,
                  CompactProofStateRealizes] using hnext
              cases hfields with
              | sequent Gamma hleftFormula =>
                  cases hleftFormula with
                  | formula leftFormula hrightFormula =>
                      cases hrightFormula with
                      | formula rightFormula hleft =>
                          cases hleft with
                          | proof left hright =>
                              cases hright with
                              | proof right rest =>
                                  simpa [compactListedProofTokens,
                                    List.append_assoc] using
                                    CompactProofTasksRealize.proof
                                      (taskAux := taskAux)
                                      (taskPayload := taskPayload)
                                      (.and Gamma leftFormula rightFormula
                                        left right) rest
            · by_cases h4 : tag = 4
              · subst tag
                have hfields : CompactProofTasksRealize
                    (compactProofSequentTask :: compactProofFormulaTask 0 ::
                      compactProofFormulaTask 0 :: compactProofTask :: tasks)
                    body suffix := by
                  simpa [compactProofNodeTokenStep, compactSyntaxContinue,
                    CompactProofStateRealizes] using hnext
                cases hfields with
                | sequent Gamma hleftFormula =>
                    cases hleftFormula with
                    | formula leftFormula hrightFormula =>
                        cases hrightFormula with
                        | formula rightFormula hpremise =>
                            cases hpremise with
                            | proof premise rest =>
                                simpa [compactListedProofTokens,
                                  List.append_assoc] using
                                  CompactProofTasksRealize.proof
                                    (taskAux := taskAux)
                                    (taskPayload := taskPayload)
                                    (.or Gamma leftFormula rightFormula
                                      premise) rest
              · by_cases h5 : tag = 5
                · subst tag
                  have hfields : CompactProofTasksRealize
                      (compactProofSequentTask ::
                        compactProofFormulaTask 1 :: compactProofTask :: tasks)
                      body suffix := by
                    simpa [compactProofNodeTokenStep, compactSyntaxContinue,
                      CompactProofStateRealizes] using hnext
                  cases hfields with
                  | sequent Gamma hformula =>
                      cases hformula with
                      | formula formula hpremise =>
                          cases hpremise with
                          | proof premise rest =>
                              simpa [compactListedProofTokens,
                                List.append_assoc] using
                                CompactProofTasksRealize.proof
                                  (taskAux := taskAux)
                                  (taskPayload := taskPayload)
                                  (.all Gamma formula premise) rest
                · by_cases h6 : tag = 6
                  · subst tag
                    have hfields : CompactProofTasksRealize
                        (compactProofSequentTask ::
                          compactProofFormulaTask 1 ::
                          compactProofTermTask 0 :: compactProofTask :: tasks)
                        body suffix := by
                      simpa [compactProofNodeTokenStep,
                        compactSyntaxContinue, CompactProofStateRealizes]
                        using hnext
                    cases hfields with
                    | sequent Gamma hformula =>
                        cases hformula with
                        | formula formula hwitness =>
                            cases hwitness with
                            | term witness hpremise =>
                                cases hpremise with
                                | proof premise rest =>
                                    simpa [compactListedProofTokens,
                                      List.append_assoc] using
                                      CompactProofTasksRealize.proof
                                        (taskAux := taskAux)
                                        (taskPayload := taskPayload)
                                        (.exs Gamma formula witness premise)
                                        rest
                  · by_cases h7 : tag = 7
                    · subst tag
                      have hfields : CompactProofTasksRealize
                          (compactProofSequentTask :: compactProofTask :: tasks)
                          body suffix := by
                        simpa [compactProofNodeTokenStep,
                          compactSyntaxContinue, CompactProofStateRealizes]
                          using hnext
                      cases hfields with
                      | sequent Gamma hpremise =>
                          cases hpremise with
                          | proof premise rest =>
                              simpa [compactListedProofTokens,
                                List.append_assoc] using
                                CompactProofTasksRealize.proof
                                  (taskAux := taskAux)
                                  (taskPayload := taskPayload)
                                  (.wk Gamma premise) rest
                    · by_cases h8 : tag = 8
                      · subst tag
                        have hfields : CompactProofTasksRealize
                            (compactProofSequentTask ::
                              compactProofTask :: tasks) body suffix := by
                          simpa [compactProofNodeTokenStep,
                            compactSyntaxContinue, CompactProofStateRealizes]
                            using hnext
                        cases hfields with
                        | sequent Gamma hpremise =>
                            cases hpremise with
                            | proof premise rest =>
                                simpa [compactListedProofTokens,
                                  List.append_assoc] using
                                  CompactProofTasksRealize.proof
                                    (taskAux := taskAux)
                                    (taskPayload := taskPayload)
                                    (.shift Gamma premise) rest
                      · by_cases h9 : tag = 9
                        · subst tag
                          have hfields : CompactProofTasksRealize
                              (compactProofSequentTask ::
                                compactProofFormulaTask 0 ::
                                compactProofTask :: compactProofTask :: tasks)
                              body suffix := by
                            simpa [compactProofNodeTokenStep,
                              compactSyntaxContinue,
                              CompactProofStateRealizes] using hnext
                          cases hfields with
                          | sequent Gamma hformula =>
                              cases hformula with
                              | formula formula hleft =>
                                  cases hleft with
                                  | proof left hright =>
                                      cases hright with
                                      | proof right rest =>
                                          simpa [compactListedProofTokens,
                                            List.append_assoc] using
                                            CompactProofTasksRealize.proof
                                              (taskAux := taskAux)
                                              (taskPayload := taskPayload)
                                              (.cut Gamma formula left right)
                                              rest
                        · exfalso
                          simpa [compactProofNodeTokenStep, h0, h1, h2, h3,
                            h4, h5, h6, h7, h8, h9,
                            compactSyntaxFailure, CompactProofStateRealizes]
                            using hnext

theorem compactProofParserTaskTokenStep_realizes_backward
    (task : CompactProofParserTask) (tokens suffix : List Nat)
    (tasks : List CompactProofParserTask)
    (hnext : CompactProofStateRealizes
      (compactProofParserTaskTokenStep (task, tokens, tasks)) suffix) :
    CompactProofTasksRealize (task :: tasks) tokens suffix := by
  rcases task with ⟨kind, taskAux, taskPayload⟩
  by_cases h3 : kind = 3
  · subst kind
    simpa [compactProofParserTaskTokenStep] using
      compactProofNodeTokenStep_realizes_backward
        taskAux taskPayload tokens suffix tasks hnext
  · by_cases h4 : kind = 4
    · subst kind
      simpa [compactProofParserTaskTokenStep] using
        compactProofFormulaTokenStep_realizes_backward
          taskAux taskPayload tokens suffix tasks hnext
    · by_cases h5 : kind = 5
      · subst kind
        simpa [compactProofParserTaskTokenStep] using
          compactProofTermTokenStep_realizes_backward
            taskAux taskPayload tokens suffix tasks hnext
      · by_cases h6 : kind = 6
        · subst kind
          exact compactProofRepeatFormulaTokenStep_realizes_backward
            (6, taskAux, taskPayload) tokens suffix tasks (by rfl) <| by
              simpa [compactProofParserTaskTokenStep] using hnext
        · by_cases h7 : kind = 7
          · subst kind
            simpa [compactProofParserTaskTokenStep] using
              compactProofSequentTokenStep_realizes_backward
                taskAux taskPayload tokens suffix tasks hnext
          · by_cases h8 : kind = 8
            · subst kind
              simpa [compactProofParserTaskTokenStep] using
                compactProofClosedFormulaTokenStep_realizes_backward
                  taskAux taskPayload tokens suffix tasks hnext
            · exfalso
              simpa [compactProofParserTaskTokenStep, h3, h4, h5, h6,
                h7, h8, compactSyntaxFailure, CompactProofStateRealizes]
                using hnext

theorem compactProofParserStep_realizes_backward
    (state : CompactProofParserState) (suffix : List Nat)
    (hnext : CompactProofStateRealizes
      (compactProofParserStep state) suffix) :
    CompactProofStateRealizes state suffix := by
  rcases state with ⟨tokens, tasks, status⟩
  cases status with
  | some result =>
      simpa [compactProofParserStep,
        CompactProofStateRealizes] using hnext
  | none =>
      cases tasks with
      | nil =>
          have htokens : tokens = suffix := by
            simpa [compactProofParserStep, compactProofParserRunningStep,
              CompactProofStateRealizes] using hnext
          subst tokens
          exact CompactProofTasksRealize.nil suffix
      | cons task tasks =>
          change CompactProofTasksRealize (task :: tasks) tokens suffix
          exact compactProofParserTaskTokenStep_realizes_backward
            task tokens suffix tasks <| by
              simpa [compactProofParserStep,
                compactProofParserRunningStep] using hnext

theorem compactProofParser_iterate_realizes_backward
    (fuel : Nat) (state : CompactProofParserState) (suffix : List Nat)
    (hfinal : CompactProofStateRealizes
      ((compactProofParserStep^[fuel]) state) suffix) :
    CompactProofStateRealizes state suffix := by
  induction fuel generalizing state with
  | zero => exact hfinal
  | succ fuel ih =>
      rw [Function.iterate_succ_apply] at hfinal
      exact compactProofParserStep_realizes_backward state suffix
        (ih (compactProofParserStep state) hfinal)

theorem compactProofParserStateOutput_realizes
    (state : CompactProofParserState) (suffix : List Nat)
    (houtput : compactSyntaxParserStateOutput state = some suffix) :
    CompactProofStateRealizes state suffix := by
  rcases state with ⟨tokens, tasks, status⟩
  cases status with
  | none => simp [compactSyntaxParserStateOutput] at houtput
  | some result =>
      cases result with
      | none => simp [compactSyntaxParserStateOutput] at houtput
      | some output =>
          simpa [compactSyntaxParserStateOutput,
            CompactProofStateRealizes] using houtput

theorem compactProofTokenParser_success_iff
    (tokens suffix : List Nat) :
    compactProofTokenParser tokens = some suffix <->
      exists tree : ListedCheckedPAProofTree,
        tokens = compactListedProofTokens tree ++ suffix := by
  constructor
  · intro hparser
    have hfinal := compactProofParserStateOutput_realizes
      (compactProofTokenParserRun tokens) suffix hparser
    have hinitial := compactProofParser_iterate_realizes_backward
      (compactProofParserFuelBound tokens)
      (compactProofParserInitialState tokens) suffix hfinal
    change CompactProofTasksRealize [compactProofTask] tokens suffix
      at hinitial
    cases hinitial with
    | proof tree rest =>
        cases rest
        exact ⟨tree, rfl⟩
  · rintro ⟨tree, rfl⟩
    exact compactProofTokenParser_canonical_append tree suffix

#print axioms compactProofTokenParser_success_iff

end FoundationCompactProofTokenMachineInversion
