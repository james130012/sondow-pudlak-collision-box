import integration.FoundationCompactCertificateTokenMachine
import integration.FoundationCompactSyntaxTokenMachineInversion

/-!
# Exact inversion for compact PA certificates

This file closes arbitrary-input inversion for both the 23 PA-axiom
certificate constructors and the recursive structural certificate tree.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationCompactCertificateTokenMachineInversion

open FoundationCompactArithmeticSymbolCode
open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTokenMachineInversion
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertificateTokenMachine

theorem compactPAAxiomCertificateTokenParser_success_iff
    (tokens suffix : List Nat) :
    compactPAAxiomCertificateTokenParser tokens = some suffix <->
      exists certificate : PAAxiomCertificate,
        tokens = compactPAAxiomCertificateTokens certificate ++ suffix := by
  constructor
  · intro hparse
    cases tokens with
    | nil =>
        simp [compactPAAxiomCertificateTokenParser] at hparse
    | cons tag body =>
        by_cases h3 : tag = 3
        · subst tag
          cases body with
          | nil =>
              simp [compactPAAxiomCertificateTokenParser] at hparse
          | cons arity tail =>
              cases tail with
              | nil =>
                  simp [compactPAAxiomCertificateTokenParser,
                    compactTokenAt] at hparse
              | cons functionCode rest =>
                  by_cases hvalid :
                      ArithmeticFuncCodeValid arity functionCode
                  · have hsuffix : rest = suffix := by
                      simpa [compactPAAxiomCertificateTokenParser,
                        compactTokenAt, hvalid] using hparse
                    obtain ⟨functionSymbol, hcode⟩ :=
                      arithmeticFuncCodeValid_exists_symbol hvalid
                    subst functionCode
                    subst rest
                    exact ⟨.eqFuncExt functionSymbol,
                      by simp [compactPAAxiomCertificateTokens]⟩
                  · simp [compactPAAxiomCertificateTokenParser,
                      compactTokenAt, hvalid] at hparse
        · by_cases h4 : tag = 4
          · subst tag
            cases body with
            | nil =>
                simp [compactPAAxiomCertificateTokenParser] at hparse
            | cons arity tail =>
                cases tail with
                | nil =>
                    simp [compactPAAxiomCertificateTokenParser,
                      compactTokenAt] at hparse
                | cons relationCode rest =>
                    by_cases hvalid :
                        ArithmeticRelCodeValid arity relationCode
                    · have hsuffix : rest = suffix := by
                        simpa [compactPAAxiomCertificateTokenParser,
                          compactTokenAt, hvalid] using hparse
                      obtain ⟨relationSymbol, hcode⟩ :=
                        arithmeticRelCodeValid_exists_symbol hvalid
                      subst relationCode
                      subst rest
                      exact ⟨.eqRelExt relationSymbol,
                        by simp [compactPAAxiomCertificateTokens]⟩
                    · simp [compactPAAxiomCertificateTokenParser,
                        compactTokenAt, hvalid] at hparse
          · by_cases h22 : tag = 22
            · subst tag
              have hformula :
                  compactFormulaTokenParser 1 body = some suffix := by
                simpa [compactPAAxiomCertificateTokenParser] using hparse
              obtain ⟨formula, htokens⟩ :=
                (compactFormulaTokenParser_success_iff
                  1 body suffix).1 hformula
              subst body
              exact ⟨.induction formula,
                by simp [compactPAAxiomCertificateTokens]⟩
            · have hlt : tag < 22 := by
                by_contra hnot
                have hge : 22 <= tag := Nat.le_of_not_gt hnot
                simp [compactPAAxiomCertificateTokenParser, h3, h4,
                  h22, Nat.not_lt_of_ge hge] at hparse
              have hsuffix : body = suffix := by
                simpa [compactPAAxiomCertificateTokenParser, h3, h4,
                  h22, hlt] using hparse
              subst body
              have hcases :
                  tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 ∨
                  tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8 ∨ tag = 9 ∨
                  tag = 10 ∨ tag = 11 ∨ tag = 12 ∨ tag = 13 ∨
                  tag = 14 ∨ tag = 15 ∨ tag = 16 ∨ tag = 17 ∨
                  tag = 18 ∨ tag = 19 ∨ tag = 20 ∨ tag = 21 := by
                omega
              rcases hcases with
                (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                  rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                  rfl | rfl | rfl | rfl | rfl | rfl)
              · exact ⟨.eqRefl,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.eqSymm,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.eqTrans,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact False.elim (h3 rfl)
              · exact False.elim (h4 rfl)
              · exact ⟨.addZero,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.addAssoc,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.addComm,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.addEqOfLt,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.zeroLe,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.zeroLtOne,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.oneLeOfZeroLt,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.addLtAdd,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.mulZero,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.mulOne,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.mulAssoc,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.mulComm,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.mulLtMul,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.distr,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.ltIrrefl,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.ltTrans,
                  by simp [compactPAAxiomCertificateTokens]⟩
              · exact ⟨.ltTri,
                  by simp [compactPAAxiomCertificateTokens]⟩
  · rintro ⟨certificate, rfl⟩
    exact compactPAAxiomCertificateTokenParser_canonical_append
      certificate suffix

inductive CompactCertificateTasksRealize :
    List CompactCertificateTask -> List Nat -> List Nat -> Prop
  | nil (suffix : List Nat) :
      CompactCertificateTasksRealize [] suffix suffix
  | structural {taskAux taskPayload : Nat}
      (certificate : StructuralValidityCertificate)
      {middle suffix : List Nat} {tasks : List CompactCertificateTask}
      (rest : CompactCertificateTasksRealize tasks middle suffix) :
      CompactCertificateTasksRealize
        ((8, taskAux, taskPayload) :: tasks)
        (compactStructuralCertificateTokens certificate ++ middle) suffix
  | paAxiom {taskAux taskPayload : Nat}
      (certificate : PAAxiomCertificate)
      {middle suffix : List Nat} {tasks : List CompactCertificateTask}
      (rest : CompactCertificateTasksRealize tasks middle suffix) :
      CompactCertificateTasksRealize
        ((9, taskAux, taskPayload) :: tasks)
        (compactPAAxiomCertificateTokens certificate ++ middle) suffix

def CompactCertificateStateRealizes
    (state : CompactCertificateParserState) (suffix : List Nat) : Prop :=
  match state.2.2 with
  | none => CompactCertificateTasksRealize state.2.1 state.1 suffix
  | some none => False
  | some (some output) => output = suffix

@[simp] theorem compactCertificateStateRealizes_continue
    (tokens suffix : List Nat) (tasks : List CompactCertificateTask) :
    CompactCertificateStateRealizes
        (compactSyntaxContinue tokens tasks) suffix <->
      CompactCertificateTasksRealize tasks tokens suffix := by
  rfl

@[simp] theorem compactCertificateStateRealizes_failure
    (tokens suffix : List Nat) (tasks : List CompactCertificateTask) :
    ¬ CompactCertificateStateRealizes
      (compactSyntaxFailure tokens tasks) suffix := by
  exact fun h => h

theorem compactCertificateAxiomTokenStep_realizes_backward
    (taskAux taskPayload : Nat) (tokens suffix : List Nat)
    (tasks : List CompactCertificateTask)
    (hnext : CompactCertificateStateRealizes
      (compactCertificateAxiomTokenStep tokens tasks) suffix) :
    CompactCertificateTasksRealize
      ((9, taskAux, taskPayload) :: tasks) tokens suffix := by
  cases hparse : compactPAAxiomCertificateTokenParser tokens with
  | none =>
      exfalso
      simpa [compactCertificateAxiomTokenStep, hparse,
        compactSyntaxFailure, CompactCertificateStateRealizes] using hnext
  | some middle =>
      have hrest :
          CompactCertificateTasksRealize tasks middle suffix := by
        simpa [compactCertificateAxiomTokenStep, hparse,
          compactSyntaxContinue, CompactCertificateStateRealizes] using hnext
      obtain ⟨certificate, htokens⟩ :=
        (compactPAAxiomCertificateTokenParser_success_iff
          tokens middle).1 hparse
      subst tokens
      exact CompactCertificateTasksRealize.paAxiom
        (taskAux := taskAux) (taskPayload := taskPayload)
        certificate hrest

theorem compactStructuralCertificateNodeTokenStep_realizes_backward
    (taskAux taskPayload : Nat) (tokens suffix : List Nat)
    (tasks : List CompactCertificateTask)
    (hnext : CompactCertificateStateRealizes
      (compactStructuralCertificateNodeTokenStep tokens tasks) suffix) :
    CompactCertificateTasksRealize
      ((8, taskAux, taskPayload) :: tasks) tokens suffix := by
  cases tokens with
  | nil =>
      exfalso
      simpa [compactStructuralCertificateNodeTokenStep,
        compactSyntaxFailure, CompactCertificateStateRealizes] using hnext
  | cons tag body =>
      by_cases h0 : tag = 0
      · subst tag
        have hrest : CompactCertificateTasksRealize tasks body suffix := by
          simpa [compactStructuralCertificateNodeTokenStep,
            compactSyntaxContinue, CompactCertificateStateRealizes]
            using hnext
        simpa [compactStructuralCertificateTokens] using
          CompactCertificateTasksRealize.structural
            (taskAux := taskAux) (taskPayload := taskPayload)
            .leaf hrest
      · by_cases h1 : tag = 1
        · subst tag
          have hfield : CompactCertificateTasksRealize
              (compactPAAxiomCertificateTask :: tasks) body suffix := by
            simpa [compactStructuralCertificateNodeTokenStep,
              compactSyntaxContinue, CompactCertificateStateRealizes]
              using hnext
          cases hfield with
          | paAxiom certificate rest =>
              simpa [compactStructuralCertificateTokens] using
                CompactCertificateTasksRealize.structural
                  (taskAux := taskAux) (taskPayload := taskPayload)
                  (.axiomCert certificate) rest
        · by_cases h2 : tag = 2
          · subst tag
            have hfield : CompactCertificateTasksRealize
                (compactStructuralCertificateTask :: tasks) body suffix := by
              simpa [compactStructuralCertificateNodeTokenStep,
                compactSyntaxContinue, CompactCertificateStateRealizes]
                using hnext
            cases hfield with
            | structural premise rest =>
                simpa [compactStructuralCertificateTokens] using
                  CompactCertificateTasksRealize.structural
                    (taskAux := taskAux) (taskPayload := taskPayload)
                    (.unary premise) rest
          · by_cases h3 : tag = 3
            · subst tag
              have hfields : CompactCertificateTasksRealize
                  (compactStructuralCertificateTask ::
                    compactStructuralCertificateTask :: tasks)
                  body suffix := by
                simpa [compactStructuralCertificateNodeTokenStep,
                  compactSyntaxContinue, CompactCertificateStateRealizes]
                  using hnext
              cases hfields with
              | structural left hright =>
                  cases hright with
                  | structural right rest =>
                      simpa [compactStructuralCertificateTokens,
                        List.append_assoc] using
                        CompactCertificateTasksRealize.structural
                          (taskAux := taskAux) (taskPayload := taskPayload)
                          (.binary left right) rest
            · exfalso
              simpa [compactStructuralCertificateNodeTokenStep, h0, h1,
                h2, h3, compactSyntaxFailure,
                CompactCertificateStateRealizes] using hnext

theorem compactCertificateTaskTokenStep_realizes_backward
    (task : CompactCertificateTask) (tokens suffix : List Nat)
    (tasks : List CompactCertificateTask)
    (hnext : CompactCertificateStateRealizes
      (compactCertificateTaskTokenStep (task, tokens, tasks)) suffix) :
    CompactCertificateTasksRealize (task :: tasks) tokens suffix := by
  rcases task with ⟨kind, taskAux, taskPayload⟩
  by_cases h8 : kind = 8
  · subst kind
    simpa [compactCertificateTaskTokenStep] using
      compactStructuralCertificateNodeTokenStep_realizes_backward
        taskAux taskPayload tokens suffix tasks hnext
  · by_cases h9 : kind = 9
    · subst kind
      simpa [compactCertificateTaskTokenStep] using
        compactCertificateAxiomTokenStep_realizes_backward
          taskAux taskPayload tokens suffix tasks hnext
    · exfalso
      simpa [compactCertificateTaskTokenStep, h8, h9,
        compactSyntaxFailure, CompactCertificateStateRealizes] using hnext

theorem compactCertificateParserStep_realizes_backward
    (state : CompactCertificateParserState) (suffix : List Nat)
    (hnext : CompactCertificateStateRealizes
      (compactCertificateParserStep state) suffix) :
    CompactCertificateStateRealizes state suffix := by
  rcases state with ⟨tokens, tasks, status⟩
  cases status with
  | some result =>
      simpa [compactCertificateParserStep,
        CompactCertificateStateRealizes] using hnext
  | none =>
      cases tasks with
      | nil =>
          have htokens : tokens = suffix := by
            simpa [compactCertificateParserStep,
              compactCertificateParserRunningStep,
              CompactCertificateStateRealizes] using hnext
          subst tokens
          exact CompactCertificateTasksRealize.nil suffix
      | cons task tasks =>
          change CompactCertificateTasksRealize
            (task :: tasks) tokens suffix
          exact compactCertificateTaskTokenStep_realizes_backward
            task tokens suffix tasks <| by
              simpa [compactCertificateParserStep,
                compactCertificateParserRunningStep] using hnext

theorem compactCertificateParser_iterate_realizes_backward
    (fuel : Nat) (state : CompactCertificateParserState)
    (suffix : List Nat)
    (hfinal : CompactCertificateStateRealizes
      ((compactCertificateParserStep^[fuel]) state) suffix) :
    CompactCertificateStateRealizes state suffix := by
  induction fuel generalizing state with
  | zero => exact hfinal
  | succ fuel ih =>
      rw [Function.iterate_succ_apply] at hfinal
      exact compactCertificateParserStep_realizes_backward state suffix
        (ih (compactCertificateParserStep state) hfinal)

theorem compactCertificateParserStateOutput_realizes
    (state : CompactCertificateParserState) (suffix : List Nat)
    (houtput : compactSyntaxParserStateOutput state = some suffix) :
    CompactCertificateStateRealizes state suffix := by
  rcases state with ⟨tokens, tasks, status⟩
  cases status with
  | none => simp [compactSyntaxParserStateOutput] at houtput
  | some result =>
      cases result with
      | none => simp [compactSyntaxParserStateOutput] at houtput
      | some output =>
          simpa [compactSyntaxParserStateOutput,
            CompactCertificateStateRealizes] using houtput

theorem compactStructuralCertificateTokenParser_success_iff
    (tokens suffix : List Nat) :
    compactStructuralCertificateTokenParser tokens = some suffix <->
      exists certificate : StructuralValidityCertificate,
        tokens = compactStructuralCertificateTokens certificate ++ suffix := by
  constructor
  · intro hparser
    have hfinal := compactCertificateParserStateOutput_realizes
      (compactStructuralCertificateTokenParserRun tokens) suffix hparser
    have hinitial := compactCertificateParser_iterate_realizes_backward
      (compactCertificateParserFuelBound tokens)
      (compactCertificateParserInitialState tokens) suffix hfinal
    change CompactCertificateTasksRealize
      [compactStructuralCertificateTask] tokens suffix at hinitial
    cases hinitial with
    | structural certificate rest =>
        cases rest
        exact ⟨certificate, rfl⟩
  · rintro ⟨certificate, rfl⟩
    exact compactStructuralCertificateTokenParser_canonical_append
      certificate suffix

#print axioms compactPAAxiomCertificateTokenParser_success_iff
#print axioms compactStructuralCertificateTokenParser_success_iff

end FoundationCompactCertificateTokenMachineInversion
