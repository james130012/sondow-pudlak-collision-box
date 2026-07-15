import integration.FoundationCompactNumericListedDirectParserSyntaxTraceInstallation
import integration.FoundationCompactClosedFormulaTokenMachine

/-!
# Successful closed-parser traces use the ordinary syntax step safely

The closed formula parser differs from the ordinary syntax parser only when a
term task sees the free-variable tag `1`.  Such a step immediately enters the
absorbing failure state.  Consequently no successful closed-parser trace can
take that branch.  This file proves the exact semantic bridge in both
directions before the safety condition is arithmetized.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserClosedSuccessBridge

open FoundationCompactSyntaxTokenMachine
open FoundationCompactClosedFormulaTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectParserSyntaxTraceInstallation

/-- A state is safe for replacing the closed parser step by the ordinary
syntax step.  Only a running term task with at least two tokens and tag `1`
is excluded. -/
def CompactClosedSyntaxStepSafe
    (state : CompactUnifiedParserState) : Prop :=
  state.2.2 = none →
    ∀ binderArity repeatCount tail,
      state.2.1 = (0, binderArity, repeatCount) :: tail →
        state.1.length ≤ 1 ∨ compactTokenAt 0 state.1 ≠ 1

theorem compactClosedSyntaxParserStep_eq_compactSyntaxParserStep_of_safe
    (state : CompactUnifiedParserState)
    (hsafe : CompactClosedSyntaxStepSafe state) :
    compactClosedSyntaxParserStep state = compactSyntaxParserStep state := by
  rcases state with ⟨tokens, tasks, status⟩
  cases status with
  | some result =>
      simp [compactClosedSyntaxParserStep, compactSyntaxParserStep]
  | none =>
      cases tasks with
      | nil =>
          simp [compactClosedSyntaxParserStep, compactSyntaxParserStep,
            compactClosedSyntaxRunningStep, compactSyntaxRunningStep]
      | cons task tail =>
          rcases task with ⟨kind, binderArity, repeatCount⟩
          by_cases hkind : kind = 0
          . subst kind
            by_cases hlength : 2 ≤ tokens.length
            . have htag : compactTokenAt 0 tokens ≠ 1 := by
                have hsafe' :
                    tokens.length ≤ 1 ∨ compactTokenAt 0 tokens ≠ 1 := by
                  exact hsafe rfl binderArity repeatCount tail rfl
                rcases hsafe' with
                  hshort | htag
                · omega
                · exact htag
              simp [compactClosedSyntaxParserStep, compactSyntaxParserStep,
                compactClosedSyntaxRunningStep, compactSyntaxRunningStep,
                compactClosedSyntaxTaskTokenStep, compactSyntaxTaskTokenStep,
                compactClosedTermTokenStep, compactTermTokenStep,
                hlength, htag]
            . simp [compactClosedSyntaxParserStep, compactSyntaxParserStep,
                compactClosedSyntaxRunningStep, compactSyntaxRunningStep,
                compactClosedSyntaxTaskTokenStep, compactSyntaxTaskTokenStep,
                compactClosedTermTokenStep, compactTermTokenStep,
                hlength]
          . simp [compactClosedSyntaxParserStep, compactSyntaxParserStep,
              compactClosedSyntaxRunningStep, compactSyntaxRunningStep,
              compactClosedSyntaxTaskTokenStep, compactSyntaxTaskTokenStep,
              hkind]

/-- A state from which the closed parser still reaches a successful output
cannot be poised at the rejected free-variable branch. -/
theorem compactClosedSyntaxStepSafe_of_eventual_success
    (state : CompactUnifiedParserState) (fuel : Nat) (suffix : List Nat)
    (houtput : compactSyntaxParserStateOutput
      ((compactClosedSyntaxParserStep^[fuel]) state) = some suffix) :
    CompactClosedSyntaxStepSafe state := by
  rcases state with ⟨tokens, tasks, status⟩
  intro hstatus binderArity repeatCount tail htasks
  by_cases hshort : tokens.length ≤ 1
  · exact Or.inl hshort
  · apply Or.inr
    intro htag
    have hlength : 2 ≤ tokens.length := by omega
    change status = none at hstatus
    change tasks = (0, binderArity, repeatCount) :: tail at htasks
    change compactTokenAt 0 tokens = 1 at htag
    subst status
    subst tasks
    cases fuel with
    | zero =>
        simp [compactSyntaxParserStateOutput] at houtput
    | succ remaining =>
        have hstep :
            compactClosedSyntaxParserStep
                (tokens, (0, binderArity, repeatCount) :: tail, none) =
              (tokens, tail, some none) := by
          simp [compactClosedSyntaxParserStep, compactClosedSyntaxRunningStep,
            compactClosedSyntaxTaskTokenStep, compactClosedTermTokenStep,
            compactSyntaxFailure, hlength, htag]
        rw [Function.iterate_succ_apply, hstep,
          compactClosedSyntaxParserStep_iterate_done] at houtput
        simp [compactSyntaxParserStateOutput] at houtput

private theorem compactParserTraceState?_eq_some_getI
    {states : List CompactUnifiedParserState} {index : Nat}
    (hindex : index < states.length) :
    compactParserTraceState? states index = some (states.getI index) := by
  unfold compactParserTraceState?
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨hindex, ?_⟩
  rw [List.getI_eq_getElem _ hindex]

/-- Every state before the end of a successful closed-parser local trace is
safe. -/
theorem CompactParserOutputLocalTraceValid.closed_safe_at
    {fuel : Nat} {start : CompactUnifiedParserState}
    {suffix : List Nat} {states : List CompactUnifiedParserState}
    (hvalid : CompactParserOutputLocalTraceValid
      compactClosedSyntaxParserStep fuel start (some suffix) states)
    {index : Nat} (hindex : index <= fuel) :
    CompactClosedSyntaxStepSafe (states.getI index) := by
  have hwhole : compactSyntaxParserStateOutput
      ((compactClosedSyntaxParserStep^[fuel]) start) = some suffix :=
    (compactParserOutput_eq_iff_exists_localTrace
      compactClosedSyntaxParserStep fuel start (some suffix)).mpr
        ⟨states, hvalid⟩
  have hstate := CompactParserLocalTraceValid.getI_eq_stateAt
    hvalid.1 hindex
  apply compactClosedSyntaxStepSafe_of_eventual_success
    (states.getI index) (fuel - index) suffix
  rw [hstate]
  unfold compactParserStateAt
  rw [← Function.iterate_add_apply]
  rw [Nat.sub_add_cancel hindex]
  exact hwhole

/-- A successful closed-parser trace is literally an ordinary syntax-parser
trace on the same list of typed states. -/
theorem CompactParserOutputLocalTraceValid.closed_to_syntax
    {fuel : Nat} {start : CompactUnifiedParserState}
    {suffix : List Nat} {states : List CompactUnifiedParserState}
    (hvalid : CompactParserOutputLocalTraceValid
      compactClosedSyntaxParserStep fuel start (some suffix) states) :
    CompactParserOutputLocalTraceValid
      compactSyntaxParserStep fuel start (some suffix) states := by
  refine ⟨⟨hvalid.1.1, hvalid.1.2.1, ?_⟩, hvalid.2⟩
  intro index hindex
  have hstatesLength : states.length = fuel + 1 := hvalid.1.1
  have hcurrentIndex : index < states.length := by omega
  have hnextIndex : index + 1 < states.length := by omega
  rw [compactParserTraceState?_eq_some_getI hnextIndex,
    compactParserTraceState?_eq_some_getI hcurrentIndex]
  simp only [compactParserStepOption, Option.map_some, Option.some.injEq]
  rw [CompactParserLocalTraceValid.getI_step hvalid.1 hindex]
  exact compactClosedSyntaxParserStep_eq_compactSyntaxParserStep_of_safe
    (states.getI index)
    (CompactParserOutputLocalTraceValid.closed_safe_at
      hvalid (Nat.le_of_lt hindex))

/-- Conversely, an ordinary syntax trace whose states all satisfy the safety
condition is a closed-parser trace on the same state list. -/
theorem CompactParserOutputLocalTraceValid.syntax_to_closed_of_safe
    {fuel : Nat} {start : CompactUnifiedParserState}
    {suffix : List Nat} {states : List CompactUnifiedParserState}
    (hvalid : CompactParserOutputLocalTraceValid
      compactSyntaxParserStep fuel start (some suffix) states)
    (hsafe : ∀ index < fuel,
      CompactClosedSyntaxStepSafe (states.getI index)) :
    CompactParserOutputLocalTraceValid
      compactClosedSyntaxParserStep fuel start (some suffix) states := by
  refine ⟨⟨hvalid.1.1, hvalid.1.2.1, ?_⟩, hvalid.2⟩
  intro index hindex
  have hstatesLength : states.length = fuel + 1 := hvalid.1.1
  have hcurrentIndex : index < states.length := by omega
  have hnextIndex : index + 1 < states.length := by omega
  rw [compactParserTraceState?_eq_some_getI hnextIndex,
    compactParserTraceState?_eq_some_getI hcurrentIndex]
  simp only [compactParserStepOption, Option.map_some, Option.some.injEq]
  rw [CompactParserLocalTraceValid.getI_step hvalid.1 hindex]
  exact (compactClosedSyntaxParserStep_eq_compactSyntaxParserStep_of_safe
    (states.getI index) (hsafe index hindex)).symm

#print axioms compactClosedSyntaxParserStep_eq_compactSyntaxParserStep_of_safe
#print axioms compactClosedSyntaxStepSafe_of_eventual_success
#print axioms CompactParserOutputLocalTraceValid.closed_safe_at
#print axioms CompactParserOutputLocalTraceValid.closed_to_syntax
#print axioms CompactParserOutputLocalTraceValid.syntax_to_closed_of_safe

end FoundationCompactNumericListedDirectParserClosedSuccessBridge
