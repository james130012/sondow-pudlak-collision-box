import integration.FoundationCompactNumericSyntaxValueParser

/-!
# Exact failure semantics for the sequent formula parser

A nonempty sequent parse fails exactly at one formula position: every earlier
formula parse succeeds, while the formula parser returns `none` at that
position.  The theorem retains the complete successful prefix state instead
of introducing an abstract failure certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSequentFormulaFailureSemantics

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser

theorem compactFormulaTokenValues_iterate_eq_none_iff
    (count : Nat) (initialValues : List (List Nat)) (tokens : List Nat) :
    (compactFormulaTokenValuesStep^[count])
        (some (initialValues, tokens)) = none ↔
      ∃ failedIndex < count,
      ∃ values currentTokens,
        (compactFormulaTokenValuesStep^[failedIndex])
            (some (initialValues, tokens)) =
          some (values, currentTokens) ∧
        compactFormulaTokenValueParser 0 currentTokens = none := by
  induction count generalizing initialValues tokens with
  | zero => simp
  | succ count ih =>
      rw [Function.iterate_succ_apply]
      cases hparser : compactFormulaTokenValueParser 0 tokens with
      | none =>
          have hstep : compactFormulaTokenValuesStep
              (some (initialValues, tokens)) = none := by
            simp [compactFormulaTokenValuesStep, hparser]
          rw [hstep, compactFormulaTokenValuesStep_iterate_none]
          constructor
          · intro _
            exact ⟨0, Nat.zero_lt_succ count,
              initialValues, tokens, rfl, hparser⟩
          · intro _
            rfl
      | some formulaResult =>
          rcases formulaResult with ⟨formulaValue, afterFormula⟩
          have hstep : compactFormulaTokenValuesStep
              (some (initialValues, tokens)) =
                some (initialValues ++ [formulaValue], afterFormula) := by
            simp [compactFormulaTokenValuesStep, hparser]
          rw [hstep]
          constructor
          · intro hnone
            rcases (ih (initialValues ++ [formulaValue]) afterFormula).mp
                hnone with
              ⟨failedIndex, hfailedIndex, values, currentTokens,
                hprefix, hfailure⟩
            refine ⟨failedIndex + 1, by omega,
              values, currentTokens, ?_, hfailure⟩
            rw [Function.iterate_succ_apply, hstep]
            exact hprefix
          · rintro ⟨failedIndex, hfailedIndex, values, currentTokens,
              hprefix, hfailure⟩
            cases failedIndex with
            | zero =>
                simp only [Function.iterate_zero_apply] at hprefix
                cases hprefix
                rw [hparser] at hfailure
                contradiction
            | succ failedIndex =>
                have hprefix' :
                    (compactFormulaTokenValuesStep^[failedIndex])
                        (some
                          (initialValues ++ [formulaValue], afterFormula)) =
                      some (values, currentTokens) := by
                  simpa only [Function.iterate_succ_apply, hstep] using hprefix
                apply (ih (initialValues ++ [formulaValue]) afterFormula).mpr
                exact ⟨failedIndex, by omega,
                  values, currentTokens, hprefix', hfailure⟩

theorem compactFormulaTokenValuesRepeat_eq_none_iff
    (count : Nat) (tokens : List Nat) :
    compactFormulaTokenValuesRepeat count tokens = none ↔
      ∃ failedIndex < count,
      ∃ values currentTokens,
        compactFormulaTokenValuesRepeat failedIndex tokens =
          some (values, currentTokens) ∧
        compactFormulaTokenValueParser 0 currentTokens = none := by
  simpa [compactFormulaTokenValuesRepeat,
    compactFormulaTokenValuesInitial] using
      compactFormulaTokenValues_iterate_eq_none_iff count [] tokens

theorem compactSequentTokenValueParser_cons_eq_none_iff
    (count : Nat) (tokens : List Nat) :
    compactSequentTokenValueParser (count :: tokens) = none ↔
      ∃ failedIndex < count,
      ∃ values currentTokens,
        compactFormulaTokenValuesRepeat failedIndex tokens =
          some (values, currentTokens) ∧
        compactFormulaTokenValueParser 0 currentTokens = none := by
  simp only [compactSequentTokenValueParser, List.head?_cons,
    List.tail_cons, Option.bind_some]
  exact compactFormulaTokenValuesRepeat_eq_none_iff count tokens

theorem compactSequentTokenValueParser_eq_none_iff
    (input : List Nat) :
    compactSequentTokenValueParser input = none ↔
      input = [] ∨
      ∃ count tokens, input = count :: tokens ∧
      ∃ failedIndex < count,
      ∃ values currentTokens,
        compactFormulaTokenValuesRepeat failedIndex tokens =
          some (values, currentTokens) ∧
        compactFormulaTokenValueParser 0 currentTokens = none := by
  cases input with
  | nil => simp [compactSequentTokenValueParser]
  | cons count tokens =>
      constructor
      · intro hparser
        exact Or.inr ⟨count, tokens, rfl,
          (compactSequentTokenValueParser_cons_eq_none_iff
            count tokens).mp hparser⟩
      · rintro (hinput | ⟨otherCount, otherTokens, hinput, hfailure⟩)
        · contradiction
        · cases hinput
          exact (compactSequentTokenValueParser_cons_eq_none_iff
            count tokens).mpr hfailure

#print axioms compactFormulaTokenValues_iterate_eq_none_iff
#print axioms compactFormulaTokenValuesRepeat_eq_none_iff
#print axioms compactSequentTokenValueParser_cons_eq_none_iff
#print axioms compactSequentTokenValueParser_eq_none_iff

end FoundationCompactNumericListedDirectSequentFormulaFailureSemantics
