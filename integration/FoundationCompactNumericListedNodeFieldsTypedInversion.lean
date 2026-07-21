import integration.FoundationCompactNumericListedNodeFields

/-!
# Typed inversion for numeric listed-node fields

Every successful immediate-field parser result has a canonical typed source.
Besides recovering the sequent and rule-specific syntax, the theorems below
identify the complete numeric field tuple and the unconsumed child suffix.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedNodeFieldsTypedInversion

open FoundationCompactSyntaxTokenMachine
open FoundationCompactClosedFormulaTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedNodeFields

theorem compactNodeSequentOnlyFields_eq_some_iff_exists_typed
    (tokens : List Nat) (fields : CompactNumericNodeFields) :
    compactNodeSequentOnlyFields tokens = some fields <->
      exists (Gamma : List LO.FirstOrder.ArithmeticProposition)
          (suffix : List Nat),
        tokens = compactSequentListTokens Gamma ++ suffix /\
          fields =
            (arithmeticPropositionTokenValues Gamma,
              (([] : List Nat),
                (([] : List Nat), (([] : List Nat), suffix)))) := by
  constructor
  · intro hfields
    cases hsequent : compactSequentTokenValueParser tokens with
    | none =>
        simp [compactNodeSequentOnlyFields, hsequent] at hfields
    | some parsedSequent =>
        rcases parsedSequent with ⟨values, suffix⟩
        simp [compactNodeSequentOnlyFields, hsequent] at hfields
        subst fields
        obtain ⟨Gamma, htokens, hvalues⟩ :=
          compactSequentTokenValueParser_sound hsequent
        refine ⟨Gamma, suffix, htokens, ?_⟩
        rw [hvalues]
        rfl
  · rintro ⟨Gamma, suffix, rfl, rfl⟩
    exact compactNodeSequentOnlyFields_canonical_append Gamma suffix

theorem compactNodeSequentFormulaFields_eq_some_iff_exists_typed
    (binderArity : Nat) (tokens : List Nat)
    (fields : CompactNumericNodeFields) :
    compactNodeSequentFormulaFields binderArity tokens = some fields <->
      exists (Gamma : List LO.FirstOrder.ArithmeticProposition)
          (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
          (suffix : List Nat),
        tokens = compactSequentListTokens Gamma ++
            compactArithmeticFormulaTokens formula ++ suffix /\
          fields =
            (arithmeticPropositionTokenValues Gamma,
              (compactArithmeticFormulaTokens formula,
                (([] : List Nat), (([] : List Nat), suffix)))) := by
  constructor
  · intro hfields
    cases hsequent : compactSequentTokenValueParser tokens with
    | none =>
        simp [compactNodeSequentFormulaFields, hsequent] at hfields
    | some parsedSequent =>
        rcases parsedSequent with ⟨values, afterSequent⟩
        cases hformula :
            compactFormulaTokenValueParser binderArity afterSequent with
        | none =>
            simp [compactNodeSequentFormulaFields, hsequent, hformula]
              at hfields
        | some parsedFormula =>
            rcases parsedFormula with ⟨formulaValue, suffix⟩
            simp [compactNodeSequentFormulaFields, hsequent, hformula]
              at hfields
            subst fields
            obtain ⟨Gamma, htokens, hvalues⟩ :=
              compactSequentTokenValueParser_sound hsequent
            obtain ⟨formula, hafterSequent, hformulaValue⟩ :=
              compactFormulaTokenValueParser_sound hformula
            refine ⟨Gamma, formula, suffix, ?_, ?_⟩
            · rw [htokens, hafterSequent]
              simp only [List.append_assoc]
            · rw [hvalues, hformulaValue]
              rfl
  · rintro ⟨Gamma, formula, suffix, rfl, rfl⟩
    exact compactNodeSequentFormulaFields_canonical_append
      Gamma formula suffix

theorem compactNodeSequentTwoFormulaFields_eq_some_iff_exists_typed
    (binderArity : Nat) (tokens : List Nat)
    (fields : CompactNumericNodeFields) :
    compactNodeSequentTwoFormulaFields binderArity tokens = some fields <->
      exists (Gamma : List LO.FirstOrder.ArithmeticProposition)
          (first second :
            LO.FirstOrder.ArithmeticSemiformula Nat binderArity)
          (suffix : List Nat),
        tokens = compactSequentListTokens Gamma ++
            compactArithmeticFormulaTokens first ++
            compactArithmeticFormulaTokens second ++ suffix /\
          fields =
            (arithmeticPropositionTokenValues Gamma,
              (compactArithmeticFormulaTokens first,
                (compactArithmeticFormulaTokens second,
                  (([] : List Nat), suffix)))) := by
  constructor
  · intro hfields
    cases hsequent : compactSequentTokenValueParser tokens with
    | none =>
        simp [compactNodeSequentTwoFormulaFields,
          compactNodeSequentFormulaFields, hsequent] at hfields
    | some parsedSequent =>
        rcases parsedSequent with ⟨values, afterSequent⟩
        cases hfirst :
            compactFormulaTokenValueParser binderArity afterSequent with
        | none =>
            simp [compactNodeSequentTwoFormulaFields,
              compactNodeSequentFormulaFields,
              compactNumericNodeFieldsSuffix, hsequent, hfirst] at hfields
        | some parsedFirst =>
            rcases parsedFirst with ⟨firstValue, afterFirst⟩
            cases hsecond :
                compactFormulaTokenValueParser binderArity afterFirst with
            | none =>
                simp [compactNodeSequentTwoFormulaFields,
                  compactNodeSequentFormulaFields,
                  compactNumericNodeFieldsSuffix, hsequent, hfirst, hsecond]
                  at hfields
            | some parsedSecond =>
                rcases parsedSecond with ⟨secondValue, suffix⟩
                simp [compactNodeSequentTwoFormulaFields,
                  compactNodeSequentFormulaFields,
                  compactNumericNodeFieldsSuffix, hsequent, hfirst, hsecond]
                  at hfields
                subst fields
                obtain ⟨Gamma, htokens, hvalues⟩ :=
                  compactSequentTokenValueParser_sound hsequent
                obtain ⟨first, hafterSequent, hfirstValue⟩ :=
                  compactFormulaTokenValueParser_sound hfirst
                obtain ⟨second, hafterFirst, hsecondValue⟩ :=
                  compactFormulaTokenValueParser_sound hsecond
                refine ⟨Gamma, first, second, suffix, ?_, ?_⟩
                · rw [htokens, hafterSequent, hafterFirst]
                  simp only [List.append_assoc]
                · rw [hvalues, hfirstValue, hsecondValue]
                  rfl
  · rintro ⟨Gamma, first, second, suffix, rfl, rfl⟩
    exact compactNodeSequentTwoFormulaFields_canonical_append
      Gamma first second suffix

theorem compactNodeSequentFormulaTermFields_eq_some_iff_exists_typed
    (formulaArity termArity : Nat) (tokens : List Nat)
    (fields : CompactNumericNodeFields) :
    compactNodeSequentFormulaTermFields formulaArity termArity tokens =
        some fields <->
      exists (Gamma : List LO.FirstOrder.ArithmeticProposition)
          (formula : LO.FirstOrder.ArithmeticSemiformula Nat formulaArity)
          (term : LO.FirstOrder.ArithmeticSemiterm Nat termArity)
          (suffix : List Nat),
        tokens = compactSequentListTokens Gamma ++
            compactArithmeticFormulaTokens formula ++
            compactArithmeticTermTokens term ++ suffix /\
          fields =
            (arithmeticPropositionTokenValues Gamma,
              (compactArithmeticFormulaTokens formula,
                (([] : List Nat),
                  (compactArithmeticTermTokens term, suffix)))) := by
  constructor
  · intro hfields
    cases hsequent : compactSequentTokenValueParser tokens with
    | none =>
        simp [compactNodeSequentFormulaTermFields,
          compactNodeSequentFormulaFields, hsequent] at hfields
    | some parsedSequent =>
        rcases parsedSequent with ⟨values, afterSequent⟩
        cases hformula :
            compactFormulaTokenValueParser formulaArity afterSequent with
        | none =>
            simp [compactNodeSequentFormulaTermFields,
              compactNodeSequentFormulaFields,
              compactNumericNodeFieldsSuffix, hsequent, hformula] at hfields
        | some parsedFormula =>
            rcases parsedFormula with ⟨formulaValue, afterFormula⟩
            cases hterm : compactTermTokenValueParser termArity afterFormula with
            | none =>
                simp [compactNodeSequentFormulaTermFields,
                  compactNodeSequentFormulaFields,
                  compactNumericNodeFieldsSuffix, hsequent, hformula, hterm]
                  at hfields
            | some parsedTerm =>
                rcases parsedTerm with ⟨termValue, suffix⟩
                simp [compactNodeSequentFormulaTermFields,
                  compactNodeSequentFormulaFields,
                  compactNumericNodeFieldsSuffix, hsequent, hformula, hterm]
                  at hfields
                subst fields
                obtain ⟨Gamma, htokens, hvalues⟩ :=
                  compactSequentTokenValueParser_sound hsequent
                obtain ⟨formula, hafterSequent, hformulaValue⟩ :=
                  compactFormulaTokenValueParser_sound hformula
                obtain ⟨term, hafterFormula, htermValue⟩ :=
                  compactTermTokenValueParser_sound hterm
                refine ⟨Gamma, formula, term, suffix, ?_, ?_⟩
                · rw [htokens, hafterSequent, hafterFormula]
                  simp only [List.append_assoc]
                · rw [hvalues, hformulaValue, htermValue]
                  rfl
  · rintro ⟨Gamma, formula, term, suffix, rfl, rfl⟩
    exact compactNodeSequentFormulaTermFields_canonical_append
      Gamma formula term suffix

theorem compactNodeSequentClosedFormulaFields_eq_some_iff_exists_typed
    (tokens : List Nat) (fields : CompactNumericNodeFields) :
    compactNodeSequentClosedFormulaFields tokens = some fields <->
      exists (Gamma : List LO.FirstOrder.ArithmeticProposition)
          (sentence : LO.FirstOrder.ArithmeticSentence)
          (suffix : List Nat),
        tokens = compactSequentListTokens Gamma ++
            compactArithmeticFormulaTokens
              (Rewriting.emb sentence :
                LO.FirstOrder.ArithmeticProposition) ++ suffix /\
          fields =
            (arithmeticPropositionTokenValues Gamma,
              (compactArithmeticFormulaTokens
                  (Rewriting.emb sentence :
                    LO.FirstOrder.ArithmeticProposition),
                (([] : List Nat), (([] : List Nat), suffix)))) := by
  constructor
  · intro hfields
    cases hsequent : compactSequentTokenValueParser tokens with
    | none =>
        simp [compactNodeSequentClosedFormulaFields, hsequent] at hfields
    | some parsedSequent =>
        rcases parsedSequent with ⟨values, afterSequent⟩
        cases hclosedValue :
            compactClosedFormulaTokenValueParser afterSequent with
        | none =>
            simp [compactNodeSequentClosedFormulaFields,
              hsequent, hclosedValue] at hfields
        | some parsedFormula =>
            rcases parsedFormula with ⟨formulaValue, suffix⟩
            simp [compactNodeSequentClosedFormulaFields,
              hsequent, hclosedValue] at hfields
            subst fields
            obtain ⟨Gamma, htokens, hvalues⟩ :=
              compactSequentTokenValueParser_sound hsequent
            have hclosedData :
                compactClosedFormulaTokenParser 0 afterSequent = some suffix /\
                  consumedTokenPrefix afterSequent suffix = formulaValue := by
              simpa [compactClosedFormulaTokenValueParser] using hclosedValue
            obtain ⟨formula, hfree, hafterSequent⟩ :=
              (compactClosedFormulaTokenParser_success_iff
                0 afterSequent suffix).mp hclosedData.1
            let sentence : LO.FirstOrder.ArithmeticSentence :=
              formula.toEmpty hfree
            have hemb :
                (Rewriting.emb sentence :
                  LO.FirstOrder.ArithmeticProposition) = formula := by
              simp [sentence]
            have hformulaValue :
                formulaValue = compactArithmeticFormulaTokens formula := by
              calc
                formulaValue = consumedTokenPrefix afterSequent suffix :=
                  hclosedData.2.symm
                _ = compactArithmeticFormulaTokens formula := by
                  rw [hafterSequent]
                  simp
            refine ⟨Gamma, sentence, suffix, ?_, ?_⟩
            · rw [htokens, hafterSequent, hemb]
              simp only [List.append_assoc]
            · rw [hvalues, hformulaValue, hemb]
              rfl
  · rintro ⟨Gamma, sentence, suffix, rfl, rfl⟩
    exact compactNodeSequentClosedFormulaFields_canonical_append
      Gamma sentence suffix

#print axioms compactNodeSequentOnlyFields_eq_some_iff_exists_typed
#print axioms compactNodeSequentFormulaFields_eq_some_iff_exists_typed
#print axioms compactNodeSequentTwoFormulaFields_eq_some_iff_exists_typed
#print axioms compactNodeSequentFormulaTermFields_eq_some_iff_exists_typed
#print axioms compactNodeSequentClosedFormulaFields_eq_some_iff_exists_typed

end FoundationCompactNumericListedNodeFieldsTypedInversion
