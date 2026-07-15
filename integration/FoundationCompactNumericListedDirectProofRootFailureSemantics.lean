import integration.FoundationCompactNumericListedNodeFields

/-!
# Exact failure semantics for the proof-root field parser

Every `none` result is classified by the public tag and by the first failing
subparser.  These propositions contain no certificate or bounded-formula
assumption; they are exact unfoldings of the executable parser.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootFailureSemantics

open FoundationCompactSyntaxTokenMachine
open FoundationCompactClosedFormulaTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields

def CompactNodeSequentFormulaFailure
    (binderArity : Nat) (tokens : List Nat) : Prop :=
  compactSequentTokenValueParser tokens = none ∨
    ∃ sequentValues suffix,
      compactSequentTokenValueParser tokens = some (sequentValues, suffix) ∧
      compactFormulaTokenParser binderArity suffix = none

def CompactNodeSequentClosedFormulaFailure
    (tokens : List Nat) : Prop :=
  compactSequentTokenValueParser tokens = none ∨
    ∃ sequentValues suffix,
      compactSequentTokenValueParser tokens = some (sequentValues, suffix) ∧
      compactClosedFormulaTokenParser 0 suffix = none

def CompactNodeSequentTwoFormulaFailure
    (binderArity : Nat) (tokens : List Nat) : Prop :=
  compactNodeSequentFormulaFields binderArity tokens = none ∨
    ∃ first,
      compactNodeSequentFormulaFields binderArity tokens = some first ∧
      compactFormulaTokenParser binderArity
        (compactNumericNodeFieldsSuffix first) = none

def CompactNodeSequentFormulaTermFailure
    (formulaArity termArity : Nat) (tokens : List Nat) : Prop :=
  compactNodeSequentFormulaFields formulaArity tokens = none ∨
    ∃ first,
      compactNodeSequentFormulaFields formulaArity tokens = some first ∧
      compactTermTokenParser termArity
        (compactNumericNodeFieldsSuffix first) = none

theorem compactTermTokenValueParser_eq_none_iff
    (binderArity : Nat) (tokens : List Nat) :
    compactTermTokenValueParser binderArity tokens = none ↔
      compactTermTokenParser binderArity tokens = none := by
  cases hparser : compactTermTokenParser binderArity tokens <;>
    simp [compactTermTokenValueParser, hparser]

theorem compactFormulaTokenValueParser_eq_none_iff
    (binderArity : Nat) (tokens : List Nat) :
    compactFormulaTokenValueParser binderArity tokens = none ↔
      compactFormulaTokenParser binderArity tokens = none := by
  cases hparser : compactFormulaTokenParser binderArity tokens <;>
    simp [compactFormulaTokenValueParser, hparser]

theorem compactClosedFormulaTokenValueParser_eq_none_iff
    (tokens : List Nat) :
    compactClosedFormulaTokenValueParser tokens = none ↔
      compactClosedFormulaTokenParser 0 tokens = none := by
  cases hparser : compactClosedFormulaTokenParser 0 tokens <;>
    simp [compactClosedFormulaTokenValueParser, hparser]

theorem compactNodeSequentOnlyFields_eq_none_iff
    (tokens : List Nat) :
    compactNodeSequentOnlyFields tokens = none ↔
      compactSequentTokenValueParser tokens = none := by
  cases hparser : compactSequentTokenValueParser tokens <;>
    simp [compactNodeSequentOnlyFields, hparser]

theorem compactNodeSequentFormulaFields_eq_none_iff
    (binderArity : Nat) (tokens : List Nat) :
    compactNodeSequentFormulaFields binderArity tokens = none ↔
      CompactNodeSequentFormulaFailure binderArity tokens := by
  cases hsequent : compactSequentTokenValueParser tokens with
  | none =>
      simp [compactNodeSequentFormulaFields,
        CompactNodeSequentFormulaFailure, hsequent]
  | some parsed =>
      rcases parsed with ⟨sequentValues, suffix⟩
      rw [CompactNodeSequentFormulaFailure]
      simp only [hsequent, Option.some.injEq, Prod.mk.injEq]
      simp [compactNodeSequentFormulaFields, hsequent,
        compactFormulaTokenValueParser_eq_none_iff]

theorem compactNodeSequentClosedFormulaFields_eq_none_iff
    (tokens : List Nat) :
    compactNodeSequentClosedFormulaFields tokens = none ↔
      CompactNodeSequentClosedFormulaFailure tokens := by
  cases hsequent : compactSequentTokenValueParser tokens with
  | none =>
      simp [compactNodeSequentClosedFormulaFields,
        CompactNodeSequentClosedFormulaFailure, hsequent]
  | some parsed =>
      rcases parsed with ⟨sequentValues, suffix⟩
      rw [CompactNodeSequentClosedFormulaFailure]
      simp only [hsequent, Option.some.injEq, Prod.mk.injEq]
      simp [compactNodeSequentClosedFormulaFields, hsequent,
        compactClosedFormulaTokenValueParser_eq_none_iff]

theorem compactNodeSequentTwoFormulaFields_eq_none_iff
    (binderArity : Nat) (tokens : List Nat) :
    compactNodeSequentTwoFormulaFields binderArity tokens = none ↔
      CompactNodeSequentTwoFormulaFailure binderArity tokens := by
  cases hfirst : compactNodeSequentFormulaFields binderArity tokens with
  | none =>
      simp [compactNodeSequentTwoFormulaFields,
        CompactNodeSequentTwoFormulaFailure, hfirst]
  | some first =>
      rw [CompactNodeSequentTwoFormulaFailure]
      simp only [hfirst]
      simp [compactNodeSequentTwoFormulaFields, hfirst,
        compactFormulaTokenValueParser_eq_none_iff]

theorem compactNodeSequentFormulaTermFields_eq_none_iff
    (formulaArity termArity : Nat) (tokens : List Nat) :
    compactNodeSequentFormulaTermFields formulaArity termArity tokens = none ↔
      CompactNodeSequentFormulaTermFailure formulaArity termArity tokens := by
  cases hfirst : compactNodeSequentFormulaFields formulaArity tokens with
  | none =>
      simp [compactNodeSequentFormulaTermFields,
        CompactNodeSequentFormulaTermFailure, hfirst]
  | some first =>
      rw [CompactNodeSequentFormulaTermFailure]
      simp only [hfirst]
      simp [compactNodeSequentFormulaTermFields, hfirst,
        compactTermTokenValueParser_eq_none_iff]

inductive CompactProofRootFailure : List Nat → Prop
  | empty : CompactProofRootFailure []
  | invalid (tag : Nat) (body : List Nat) (htag : 9 < tag) :
      CompactProofRootFailure (tag :: body)
  | tag0 (body : List Nat)
      (hfailure : compactNodeSequentFormulaFields 0 body = none) :
      CompactProofRootFailure (0 :: body)
  | tag1 (body : List Nat)
      (hfailure : compactNodeSequentClosedFormulaFields body = none) :
      CompactProofRootFailure (1 :: body)
  | tag2 (body : List Nat)
      (hfailure : compactNodeSequentOnlyFields body = none) :
      CompactProofRootFailure (2 :: body)
  | tag3 (body : List Nat)
      (hfailure : compactNodeSequentTwoFormulaFields 0 body = none) :
      CompactProofRootFailure (3 :: body)
  | tag4 (body : List Nat)
      (hfailure : compactNodeSequentTwoFormulaFields 0 body = none) :
      CompactProofRootFailure (4 :: body)
  | tag5 (body : List Nat)
      (hfailure : compactNodeSequentFormulaFields 1 body = none) :
      CompactProofRootFailure (5 :: body)
  | tag6 (body : List Nat)
      (hfailure : compactNodeSequentFormulaTermFields 1 0 body = none) :
      CompactProofRootFailure (6 :: body)
  | tag7 (body : List Nat)
      (hfailure : compactNodeSequentOnlyFields body = none) :
      CompactProofRootFailure (7 :: body)
  | tag8 (body : List Nat)
      (hfailure : compactNodeSequentOnlyFields body = none) :
      CompactProofRootFailure (8 :: body)
  | tag9 (body : List Nat)
      (hfailure : compactNodeSequentFormulaFields 0 body = none) :
      CompactProofRootFailure (9 :: body)

theorem compactListedProofNodeFieldsParser_eq_none_iff
    (input : List Nat) :
    compactListedProofNodeFieldsParser input = none ↔
      CompactProofRootFailure input := by
  constructor
  · intro hparser
    cases input with
    | nil => exact .empty
    | cons tag body =>
        by_cases h0 : tag = 0
        · subst tag
          exact .tag0 body (by
            simpa [compactListedProofNodeFieldsParser,
              compactTagNumericNodeFields] using hparser)
        by_cases h1 : tag = 1
        · subst tag
          exact .tag1 body (by
            simpa [compactListedProofNodeFieldsParser, h0,
              compactTagNumericNodeFields] using hparser)
        by_cases h2 : tag = 2
        · subst tag
          exact .tag2 body (by
            simpa [compactListedProofNodeFieldsParser, h0, h1,
              compactTagNumericNodeFields] using hparser)
        by_cases h3 : tag = 3
        · subst tag
          exact .tag3 body (by
            simpa [compactListedProofNodeFieldsParser, h0, h1, h2,
              compactTagNumericNodeFields] using hparser)
        by_cases h4 : tag = 4
        · subst tag
          exact .tag4 body (by
            simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3,
              compactTagNumericNodeFields] using hparser)
        by_cases h5 : tag = 5
        · subst tag
          exact .tag5 body (by
            simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
              compactTagNumericNodeFields] using hparser)
        by_cases h6 : tag = 6
        · subst tag
          exact .tag6 body (by
            simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
              h5, compactTagNumericNodeFields] using hparser)
        by_cases h7 : tag = 7
        · subst tag
          exact .tag7 body (by
            simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
              h5, h6, compactTagNumericNodeFields] using hparser)
        by_cases h8 : tag = 8
        · subst tag
          exact .tag8 body (by
            simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
              h5, h6, h7, compactTagNumericNodeFields] using hparser)
        by_cases h9 : tag = 9
        · subst tag
          exact .tag9 body (by
            simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
              h5, h6, h7, h8, compactTagNumericNodeFields] using hparser)
        exact .invalid tag body (by omega)
  · intro hfailure
    cases hfailure with
    | empty => rfl
    | invalid tag body htag =>
        have h0 : tag ≠ 0 := by omega
        have h1 : tag ≠ 1 := by omega
        have h2 : tag ≠ 2 := by omega
        have h3 : tag ≠ 3 := by omega
        have h4 : tag ≠ 4 := by omega
        have h5 : tag ≠ 5 := by omega
        have h6 : tag ≠ 6 := by omega
        have h7 : tag ≠ 7 := by omega
        have h8 : tag ≠ 8 := by omega
        have h9 : tag ≠ 9 := by omega
        simp [compactListedProofNodeFieldsParser,
          h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
    | tag0 body hfailure =>
        simp [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields, hfailure]
    | tag1 body hfailure =>
        simp [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields, hfailure]
    | tag2 body hfailure =>
        simp [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields, hfailure]
    | tag3 body hfailure =>
        simp [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields, hfailure]
    | tag4 body hfailure =>
        simp [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields, hfailure]
    | tag5 body hfailure =>
        simp [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields, hfailure]
    | tag6 body hfailure =>
        simp [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields, hfailure]
    | tag7 body hfailure =>
        simp [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields, hfailure]
    | tag8 body hfailure =>
        simp [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields, hfailure]
    | tag9 body hfailure =>
        simp [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields, hfailure]

#print axioms compactNodeSequentFormulaFields_eq_none_iff
#print axioms compactNodeSequentClosedFormulaFields_eq_none_iff
#print axioms compactNodeSequentTwoFormulaFields_eq_none_iff
#print axioms compactNodeSequentFormulaTermFields_eq_none_iff
#print axioms compactListedProofNodeFieldsParser_eq_none_iff

end FoundationCompactNumericListedDirectProofRootFailureSemantics
