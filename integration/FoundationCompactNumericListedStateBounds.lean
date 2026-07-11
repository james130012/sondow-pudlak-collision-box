import integration.FoundationCompactNumericListedDirectTraceCode
import integration.FoundationCompactCertificateTokenMachineInversion

/-!
# Structural bounds for compact numeric verifier states

This module proves the source invariants needed to bound every row of the
central verifier tableau.  The first invariant is exact: every successful
node parser returns an unconsumed suffix of its input stream.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedStateBounds

open FoundationCompactSyntaxTokenMachine
open FoundationCompactClosedFormulaTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields
open FoundationCompactCertificateTokenMachine
open FoundationCompactCertificateTokenMachineInversion
open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode

theorem compactClosedFormulaTokenValueParser_suffix
    {tokens value suffix : List Nat}
    (hparser : compactClosedFormulaTokenValueParser tokens =
      some (value, suffix)) :
    suffix <:+ tokens := by
  cases hraw : compactClosedFormulaTokenParser 0 tokens with
  | none =>
      simp [compactClosedFormulaTokenValueParser, hraw] at hparser
  | some rawSuffix =>
      simp [compactClosedFormulaTokenValueParser, hraw] at hparser
      rcases hparser with ⟨rfl, rfl⟩
      obtain ⟨formula, _hclosed, htokens⟩ :=
        (compactClosedFormulaTokenParser_success_iff
          0 tokens rawSuffix).mp hraw
      exact ⟨compactArithmeticFormulaTokens formula, htokens.symm⟩

theorem compactNodeSequentOnlyFields_suffix
    {tokens : List Nat} {fields : CompactNumericNodeFields}
    (hparser : compactNodeSequentOnlyFields tokens = some fields) :
    compactNumericNodeFieldsSuffix fields <:+ tokens := by
  cases hsequent : compactSequentTokenValueParser tokens with
  | none =>
      simp [compactNodeSequentOnlyFields, hsequent] at hparser
  | some parsed =>
      rcases parsed with ⟨values, suffix⟩
      simp [compactNodeSequentOnlyFields, hsequent] at hparser
      subst fields
      obtain ⟨Gamma, htokens, _hvalues⟩ :=
        compactSequentTokenValueParser_sound hsequent
      exact ⟨compactSequentListTokens Gamma, htokens.symm⟩

theorem compactNodeSequentFormulaFields_suffix
    (binderArity : Nat) {tokens : List Nat}
    {fields : CompactNumericNodeFields}
    (hparser : compactNodeSequentFormulaFields binderArity tokens =
      some fields) :
    compactNumericNodeFieldsSuffix fields <:+ tokens := by
  cases hsequent : compactSequentTokenValueParser tokens with
  | none =>
      simp [compactNodeSequentFormulaFields, hsequent] at hparser
  | some parsedSequent =>
      rcases parsedSequent with ⟨values, afterSequent⟩
      cases hformula :
          compactFormulaTokenValueParser binderArity afterSequent with
      | none =>
          simp [compactNodeSequentFormulaFields, hsequent, hformula]
            at hparser
      | some parsedFormula =>
          rcases parsedFormula with ⟨formulaValue, suffix⟩
          simp [compactNodeSequentFormulaFields, hsequent, hformula]
            at hparser
          subst fields
          obtain ⟨Gamma, htokens, _hvalues⟩ :=
            compactSequentTokenValueParser_sound hsequent
          obtain ⟨formula, hafter, _hformulaValue⟩ :=
            compactFormulaTokenValueParser_sound hformula
          refine ⟨compactSequentListTokens Gamma ++
            compactArithmeticFormulaTokens formula, ?_⟩
          rw [htokens, hafter]
          simp [compactNumericNodeFieldsSuffix, List.append_assoc]

theorem compactNodeSequentTwoFormulaFields_suffix
    (binderArity : Nat) {tokens : List Nat}
    {fields : CompactNumericNodeFields}
    (hparser : compactNodeSequentTwoFormulaFields binderArity tokens =
      some fields) :
    compactNumericNodeFieldsSuffix fields <:+ tokens := by
  cases hfirst : compactNodeSequentFormulaFields binderArity tokens with
  | none =>
      simp [compactNodeSequentTwoFormulaFields, hfirst] at hparser
  | some first =>
      cases hsecond : compactFormulaTokenValueParser binderArity
          (compactNumericNodeFieldsSuffix first) with
      | none =>
          simp [compactNodeSequentTwoFormulaFields, hfirst, hsecond]
            at hparser
      | some second =>
          rcases second with ⟨secondValue, suffix⟩
          simp [compactNodeSequentTwoFormulaFields, hfirst, hsecond]
            at hparser
          subst fields
          have hfirstSuffix :=
            compactNodeSequentFormulaFields_suffix binderArity hfirst
          obtain ⟨formula, hafter, _hvalue⟩ :=
            compactFormulaTokenValueParser_sound hsecond
          have hsecondSuffix : suffix <:+
              compactNumericNodeFieldsSuffix first :=
            ⟨compactArithmeticFormulaTokens formula, hafter.symm⟩
          exact hsecondSuffix.trans hfirstSuffix

theorem compactNodeSequentFormulaTermFields_suffix
    (formulaArity termArity : Nat) {tokens : List Nat}
    {fields : CompactNumericNodeFields}
    (hparser : compactNodeSequentFormulaTermFields
        formulaArity termArity tokens = some fields) :
    compactNumericNodeFieldsSuffix fields <:+ tokens := by
  cases hfirst : compactNodeSequentFormulaFields formulaArity tokens with
  | none =>
      simp [compactNodeSequentFormulaTermFields, hfirst] at hparser
  | some first =>
      cases hterm : compactTermTokenValueParser termArity
          (compactNumericNodeFieldsSuffix first) with
      | none =>
          simp [compactNodeSequentFormulaTermFields, hfirst, hterm]
            at hparser
      | some term =>
          rcases term with ⟨termValue, suffix⟩
          simp [compactNodeSequentFormulaTermFields, hfirst, hterm]
            at hparser
          subst fields
          have hfirstSuffix :=
            compactNodeSequentFormulaFields_suffix formulaArity hfirst
          obtain ⟨parsedTerm, hafter, _hvalue⟩ :=
            compactTermTokenValueParser_sound hterm
          have htermSuffix : suffix <:+
              compactNumericNodeFieldsSuffix first :=
            ⟨compactArithmeticTermTokens parsedTerm, hafter.symm⟩
          exact htermSuffix.trans hfirstSuffix

theorem compactNodeSequentClosedFormulaFields_suffix
    {tokens : List Nat} {fields : CompactNumericNodeFields}
    (hparser : compactNodeSequentClosedFormulaFields tokens = some fields) :
    compactNumericNodeFieldsSuffix fields <:+ tokens := by
  cases hsequent : compactSequentTokenValueParser tokens with
  | none =>
      simp [compactNodeSequentClosedFormulaFields, hsequent] at hparser
  | some parsedSequent =>
      rcases parsedSequent with ⟨values, afterSequent⟩
      cases hformula : compactClosedFormulaTokenValueParser afterSequent with
      | none =>
          simp [compactNodeSequentClosedFormulaFields, hsequent, hformula]
            at hparser
      | some parsedFormula =>
          rcases parsedFormula with ⟨formulaValue, suffix⟩
          simp [compactNodeSequentClosedFormulaFields, hsequent, hformula]
            at hparser
          subst fields
          have hsequentSuffix : afterSequent <:+ tokens := by
            obtain ⟨Gamma, htokens, _hvalues⟩ :=
              compactSequentTokenValueParser_sound hsequent
            exact ⟨compactSequentListTokens Gamma, htokens.symm⟩
          exact (compactClosedFormulaTokenValueParser_suffix hformula).trans
            hsequentSuffix

theorem compactListedProofNodeFieldsParser_suffix
    {tokens : List Nat} {tag : Nat} {fields : CompactNumericNodeFields}
    (hparser : compactListedProofNodeFieldsParser tokens =
      some (tag, fields)) :
    compactNumericNodeFieldsSuffix fields <:+ tokens := by
  cases tokens with
  | nil =>
      simp [compactListedProofNodeFieldsParser] at hparser
  | cons head tail =>
      have htail : tail <:+ head :: tail :=
        List.suffix_append [head] tail
      by_cases h0 : head = 0
      · have hboth : compactNodeSequentFormulaFields 0 tail =
            some fields ∧ 0 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0,
            compactTagNumericNodeFields] using hparser
        have hfields := hboth.1
        exact (compactNodeSequentFormulaFields_suffix 0 hfields).trans htail
      by_cases h1 : head = 1
      · have hboth : compactNodeSequentClosedFormulaFields tail =
            some fields ∧ 1 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1,
            compactTagNumericNodeFields] using hparser
        have hfields := hboth.1
        exact compactNodeSequentClosedFormulaFields_suffix hfields |>.trans htail
      by_cases h2 : head = 2
      · have hboth : compactNodeSequentOnlyFields tail = some fields ∧
            2 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2,
            compactTagNumericNodeFields] using hparser
        have hfields := hboth.1
        exact compactNodeSequentOnlyFields_suffix hfields |>.trans htail
      by_cases h3 : head = 3
      · have hboth : compactNodeSequentTwoFormulaFields 0 tail =
            some fields ∧ 3 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3,
            compactTagNumericNodeFields] using hparser
        have hfields := hboth.1
        exact (compactNodeSequentTwoFormulaFields_suffix 0 hfields).trans htail
      by_cases h4 : head = 4
      · have hboth : compactNodeSequentTwoFormulaFields 0 tail =
            some fields ∧ 4 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            compactTagNumericNodeFields] using hparser
        have hfields := hboth.1
        exact (compactNodeSequentTwoFormulaFields_suffix 0 hfields).trans htail
      by_cases h5 : head = 5
      · have hboth : compactNodeSequentFormulaFields 1 tail =
            some fields ∧ 5 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            h5, compactTagNumericNodeFields] using hparser
        have hfields := hboth.1
        exact (compactNodeSequentFormulaFields_suffix 1 hfields).trans htail
      by_cases h6 : head = 6
      · have hboth : compactNodeSequentFormulaTermFields 1 0 tail =
            some fields ∧ 6 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            h5, h6, compactTagNumericNodeFields] using hparser
        have hfields := hboth.1
        exact (compactNodeSequentFormulaTermFields_suffix 1 0 hfields).trans
          htail
      by_cases h7 : head = 7
      · have hboth : compactNodeSequentOnlyFields tail = some fields ∧
            7 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            h5, h6, h7, compactTagNumericNodeFields] using hparser
        have hfields := hboth.1
        exact compactNodeSequentOnlyFields_suffix hfields |>.trans htail
      by_cases h8 : head = 8
      · have hboth : compactNodeSequentOnlyFields tail = some fields ∧
            8 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            h5, h6, h7, h8, compactTagNumericNodeFields] using hparser
        have hfields := hboth.1
        exact compactNodeSequentOnlyFields_suffix hfields |>.trans htail
      by_cases h9 : head = 9
      · have hboth : compactNodeSequentFormulaFields 0 tail =
            some fields ∧ 9 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            h5, h6, h7, h8, h9, compactTagNumericNodeFields] using hparser
        have hfields := hboth.1
        exact (compactNodeSequentFormulaFields_suffix 0 hfields).trans htail
      simp [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
        h5, h6, h7, h8, h9] at hparser

/-! ## Honest bounds for parsed immediate fields -/

/-- A list of formula-token lists has one outer length token and at most
`W` inner values, each of weight at most `W`. -/
def compactNumericNestedListWeightBound (W : Nat) : Nat :=
  Nat.size W + 1 + W * W

theorem compactFormulaTokenValueParser_value_weight_le
    {binderArity : Nat} {tokens value suffix : List Nat}
    (hparser : compactFormulaTokenValueParser binderArity tokens =
      some (value, suffix)) :
    compactAdditiveValueWeight value <=
      compactAdditiveValueWeight tokens := by
  obtain ⟨formula, htokens, hvalue⟩ :=
    compactFormulaTokenValueParser_sound hparser
  rw [hvalue, htokens]
  exact compactAdditiveValueWeight_infix_le
    (List.prefix_append
      (compactArithmeticFormulaTokens formula) suffix).isInfix

theorem compactTermTokenValueParser_value_weight_le
    {binderArity : Nat} {tokens value suffix : List Nat}
    (hparser : compactTermTokenValueParser binderArity tokens =
      some (value, suffix)) :
    compactAdditiveValueWeight value <=
      compactAdditiveValueWeight tokens := by
  obtain ⟨term, htokens, hvalue⟩ :=
    compactTermTokenValueParser_sound hparser
  rw [hvalue, htokens]
  exact compactAdditiveValueWeight_infix_le
    (List.prefix_append
      (compactArithmeticTermTokens term) suffix).isInfix

theorem compactClosedFormulaTokenValueParser_parts
    {tokens value suffix : List Nat}
    (hparser : compactClosedFormulaTokenValueParser tokens =
      some (value, suffix)) :
    tokens = value ++ suffix := by
  cases hraw : compactClosedFormulaTokenParser 0 tokens with
  | none =>
      simp [compactClosedFormulaTokenValueParser, hraw] at hparser
  | some rawSuffix =>
      simp [compactClosedFormulaTokenValueParser, hraw] at hparser
      rcases hparser with ⟨rfl, rfl⟩
      obtain ⟨formula, _hclosed, htokens⟩ :=
        (compactClosedFormulaTokenParser_success_iff
          0 tokens rawSuffix).mp hraw
      rw [htokens]
      simp only [consumedTokenPrefix_append]

theorem compactClosedFormulaTokenValueParser_value_weight_le
    {tokens value suffix : List Nat}
    (hparser : compactClosedFormulaTokenValueParser tokens =
      some (value, suffix)) :
    compactAdditiveValueWeight value <=
      compactAdditiveValueWeight tokens := by
  have hparts := compactClosedFormulaTokenValueParser_parts hparser
  rw [hparts]
  exact compactAdditiveValueWeight_infix_le
    (List.prefix_append value suffix).isInfix

theorem compactSequentTokenValueParser_values_weight_le
    {tokens suffix : List Nat} {values : List (List Nat)}
    (hparser : compactSequentTokenValueParser tokens =
      some (values, suffix)) :
    compactAdditiveValueWeight values <=
      compactNumericNestedListWeightBound
        (compactAdditiveValueWeight tokens) := by
  obtain ⟨Gamma, htokens, hvalues⟩ :=
    compactSequentTokenValueParser_sound hparser
  let W := compactAdditiveValueWeight tokens
  change compactAdditiveValueWeight values <=
    compactNumericNestedListWeightBound W
  have hitem : ∀ value ∈ values,
      compactAdditiveValueWeight value <= W := by
    intro value hvalue
    rw [hvalues] at hvalue
    obtain ⟨formula, hformula, rfl⟩ := List.mem_map.mp hvalue
    have hformulaInfix : compactArithmeticFormulaTokens formula <:+:
        Gamma.flatMap compactArithmeticFormulaTokens := by
      simpa [List.flatMap] using
        (List.infix_of_mem_flatten
          (List.mem_map_of_mem
            (f := compactArithmeticFormulaTokens) hformula))
    have hflatMapInfix :
        Gamma.flatMap compactArithmeticFormulaTokens <:+: tokens := by
      have hsequentSuffix : Gamma.flatMap compactArithmeticFormulaTokens <:+
          compactSequentListTokens Gamma := by
        exact List.suffix_cons Gamma.length
          (Gamma.flatMap compactArithmeticFormulaTokens)
      have hsequentPrefix : compactSequentListTokens Gamma <+: tokens := by
        rw [htokens]
        exact List.prefix_append _ _
      exact hsequentSuffix.isInfix.trans hsequentPrefix.isInfix
    simpa [W] using compactAdditiveValueWeight_infix_le
      (hformulaInfix.trans hflatMapInfix)
  have hGammaLength : Gamma.length <= tokens.length := by
    have hformulaLength := formulaList_length_le_flatMap_tokenLength Gamma
    rw [htokens]
    simp only [compactSequentListTokens, List.length_append,
      List.length_cons]
    omega
  have hvalueLength : values.length <= W := by
    have htokenLength := compactAdditiveValueWeight_natList_length_le tokens
    rw [hvalues]
    simp only [List.length_map]
    exact hGammaLength.trans htokenLength
  have hraw := compactAdditiveValueWeight_list_le values W hitem
  have hsize := Nat.size_le_size hvalueLength
  have hmul := Nat.mul_le_mul_right W hvalueLength
  unfold compactNumericNestedListWeightBound
  omega

/-- Componentwise source bound for the five immediate-field slots stored by
the verifier.  The sequent value is nested; the other four slots are flat
token slices. -/
def CompactNumericNodeFieldsComponentsWithin
    (W : Nat) (fields : CompactNumericNodeFields) : Prop :=
  compactAdditiveValueWeight fields.1 <=
      compactNumericNestedListWeightBound W ∧
    compactAdditiveValueWeight fields.2.1 <= W ∧
    compactAdditiveValueWeight fields.2.2.1 <= W ∧
    compactAdditiveValueWeight fields.2.2.2.1 <= W ∧
    compactAdditiveValueWeight fields.2.2.2.2 <= W

def compactNumericNodeFieldsWeightBound (W : Nat) : Nat :=
  compactNumericNestedListWeightBound W + 4 * W

theorem compactNumericNestedListWeightBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericNestedListWeightBound left <=
      compactNumericNestedListWeightBound right := by
  have hsize := Nat.size_le_size h
  have hsquare := Nat.mul_le_mul h h
  unfold compactNumericNestedListWeightBound
  omega

theorem CompactNumericNodeFieldsComponentsWithin.mono
    {left right : Nat} {fields : CompactNumericNodeFields}
    (hfields : CompactNumericNodeFieldsComponentsWithin left fields)
    (h : left <= right) :
    CompactNumericNodeFieldsComponentsWithin right fields := by
  rcases hfields with ⟨hGamma, hfirst, hsecond, hwitness, hsuffix⟩
  exact ⟨hGamma.trans (compactNumericNestedListWeightBound_mono h),
    hfirst.trans h, hsecond.trans h, hwitness.trans h, hsuffix.trans h⟩

theorem compactNumericNodeFields_weight_eq
    (fields : CompactNumericNodeFields) :
    compactAdditiveValueWeight fields =
      compactAdditiveValueWeight fields.1 +
        (compactAdditiveValueWeight fields.2.1 +
          (compactAdditiveValueWeight fields.2.2.1 +
            (compactAdditiveValueWeight fields.2.2.2.1 +
              compactAdditiveValueWeight fields.2.2.2.2))) := by
  simp only [compactAdditiveValueWeight_prod]

theorem CompactNumericNodeFieldsComponentsWithin.weight_le
    {W : Nat} {fields : CompactNumericNodeFields}
    (hfields : CompactNumericNodeFieldsComponentsWithin W fields) :
    compactAdditiveValueWeight fields <=
      compactNumericNodeFieldsWeightBound W := by
  rcases hfields with ⟨hGamma, hfirst, hsecond, hwitness, hsuffix⟩
  rw [compactNumericNodeFields_weight_eq]
  unfold compactNumericNodeFieldsWeightBound
  omega

theorem compactNodeSequentOnlyFields_componentsWithin
    {tokens : List Nat} {fields : CompactNumericNodeFields}
    (hparser : compactNodeSequentOnlyFields tokens = some fields) :
    CompactNumericNodeFieldsComponentsWithin
      (compactAdditiveValueWeight tokens) fields := by
  cases hsequent : compactSequentTokenValueParser tokens with
  | none =>
      simp [compactNodeSequentOnlyFields, hsequent] at hparser
  | some parsed =>
      rcases parsed with ⟨values, suffix⟩
      simp [compactNodeSequentOnlyFields, hsequent] at hparser
      subst fields
      have hGamma :=
        compactSequentTokenValueParser_values_weight_le hsequent
      obtain ⟨Gamma, htokens, _hvalues⟩ :=
        compactSequentTokenValueParser_sound hsequent
      have hsuffix : compactAdditiveValueWeight suffix <=
          compactAdditiveValueWeight tokens :=
        compactAdditiveValueWeight_suffix_le
          ⟨compactSequentListTokens Gamma, htokens.symm⟩
      have hempty : compactAdditiveValueWeight ([] : List Nat) <=
          compactAdditiveValueWeight tokens := by
        simpa using compactAdditiveValueWeight_list_pos tokens
      exact ⟨hGamma, hempty, hempty, hempty, hsuffix⟩

theorem compactNodeSequentFormulaFields_componentsWithin
    (binderArity : Nat) {tokens : List Nat}
    {fields : CompactNumericNodeFields}
    (hparser : compactNodeSequentFormulaFields binderArity tokens =
      some fields) :
    CompactNumericNodeFieldsComponentsWithin
      (compactAdditiveValueWeight tokens) fields := by
  cases hsequent : compactSequentTokenValueParser tokens with
  | none =>
      simp [compactNodeSequentFormulaFields, hsequent] at hparser
  | some parsedSequent =>
      rcases parsedSequent with ⟨values, afterSequent⟩
      cases hformula :
          compactFormulaTokenValueParser binderArity afterSequent with
      | none =>
          simp [compactNodeSequentFormulaFields, hsequent, hformula]
            at hparser
      | some parsedFormula =>
          rcases parsedFormula with ⟨formulaValue, suffix⟩
          simp [compactNodeSequentFormulaFields, hsequent, hformula]
            at hparser
          subst fields
          have hGamma :=
            compactSequentTokenValueParser_values_weight_le hsequent
          obtain ⟨Gamma, htokens, _hvalues⟩ :=
            compactSequentTokenValueParser_sound hsequent
          have hafter : compactAdditiveValueWeight afterSequent <=
              compactAdditiveValueWeight tokens :=
            compactAdditiveValueWeight_suffix_le
              ⟨compactSequentListTokens Gamma, htokens.symm⟩
          have hformulaValue :
              compactAdditiveValueWeight formulaValue <=
                compactAdditiveValueWeight tokens :=
            (compactFormulaTokenValueParser_value_weight_le hformula).trans
              hafter
          obtain ⟨formula, hformulaTokens, _hvalue⟩ :=
            compactFormulaTokenValueParser_sound hformula
          have hsuffix : compactAdditiveValueWeight suffix <=
              compactAdditiveValueWeight tokens :=
            (compactAdditiveValueWeight_suffix_le
              ⟨compactArithmeticFormulaTokens formula,
                hformulaTokens.symm⟩).trans hafter
          have hempty : compactAdditiveValueWeight ([] : List Nat) <=
              compactAdditiveValueWeight tokens := by
            simpa using compactAdditiveValueWeight_list_pos tokens
          exact ⟨hGamma, hformulaValue, hempty, hempty, hsuffix⟩

theorem compactNodeSequentTwoFormulaFields_componentsWithin
    (binderArity : Nat) {tokens : List Nat}
    {fields : CompactNumericNodeFields}
    (hparser : compactNodeSequentTwoFormulaFields binderArity tokens =
      some fields) :
    CompactNumericNodeFieldsComponentsWithin
      (compactAdditiveValueWeight tokens) fields := by
  cases hfirst : compactNodeSequentFormulaFields binderArity tokens with
  | none =>
      simp [compactNodeSequentTwoFormulaFields, hfirst] at hparser
  | some first =>
      cases hsecond : compactFormulaTokenValueParser binderArity
          (compactNumericNodeFieldsSuffix first) with
      | none =>
          simp [compactNodeSequentTwoFormulaFields, hfirst, hsecond]
            at hparser
      | some second =>
          rcases second with ⟨secondValue, suffix⟩
          simp [compactNodeSequentTwoFormulaFields, hfirst, hsecond]
            at hparser
          subst fields
          rcases compactNodeSequentFormulaFields_componentsWithin
              binderArity hfirst with
            ⟨hGamma, hfirstValue, _hemptySecond,
              _hemptyWitness, hfirstSuffix⟩
          have hsecondValue : compactAdditiveValueWeight secondValue <=
              compactAdditiveValueWeight tokens :=
            (compactFormulaTokenValueParser_value_weight_le hsecond).trans
              hfirstSuffix
          obtain ⟨formula, hformulaTokens, _hvalue⟩ :=
            compactFormulaTokenValueParser_sound hsecond
          have hsuffix : compactAdditiveValueWeight suffix <=
              compactAdditiveValueWeight tokens :=
            (compactAdditiveValueWeight_suffix_le
              ⟨compactArithmeticFormulaTokens formula,
                hformulaTokens.symm⟩).trans hfirstSuffix
          have hempty : compactAdditiveValueWeight ([] : List Nat) <=
              compactAdditiveValueWeight tokens := by
            simpa using compactAdditiveValueWeight_list_pos tokens
          exact ⟨hGamma, hfirstValue, hsecondValue,
            hempty, hsuffix⟩

theorem compactNodeSequentFormulaTermFields_componentsWithin
    (formulaArity termArity : Nat) {tokens : List Nat}
    {fields : CompactNumericNodeFields}
    (hparser : compactNodeSequentFormulaTermFields
      formulaArity termArity tokens = some fields) :
    CompactNumericNodeFieldsComponentsWithin
      (compactAdditiveValueWeight tokens) fields := by
  cases hfirst : compactNodeSequentFormulaFields formulaArity tokens with
  | none =>
      simp [compactNodeSequentFormulaTermFields, hfirst] at hparser
  | some first =>
      cases hterm : compactTermTokenValueParser termArity
          (compactNumericNodeFieldsSuffix first) with
      | none =>
          simp [compactNodeSequentFormulaTermFields, hfirst, hterm]
            at hparser
      | some term =>
          rcases term with ⟨termValue, suffix⟩
          simp [compactNodeSequentFormulaTermFields, hfirst, hterm]
            at hparser
          subst fields
          rcases compactNodeSequentFormulaFields_componentsWithin
              formulaArity hfirst with
            ⟨hGamma, hformulaValue, _hemptySecond,
              _hemptyWitness, hfirstSuffix⟩
          have htermValue : compactAdditiveValueWeight termValue <=
              compactAdditiveValueWeight tokens :=
            (compactTermTokenValueParser_value_weight_le hterm).trans
              hfirstSuffix
          obtain ⟨parsedTerm, htermTokens, _hvalue⟩ :=
            compactTermTokenValueParser_sound hterm
          have hsuffix : compactAdditiveValueWeight suffix <=
              compactAdditiveValueWeight tokens :=
            (compactAdditiveValueWeight_suffix_le
              ⟨compactArithmeticTermTokens parsedTerm,
                htermTokens.symm⟩).trans hfirstSuffix
          have hempty : compactAdditiveValueWeight ([] : List Nat) <=
              compactAdditiveValueWeight tokens := by
            simpa using compactAdditiveValueWeight_list_pos tokens
          exact ⟨hGamma, hformulaValue, hempty,
            htermValue, hsuffix⟩

theorem compactNodeSequentClosedFormulaFields_componentsWithin
    {tokens : List Nat} {fields : CompactNumericNodeFields}
    (hparser : compactNodeSequentClosedFormulaFields tokens = some fields) :
    CompactNumericNodeFieldsComponentsWithin
      (compactAdditiveValueWeight tokens) fields := by
  cases hsequent : compactSequentTokenValueParser tokens with
  | none =>
      simp [compactNodeSequentClosedFormulaFields, hsequent] at hparser
  | some parsedSequent =>
      rcases parsedSequent with ⟨values, afterSequent⟩
      cases hformula : compactClosedFormulaTokenValueParser afterSequent with
      | none =>
          simp [compactNodeSequentClosedFormulaFields, hsequent, hformula]
            at hparser
      | some parsedFormula =>
          rcases parsedFormula with ⟨formulaValue, suffix⟩
          simp [compactNodeSequentClosedFormulaFields, hsequent, hformula]
            at hparser
          subst fields
          have hGamma :=
            compactSequentTokenValueParser_values_weight_le hsequent
          obtain ⟨Gamma, htokens, _hvalues⟩ :=
            compactSequentTokenValueParser_sound hsequent
          have hafter : compactAdditiveValueWeight afterSequent <=
              compactAdditiveValueWeight tokens :=
            compactAdditiveValueWeight_suffix_le
              ⟨compactSequentListTokens Gamma, htokens.symm⟩
          have hformulaValue :
              compactAdditiveValueWeight formulaValue <=
                compactAdditiveValueWeight tokens :=
            (compactClosedFormulaTokenValueParser_value_weight_le
              hformula).trans hafter
          have hparts := compactClosedFormulaTokenValueParser_parts hformula
          have hsuffix : compactAdditiveValueWeight suffix <=
              compactAdditiveValueWeight tokens :=
            (compactAdditiveValueWeight_suffix_le
              ⟨formulaValue, hparts.symm⟩).trans hafter
          have hempty : compactAdditiveValueWeight ([] : List Nat) <=
              compactAdditiveValueWeight tokens := by
            simpa using compactAdditiveValueWeight_list_pos tokens
          exact ⟨hGamma, hformulaValue, hempty, hempty, hsuffix⟩

theorem compactListedProofNodeFieldsParser_componentsWithin
    {tokens : List Nat} {tag : Nat} {fields : CompactNumericNodeFields}
    (hparser : compactListedProofNodeFieldsParser tokens =
      some (tag, fields)) :
    CompactNumericNodeFieldsComponentsWithin
      (compactAdditiveValueWeight tokens) fields := by
  cases tokens with
  | nil =>
      simp [compactListedProofNodeFieldsParser] at hparser
  | cons head tail =>
      have htailWeight : compactAdditiveValueWeight tail <=
          compactAdditiveValueWeight (head :: tail) :=
        compactAdditiveValueWeight_suffix_le (List.suffix_cons head tail)
      by_cases h0 : head = 0
      · have hboth : compactNodeSequentFormulaFields 0 tail =
            some fields ∧ 0 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0,
            compactTagNumericNodeFields] using hparser
        exact (compactNodeSequentFormulaFields_componentsWithin
          0 hboth.1).mono htailWeight
      by_cases h1 : head = 1
      · have hboth : compactNodeSequentClosedFormulaFields tail =
            some fields ∧ 1 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1,
            compactTagNumericNodeFields] using hparser
        exact (compactNodeSequentClosedFormulaFields_componentsWithin
          hboth.1).mono htailWeight
      by_cases h2 : head = 2
      · have hboth : compactNodeSequentOnlyFields tail = some fields ∧
            2 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2,
            compactTagNumericNodeFields] using hparser
        exact (compactNodeSequentOnlyFields_componentsWithin
          hboth.1).mono htailWeight
      by_cases h3 : head = 3
      · have hboth : compactNodeSequentTwoFormulaFields 0 tail =
            some fields ∧ 3 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3,
            compactTagNumericNodeFields] using hparser
        exact (compactNodeSequentTwoFormulaFields_componentsWithin
          0 hboth.1).mono htailWeight
      by_cases h4 : head = 4
      · have hboth : compactNodeSequentTwoFormulaFields 0 tail =
            some fields ∧ 4 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            compactTagNumericNodeFields] using hparser
        exact (compactNodeSequentTwoFormulaFields_componentsWithin
          0 hboth.1).mono htailWeight
      by_cases h5 : head = 5
      · have hboth : compactNodeSequentFormulaFields 1 tail =
            some fields ∧ 5 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            h5, compactTagNumericNodeFields] using hparser
        exact (compactNodeSequentFormulaFields_componentsWithin
          1 hboth.1).mono htailWeight
      by_cases h6 : head = 6
      · have hboth : compactNodeSequentFormulaTermFields 1 0 tail =
            some fields ∧ 6 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            h5, h6, compactTagNumericNodeFields] using hparser
        exact (compactNodeSequentFormulaTermFields_componentsWithin
          1 0 hboth.1).mono htailWeight
      by_cases h7 : head = 7
      · have hboth : compactNodeSequentOnlyFields tail = some fields ∧
            7 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            h5, h6, h7, compactTagNumericNodeFields] using hparser
        exact (compactNodeSequentOnlyFields_componentsWithin
          hboth.1).mono htailWeight
      by_cases h8 : head = 8
      · have hboth : compactNodeSequentOnlyFields tail = some fields ∧
            8 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            h5, h6, h7, h8, compactTagNumericNodeFields] using hparser
        exact (compactNodeSequentOnlyFields_componentsWithin
          hboth.1).mono htailWeight
      by_cases h9 : head = 9
      · have hboth : compactNodeSequentFormulaFields 0 tail =
            some fields ∧ 9 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            h5, h6, h7, h8, h9, compactTagNumericNodeFields] using hparser
        exact (compactNodeSequentFormulaFields_componentsWithin
          0 hboth.1).mono htailWeight
      simp [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
        h5, h6, h7, h8, h9] at hparser

theorem compactListedProofNodeFieldsParser_weight_le
    {tokens : List Nat} {tag : Nat} {fields : CompactNumericNodeFields}
    (hparser : compactListedProofNodeFieldsParser tokens =
      some (tag, fields)) :
    compactAdditiveValueWeight fields <=
      compactNumericNodeFieldsWeightBound
        (compactAdditiveValueWeight tokens) :=
  (compactListedProofNodeFieldsParser_componentsWithin hparser).weight_le

/-! ## Per-item source invariant for the central verifier -/

def CompactNumericVerifierTaskWithin
    (W : Nat) (task : CompactNumericVerifierTask) : Prop :=
  task.1 <= 10 ∧
    CompactNumericNodeFieldsComponentsWithin W task.2

def CompactNumericChildResultWithin
    (W : Nat)
    (value :
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult) :
    Prop :=
  compactAdditiveValueWeight value.1 <=
    compactNumericNestedListWeightBound W

def CompactNumericRunningPayloadItemsWithin
    (W : Nat) (payload : CompactNumericRunningPayload) : Prop :=
  compactAdditiveValueWeight payload.1.1 <= W ∧
    (∀ task ∈ payload.2.1,
      CompactNumericVerifierTaskWithin W task) ∧
    ∀ value ∈ payload.2.2,
      CompactNumericChildResultWithin W value

def CompactNumericVerifierStateItemsWithin
    (W : Nat) (state : CompactNumericVerifierState) : Prop :=
  CompactNumericRunningPayloadItemsWithin W state.1

def compactNumericVerifierTaskWeightBound (W : Nat) : Nat :=
  Nat.size 10 + 1 + compactNumericNodeFieldsWeightBound W

def compactNumericChildResultWeightBound (W : Nat) : Nat :=
  compactNumericNestedListWeightBound W + 2

theorem compactNumericEmptyNodeFields_componentsWithin
    {W : Nat} (hW : 1 <= W) :
    CompactNumericNodeFieldsComponentsWithin W
      compactNumericEmptyNodeFields := by
  simp [CompactNumericNodeFieldsComponentsWithin,
    compactNumericEmptyNodeFields, compactNumericNestedListWeightBound,
    hW]
  omega

theorem compactNumericParseTask_within
    {W : Nat} (hW : 1 <= W) :
    CompactNumericVerifierTaskWithin W compactNumericParseTask := by
  exact ⟨by simp [compactNumericParseTask],
    compactNumericEmptyNodeFields_componentsWithin hW⟩

theorem CompactNumericVerifierTaskWithin.weight_le
    {W : Nat} {task : CompactNumericVerifierTask}
    (htask : CompactNumericVerifierTaskWithin W task) :
    compactAdditiveValueWeight task <=
      compactNumericVerifierTaskWeightBound W := by
  have htagSize := Nat.size_le_size htask.1
  have hfields := htask.2.weight_le
  rw [compactAdditiveValueWeight_prod,
    compactAdditiveValueWeight_nat]
  unfold compactNumericVerifierTaskWeightBound
  omega

theorem CompactNumericChildResultWithin.weight_le
    {W : Nat}
    {value :
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    (hvalue : CompactNumericChildResultWithin W value) :
    compactAdditiveValueWeight value <=
      compactNumericChildResultWeightBound W := by
  have hbool := compactAdditiveValueWeight_bool_le value.2
  rw [compactAdditiveValueWeight_prod]
  unfold compactNumericChildResultWeightBound
  exact Nat.add_le_add hvalue hbool

theorem compactNumericNodeTransition_preserves_itemsWithin
    {W : Nat} (hW : 1 <= W)
    {proofNode : Nat × CompactNumericNodeFields}
    {certificateNode : CompactNumericCertificateNode}
    {restTasks : List CompactNumericVerifierTask}
    {values : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    {next : CompactNumericRunningPayload}
    (hfields : CompactNumericNodeFieldsComponentsWithin W proofNode.2)
    (hrest : ∀ task ∈ restTasks,
      CompactNumericVerifierTaskWithin W task)
    (hvalues : ∀ value ∈ values,
      CompactNumericChildResultWithin W value)
    (htransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values = some next) :
    CompactNumericRunningPayloadItemsWithin W next := by
  have hparseTask :
      CompactNumericVerifierTaskWithin W compactNumericParseTask :=
    compactNumericParseTask_within hW
  have hcombineTask (tag : Nat) (htag : tag <= 10) :
      CompactNumericVerifierTaskWithin W
        (compactNumericCombineTask tag proofNode.2) := by
    exact ⟨by simpa [compactNumericCombineTask] using htag,
      by simpa [compactNumericCombineTask] using hfields⟩
  have hunaryTasks (tag : Nat) (htag : tag <= 10) :
      ∀ task ∈ compactNumericParseTask ::
          compactNumericCombineTask tag proofNode.2 :: restTasks,
        CompactNumericVerifierTaskWithin W task := by
    intro task htask
    simp only [List.mem_cons] at htask
    rcases htask with rfl | htask
    · exact hparseTask
    rcases htask with rfl | htask
    · exact hcombineTask tag htag
    · exact hrest task htask
  have hbinaryTasks (tag : Nat) (htag : tag <= 10) :
      ∀ task ∈ compactNumericParseTask :: compactNumericParseTask ::
          compactNumericCombineTask tag proofNode.2 :: restTasks,
        CompactNumericVerifierTaskWithin W task := by
    intro task htask
    simp only [List.mem_cons] at htask
    rcases htask with rfl | htask
    · exact hparseTask
    rcases htask with rfl | htask
    · exact hparseTask
    rcases htask with rfl | htask
    · exact hcombineTask tag htag
    · exact hrest task htask
  have hleafValues (check : Bool) :
      ∀ value ∈ (proofNode.2.1, check) :: values,
        CompactNumericChildResultWithin W value := by
    intro value hvalue
    simp only [List.mem_cons] at hvalue
    rcases hvalue with rfl | hvalue
    · exact hfields.1
    · exact hvalues value hvalue
  by_cases h0 : proofNode.1 = 0
  · by_cases hc : certificateNode.1 = 0 <;>
      simp [compactNumericNodeTransition, h0, hc] at htransition
    subst next
    exact ⟨hfields.2.2.2.2, hrest,
      hleafValues (compactClosedRuleCheck
        (proofNode.2.1, proofNode.2.2.1))⟩
  by_cases h1 : proofNode.1 = 1
  · by_cases hc : certificateNode.1 = 1 <;>
      simp [compactNumericNodeTransition, h0, h1, hc] at htransition
    subst next
    exact ⟨hfields.2.2.2.2, hrest,
      hleafValues (compactAxmRuleCheck
        (proofNode.2.1,
          (proofNode.2.2.1, certificateNode.2.1)))⟩
  by_cases h2 : proofNode.1 = 2
  · by_cases hc : certificateNode.1 = 0 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, hc] at htransition
    subst next
    exact ⟨hfields.2.2.2.2, hrest,
      hleafValues (compactVerumRuleCheck proofNode.2.1)⟩
  by_cases h3 : proofNode.1 = 3
  · by_cases hc : certificateNode.1 = 3 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, hc]
        at htransition
    subst next
    exact ⟨hfields.2.2.2.2, hbinaryTasks 3 (by omega), hvalues⟩
  by_cases h4 : proofNode.1 = 4
  · by_cases hc : certificateNode.1 = 2 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, hc]
        at htransition
    subst next
    exact ⟨hfields.2.2.2.2, hunaryTasks 4 (by omega), hvalues⟩
  by_cases h5 : proofNode.1 = 5
  · by_cases hc : certificateNode.1 = 2 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5, hc]
        at htransition
    subst next
    exact ⟨hfields.2.2.2.2, hunaryTasks 5 (by omega), hvalues⟩
  by_cases h6 : proofNode.1 = 6
  · by_cases hc : certificateNode.1 = 2 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5,
        h6, hc] at htransition
    subst next
    exact ⟨hfields.2.2.2.2, hunaryTasks 6 (by omega), hvalues⟩
  by_cases h7 : proofNode.1 = 7
  · by_cases hc : certificateNode.1 = 2 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5,
        h6, h7, hc] at htransition
    subst next
    exact ⟨hfields.2.2.2.2, hunaryTasks 7 (by omega), hvalues⟩
  by_cases h8 : proofNode.1 = 8
  · by_cases hc : certificateNode.1 = 2 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5,
        h6, h7, h8, hc] at htransition
    subst next
    exact ⟨hfields.2.2.2.2, hunaryTasks 8 (by omega), hvalues⟩
  by_cases h9 : proofNode.1 = 9
  · by_cases hc : certificateNode.1 = 3 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5,
        h6, h7, h8, h9, hc] at htransition
    subst next
    exact ⟨hfields.2.2.2.2, hbinaryTasks 9 (by omega), hvalues⟩
  simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5, h6,
    h7, h8, h9] at htransition

theorem compactNumericCombineTransition_result_source
    {task : CompactNumericVerifierTask}
    {values : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    {combined :
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult ×
        List FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    (hcombine : compactNumericCombineTransition task values = some combined) :
    combined.1.1 = task.2.1 ∧
      ∀ value ∈ combined.2, value ∈ values := by
  by_cases h3 : task.1 = 3
  · by_cases hlength : 2 <= values.length <;>
      simp [compactNumericCombineTransition, h3, hlength] at hcombine
    subst combined
    exact ⟨rfl, fun _ hvalue => List.mem_of_mem_drop hvalue⟩
  by_cases h4 : task.1 = 4
  · by_cases hlength : 1 <= values.length <;>
      simp [compactNumericCombineTransition, h3, h4, hlength] at hcombine
    subst combined
    exact ⟨rfl, fun _ hvalue => List.mem_of_mem_tail hvalue⟩
  by_cases h5 : task.1 = 5
  · by_cases hlength : 1 <= values.length <;>
      simp [compactNumericCombineTransition, h3, h4, h5, hlength] at hcombine
    subst combined
    exact ⟨rfl, fun _ hvalue => List.mem_of_mem_tail hvalue⟩
  by_cases h6 : task.1 = 6
  · by_cases hlength : 1 <= values.length <;>
      simp [compactNumericCombineTransition, h3, h4, h5, h6, hlength]
        at hcombine
    subst combined
    exact ⟨rfl, fun _ hvalue => List.mem_of_mem_tail hvalue⟩
  by_cases h7 : task.1 = 7
  · by_cases hlength : 1 <= values.length <;>
      simp [compactNumericCombineTransition, h3, h4, h5, h6, h7,
        hlength] at hcombine
    subst combined
    exact ⟨rfl, fun _ hvalue => List.mem_of_mem_tail hvalue⟩
  by_cases h8 : task.1 = 8
  · by_cases hlength : 1 <= values.length <;>
      simp [compactNumericCombineTransition, h3, h4, h5, h6, h7, h8,
        hlength] at hcombine
    subst combined
    exact ⟨rfl, fun _ hvalue => List.mem_of_mem_tail hvalue⟩
  by_cases h9 : task.1 = 9
  · by_cases hlength : 2 <= values.length <;>
      simp [compactNumericCombineTransition, h3, h4, h5, h6, h7, h8,
        h9, hlength] at hcombine
    subst combined
    exact ⟨rfl, fun _ hvalue => List.mem_of_mem_drop hvalue⟩
  simp [compactNumericCombineTransition, h3, h4, h5, h6, h7, h8, h9]
    at hcombine

theorem compactNumericCombineTransition_preserves_childrenWithin
    {W : Nat} {task : CompactNumericVerifierTask}
    {values : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    {combined :
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult ×
        List FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    (htask : CompactNumericVerifierTaskWithin W task)
    (hvalues : ∀ value ∈ values,
      CompactNumericChildResultWithin W value)
    (hcombine : compactNumericCombineTransition task values = some combined) :
    CompactNumericChildResultWithin W combined.1 ∧
      ∀ value ∈ combined.2,
        CompactNumericChildResultWithin W value := by
  have hsource := compactNumericCombineTransition_result_source hcombine
  constructor
  · unfold CompactNumericChildResultWithin
    rw [hsource.1]
    exact htask.2.1
  · intro value hvalue
    exact hvalues value (hsource.2 value hvalue)

theorem compactNumericCombineState_preserves_itemsWithin
    {W : Nat} (task : CompactNumericVerifierTask)
    (payload : CompactNumericRunningPayload)
    (htask : CompactNumericVerifierTaskWithin W task)
    (hpayload : CompactNumericRunningPayloadItemsWithin W payload) :
    CompactNumericVerifierStateItemsWithin W
      (compactNumericCombineState task payload) := by
  cases hcombine : compactNumericCombineTransition task payload.2.2 with
  | none =>
      simpa [compactNumericCombineState, hcombine,
        CompactNumericVerifierStateItemsWithin] using hpayload
  | some combined =>
      have hchildren :=
        compactNumericCombineTransition_preserves_childrenWithin
          htask hpayload.2.2 hcombine
      unfold CompactNumericVerifierStateItemsWithin
      simp only [compactNumericCombineState, hcombine]
      refine ⟨hpayload.1, hpayload.2.1, ?_⟩
      intro value hvalue
      simp only [List.mem_cons] at hvalue
      rcases hvalue with rfl | hvalue
      · exact hchildren.1
      · exact hchildren.2 value hvalue

theorem compactNumericParsePayload_preserves_itemsWithin
    {W : Nat} (hW : 1 <= W)
    {payload next : CompactNumericRunningPayload}
    (hpayload : CompactNumericRunningPayloadItemsWithin W payload)
    (hparse : compactNumericParsePayload payload = some next) :
    CompactNumericRunningPayloadItemsWithin W next := by
  cases hproof : compactListedProofNodeFieldsParser payload.1.1 with
  | none =>
      simp [compactNumericParsePayload, hproof] at hparse
  | some proofNode =>
      cases hcertificate :
          compactStructuralCertificateNodeParser payload.1.2 with
      | none =>
          simp [compactNumericParsePayload, hproof, hcertificate] at hparse
      | some certificateNode =>
          have htransition : compactNumericNodeTransition proofNode
              certificateNode payload.2.1 payload.2.2 = some next := by
            simpa [compactNumericParsePayload, hproof, hcertificate] using
              hparse
          have hfieldsCurrent :=
            compactListedProofNodeFieldsParser_componentsWithin hproof
          have hfields : CompactNumericNodeFieldsComponentsWithin W
              proofNode.2 :=
            hfieldsCurrent.mono hpayload.1
          exact compactNumericNodeTransition_preserves_itemsWithin hW
            hfields hpayload.2.1 hpayload.2.2 htransition

theorem compactNumericParseState_preserves_itemsWithin
    {W : Nat} (hW : 1 <= W)
    (payload : CompactNumericRunningPayload)
    (hpayload : CompactNumericRunningPayloadItemsWithin W payload) :
    CompactNumericVerifierStateItemsWithin W
      (compactNumericParseState payload) := by
  cases hparse : compactNumericParsePayload payload with
  | none =>
      simpa [compactNumericParseState, hparse,
        CompactNumericVerifierStateItemsWithin] using hpayload
  | some next =>
      have hnext := compactNumericParsePayload_preserves_itemsWithin
        hW hpayload hparse
      simpa [compactNumericParseState, hparse,
        CompactNumericVerifierStateItemsWithin] using hnext

theorem compactNumericFinishState_preserves_itemsWithin
    {W : Nat} (payload : CompactNumericRunningPayload)
    (hpayload : CompactNumericRunningPayloadItemsWithin W payload) :
    CompactNumericVerifierStateItemsWithin W
      (compactNumericFinishState payload) := by
  by_cases hfinish : payload.1.1 = [] ∧ payload.1.2 = [] ∧
      payload.2.1 = [] ∧ payload.2.2.length = 1 <;>
    simpa [compactNumericFinishState, hfinish,
      CompactNumericVerifierStateItemsWithin] using hpayload

theorem compactNumericRunningStep_preserves_itemsWithin
    {W : Nat} (hW : 1 <= W)
    (payload : CompactNumericRunningPayload)
    (hpayload : CompactNumericRunningPayloadItemsWithin W payload) :
    CompactNumericVerifierStateItemsWithin W
      (compactNumericRunningStep payload) := by
  cases htasks : payload.2.1 with
  | nil =>
      simpa [compactNumericRunningStep, htasks] using
        compactNumericFinishState_preserves_itemsWithin payload hpayload
  | cons task restTasks =>
      let restPayload : CompactNumericRunningPayload :=
        (payload.1, (restTasks, payload.2.2))
      have htask : CompactNumericVerifierTaskWithin W task :=
        hpayload.2.1 task (by simp [htasks])
      have hrest : CompactNumericRunningPayloadItemsWithin W restPayload := by
        refine ⟨hpayload.1, ?_, hpayload.2.2⟩
        intro nextTask hnextTask
        have hmemRest : nextTask ∈ restTasks := by
          simpa [restPayload] using hnextTask
        exact hpayload.2.1 nextTask (by
          rw [htasks]
          exact List.mem_cons_of_mem task hmemRest)
      by_cases hparseTask : task.1 = 10
      · simpa [compactNumericRunningStep, htasks, hparseTask,
          restPayload] using
          compactNumericParseState_preserves_itemsWithin hW
            restPayload hrest
      · simpa [compactNumericRunningStep, htasks, hparseTask,
          restPayload] using
          compactNumericCombineState_preserves_itemsWithin
            task restPayload htask hrest

theorem compactNumericVerifierStep_preserves_itemsWithin
    {W : Nat} (hW : 1 <= W)
    (state : CompactNumericVerifierState)
    (hstate : CompactNumericVerifierStateItemsWithin W state) :
    CompactNumericVerifierStateItemsWithin W
      (compactNumericVerifierStep state) := by
  rcases state with ⟨payload, status⟩
  cases status with
  | none =>
      simpa [compactNumericVerifierStep,
        CompactNumericVerifierStateItemsWithin] using
          compactNumericRunningStep_preserves_itemsWithin
            hW payload hstate
  | some result =>
      simpa [compactNumericVerifierStep,
        CompactNumericVerifierStateItemsWithin] using hstate

theorem compactNumericVerifierInitialState_itemsWithin
    (proofTokens certificateTokens : List Nat) :
    CompactNumericVerifierStateItemsWithin
      (compactAdditiveValueWeight proofTokens)
      (compactNumericVerifierInitialState proofTokens certificateTokens) := by
  have hW := compactAdditiveValueWeight_list_pos proofTokens
  unfold CompactNumericVerifierStateItemsWithin
  unfold CompactNumericRunningPayloadItemsWithin
  simp only [compactNumericVerifierInitialState]
  refine ⟨Nat.le_refl _, ?_, ?_⟩
  · intro task htask
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htask
    subst task
    exact compactNumericParseTask_within hW
  · intro value hvalue
    simp at hvalue

theorem compactNumericVerifier_iterate_preserves_itemsWithin
    {W : Nat} (hW : 1 <= W)
    (stepCount : Nat) (state : CompactNumericVerifierState)
    (hstate : CompactNumericVerifierStateItemsWithin W state) :
    CompactNumericVerifierStateItemsWithin W
      ((compactNumericVerifierStep^[stepCount]) state) := by
  induction stepCount generalizing state with
  | zero => simpa
  | succ stepCount ih =>
      rw [Function.iterate_succ_apply]
      exact ih _
        (compactNumericVerifierStep_preserves_itemsWithin hW state hstate)

theorem compactNumericVerifierStateAt_itemsWithin
    (proofTokens certificateTokens : List Nat) (stepIndex : Nat) :
    CompactNumericVerifierStateItemsWithin
      (compactAdditiveValueWeight proofTokens)
      (compactNumericVerifierStateAt
        (compactNumericVerifierInitialState proofTokens certificateTokens)
        stepIndex) := by
  unfold compactNumericVerifierStateAt
  exact compactNumericVerifier_iterate_preserves_itemsWithin
    (compactAdditiveValueWeight_list_pos proofTokens) stepIndex _
      (compactNumericVerifierInitialState_itemsWithin
        proofTokens certificateTokens)

theorem compactNumericVerifierLocalTrace_member_itemsWithin
    {proofTokens certificateTokens : List Nat} {fuel : Nat}
    {states : List CompactNumericVerifierState}
    (hvalid : CompactNumericVerifierLocalTraceValid fuel
      (compactNumericVerifierInitialState proofTokens certificateTokens)
      states)
    {state : CompactNumericVerifierState} (hstate : state ∈ states) :
    CompactNumericVerifierStateItemsWithin
      (compactAdditiveValueWeight proofTokens) state := by
  obtain ⟨stepIndex, hstateAt⟩ := List.mem_iff_getElem?.mp hstate
  obtain ⟨hstepIndex, _hget⟩ :=
    List.getElem?_eq_some_iff.mp hstateAt
  have hle : stepIndex <= fuel := by
    rw [hvalid.1] at hstepIndex
    omega
  have hcanonical :=
    compactNumericVerifierLocalTraceValid_stateAt hvalid hle
  unfold compactNumericTraceState? at hcanonical
  rw [hstateAt] at hcanonical
  have heq : state = compactNumericVerifierStateAt
      (compactNumericVerifierInitialState proofTokens certificateTokens)
      stepIndex := Option.some.inj hcanonical
  rw [heq]
  exact compactNumericVerifierStateAt_itemsWithin
    proofTokens certificateTokens stepIndex

theorem compactNumericVerifierLocalTrace_member_task_weight_le
    {proofTokens certificateTokens : List Nat} {fuel : Nat}
    {states : List CompactNumericVerifierState}
    (hvalid : CompactNumericVerifierLocalTraceValid fuel
      (compactNumericVerifierInitialState proofTokens certificateTokens)
      states)
    {state : CompactNumericVerifierState} (hstate : state ∈ states)
    {task : CompactNumericVerifierTask} (htask : task ∈ state.1.2.1) :
    compactAdditiveValueWeight task <=
      compactNumericVerifierTaskWeightBound
        (compactAdditiveValueWeight proofTokens) := by
  have hitems :=
    compactNumericVerifierLocalTrace_member_itemsWithin hvalid hstate
  exact (hitems.2.1 task htask).weight_le

theorem compactNumericVerifierLocalTrace_member_child_weight_le
    {proofTokens certificateTokens : List Nat} {fuel : Nat}
    {states : List CompactNumericVerifierState}
    (hvalid : CompactNumericVerifierLocalTraceValid fuel
      (compactNumericVerifierInitialState proofTokens certificateTokens)
      states)
    {state : CompactNumericVerifierState} (hstate : state ∈ states)
    {value :
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    (hvalue : value ∈ state.1.2.2) :
    compactAdditiveValueWeight value <=
      compactNumericChildResultWeightBound
        (compactAdditiveValueWeight proofTokens) := by
  have hitems :=
    compactNumericVerifierLocalTrace_member_itemsWithin hvalid hstate
  exact (hitems.2.2 value hvalue).weight_le

/-- One common bound for the two residual input streams in a state row. -/
def compactNumericVerifierUnifiedStreamBound
    (proofTokens certificateTokens : List Nat) : Nat :=
  compactAdditiveValueWeight proofTokens +
    compactAdditiveValueWeight certificateTokens

/-- Fully explicit honest weight budget for every row in the canonical local
verifier tableau. -/
def compactNumericVerifierLocalRowBound
    (proofTokens certificateTokens : List Nat) (fuel : Nat) : Nat :=
  compactNumericVerifierStateBudget
    (compactNumericVerifierUnifiedStreamBound
      proofTokens certificateTokens)
    (1 + 2 * fuel)
    (compactNumericVerifierTaskWeightBound
      (compactAdditiveValueWeight proofTokens))
    (compactNumericChildResultWeightBound
      (compactAdditiveValueWeight proofTokens))

theorem compactStructuralCertificateNodeParser_suffix
    {tokens : List Nat} {node : CompactNumericCertificateNode}
    (hparser : compactStructuralCertificateNodeParser tokens = some node) :
    node.2.2 <:+ tokens := by
  cases tokens with
  | nil =>
      simp [compactStructuralCertificateNodeParser] at hparser
  | cons tag tail =>
      have htail : tail <:+ tag :: tail :=
        List.suffix_append [tag] tail
      by_cases h0 : tag = 0
      · simp [compactStructuralCertificateNodeParser, h0] at hparser
        subst node
        exact htail
      by_cases h1 : tag = 1
      · cases hcertificate : compactPAAxiomCertificateTokenParser tail with
        | none =>
            simp [compactStructuralCertificateNodeParser, h0, h1,
              hcertificate] at hparser
        | some after =>
            simp [compactStructuralCertificateNodeParser, h0, h1,
              hcertificate] at hparser
            subst node
            obtain ⟨certificate, htokens⟩ :=
              (compactPAAxiomCertificateTokenParser_success_iff
                tail after).mp hcertificate
            have hafter : after <:+ tail :=
              ⟨compactPAAxiomCertificateTokens certificate, htokens.symm⟩
            exact hafter.trans htail
      by_cases h2 : tag = 2
      · simp [compactStructuralCertificateNodeParser, h0, h1, h2]
          at hparser
        subst node
        exact htail
      by_cases h3 : tag = 3
      · simp [compactStructuralCertificateNodeParser, h0, h1, h2, h3]
          at hparser
        subst node
        exact htail
      simp [compactStructuralCertificateNodeParser, h0, h1, h2, h3]
        at hparser

theorem compactNumericNodeTransition_streams
    {proofNode : Nat × CompactNumericNodeFields}
    {certificateNode : CompactNumericCertificateNode}
    {restTasks : List CompactNumericVerifierTask}
    {values : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    {next : CompactNumericRunningPayload}
    (htransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values = some next) :
    next.1.1 = compactNumericNodeFieldsSuffix proofNode.2 ∧
      next.1.2 = certificateNode.2.2 := by
  by_cases h0 : proofNode.1 = 0
  · by_cases hc : certificateNode.1 = 0 <;>
      simp [compactNumericNodeTransition, h0, hc] at htransition
    subst next
    constructor <;> rfl
  by_cases h1 : proofNode.1 = 1
  · by_cases hc : certificateNode.1 = 1 <;>
      simp [compactNumericNodeTransition, h0, h1, hc] at htransition
    subst next
    constructor <;> rfl
  by_cases h2 : proofNode.1 = 2
  · by_cases hc : certificateNode.1 = 0 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, hc] at htransition
    subst next
    constructor <;> rfl
  by_cases h3 : proofNode.1 = 3
  · by_cases hc : certificateNode.1 = 3 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, hc]
        at htransition
    subst next
    constructor <;> rfl
  by_cases h4 : proofNode.1 = 4
  · by_cases hc : certificateNode.1 = 2 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, hc]
        at htransition
    subst next
    constructor <;> rfl
  by_cases h5 : proofNode.1 = 5
  · by_cases hc : certificateNode.1 = 2 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5, hc]
        at htransition
    subst next
    constructor <;> rfl
  by_cases h6 : proofNode.1 = 6
  · by_cases hc : certificateNode.1 = 2 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5,
        h6, hc] at htransition
    subst next
    constructor <;> rfl
  by_cases h7 : proofNode.1 = 7
  · by_cases hc : certificateNode.1 = 2 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5,
        h6, h7, hc] at htransition
    subst next
    constructor <;> rfl
  by_cases h8 : proofNode.1 = 8
  · by_cases hc : certificateNode.1 = 2 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5,
        h6, h7, h8, hc] at htransition
    subst next
    constructor <;> rfl
  by_cases h9 : proofNode.1 = 9
  · by_cases hc : certificateNode.1 = 3 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5,
        h6, h7, h8, h9, hc] at htransition
    subst next
    constructor <;> rfl
  simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5, h6,
    h7, h8, h9] at htransition

theorem compactNumericParsePayload_streams_suffix
    {payload next : CompactNumericRunningPayload}
    (hparse : compactNumericParsePayload payload = some next) :
    next.1.1 <:+ payload.1.1 ∧ next.1.2 <:+ payload.1.2 := by
  cases hproof : compactListedProofNodeFieldsParser payload.1.1 with
  | none =>
      simp [compactNumericParsePayload, hproof] at hparse
  | some proofNode =>
      cases hcertificate :
          compactStructuralCertificateNodeParser payload.1.2 with
      | none =>
          simp [compactNumericParsePayload, hproof, hcertificate] at hparse
      | some certificateNode =>
          have htransition : compactNumericNodeTransition proofNode
              certificateNode payload.2.1 payload.2.2 = some next := by
            simpa [compactNumericParsePayload, hproof, hcertificate] using hparse
          have hstreams := compactNumericNodeTransition_streams htransition
          have hproofSuffix :=
            compactListedProofNodeFieldsParser_suffix hproof
          have hcertificateSuffix :=
            compactStructuralCertificateNodeParser_suffix hcertificate
          rw [hstreams.1, hstreams.2]
          exact ⟨hproofSuffix, hcertificateSuffix⟩

/-- Both streams in a verifier state are suffixes of fixed initial streams. -/
def CompactNumericVerifierStreamsSuffixOf
    (initialProof initialCertificate : List Nat)
    (state : CompactNumericVerifierState) : Prop :=
  state.1.1.1 <:+ initialProof ∧
    state.1.1.2 <:+ initialCertificate

theorem compactNumericVerifierStreamsSuffixOf_payload
    {initialProof initialCertificate : List Nat}
    {payload : CompactNumericRunningPayload}
    (hstreams : payload.1.1 <:+ initialProof ∧
      payload.1.2 <:+ initialCertificate)
    (status : Option Bool) :
    CompactNumericVerifierStreamsSuffixOf
      initialProof initialCertificate (payload, status) :=
  hstreams

theorem compactNumericParseState_preserves_stream_suffixes
    {initialProof initialCertificate : List Nat}
    (payload : CompactNumericRunningPayload)
    (hstreams : payload.1.1 <:+ initialProof ∧
      payload.1.2 <:+ initialCertificate) :
    CompactNumericVerifierStreamsSuffixOf initialProof initialCertificate
      (compactNumericParseState payload) := by
  cases hparse : compactNumericParsePayload payload with
  | none =>
      simpa [compactNumericParseState, hparse,
        CompactNumericVerifierStreamsSuffixOf] using hstreams
  | some next =>
      have hnext := compactNumericParsePayload_streams_suffix hparse
      have hproof := hnext.1.trans hstreams.1
      have hcertificate := hnext.2.trans hstreams.2
      simpa [compactNumericParseState, hparse,
        CompactNumericVerifierStreamsSuffixOf] using
          And.intro hproof hcertificate

theorem compactNumericCombineState_preserves_stream_suffixes
    {initialProof initialCertificate : List Nat}
    (task : CompactNumericVerifierTask)
    (payload : CompactNumericRunningPayload)
    (hstreams : payload.1.1 <:+ initialProof ∧
      payload.1.2 <:+ initialCertificate) :
    CompactNumericVerifierStreamsSuffixOf initialProof initialCertificate
      (compactNumericCombineState task payload) := by
  cases hcombine : compactNumericCombineTransition task payload.2.2 <;>
    simp [compactNumericCombineState, hcombine,
      CompactNumericVerifierStreamsSuffixOf, hstreams]

theorem compactNumericFinishState_preserves_stream_suffixes
    {initialProof initialCertificate : List Nat}
    (payload : CompactNumericRunningPayload)
    (hstreams : payload.1.1 <:+ initialProof ∧
      payload.1.2 <:+ initialCertificate) :
    CompactNumericVerifierStreamsSuffixOf initialProof initialCertificate
      (compactNumericFinishState payload) := by
  by_cases hfinish : payload.1.1 = [] ∧ payload.1.2 = [] ∧
      payload.2.1 = [] ∧ payload.2.2.length = 1 <;>
    simp [compactNumericFinishState, hfinish,
      CompactNumericVerifierStreamsSuffixOf, hstreams]

theorem compactNumericRunningStep_preserves_stream_suffixes
    {initialProof initialCertificate : List Nat}
    (payload : CompactNumericRunningPayload)
    (hstreams : payload.1.1 <:+ initialProof ∧
      payload.1.2 <:+ initialCertificate) :
    CompactNumericVerifierStreamsSuffixOf initialProof initialCertificate
      (compactNumericRunningStep payload) := by
  cases htasks : payload.2.1 with
  | nil =>
      simpa [compactNumericRunningStep, htasks] using
        compactNumericFinishState_preserves_stream_suffixes payload hstreams
  | cons task restTasks =>
      let restPayload : CompactNumericRunningPayload :=
        (payload.1, (restTasks, payload.2.2))
      have hrest : restPayload.1.1 <:+ initialProof ∧
          restPayload.1.2 <:+ initialCertificate := hstreams
      by_cases hparseTask : task.1 = 10
      · simpa [compactNumericRunningStep, htasks, hparseTask, restPayload] using
          compactNumericParseState_preserves_stream_suffixes
            restPayload hrest
      · simpa [compactNumericRunningStep, htasks, hparseTask, restPayload] using
          compactNumericCombineState_preserves_stream_suffixes
            task restPayload hrest

theorem compactNumericVerifierStep_preserves_stream_suffixes
    {initialProof initialCertificate : List Nat}
    (state : CompactNumericVerifierState)
    (hstreams : CompactNumericVerifierStreamsSuffixOf
      initialProof initialCertificate state) :
    CompactNumericVerifierStreamsSuffixOf initialProof initialCertificate
      (compactNumericVerifierStep state) := by
  rcases state with ⟨payload, status⟩
  cases status with
  | none =>
      simpa [compactNumericVerifierStep,
        CompactNumericVerifierStreamsSuffixOf] using
          compactNumericRunningStep_preserves_stream_suffixes payload hstreams
  | some result =>
      simpa [compactNumericVerifierStep,
        CompactNumericVerifierStreamsSuffixOf] using hstreams

theorem compactNumericVerifier_iterate_preserves_stream_suffixes
    {initialProof initialCertificate : List Nat}
    (fuel : Nat) (state : CompactNumericVerifierState)
    (hstreams : CompactNumericVerifierStreamsSuffixOf
      initialProof initialCertificate state) :
    CompactNumericVerifierStreamsSuffixOf initialProof initialCertificate
      ((compactNumericVerifierStep^[fuel]) state) := by
  induction fuel generalizing state with
  | zero => simpa
  | succ fuel ih =>
      rw [Function.iterate_succ_apply]
      exact ih _
        (compactNumericVerifierStep_preserves_stream_suffixes state hstreams)

theorem compactNumericVerifierInitialState_stream_suffixes
    (proofTokens certificateTokens : List Nat) :
    CompactNumericVerifierStreamsSuffixOf proofTokens certificateTokens
      (compactNumericVerifierInitialState proofTokens certificateTokens) := by
  constructor <;> exact ⟨[], by simp [compactNumericVerifierInitialState]⟩

theorem compactNumericVerifierStateAt_stream_suffixes
    (proofTokens certificateTokens : List Nat) (stepIndex : Nat) :
    CompactNumericVerifierStreamsSuffixOf proofTokens certificateTokens
      (compactNumericVerifierStateAt
        (compactNumericVerifierInitialState proofTokens certificateTokens)
        stepIndex) := by
  exact compactNumericVerifier_iterate_preserves_stream_suffixes
    stepIndex _
      (compactNumericVerifierInitialState_stream_suffixes
        proofTokens certificateTokens)

theorem compactNumericVerifierLocalTrace_member_stream_suffixes
    {proofTokens certificateTokens : List Nat} {fuel : Nat}
    {states : List CompactNumericVerifierState}
    (hvalid : CompactNumericVerifierLocalTraceValid fuel
      (compactNumericVerifierInitialState proofTokens certificateTokens)
      states)
    {state : CompactNumericVerifierState} (hstate : state ∈ states) :
    CompactNumericVerifierStreamsSuffixOf proofTokens certificateTokens
      state := by
  obtain ⟨stepIndex, hstateAt⟩ := List.mem_iff_getElem?.mp hstate
  obtain ⟨hstepIndex, _hget⟩ :=
    List.getElem?_eq_some_iff.mp hstateAt
  have hle : stepIndex <= fuel := by
    rw [hvalid.1] at hstepIndex
    omega
  have hcanonical :=
    compactNumericVerifierLocalTraceValid_stateAt hvalid hle
  unfold compactNumericTraceState? at hcanonical
  rw [hstateAt] at hcanonical
  have heq : state = compactNumericVerifierStateAt
      (compactNumericVerifierInitialState proofTokens certificateTokens)
      stepIndex := Option.some.inj hcanonical
  rw [heq]
  exact compactNumericVerifierStateAt_stream_suffixes
    proofTokens certificateTokens stepIndex

theorem compactNumericVerifierLocalTrace_member_stream_weight_le
    {proofTokens certificateTokens : List Nat} {fuel : Nat}
    {states : List CompactNumericVerifierState}
    (hvalid : CompactNumericVerifierLocalTraceValid fuel
      (compactNumericVerifierInitialState proofTokens certificateTokens)
      states)
    {state : CompactNumericVerifierState} (hstate : state ∈ states) :
    compactAdditiveValueWeight state.1.1.1 <=
        compactAdditiveValueWeight proofTokens ∧
      compactAdditiveValueWeight state.1.1.2 <=
        compactAdditiveValueWeight certificateTokens := by
  have hsuffix :=
    compactNumericVerifierLocalTrace_member_stream_suffixes hvalid hstate
  exact ⟨compactAdditiveValueWeight_suffix_le hsuffix.1,
    compactAdditiveValueWeight_suffix_le hsuffix.2⟩

/-- Number of pending tasks plus completed child results in a running payload. -/
def compactNumericRunningPayloadStackCount
    (payload : CompactNumericRunningPayload) : Nat :=
  payload.2.1.length + payload.2.2.length

def compactNumericVerifierStackCount
    (state : CompactNumericVerifierState) : Nat :=
  compactNumericRunningPayloadStackCount state.1

theorem compactNumericNodeTransition_stackCount_le
    {proofNode : Nat × CompactNumericNodeFields}
    {certificateNode : CompactNumericCertificateNode}
    {restTasks : List CompactNumericVerifierTask}
    {values : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    {next : CompactNumericRunningPayload}
    (htransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values = some next) :
    compactNumericRunningPayloadStackCount next <=
      restTasks.length + values.length + 3 := by
  by_cases h0 : proofNode.1 = 0
  · by_cases hc : certificateNode.1 = 0 <;>
      simp [compactNumericNodeTransition, h0, hc] at htransition
    subst next
    simp [compactNumericRunningPayloadStackCount]
    omega
  by_cases h1 : proofNode.1 = 1
  · by_cases hc : certificateNode.1 = 1 <;>
      simp [compactNumericNodeTransition, h0, h1, hc] at htransition
    subst next
    simp [compactNumericRunningPayloadStackCount]
    omega
  by_cases h2 : proofNode.1 = 2
  · by_cases hc : certificateNode.1 = 0 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, hc] at htransition
    subst next
    simp [compactNumericRunningPayloadStackCount]
    omega
  by_cases h3 : proofNode.1 = 3
  · by_cases hc : certificateNode.1 = 3 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, hc]
        at htransition
    subst next
    simp [compactNumericRunningPayloadStackCount]
    omega
  by_cases h4 : proofNode.1 = 4
  · by_cases hc : certificateNode.1 = 2 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, hc]
        at htransition
    subst next
    simp [compactNumericRunningPayloadStackCount]
    omega
  by_cases h5 : proofNode.1 = 5
  · by_cases hc : certificateNode.1 = 2 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5, hc]
        at htransition
    subst next
    simp [compactNumericRunningPayloadStackCount]
    omega
  by_cases h6 : proofNode.1 = 6
  · by_cases hc : certificateNode.1 = 2 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5,
        h6, hc] at htransition
    subst next
    simp [compactNumericRunningPayloadStackCount]
    omega
  by_cases h7 : proofNode.1 = 7
  · by_cases hc : certificateNode.1 = 2 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5,
        h6, h7, hc] at htransition
    subst next
    simp [compactNumericRunningPayloadStackCount]
    omega
  by_cases h8 : proofNode.1 = 8
  · by_cases hc : certificateNode.1 = 2 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5,
        h6, h7, h8, hc] at htransition
    subst next
    simp [compactNumericRunningPayloadStackCount]
    omega
  by_cases h9 : proofNode.1 = 9
  · by_cases hc : certificateNode.1 = 3 <;>
      simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5,
        h6, h7, h8, h9, hc] at htransition
    subst next
    simp [compactNumericRunningPayloadStackCount]
    omega
  simp [compactNumericNodeTransition, h0, h1, h2, h3, h4, h5, h6,
    h7, h8, h9] at htransition

theorem compactNumericParsePayload_stackCount_le
    {payload next : CompactNumericRunningPayload}
    (hparse : compactNumericParsePayload payload = some next) :
    compactNumericRunningPayloadStackCount next <=
      compactNumericRunningPayloadStackCount payload + 3 := by
  cases hproof : compactListedProofNodeFieldsParser payload.1.1 with
  | none =>
      simp [compactNumericParsePayload, hproof] at hparse
  | some proofNode =>
      cases hcertificate :
          compactStructuralCertificateNodeParser payload.1.2 with
      | none =>
          simp [compactNumericParsePayload, hproof, hcertificate] at hparse
      | some certificateNode =>
          have htransition : compactNumericNodeTransition proofNode
              certificateNode payload.2.1 payload.2.2 = some next := by
            simpa [compactNumericParsePayload, hproof, hcertificate] using hparse
          have hbound := compactNumericNodeTransition_stackCount_le htransition
          simpa [compactNumericRunningPayloadStackCount,
            Nat.add_assoc] using hbound

theorem compactNumericParseState_stackCount_le
    (payload : CompactNumericRunningPayload) :
    compactNumericVerifierStackCount (compactNumericParseState payload) <=
      compactNumericRunningPayloadStackCount payload + 3 := by
  cases hparse : compactNumericParsePayload payload with
  | none =>
      simp [compactNumericParseState, hparse,
        compactNumericVerifierStackCount]
  | some next =>
      simpa [compactNumericParseState, hparse,
        compactNumericVerifierStackCount] using
          compactNumericParsePayload_stackCount_le hparse

theorem compactNumericCombineTransition_tail_length_le
    {task : CompactNumericVerifierTask}
    {values : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    {combined :
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult ×
        List FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    (hcombine : compactNumericCombineTransition task values = some combined) :
    combined.2.length <= values.length := by
  by_cases h3 : task.1 = 3
  · by_cases hlength : 2 <= values.length <;>
      simp [compactNumericCombineTransition, h3, hlength] at hcombine
    subst combined
    simp
  by_cases h4 : task.1 = 4
  · by_cases hlength : 1 <= values.length <;>
      simp [compactNumericCombineTransition, h3, h4, hlength] at hcombine
    subst combined
    simp
  by_cases h5 : task.1 = 5
  · by_cases hlength : 1 <= values.length <;>
      simp [compactNumericCombineTransition, h3, h4, h5, hlength] at hcombine
    subst combined
    simp
  by_cases h6 : task.1 = 6
  · by_cases hlength : 1 <= values.length <;>
      simp [compactNumericCombineTransition, h3, h4, h5, h6, hlength]
        at hcombine
    subst combined
    simp
  by_cases h7 : task.1 = 7
  · by_cases hlength : 1 <= values.length <;>
      simp [compactNumericCombineTransition, h3, h4, h5, h6, h7,
        hlength] at hcombine
    subst combined
    simp
  by_cases h8 : task.1 = 8
  · by_cases hlength : 1 <= values.length <;>
      simp [compactNumericCombineTransition, h3, h4, h5, h6, h7, h8,
        hlength] at hcombine
    subst combined
    simp
  by_cases h9 : task.1 = 9
  · by_cases hlength : 2 <= values.length <;>
      simp [compactNumericCombineTransition, h3, h4, h5, h6, h7, h8,
        h9, hlength] at hcombine
    subst combined
    simp
  simp [compactNumericCombineTransition, h3, h4, h5, h6, h7, h8, h9]
    at hcombine

theorem compactNumericCombineState_stackCount_le
    (task : CompactNumericVerifierTask)
    (payload : CompactNumericRunningPayload) :
    compactNumericVerifierStackCount
        (compactNumericCombineState task payload) <=
      compactNumericRunningPayloadStackCount payload + 1 := by
  cases hcombine : compactNumericCombineTransition task payload.2.2 with
  | none =>
      simp [compactNumericCombineState, hcombine,
        compactNumericVerifierStackCount]
  | some combined =>
      have htail := compactNumericCombineTransition_tail_length_le hcombine
      simp only [compactNumericCombineState, hcombine,
        compactNumericVerifierStackCount,
        compactNumericRunningPayloadStackCount, List.length_cons]
      omega

theorem compactNumericFinishState_stackCount_le
    (payload : CompactNumericRunningPayload) :
    compactNumericVerifierStackCount (compactNumericFinishState payload) <=
      compactNumericRunningPayloadStackCount payload := by
  by_cases hfinish : payload.1.1 = [] ∧ payload.1.2 = [] ∧
      payload.2.1 = [] ∧ payload.2.2.length = 1 <;>
    simp [compactNumericFinishState, hfinish,
      compactNumericVerifierStackCount]

theorem compactNumericRunningStep_stackCount_le
    (payload : CompactNumericRunningPayload) :
    compactNumericVerifierStackCount (compactNumericRunningStep payload) <=
      compactNumericRunningPayloadStackCount payload + 2 := by
  cases htasks : payload.2.1 with
  | nil =>
      have hfinish := compactNumericFinishState_stackCount_le payload
      simpa [compactNumericRunningStep, htasks] using hfinish.trans
        (Nat.le_add_right _ _)
  | cons task restTasks =>
      let restPayload : CompactNumericRunningPayload :=
        (payload.1, (restTasks, payload.2.2))
      by_cases hparseTask : task.1 = 10
      · have hparse := compactNumericParseState_stackCount_le restPayload
        have hlift : compactNumericRunningPayloadStackCount restPayload + 3 <=
            compactNumericRunningPayloadStackCount payload + 2 := by
          simp [restPayload, compactNumericRunningPayloadStackCount, htasks]
        simpa [compactNumericRunningStep, htasks, hparseTask, restPayload] using
          hparse.trans hlift
      · have hcombine := compactNumericCombineState_stackCount_le
          task restPayload
        have hlift : compactNumericRunningPayloadStackCount restPayload + 1 <=
            compactNumericRunningPayloadStackCount payload + 2 := by
          simp [restPayload, compactNumericRunningPayloadStackCount, htasks]
          omega
        simpa [compactNumericRunningStep, htasks, hparseTask, restPayload] using
          hcombine.trans hlift

theorem compactNumericVerifierStep_stackCount_le
    (state : CompactNumericVerifierState) :
    compactNumericVerifierStackCount (compactNumericVerifierStep state) <=
      compactNumericVerifierStackCount state + 2 := by
  rcases state with ⟨payload, status⟩
  cases status with
  | none =>
      simpa [compactNumericVerifierStep,
        compactNumericVerifierStackCount] using
          compactNumericRunningStep_stackCount_le payload
  | some result =>
      simp [compactNumericVerifierStep, compactNumericVerifierStackCount]

theorem compactNumericVerifier_iterate_stackCount_le
    (fuel : Nat) (state : CompactNumericVerifierState) :
    compactNumericVerifierStackCount
        ((compactNumericVerifierStep^[fuel]) state) <=
      compactNumericVerifierStackCount state + 2 * fuel := by
  induction fuel generalizing state with
  | zero => simp
  | succ fuel ih =>
      rw [Function.iterate_succ_apply]
      have hstep := compactNumericVerifierStep_stackCount_le state
      have hrest := ih (compactNumericVerifierStep state)
      omega

theorem compactNumericVerifierStateAt_stackCount_le
    (proofTokens certificateTokens : List Nat) (stepIndex : Nat) :
    compactNumericVerifierStackCount
        (compactNumericVerifierStateAt
          (compactNumericVerifierInitialState proofTokens certificateTokens)
          stepIndex) <=
      1 + 2 * stepIndex := by
  simpa [compactNumericVerifierStateAt,
    compactNumericVerifierInitialState,
    compactNumericVerifierStackCount,
    compactNumericRunningPayloadStackCount] using
      compactNumericVerifier_iterate_stackCount_le stepIndex
        (compactNumericVerifierInitialState proofTokens certificateTokens)

theorem compactNumericVerifierLocalTrace_member_stackCount_le
    {proofTokens certificateTokens : List Nat} {fuel : Nat}
    {states : List CompactNumericVerifierState}
    (hvalid : CompactNumericVerifierLocalTraceValid fuel
      (compactNumericVerifierInitialState proofTokens certificateTokens)
      states)
    {state : CompactNumericVerifierState} (hstate : state ∈ states) :
    compactNumericVerifierStackCount state <= 1 + 2 * fuel := by
  obtain ⟨stepIndex, hstateAt⟩ := List.mem_iff_getElem?.mp hstate
  obtain ⟨hstepIndex, _hget⟩ :=
    List.getElem?_eq_some_iff.mp hstateAt
  have hle : stepIndex <= fuel := by
    rw [hvalid.1] at hstepIndex
    omega
  have hcanonical :=
    compactNumericVerifierLocalTraceValid_stateAt hvalid hle
  unfold compactNumericTraceState? at hcanonical
  rw [hstateAt] at hcanonical
  have heq : state = compactNumericVerifierStateAt
      (compactNumericVerifierInitialState proofTokens certificateTokens)
      stepIndex := Option.some.inj hcanonical
  rw [heq]
  have hraw := compactNumericVerifierStateAt_stackCount_le
    proofTokens certificateTokens stepIndex
  omega

theorem compactNumericVerifierLocalTrace_member_task_length_le
    {proofTokens certificateTokens : List Nat} {fuel : Nat}
    {states : List CompactNumericVerifierState}
    (hvalid : CompactNumericVerifierLocalTraceValid fuel
      (compactNumericVerifierInitialState proofTokens certificateTokens)
      states)
    {state : CompactNumericVerifierState} (hstate : state ∈ states) :
    state.1.2.1.length <= 1 + 2 * fuel := by
  have hcount :=
    compactNumericVerifierLocalTrace_member_stackCount_le hvalid hstate
  unfold compactNumericVerifierStackCount at hcount
  unfold compactNumericRunningPayloadStackCount at hcount
  omega

theorem compactNumericVerifierLocalTrace_member_value_length_le
    {proofTokens certificateTokens : List Nat} {fuel : Nat}
    {states : List CompactNumericVerifierState}
    (hvalid : CompactNumericVerifierLocalTraceValid fuel
      (compactNumericVerifierInitialState proofTokens certificateTokens)
      states)
    {state : CompactNumericVerifierState} (hstate : state ∈ states) :
    state.1.2.2.length <= 1 + 2 * fuel := by
  have hcount :=
    compactNumericVerifierLocalTrace_member_stackCount_le hvalid hstate
  unfold compactNumericVerifierStackCount at hcount
  unfold compactNumericRunningPayloadStackCount at hcount
  omega

theorem compactNumericVerifierLocalTrace_member_stateWeight_le
    {proofTokens certificateTokens : List Nat} {fuel : Nat}
    {states : List CompactNumericVerifierState}
    (hvalid : CompactNumericVerifierLocalTraceValid fuel
      (compactNumericVerifierInitialState proofTokens certificateTokens)
      states)
    {state : CompactNumericVerifierState} (hstate : state ∈ states) :
    compactNumericVerifierStateWeight state <=
      compactNumericVerifierLocalRowBound
        proofTokens certificateTokens fuel := by
  have hstreams :=
    compactNumericVerifierLocalTrace_member_stream_weight_le hvalid hstate
  have hproof : compactAdditiveValueWeight state.1.1.1 <=
      compactNumericVerifierUnifiedStreamBound
        proofTokens certificateTokens := by
    unfold compactNumericVerifierUnifiedStreamBound
    omega
  have hcertificate : compactAdditiveValueWeight state.1.1.2 <=
      compactNumericVerifierUnifiedStreamBound
        proofTokens certificateTokens := by
    unfold compactNumericVerifierUnifiedStreamBound
    omega
  have htaskLength :=
    compactNumericVerifierLocalTrace_member_task_length_le hvalid hstate
  have hvalueLength :=
    compactNumericVerifierLocalTrace_member_value_length_le hvalid hstate
  unfold compactNumericVerifierLocalRowBound
  apply compactNumericVerifierStateWeight_le_budget
    state
    (compactNumericVerifierUnifiedStreamBound
      proofTokens certificateTokens)
    (1 + 2 * fuel)
    (compactNumericVerifierTaskWeightBound
      (compactAdditiveValueWeight proofTokens))
    (compactNumericChildResultWeightBound
      (compactAdditiveValueWeight proofTokens))
    hproof hcertificate htaskLength hvalueLength
  · intro task htask
    exact compactNumericVerifierLocalTrace_member_task_weight_le
      hvalid hstate htask
  · intro value hvalue
    exact compactNumericVerifierLocalTrace_member_child_weight_le
      hvalid hstate hvalue

theorem compactNumericVerifierLocalTrace_tableWeight_explicit_le
    {proofTokens certificateTokens : List Nat} {fuel : Nat}
    {states : List CompactNumericVerifierState}
    (hvalid : CompactNumericVerifierLocalTraceValid fuel
      (compactNumericVerifierInitialState proofTokens certificateTokens)
      states) :
    compactNumericVerifierStateTableWeight states <=
      Nat.size (fuel + 1) + 1 +
        (fuel + 1) * compactNumericVerifierLocalRowBound
          proofTokens certificateTokens fuel := by
  apply compactNumericVerifierLocalTrace_tableWeight_le
    fuel
    (compactNumericVerifierInitialState proofTokens certificateTokens)
    states
    (compactNumericVerifierLocalRowBound
      proofTokens certificateTokens fuel)
    hvalid
  intro state hstate
  exact compactNumericVerifierLocalTrace_member_stateWeight_le
    hvalid hstate

#print axioms compactClosedFormulaTokenValueParser_suffix
#print axioms compactNodeSequentOnlyFields_suffix
#print axioms compactNodeSequentFormulaFields_suffix
#print axioms compactNodeSequentTwoFormulaFields_suffix
#print axioms compactNodeSequentFormulaTermFields_suffix
#print axioms compactNodeSequentClosedFormulaFields_suffix
#print axioms compactListedProofNodeFieldsParser_suffix
#print axioms compactSequentTokenValueParser_values_weight_le
#print axioms CompactNumericNodeFieldsComponentsWithin.weight_le
#print axioms compactNodeSequentOnlyFields_componentsWithin
#print axioms compactNodeSequentFormulaFields_componentsWithin
#print axioms compactNodeSequentTwoFormulaFields_componentsWithin
#print axioms compactNodeSequentFormulaTermFields_componentsWithin
#print axioms compactNodeSequentClosedFormulaFields_componentsWithin
#print axioms compactListedProofNodeFieldsParser_componentsWithin
#print axioms compactListedProofNodeFieldsParser_weight_le
#print axioms compactNumericNodeTransition_preserves_itemsWithin
#print axioms compactNumericCombineTransition_result_source
#print axioms compactNumericCombineState_preserves_itemsWithin
#print axioms compactNumericVerifierStep_preserves_itemsWithin
#print axioms compactNumericVerifier_iterate_preserves_itemsWithin
#print axioms compactNumericVerifierLocalTrace_member_itemsWithin
#print axioms compactNumericVerifierLocalTrace_member_task_weight_le
#print axioms compactNumericVerifierLocalTrace_member_child_weight_le
#print axioms compactStructuralCertificateNodeParser_suffix
#print axioms compactNumericNodeTransition_streams
#print axioms compactNumericParsePayload_streams_suffix
#print axioms compactNumericVerifierStep_preserves_stream_suffixes
#print axioms compactNumericVerifier_iterate_preserves_stream_suffixes
#print axioms compactNumericVerifierLocalTrace_member_stream_suffixes
#print axioms compactNumericVerifierLocalTrace_member_stream_weight_le
#print axioms compactNumericNodeTransition_stackCount_le
#print axioms compactNumericCombineTransition_tail_length_le
#print axioms compactNumericVerifierStep_stackCount_le
#print axioms compactNumericVerifier_iterate_stackCount_le
#print axioms compactNumericVerifierLocalTrace_member_stackCount_le
#print axioms compactNumericVerifierLocalTrace_member_task_length_le
#print axioms compactNumericVerifierLocalTrace_member_value_length_le
#print axioms compactNumericVerifierLocalTrace_member_stateWeight_le
#print axioms compactNumericVerifierLocalTrace_tableWeight_explicit_le

end FoundationCompactNumericListedStateBounds
