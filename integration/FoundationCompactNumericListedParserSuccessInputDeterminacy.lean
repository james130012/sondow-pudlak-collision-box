import integration.FoundationCompactNumericListedRootFieldsDecomposition
import integration.FoundationCompactCertificateTokenMachineInversion

/-!
# Exact input reconstruction for successful node parsers

Every successful listed proof-root or structural-certificate parser result
determines the complete input token stream.  These reconstruction identities
let independently canonical endpoint tables be tied to the actual verifier
state without assuming that two successful parses used the same input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedParserSuccessInputDeterminacy

open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactClosedFormulaTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactCertificateTokenMachine
open FoundationCompactCertificateTokenMachineInversion

def compactNumericNodeFieldsInput
    (fields : CompactNumericNodeFields) : List Nat :=
  fields.1.length ::
    fields.1.flatten ++ fields.2.1 ++ fields.2.2.1 ++
      fields.2.2.2.1 ++ fields.2.2.2.2

def compactNumericProofRootInput
    (root : CompactNumericProofRoot) : List Nat :=
  root.1 :: compactNumericNodeFieldsInput root.2

theorem compactSequentTokenValueParser_input_eq
    {tokens suffix : List Nat} {values : List (List Nat)}
    (hparser : compactSequentTokenValueParser tokens =
      some (values, suffix)) :
    tokens = values.length :: values.flatten ++ suffix := by
  rcases compactSequentTokenValueParser_sound hparser with
    ⟨Gamma, htokens, hvalues⟩
  have hflat :
      Gamma.flatMap compactArithmeticFormulaTokens =
        (Gamma.map compactArithmeticFormulaTokens).flatten := by
    induction Gamma with
    | nil => rfl
    | cons formula Gamma ih =>
        simp [List.flatMap]
  rw [htokens, hvalues]
  simp [compactSequentListTokens, hflat]

theorem compactFormulaTokenValueParser_input_eq
    {binderArity : Nat} {tokens value suffix : List Nat}
    (hparser : compactFormulaTokenValueParser binderArity tokens =
      some (value, suffix)) :
    tokens = value ++ suffix := by
  rcases compactFormulaTokenValueParser_sound hparser with
    ⟨formula, htokens, hvalue⟩
  simpa only [hvalue] using htokens

theorem compactTermTokenValueParser_input_eq
    {binderArity : Nat} {tokens value suffix : List Nat}
    (hparser : compactTermTokenValueParser binderArity tokens =
      some (value, suffix)) :
    tokens = value ++ suffix := by
  rcases compactTermTokenValueParser_sound hparser with
    ⟨term, htokens, hvalue⟩
  simpa only [hvalue] using htokens

theorem compactClosedFormulaTokenValueParser_input_eq
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
      rcases (compactClosedFormulaTokenParser_success_iff
          0 tokens rawSuffix).mp hraw with
        ⟨formula, _hclosed, htokens⟩
      rw [htokens]
      simp only [consumedTokenPrefix_append]

theorem compactNodeSequentOnlyFields_input_eq
    {tokens : List Nat} {fields : CompactNumericNodeFields}
    (hparser : compactNodeSequentOnlyFields tokens = some fields) :
    tokens = compactNumericNodeFieldsInput fields := by
  cases hsequent : compactSequentTokenValueParser tokens with
  | none =>
      simp [compactNodeSequentOnlyFields, hsequent] at hparser
  | some parsed =>
      rcases parsed with ⟨values, suffix⟩
      simp [compactNodeSequentOnlyFields, hsequent] at hparser
      subst fields
      simpa [compactNumericNodeFieldsInput] using
        compactSequentTokenValueParser_input_eq hsequent

theorem compactNodeSequentFormulaFields_input_eq
    (binderArity : Nat) {tokens : List Nat}
    {fields : CompactNumericNodeFields}
    (hparser : compactNodeSequentFormulaFields binderArity tokens =
      some fields) :
    tokens = compactNumericNodeFieldsInput fields := by
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
          rw [compactSequentTokenValueParser_input_eq hsequent,
            compactFormulaTokenValueParser_input_eq hformula]
          simp [compactNumericNodeFieldsInput, List.append_assoc]

theorem compactNodeSequentTwoFormulaFields_input_eq
    (binderArity : Nat) {tokens : List Nat}
    {fields : CompactNumericNodeFields}
    (hparser : compactNodeSequentTwoFormulaFields binderArity tokens =
      some fields) :
    tokens = compactNumericNodeFieldsInput fields := by
  cases hsequent : compactSequentTokenValueParser tokens with
  | none =>
      simp [compactNodeSequentTwoFormulaFields,
        compactNodeSequentFormulaFields, hsequent] at hparser
  | some parsedSequent =>
      rcases parsedSequent with ⟨values, afterSequent⟩
      cases hfirst : compactFormulaTokenValueParser binderArity
          afterSequent with
      | none =>
          simp [compactNodeSequentTwoFormulaFields,
            compactNodeSequentFormulaFields, compactNumericNodeFieldsSuffix,
            hsequent, hfirst]
            at hparser
      | some parsedFirst =>
          rcases parsedFirst with ⟨firstValue, afterFirst⟩
          cases hsecond : compactFormulaTokenValueParser binderArity
              afterFirst with
          | none =>
              simp [compactNodeSequentTwoFormulaFields,
                compactNodeSequentFormulaFields,
                compactNumericNodeFieldsSuffix,
                hsequent, hfirst, hsecond]
                at hparser
          | some parsedSecond =>
              rcases parsedSecond with ⟨secondValue, suffix⟩
              simp [compactNodeSequentTwoFormulaFields,
                compactNodeSequentFormulaFields,
                compactNumericNodeFieldsSuffix,
                hsequent, hfirst, hsecond]
                at hparser
              subst fields
              rw [compactSequentTokenValueParser_input_eq hsequent,
                compactFormulaTokenValueParser_input_eq hfirst,
                compactFormulaTokenValueParser_input_eq hsecond]
              simp [compactNumericNodeFieldsInput, List.append_assoc]

theorem compactNodeSequentFormulaTermFields_input_eq
    (formulaArity termArity : Nat) {tokens : List Nat}
    {fields : CompactNumericNodeFields}
    (hparser : compactNodeSequentFormulaTermFields
      formulaArity termArity tokens = some fields) :
    tokens = compactNumericNodeFieldsInput fields := by
  cases hsequent : compactSequentTokenValueParser tokens with
  | none =>
      simp [compactNodeSequentFormulaTermFields,
        compactNodeSequentFormulaFields, hsequent] at hparser
  | some parsedSequent =>
      rcases parsedSequent with ⟨values, afterSequent⟩
      cases hformula : compactFormulaTokenValueParser formulaArity
          afterSequent with
      | none =>
          simp [compactNodeSequentFormulaTermFields,
            compactNodeSequentFormulaFields, compactNumericNodeFieldsSuffix,
            hsequent, hformula]
            at hparser
      | some parsedFormula =>
          rcases parsedFormula with ⟨formulaValue, afterFormula⟩
          cases hterm : compactTermTokenValueParser termArity
              afterFormula with
          | none =>
              simp [compactNodeSequentFormulaTermFields,
                compactNodeSequentFormulaFields,
                compactNumericNodeFieldsSuffix,
                hsequent, hformula, hterm] at hparser
          | some parsedTerm =>
              rcases parsedTerm with ⟨termValue, suffix⟩
              simp [compactNodeSequentFormulaTermFields,
                compactNodeSequentFormulaFields,
                compactNumericNodeFieldsSuffix,
                hsequent, hformula, hterm] at hparser
              subst fields
              rw [compactSequentTokenValueParser_input_eq hsequent,
                compactFormulaTokenValueParser_input_eq hformula,
                compactTermTokenValueParser_input_eq hterm]
              simp [compactNumericNodeFieldsInput, List.append_assoc]

theorem compactNodeSequentClosedFormulaFields_input_eq
    {tokens : List Nat} {fields : CompactNumericNodeFields}
    (hparser : compactNodeSequentClosedFormulaFields tokens = some fields) :
    tokens = compactNumericNodeFieldsInput fields := by
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
          rw [compactSequentTokenValueParser_input_eq hsequent,
            compactClosedFormulaTokenValueParser_input_eq hformula]
          simp [compactNumericNodeFieldsInput, List.append_assoc]

theorem compactListedProofNodeFieldsParser_input_eq
    {tokens : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser tokens = some root) :
    tokens = compactNumericProofRootInput root := by
  rw [compactListedProofNodeFieldsParser_eq_some_iff_branchValid]
    at hparser
  cases tokens with
  | nil =>
      simp [CompactNumericProofRootBranchValid] at hparser
  | cons tag suffix =>
      by_cases h0 : tag = 0
      · simp [CompactNumericProofRootBranchValid, h0] at hparser
        rcases hparser with ⟨hrootTag, hfields⟩
        simp only [compactNumericProofRootInput, List.cons.injEq]
        exact ⟨h0.trans hrootTag.symm,
          compactNodeSequentFormulaFields_input_eq 0 hfields⟩
      by_cases h1 : tag = 1
      · simp [CompactNumericProofRootBranchValid, h0, h1] at hparser
        rcases hparser with ⟨hrootTag, hfields⟩
        simp only [compactNumericProofRootInput, List.cons.injEq]
        exact ⟨h1.trans hrootTag.symm,
          compactNodeSequentClosedFormulaFields_input_eq hfields⟩
      by_cases h2 : tag = 2
      · simp [CompactNumericProofRootBranchValid, h0, h1, h2] at hparser
        rcases hparser with ⟨hrootTag, hfields⟩
        simp only [compactNumericProofRootInput, List.cons.injEq]
        exact ⟨h2.trans hrootTag.symm,
          compactNodeSequentOnlyFields_input_eq hfields⟩
      by_cases h3 : tag = 3
      · simp [CompactNumericProofRootBranchValid, h0, h1, h2, h3]
          at hparser
        rcases hparser with ⟨hrootTag, hfields⟩
        simp only [compactNumericProofRootInput, List.cons.injEq]
        exact ⟨h3.trans hrootTag.symm,
          compactNodeSequentTwoFormulaFields_input_eq 0 hfields⟩
      by_cases h4 : tag = 4
      · simp [CompactNumericProofRootBranchValid,
          h0, h1, h2, h3, h4] at hparser
        rcases hparser with ⟨hrootTag, hfields⟩
        simp only [compactNumericProofRootInput, List.cons.injEq]
        exact ⟨h4.trans hrootTag.symm,
          compactNodeSequentTwoFormulaFields_input_eq 0 hfields⟩
      by_cases h5 : tag = 5
      · simp [CompactNumericProofRootBranchValid,
          h0, h1, h2, h3, h4, h5] at hparser
        rcases hparser with ⟨hrootTag, hfields⟩
        simp only [compactNumericProofRootInput, List.cons.injEq]
        exact ⟨h5.trans hrootTag.symm,
          compactNodeSequentFormulaFields_input_eq 1 hfields⟩
      by_cases h6 : tag = 6
      · simp [CompactNumericProofRootBranchValid,
          h0, h1, h2, h3, h4, h5, h6] at hparser
        rcases hparser with ⟨hrootTag, hfields⟩
        simp only [compactNumericProofRootInput, List.cons.injEq]
        exact ⟨h6.trans hrootTag.symm,
          compactNodeSequentFormulaTermFields_input_eq 1 0 hfields⟩
      by_cases h7 : tag = 7
      · simp [CompactNumericProofRootBranchValid,
          h0, h1, h2, h3, h4, h5, h6, h7] at hparser
        rcases hparser with ⟨hrootTag, hfields⟩
        simp only [compactNumericProofRootInput, List.cons.injEq]
        exact ⟨h7.trans hrootTag.symm,
          compactNodeSequentOnlyFields_input_eq hfields⟩
      by_cases h8 : tag = 8
      · simp [CompactNumericProofRootBranchValid,
          h0, h1, h2, h3, h4, h5, h6, h7, h8] at hparser
        rcases hparser with ⟨hrootTag, hfields⟩
        simp only [compactNumericProofRootInput, List.cons.injEq]
        exact ⟨h8.trans hrootTag.symm,
          compactNodeSequentOnlyFields_input_eq hfields⟩
      by_cases h9 : tag = 9
      · simp [CompactNumericProofRootBranchValid,
          h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] at hparser
        rcases hparser with ⟨hrootTag, hfields⟩
        simp only [compactNumericProofRootInput, List.cons.injEq]
        exact ⟨h9.trans hrootTag.symm,
          compactNodeSequentFormulaFields_input_eq 0 hfields⟩
      simp [CompactNumericProofRootBranchValid,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] at hparser

theorem compactListedProofNodeFieldsParser_input_deterministic
    {left right : List Nat} {root : CompactNumericProofRoot}
    (hleft : compactListedProofNodeFieldsParser left = some root)
    (hright : compactListedProofNodeFieldsParser right = some root) :
    left = right := by
  rw [compactListedProofNodeFieldsParser_input_eq hleft,
    compactListedProofNodeFieldsParser_input_eq hright]

theorem compactStructuralCertificateNodeParser_input_eq
    {tokens : List Nat} {node : CompactNumericCertificateNode}
    (hparser : compactStructuralCertificateNodeParser tokens = some node) :
    tokens = node.1 :: node.2.1 ++ node.2.2 := by
  cases tokens with
  | nil =>
      simp [compactStructuralCertificateNodeParser] at hparser
  | cons tag tail =>
      by_cases h0 : tag = 0
      · simp [compactStructuralCertificateNodeParser, h0] at hparser
        subst node
        subst tag
        rfl
      by_cases h1 : tag = 1
      · subst tag
        cases hpa : compactPAAxiomCertificateTokenParser tail with
        | none =>
            simp [compactStructuralCertificateNodeParser, h0, hpa] at hparser
        | some after =>
            simp [compactStructuralCertificateNodeParser, h0, hpa] at hparser
            subst node
            rcases (compactPAAxiomCertificateTokenParser_success_iff
                tail after).mp hpa with ⟨certificate, htail⟩
            rw [htail]
            simp only [consumedTokenPrefix_append]
            rfl
      by_cases h2 : tag = 2
      · simp [compactStructuralCertificateNodeParser, h0, h1, h2]
          at hparser
        subst node
        subst tag
        rfl
      by_cases h3 : tag = 3
      · simp [compactStructuralCertificateNodeParser, h0, h1, h2, h3]
          at hparser
        subst node
        subst tag
        rfl
      simp [compactStructuralCertificateNodeParser, h0, h1, h2, h3]
        at hparser

theorem compactStructuralCertificateNodeParser_input_deterministic
    {left right : List Nat} {node : CompactNumericCertificateNode}
    (hleft : compactStructuralCertificateNodeParser left = some node)
    (hright : compactStructuralCertificateNodeParser right = some node) :
    left = right := by
  rw [compactStructuralCertificateNodeParser_input_eq hleft,
    compactStructuralCertificateNodeParser_input_eq hright]

#print axioms compactSequentTokenValueParser_input_eq
#print axioms compactFormulaTokenValueParser_input_eq
#print axioms compactTermTokenValueParser_input_eq
#print axioms compactClosedFormulaTokenValueParser_input_eq
#print axioms compactNodeSequentOnlyFields_input_eq
#print axioms compactNodeSequentFormulaFields_input_eq
#print axioms compactNodeSequentTwoFormulaFields_input_eq
#print axioms compactNodeSequentFormulaTermFields_input_eq
#print axioms compactNodeSequentClosedFormulaFields_input_eq
#print axioms compactListedProofNodeFieldsParser_input_eq
#print axioms compactListedProofNodeFieldsParser_input_deterministic
#print axioms compactStructuralCertificateNodeParser_input_eq
#print axioms compactStructuralCertificateNodeParser_input_deterministic

end FoundationCompactNumericListedParserSuccessInputDeterminacy
