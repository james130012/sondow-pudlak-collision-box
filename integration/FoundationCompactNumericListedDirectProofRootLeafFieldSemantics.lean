import integration.FoundationCompactNumericListedRootFieldsDecomposition
import integration.FoundationCompactNumericSyntaxValueParser
import integration.FoundationCompactNumericFixedPAAxiomSentence

/-!
# Semantic fields of successfully parsed leaf proof roots

The public proof-root parser itself certifies that a tag-zero leaf carries a
genuine arity-zero arithmetic formula.  This removes a separate parseability
premise from the closed-leaf verifier branch.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootLeafFieldSemantics

open FoundationCompactSyntaxTokenMachine
open FoundationCompactClosedFormulaTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericFixedPAAxiomSentence

theorem compactListedProofNodeFieldsParser_tag_zero_firstFormula
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root)
    (htag : root.1 = 0) :
    exists parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0,
      root.2.2.1 = compactArithmeticFormulaTokens parsed := by
  have hvalid :=
    (compactListedProofNodeFieldsParser_eq_some_iff_branchValid
      input root).mp hparser
  cases input with
  | nil =>
      simp [CompactNumericProofRootBranchValid] at hvalid
  | cons inputTag body =>
      have hinputTag : inputTag = 0 := by
        by_contra hne
        simp [CompactNumericProofRootBranchValid, hne, htag] at hvalid
      subst inputTag
      have hfields : compactNodeSequentFormulaFields 0 body = some root.2 := by
        simpa [CompactNumericProofRootBranchValid, htag] using hvalid
      cases hsequent : compactSequentTokenValueParser body with
      | none =>
          simp [compactNodeSequentFormulaFields, hsequent] at hfields
      | some parsedSequent =>
          rcases parsedSequent with ⟨Gamma, afterSequent⟩
          cases hformula :
              compactFormulaTokenValueParser 0 afterSequent with
          | none =>
              simp [compactNodeSequentFormulaFields,
                hsequent, hformula] at hfields
          | some parsedFormula =>
              rcases parsedFormula with ⟨formula, suffix⟩
              have hrootFields :
                  (Gamma, (formula,
                    (([] : List Nat), (([] : List Nat), suffix)))) =
                    root.2 := by
                simpa [compactNodeSequentFormulaFields,
                  hsequent, hformula] using hfields
              rcases compactFormulaTokenValueParser_sound hformula with
                ⟨parsed, _hafterSequent, hformulaCanonical⟩
              refine ⟨parsed, ?_⟩
              rw [← hrootFields]
              exact hformulaCanonical

theorem compactListedProofNodeFieldsParser_tag_one_firstFormula
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root)
    (htag : root.1 = 1) :
    exists sentence : LO.FirstOrder.ArithmeticSentence,
      root.2.2.1 = compactSentenceTokens sentence := by
  have hvalid :=
    (compactListedProofNodeFieldsParser_eq_some_iff_branchValid
      input root).mp hparser
  cases input with
  | nil =>
      simp [CompactNumericProofRootBranchValid] at hvalid
  | cons inputTag body =>
      have hinputTag : inputTag = 1 := by
        by_contra hne
        simp [CompactNumericProofRootBranchValid, hne, htag] at hvalid
      subst inputTag
      have hfields : compactNodeSequentClosedFormulaFields body =
          some root.2 := by
        simpa [CompactNumericProofRootBranchValid, htag] using hvalid
      cases hsequent : compactSequentTokenValueParser body with
      | none =>
          simp [compactNodeSequentClosedFormulaFields, hsequent] at hfields
      | some parsedSequent =>
          rcases parsedSequent with ⟨Gamma, afterSequent⟩
          cases hclosedValue :
              compactClosedFormulaTokenValueParser afterSequent with
          | none =>
              simp [compactNodeSequentClosedFormulaFields,
                hsequent, hclosedValue] at hfields
          | some parsedFormula =>
              rcases parsedFormula with ⟨formulaTokens, suffix⟩
              have hrootFields :
                  (Gamma, (formulaTokens,
                    (([] : List Nat), (([] : List Nat), suffix)))) =
                    root.2 := by
                simpa [compactNodeSequentClosedFormulaFields,
                  hsequent, hclosedValue] using hfields
              have hclosedData :
                  compactClosedFormulaTokenParser 0 afterSequent =
                      some suffix ∧
                    consumedTokenPrefix afterSequent suffix =
                      formulaTokens := by
                simpa [compactClosedFormulaTokenValueParser] using
                  hclosedValue
              have hclosed :
                  compactClosedFormulaTokenParser 0 afterSequent =
                    some suffix := hclosedData.1
              rcases (compactClosedFormulaTokenParser_success_iff
                  0 afterSequent suffix).mp hclosed with
                ⟨formula, hfree, hsplit⟩
              let sentence : LO.FirstOrder.ArithmeticSentence :=
                formula.toEmpty hfree
              refine ⟨sentence, ?_⟩
              have hformulaTokens : formulaTokens =
                  compactArithmeticFormulaTokens formula := by
                have hconsumed : formulaTokens =
                    consumedTokenPrefix afterSequent suffix :=
                  hclosedData.2.symm
                rw [hconsumed, hsplit]
                simp
              calc
                root.2.2.1 = formulaTokens := by rw [← hrootFields]
                _ = compactArithmeticFormulaTokens formula := hformulaTokens
                _ = compactSentenceTokens sentence := by
                  simp [sentence, compactSentenceTokens]

#print axioms compactListedProofNodeFieldsParser_tag_zero_firstFormula
#print axioms compactListedProofNodeFieldsParser_tag_one_firstFormula

end FoundationCompactNumericListedDirectProofRootLeafFieldSemantics
