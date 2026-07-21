import integration.FoundationCompactNumericListedRootFieldsDecomposition
import integration.FoundationCompactNumericListedNodeFieldsTypedInversion

/-!
# Typed inversion of one listed-proof root node
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedProofNodeTypedInversion

open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedNodeFieldsTypedInversion

inductive CompactNumericProofNodeTyped :
    List Nat -> CompactNumericProofRoot -> Prop
  | closed (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (formula : LO.FirstOrder.ArithmeticProposition) (suffix : List Nat) :
      CompactNumericProofNodeTyped
        (0 :: compactSequentListTokens Gamma ++
          compactArithmeticFormulaTokens formula ++ suffix)
        (0, (arithmeticPropositionTokenValues Gamma,
          (compactArithmeticFormulaTokens formula,
            ([], ([], suffix)))))
  | axm (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (sentence : LO.FirstOrder.ArithmeticSentence) (suffix : List Nat) :
      CompactNumericProofNodeTyped
        (1 :: compactSequentListTokens Gamma ++
          compactArithmeticFormulaTokens
            (Rewriting.emb sentence : LO.FirstOrder.ArithmeticProposition) ++
          suffix)
        (1, (arithmeticPropositionTokenValues Gamma,
          (compactArithmeticFormulaTokens
              (Rewriting.emb sentence : LO.FirstOrder.ArithmeticProposition),
            ([], ([], suffix)))))
  | verum (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (suffix : List Nat) :
      CompactNumericProofNodeTyped
        (2 :: compactSequentListTokens Gamma ++ suffix)
        (2, (arithmeticPropositionTokenValues Gamma, ([], ([], ([], suffix)))))
  | andNode (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
      (suffix : List Nat) :
      CompactNumericProofNodeTyped
        (3 :: compactSequentListTokens Gamma ++
          compactArithmeticFormulaTokens leftFormula ++
          compactArithmeticFormulaTokens rightFormula ++ suffix)
        (3, (arithmeticPropositionTokenValues Gamma,
          (compactArithmeticFormulaTokens leftFormula,
            (compactArithmeticFormulaTokens rightFormula, ([], suffix)))))
  | orNode (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
      (suffix : List Nat) :
      CompactNumericProofNodeTyped
        (4 :: compactSequentListTokens Gamma ++
          compactArithmeticFormulaTokens leftFormula ++
          compactArithmeticFormulaTokens rightFormula ++ suffix)
        (4, (arithmeticPropositionTokenValues Gamma,
          (compactArithmeticFormulaTokens leftFormula,
            (compactArithmeticFormulaTokens rightFormula, ([], suffix)))))
  | allNode (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
      (suffix : List Nat) :
      CompactNumericProofNodeTyped
        (5 :: compactSequentListTokens Gamma ++
          compactArithmeticFormulaTokens formula ++ suffix)
        (5, (arithmeticPropositionTokenValues Gamma,
          (compactArithmeticFormulaTokens formula, ([], ([], suffix)))))
  | exsNode (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
      (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      (suffix : List Nat) :
      CompactNumericProofNodeTyped
        (6 :: compactSequentListTokens Gamma ++
          compactArithmeticFormulaTokens formula ++
          compactArithmeticTermTokens witness ++ suffix)
        (6, (arithmeticPropositionTokenValues Gamma,
          (compactArithmeticFormulaTokens formula,
            ([], (compactArithmeticTermTokens witness, suffix)))))
  | wkNode (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (suffix : List Nat) :
      CompactNumericProofNodeTyped
        (7 :: compactSequentListTokens Gamma ++ suffix)
        (7, (arithmeticPropositionTokenValues Gamma, ([], ([], ([], suffix)))))
  | shiftNode (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (suffix : List Nat) :
      CompactNumericProofNodeTyped
        (8 :: compactSequentListTokens Gamma ++ suffix)
        (8, (arithmeticPropositionTokenValues Gamma, ([], ([], ([], suffix)))))
  | cutNode (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (formula : LO.FirstOrder.ArithmeticProposition) (suffix : List Nat) :
      CompactNumericProofNodeTyped
        (9 :: compactSequentListTokens Gamma ++
          compactArithmeticFormulaTokens formula ++ suffix)
        (9, (arithmeticPropositionTokenValues Gamma,
          (compactArithmeticFormulaTokens formula, ([], ([], suffix)))))

theorem compactListedProofNodeFieldsParser_eq_some_iff_typed
    (tokens : List Nat) (root : CompactNumericProofRoot) :
    compactListedProofNodeFieldsParser tokens = some root <->
      CompactNumericProofNodeTyped tokens root := by
  constructor
  · intro hparser
    have hvalid :=
      (compactListedProofNodeFieldsParser_eq_some_iff_branchValid
        tokens root).mp hparser
    rcases root with ⟨rootTag, fields⟩
    cases tokens with
    | nil =>
        simp [CompactNumericProofRootBranchValid] at hvalid
    | cons tag body =>
        by_cases h0 : tag = 0
        · subst tag
          have hdata : rootTag = 0 ∧
              compactNodeSequentFormulaFields 0 body = some fields := by
            simpa [CompactNumericProofRootBranchValid] using hvalid
          have hrootTag := hdata.1
          rcases (compactNodeSequentFormulaFields_eq_some_iff_exists_typed
            0 body fields).mp hdata.2 with
            ⟨Gamma, formula, suffix, hbody, hfields⟩
          subst rootTag
          subst fields
          subst body
          exact CompactNumericProofNodeTyped.closed Gamma formula suffix
        · by_cases h1 : tag = 1
          · subst tag
            have hdata : rootTag = 1 ∧
                compactNodeSequentClosedFormulaFields body = some fields := by
              simpa [CompactNumericProofRootBranchValid, h0] using hvalid
            have hrootTag := hdata.1
            rcases (compactNodeSequentClosedFormulaFields_eq_some_iff_exists_typed
              body fields).mp hdata.2 with
              ⟨Gamma, sentence, suffix, hbody, hfields⟩
            subst rootTag
            subst fields
            subst body
            exact CompactNumericProofNodeTyped.axm Gamma sentence suffix
          · by_cases h2 : tag = 2
            · subst tag
              have hdata : rootTag = 2 ∧
                  compactNodeSequentOnlyFields body = some fields := by
                simpa [CompactNumericProofRootBranchValid, h0, h1] using hvalid
              have hrootTag := hdata.1
              rcases (compactNodeSequentOnlyFields_eq_some_iff_exists_typed
                body fields).mp hdata.2 with
                ⟨Gamma, suffix, hbody, hfields⟩
              subst rootTag
              subst fields
              subst body
              exact CompactNumericProofNodeTyped.verum Gamma suffix
            · by_cases h3 : tag = 3
              · subst tag
                have hdata : rootTag = 3 ∧
                    compactNodeSequentTwoFormulaFields 0 body =
                      some fields := by
                  simpa [CompactNumericProofRootBranchValid, h0, h1, h2]
                    using hvalid
                have hrootTag := hdata.1
                rcases (compactNodeSequentTwoFormulaFields_eq_some_iff_exists_typed
                  0 body fields).mp hdata.2 with
                  ⟨Gamma, leftFormula, rightFormula, suffix,
                    hbody, hfields⟩
                subst rootTag
                subst fields
                subst body
                exact CompactNumericProofNodeTyped.andNode
                  Gamma leftFormula rightFormula suffix
              · by_cases h4 : tag = 4
                · subst tag
                  have hdata : rootTag = 4 ∧
                      compactNodeSequentTwoFormulaFields 0 body =
                        some fields := by
                    simpa [CompactNumericProofRootBranchValid,
                      h0, h1, h2, h3] using hvalid
                  have hrootTag := hdata.1
                  rcases (compactNodeSequentTwoFormulaFields_eq_some_iff_exists_typed
                    0 body fields).mp hdata.2 with
                    ⟨Gamma, leftFormula, rightFormula, suffix,
                      hbody, hfields⟩
                  subst rootTag
                  subst fields
                  subst body
                  exact CompactNumericProofNodeTyped.orNode
                    Gamma leftFormula rightFormula suffix
                · by_cases h5 : tag = 5
                  · subst tag
                    have hdata : rootTag = 5 ∧
                        compactNodeSequentFormulaFields 1 body =
                          some fields := by
                      simpa [CompactNumericProofRootBranchValid,
                        h0, h1, h2, h3, h4] using hvalid
                    have hrootTag := hdata.1
                    rcases (compactNodeSequentFormulaFields_eq_some_iff_exists_typed
                      1 body fields).mp hdata.2 with
                      ⟨Gamma, formula, suffix, hbody, hfields⟩
                    subst rootTag
                    subst fields
                    subst body
                    exact CompactNumericProofNodeTyped.allNode
                      Gamma formula suffix
                  · by_cases h6 : tag = 6
                    · subst tag
                      have hdata : rootTag = 6 ∧
                          compactNodeSequentFormulaTermFields 1 0 body =
                            some fields := by
                        simpa [CompactNumericProofRootBranchValid,
                          h0, h1, h2, h3, h4, h5] using hvalid
                      have hrootTag := hdata.1
                      rcases (compactNodeSequentFormulaTermFields_eq_some_iff_exists_typed
                        1 0 body fields).mp hdata.2 with
                        ⟨Gamma, formula, witness, suffix,
                          hbody, hfields⟩
                      subst rootTag
                      subst fields
                      subst body
                      exact CompactNumericProofNodeTyped.exsNode
                        Gamma formula witness suffix
                    · by_cases h7 : tag = 7
                      · subst tag
                        have hdata : rootTag = 7 ∧
                            compactNodeSequentOnlyFields body =
                              some fields := by
                          simpa [CompactNumericProofRootBranchValid,
                            h0, h1, h2, h3, h4, h5, h6] using hvalid
                        have hrootTag := hdata.1
                        rcases (compactNodeSequentOnlyFields_eq_some_iff_exists_typed
                          body fields).mp hdata.2 with
                          ⟨Gamma, suffix, hbody, hfields⟩
                        subst rootTag
                        subst fields
                        subst body
                        exact CompactNumericProofNodeTyped.wkNode Gamma suffix
                      · by_cases h8 : tag = 8
                        · subst tag
                          have hdata : rootTag = 8 ∧
                              compactNodeSequentOnlyFields body =
                                some fields := by
                            simpa [CompactNumericProofRootBranchValid,
                              h0, h1, h2, h3, h4, h5, h6, h7] using hvalid
                          have hrootTag := hdata.1
                          rcases (compactNodeSequentOnlyFields_eq_some_iff_exists_typed
                            body fields).mp hdata.2 with
                            ⟨Gamma, suffix, hbody, hfields⟩
                          subst rootTag
                          subst fields
                          subst body
                          exact CompactNumericProofNodeTyped.shiftNode
                            Gamma suffix
                        · by_cases h9 : tag = 9
                          · subst tag
                            have hdata : rootTag = 9 ∧
                                compactNodeSequentFormulaFields 0 body =
                                  some fields := by
                              simpa [CompactNumericProofRootBranchValid,
                                h0, h1, h2, h3, h4, h5, h6, h7, h8]
                                using hvalid
                            have hrootTag := hdata.1
                            rcases (compactNodeSequentFormulaFields_eq_some_iff_exists_typed
                              0 body fields).mp hdata.2 with
                              ⟨Gamma, formula, suffix, hbody, hfields⟩
                            subst rootTag
                            subst fields
                            subst body
                            exact CompactNumericProofNodeTyped.cutNode
                              Gamma formula suffix
                          · simp [CompactNumericProofRootBranchValid,
                              h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
                              at hvalid
  · intro htyped
    cases htyped with
    | closed Gamma formula suffix =>
        simpa [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields] using
          compactNodeSequentFormulaFields_canonical_append
            Gamma formula suffix
    | axm Gamma sentence suffix =>
        simpa [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields] using
          compactNodeSequentClosedFormulaFields_canonical_append
            Gamma sentence suffix
    | verum Gamma suffix =>
        simpa [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields] using
          compactNodeSequentOnlyFields_canonical_append Gamma suffix
    | andNode Gamma leftFormula rightFormula suffix =>
        simpa [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields] using
          compactNodeSequentTwoFormulaFields_canonical_append
            Gamma leftFormula rightFormula suffix
    | orNode Gamma leftFormula rightFormula suffix =>
        simpa [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields] using
          compactNodeSequentTwoFormulaFields_canonical_append
            Gamma leftFormula rightFormula suffix
    | allNode Gamma formula suffix =>
        simpa [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields] using
          compactNodeSequentFormulaFields_canonical_append
            Gamma formula suffix
    | exsNode Gamma formula witness suffix =>
        simpa [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields] using
          compactNodeSequentFormulaTermFields_canonical_append
            Gamma formula witness suffix
    | wkNode Gamma suffix =>
        simpa [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields] using
          compactNodeSequentOnlyFields_canonical_append Gamma suffix
    | shiftNode Gamma suffix =>
        simpa [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields] using
          compactNodeSequentOnlyFields_canonical_append Gamma suffix
    | cutNode Gamma formula suffix =>
        simpa [compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields] using
          compactNodeSequentFormulaFields_canonical_append
            Gamma formula suffix

#print axioms compactListedProofNodeFieldsParser_eq_some_iff_typed

end FoundationCompactNumericListedProofNodeTypedInversion
