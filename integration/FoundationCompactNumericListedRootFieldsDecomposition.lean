import integration.FoundationCompactNumericListedNodeFields

/-!
# Exact root-field tag dispatch

This module removes the ten-way root parser dispatcher from the direct trace
boundary.  Its residual relation names the selected branch parser explicitly;
the sequent, formula, closed-formula, and term value parsers inside those
branches remain the next trace boundary.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedRootFieldsDecomposition

open FoundationCompactNumericListedNodeFields

abbrev CompactNumericProofRoot := Nat × CompactNumericNodeFields

def CompactNumericProofRootBranchValid
    (tokens : List Nat) (root : CompactNumericProofRoot) : Prop :=
  match tokens with
  | [] => False
  | tag :: suffix =>
      if tag = 0 then
        root.1 = 0 ∧ compactNodeSequentFormulaFields 0 suffix = some root.2
      else if tag = 1 then
        root.1 = 1 ∧ compactNodeSequentClosedFormulaFields suffix = some root.2
      else if tag = 2 then
        root.1 = 2 ∧ compactNodeSequentOnlyFields suffix = some root.2
      else if tag = 3 then
        root.1 = 3 ∧ compactNodeSequentTwoFormulaFields 0 suffix = some root.2
      else if tag = 4 then
        root.1 = 4 ∧ compactNodeSequentTwoFormulaFields 0 suffix = some root.2
      else if tag = 5 then
        root.1 = 5 ∧ compactNodeSequentFormulaFields 1 suffix = some root.2
      else if tag = 6 then
        root.1 = 6 ∧
          compactNodeSequentFormulaTermFields 1 0 suffix = some root.2
      else if tag = 7 then
        root.1 = 7 ∧ compactNodeSequentOnlyFields suffix = some root.2
      else if tag = 8 then
        root.1 = 8 ∧ compactNodeSequentOnlyFields suffix = some root.2
      else if tag = 9 then
        root.1 = 9 ∧ compactNodeSequentFormulaFields 0 suffix = some root.2
      else
        False

theorem compactTagNumericNodeFields_eq_some_iff
    (tag : Nat) (fields : Option CompactNumericNodeFields)
    (root : CompactNumericProofRoot) :
    compactTagNumericNodeFields tag fields = some root ↔
      root.1 = tag ∧ fields = some root.2 := by
  cases fields with
  | none => simp [compactTagNumericNodeFields]
  | some parsed =>
      rcases root with ⟨rootTag, rootFields⟩
      simp [compactTagNumericNodeFields, Prod.ext_iff, eq_comm]

theorem compactListedProofNodeFieldsParser_eq_some_iff_branchValid
    (tokens : List Nat) (root : CompactNumericProofRoot) :
    compactListedProofNodeFieldsParser tokens = some root ↔
      CompactNumericProofRootBranchValid tokens root := by
  cases tokens with
  | nil =>
      simp [compactListedProofNodeFieldsParser,
        CompactNumericProofRootBranchValid]
  | cons tag suffix =>
      by_cases h0 : tag = 0
      · simp_all [compactListedProofNodeFieldsParser,
          CompactNumericProofRootBranchValid,
          compactTagNumericNodeFields_eq_some_iff]
      by_cases h1 : tag = 1
      · simp_all [compactListedProofNodeFieldsParser,
          CompactNumericProofRootBranchValid,
          compactTagNumericNodeFields_eq_some_iff]
      by_cases h2 : tag = 2
      · simp_all [compactListedProofNodeFieldsParser,
          CompactNumericProofRootBranchValid,
          compactTagNumericNodeFields_eq_some_iff]
      by_cases h3 : tag = 3
      · simp_all [compactListedProofNodeFieldsParser,
          CompactNumericProofRootBranchValid,
          compactTagNumericNodeFields_eq_some_iff]
      by_cases h4 : tag = 4
      · simp_all [compactListedProofNodeFieldsParser,
          CompactNumericProofRootBranchValid,
          compactTagNumericNodeFields_eq_some_iff]
      by_cases h5 : tag = 5
      · simp_all [compactListedProofNodeFieldsParser,
          CompactNumericProofRootBranchValid,
          compactTagNumericNodeFields_eq_some_iff]
      by_cases h6 : tag = 6
      · simp_all [compactListedProofNodeFieldsParser,
          CompactNumericProofRootBranchValid,
          compactTagNumericNodeFields_eq_some_iff]
      by_cases h7 : tag = 7
      · simp_all [compactListedProofNodeFieldsParser,
          CompactNumericProofRootBranchValid,
          compactTagNumericNodeFields_eq_some_iff]
      by_cases h8 : tag = 8
      · simp_all [compactListedProofNodeFieldsParser,
          CompactNumericProofRootBranchValid,
          compactTagNumericNodeFields_eq_some_iff]
      by_cases h9 : tag = 9
      · simp_all [compactListedProofNodeFieldsParser,
          CompactNumericProofRootBranchValid,
          compactTagNumericNodeFields_eq_some_iff]
      simp_all [compactListedProofNodeFieldsParser,
        CompactNumericProofRootBranchValid]

theorem compactNumericProofRootBranchValid_primrec :
    PrimrecPred (fun input : List Nat × CompactNumericProofRoot =>
      CompactNumericProofRootBranchValid input.1 input.2) := by
  have hparser : Primrec (fun input : List Nat × CompactNumericProofRoot =>
      compactListedProofNodeFieldsParser input.1) :=
    compactListedProofNodeFieldsParser_primrec.comp Primrec.fst
  have hroot : Primrec (fun input : List Nat × CompactNumericProofRoot =>
      some input.2) :=
    Primrec.option_some.comp Primrec.snd
  exact
    (Primrec.eq.comp hparser hroot).of_eq fun input =>
      compactListedProofNodeFieldsParser_eq_some_iff_branchValid
        input.1 input.2

#print axioms compactTagNumericNodeFields_eq_some_iff
#print axioms compactListedProofNodeFieldsParser_eq_some_iff_branchValid
#print axioms compactNumericProofRootBranchValid_primrec

end FoundationCompactNumericListedRootFieldsDecomposition
