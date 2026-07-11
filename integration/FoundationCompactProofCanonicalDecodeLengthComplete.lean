import integration.FoundationCompactProofCanonicalDecodeLength

/-!
# Canonical decode length for the complete compact proof tree

This layer closes the three remaining rule cases and performs the common
fuel induction over all ten proof constructors.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactProofCanonicalDecodeLengthComplete

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactCanonicalDecodeLength
open FoundationCompactProofCanonicalDecodeLengthBase
open FoundationCompactProofCanonicalDecodeLength

theorem canonicalProofBudget_tag7
    {fuel : Nat} (hrec : CompactProofCanonicalBudget fuel)
    {bits afterTag suffix : List Bool} {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (7, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.binaryLength + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_canonical_length_le htag
  simp only [decodeCompactProof] at hdecode
  rw [htag] at hdecode
  cases hsequent : decodeCompactSequent fuel afterTag with
  | none => simp [hsequent] at hdecode
  | some sequentResult =>
      rcases sequentResult with ⟨Gamma, afterSequent⟩
      cases hpremise : decodeCompactProof fuel afterSequent with
      | none => simp [hsequent, hpremise] at hdecode
      | some premiseResult =>
          rcases premiseResult with ⟨premise, afterPremise⟩
          simp [hsequent, hpremise] at hdecode
          rcases hdecode with ⟨rfl, rfl⟩
          have hsequentLength :=
            decodeCompactSequent_canonical_length_le hsequent
          have hpremiseLength := hrec hpremise
          simp only [CheckedPAProofTree.binaryLength] at hpremiseLength
          change (binaryNatCode 7).length + afterTag.length <= bits.length at htagLength
          simp only [CheckedPAProofTree.binaryLength,
            CheckedPAProofTree.binaryCode, List.length_append]
          omega

theorem canonicalProofBudget_tag8
    {fuel : Nat} (hrec : CompactProofCanonicalBudget fuel)
    {bits afterTag suffix : List Bool} {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (8, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.binaryLength + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_canonical_length_le htag
  simp only [decodeCompactProof] at hdecode
  rw [htag] at hdecode
  cases hsequent : decodeCompactSequent fuel afterTag with
  | none => simp [hsequent] at hdecode
  | some sequentResult =>
      rcases sequentResult with ⟨Gamma, afterSequent⟩
      cases hpremise : decodeCompactProof fuel afterSequent with
      | none => simp [hsequent, hpremise] at hdecode
      | some premiseResult =>
          rcases premiseResult with ⟨premise, afterPremise⟩
          simp [hsequent, hpremise] at hdecode
          rcases hdecode with ⟨rfl, rfl⟩
          have hsequentLength :=
            decodeCompactSequent_canonical_length_le hsequent
          have hpremiseLength := hrec hpremise
          simp only [CheckedPAProofTree.binaryLength] at hpremiseLength
          change (binaryNatCode 8).length + afterTag.length <= bits.length at htagLength
          simp only [CheckedPAProofTree.binaryLength,
            CheckedPAProofTree.binaryCode, List.length_append]
          omega

theorem canonicalProofBudget_tag9
    {fuel : Nat} (hrec : CompactProofCanonicalBudget fuel)
    {bits afterTag suffix : List Bool} {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (9, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.binaryLength + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_canonical_length_le htag
  simp only [decodeCompactProof] at hdecode
  rw [htag] at hdecode
  cases hsequent : decodeCompactSequent fuel afterTag with
  | none => simp [hsequent] at hdecode
  | some sequentResult =>
      rcases sequentResult with ⟨Gamma, afterSequent⟩
      cases hformula : decodeCompactFormula 0 fuel afterSequent with
      | none => simp [hsequent, hformula] at hdecode
      | some formulaResult =>
          rcases formulaResult with ⟨formula, afterFormula⟩
          cases hleft : decodeCompactProof fuel afterFormula with
          | none => simp [hsequent, hformula, hleft] at hdecode
          | some leftResult =>
              rcases leftResult with ⟨left, afterLeft⟩
              cases hright : decodeCompactProof fuel afterLeft with
              | none =>
                  simp [hsequent, hformula, hleft, hright] at hdecode
              | some rightResult =>
                  rcases rightResult with ⟨right, afterRight⟩
                  simp [hsequent, hformula, hleft, hright] at hdecode
                  rcases hdecode with ⟨rfl, rfl⟩
                  have hsequentLength :=
                    decodeCompactSequent_canonical_length_le hsequent
                  have hformulaLength :=
                    decodeCompactFormula_canonical_length_le hformula
                  have hleftLength := hrec hleft
                  have hrightLength := hrec hright
                  simp only [CheckedPAProofTree.binaryLength] at hleftLength hrightLength
                  change (binaryNatCode 9).length +
                      afterTag.length <= bits.length at htagLength
                  simp only [CheckedPAProofTree.binaryLength,
                    CheckedPAProofTree.binaryCode, List.length_append]
                  omega

theorem decodeCompactProof_binaryLength_le
    {fuel : Nat} : CompactProofCanonicalBudget fuel := by
  induction fuel with
  | zero =>
      intro bits suffix tree hdecode
      simp [decodeCompactProof] at hdecode
  | succ fuel ih =>
      intro bits suffix tree hdecode
      cases htag : decodeBinaryNat bits with
      | none => simp [decodeCompactProof, htag] at hdecode
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          cases tag with
          | zero => exact canonicalProofBudget_tag0 htag hdecode
          | succ tag =>
              cases tag with
              | zero => exact canonicalProofBudget_tag1 htag hdecode
              | succ tag =>
                  cases tag with
                  | zero => exact canonicalProofBudget_tag2 htag hdecode
                  | succ tag =>
                      cases tag with
                      | zero => exact canonicalProofBudget_tag3 ih htag hdecode
                      | succ tag =>
                          cases tag with
                          | zero => exact canonicalProofBudget_tag4 ih htag hdecode
                          | succ tag =>
                              cases tag with
                              | zero => exact canonicalProofBudget_tag5 ih htag hdecode
                              | succ tag =>
                                  cases tag with
                                  | zero => exact canonicalProofBudget_tag6 ih htag hdecode
                                  | succ tag =>
                                      cases tag with
                                      | zero => exact canonicalProofBudget_tag7 ih htag hdecode
                                      | succ tag =>
                                          cases tag with
                                          | zero =>
                                              exact canonicalProofBudget_tag8 ih htag hdecode
                                          | succ tag =>
                                              cases tag with
                                              | zero =>
                                                  exact canonicalProofBudget_tag9 ih htag hdecode
                                              | succ tag =>
                                                  simp [decodeCompactProof,
                                                    htag] at hdecode

#print axioms decodeCompactProof_binaryLength_le

end FoundationCompactProofCanonicalDecodeLengthComplete
