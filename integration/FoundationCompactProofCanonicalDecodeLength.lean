import integration.FoundationCompactProofCanonicalDecodeLengthBase

/-!
# Canonical decode length for the complete compact proof tree
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactProofCanonicalDecodeLength

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactCanonicalDecodeLength
open FoundationCompactProofCanonicalDecodeLengthBase

theorem canonicalProofBudget_tag3
    {fuel : Nat} (hrec : CompactProofCanonicalBudget fuel)
    {bits afterTag suffix : List Bool} {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (3, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.binaryLength + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_canonical_length_le htag
  simp only [decodeCompactProof] at hdecode
  rw [htag] at hdecode
  cases hsequent : decodeCompactSequent fuel afterTag with
  | none => simp [hsequent] at hdecode
  | some sequentResult =>
      rcases sequentResult with ⟨Gamma, afterSequent⟩
      cases hleftFormula : decodeCompactFormula 0 fuel afterSequent with
      | none => simp [hsequent, hleftFormula] at hdecode
      | some leftFormulaResult =>
          rcases leftFormulaResult with ⟨leftFormula, afterLeftFormula⟩
          cases hrightFormula :
              decodeCompactFormula 0 fuel afterLeftFormula with
          | none =>
              simp [hsequent, hleftFormula, hrightFormula] at hdecode
          | some rightFormulaResult =>
              rcases rightFormulaResult with
                ⟨rightFormula, afterRightFormula⟩
              cases hleft : decodeCompactProof fuel afterRightFormula with
              | none =>
                  simp [hsequent, hleftFormula, hrightFormula, hleft]
                    at hdecode
              | some leftResult =>
                  rcases leftResult with ⟨left, afterLeft⟩
                  cases hright : decodeCompactProof fuel afterLeft with
                  | none =>
                      simp [hsequent, hleftFormula, hrightFormula, hleft,
                        hright] at hdecode
                  | some rightResult =>
                      rcases rightResult with ⟨right, afterRight⟩
                      simp [hsequent, hleftFormula, hrightFormula, hleft,
                        hright] at hdecode
                      rcases hdecode with ⟨rfl, rfl⟩
                      have hsequentLength :=
                        decodeCompactSequent_canonical_length_le hsequent
                      have hleftFormulaLength :=
                        decodeCompactFormula_canonical_length_le hleftFormula
                      have hrightFormulaLength :=
                        decodeCompactFormula_canonical_length_le hrightFormula
                      have hleftLength := hrec hleft
                      have hrightLength := hrec hright
                      simp only [CheckedPAProofTree.binaryLength] at hleftLength hrightLength
                      change (binaryNatCode 3).length +
                          afterTag.length <= bits.length at htagLength
                      simp only [CheckedPAProofTree.binaryLength,
                        CheckedPAProofTree.binaryCode, List.length_append]
                      omega

theorem canonicalProofBudget_tag4
    {fuel : Nat} (hrec : CompactProofCanonicalBudget fuel)
    {bits afterTag suffix : List Bool} {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (4, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.binaryLength + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_canonical_length_le htag
  simp only [decodeCompactProof] at hdecode
  rw [htag] at hdecode
  cases hsequent : decodeCompactSequent fuel afterTag with
  | none => simp [hsequent] at hdecode
  | some sequentResult =>
      rcases sequentResult with ⟨Gamma, afterSequent⟩
      cases hleftFormula : decodeCompactFormula 0 fuel afterSequent with
      | none => simp [hsequent, hleftFormula] at hdecode
      | some leftFormulaResult =>
          rcases leftFormulaResult with ⟨leftFormula, afterLeftFormula⟩
          cases hrightFormula :
              decodeCompactFormula 0 fuel afterLeftFormula with
          | none =>
              simp [hsequent, hleftFormula, hrightFormula] at hdecode
          | some rightFormulaResult =>
              rcases rightFormulaResult with
                ⟨rightFormula, afterRightFormula⟩
              cases hpremise : decodeCompactProof fuel afterRightFormula with
              | none =>
                  simp [hsequent, hleftFormula, hrightFormula, hpremise]
                    at hdecode
              | some premiseResult =>
                  rcases premiseResult with ⟨premise, afterPremise⟩
                  simp [hsequent, hleftFormula, hrightFormula, hpremise]
                    at hdecode
                  rcases hdecode with ⟨rfl, rfl⟩
                  have hsequentLength :=
                    decodeCompactSequent_canonical_length_le hsequent
                  have hleftFormulaLength :=
                    decodeCompactFormula_canonical_length_le hleftFormula
                  have hrightFormulaLength :=
                    decodeCompactFormula_canonical_length_le hrightFormula
                  have hpremiseLength := hrec hpremise
                  simp only [CheckedPAProofTree.binaryLength] at hpremiseLength
                  change (binaryNatCode 4).length +
                      afterTag.length <= bits.length at htagLength
                  simp only [CheckedPAProofTree.binaryLength,
                    CheckedPAProofTree.binaryCode, List.length_append]
                  omega

theorem canonicalProofBudget_tag5
    {fuel : Nat} (hrec : CompactProofCanonicalBudget fuel)
    {bits afterTag suffix : List Bool} {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (5, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.binaryLength + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_canonical_length_le htag
  simp only [decodeCompactProof] at hdecode
  rw [htag] at hdecode
  cases hsequent : decodeCompactSequent fuel afterTag with
  | none => simp [hsequent] at hdecode
  | some sequentResult =>
      rcases sequentResult with ⟨Gamma, afterSequent⟩
      cases hformula : decodeCompactFormula 1 fuel afterSequent with
      | none => simp [hsequent, hformula] at hdecode
      | some formulaResult =>
          rcases formulaResult with ⟨formula, afterFormula⟩
          cases hpremise : decodeCompactProof fuel afterFormula with
          | none => simp [hsequent, hformula, hpremise] at hdecode
          | some premiseResult =>
              rcases premiseResult with ⟨premise, afterPremise⟩
              simp [hsequent, hformula, hpremise] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              have hsequentLength :=
                decodeCompactSequent_canonical_length_le hsequent
              have hformulaLength :=
                decodeCompactFormula_canonical_length_le hformula
              have hpremiseLength := hrec hpremise
              simp only [CheckedPAProofTree.binaryLength] at hpremiseLength
              change (binaryNatCode 5).length +
                  afterTag.length <= bits.length at htagLength
              simp only [CheckedPAProofTree.binaryLength,
                CheckedPAProofTree.binaryCode, List.length_append]
              omega

theorem canonicalProofBudget_tag6
    {fuel : Nat} (hrec : CompactProofCanonicalBudget fuel)
    {bits afterTag suffix : List Bool} {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (6, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.binaryLength + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_canonical_length_le htag
  simp only [decodeCompactProof] at hdecode
  rw [htag] at hdecode
  cases hsequent : decodeCompactSequent fuel afterTag with
  | none => simp [hsequent] at hdecode
  | some sequentResult =>
      rcases sequentResult with ⟨Gamma, afterSequent⟩
      cases hformula : decodeCompactFormula 1 fuel afterSequent with
      | none => simp [hsequent, hformula] at hdecode
      | some formulaResult =>
          rcases formulaResult with ⟨formula, afterFormula⟩
          cases hwitness : decodeCompactTerm 0 fuel afterFormula with
          | none => simp [hsequent, hformula, hwitness] at hdecode
          | some witnessResult =>
              rcases witnessResult with ⟨witness, afterWitness⟩
              cases hpremise : decodeCompactProof fuel afterWitness with
              | none =>
                  simp [hsequent, hformula, hwitness, hpremise] at hdecode
              | some premiseResult =>
                  rcases premiseResult with ⟨premise, afterPremise⟩
                  simp [hsequent, hformula, hwitness, hpremise] at hdecode
                  rcases hdecode with ⟨rfl, rfl⟩
                  have hsequentLength :=
                    decodeCompactSequent_canonical_length_le hsequent
                  have hformulaLength :=
                    decodeCompactFormula_canonical_length_le hformula
                  have hwitnessLength :=
                    decodeCompactTerm_canonical_length_le hwitness
                  have hpremiseLength := hrec hpremise
                  simp only [CheckedPAProofTree.binaryLength] at hpremiseLength
                  change (binaryNatCode 6).length +
                      afterTag.length <= bits.length at htagLength
                  simp only [CheckedPAProofTree.binaryLength,
                    CheckedPAProofTree.binaryCode, List.length_append]
                  omega

end FoundationCompactProofCanonicalDecodeLength
