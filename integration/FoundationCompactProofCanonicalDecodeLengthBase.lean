import integration.FoundationCompactCanonicalDecodeLength

/-!
# Canonical decode length for compact proof rules: base cases
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactProofCanonicalDecodeLengthBase

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactCanonicalDecodeLength

def CompactProofCanonicalBudget (fuel : Nat) : Prop :=
  forall {bits suffix tree},
    decodeCompactProof fuel bits = some (tree, suffix) ->
      tree.binaryLength + suffix.length <= bits.length

theorem canonicalProofBudget_tag0
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (0, afterTag))
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
          simp [hsequent, hformula] at hdecode
          rcases hdecode with ⟨rfl, rfl⟩
          have hsequentLength :=
            decodeCompactSequent_canonical_length_le hsequent
          have hformulaLength :=
            decodeCompactFormula_canonical_length_le hformula
          simp only [CheckedPAProofTree.binaryLength,
            CheckedPAProofTree.binaryCode, List.length_append]
          omega

theorem canonicalProofBudget_tag1
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (1, afterTag))
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
          cases hsentence : propositionToSentence formula with
          | none => simp [hsequent, hformula, hsentence] at hdecode
          | some sigma =>
              simp [hsequent, hformula, hsentence] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              have hsequentLength :=
                decodeCompactSequent_canonical_length_le hsequent
              have hformulaLength :=
                decodeCompactFormula_canonical_length_le hformula
              have hemb :
                  (Rewriting.emb sigma :
                    LO.FirstOrder.ArithmeticProposition) = formula := by
                unfold propositionToSentence at hsentence
                split at hsentence
                next hclosed =>
                  simp at hsentence
                  subst sigma
                  exact Semiformula.emb_toEmpty formula hclosed
                next hnotClosed => simp at hsentence
              simp only [CheckedPAProofTree.binaryLength,
                CheckedPAProofTree.binaryCode, List.length_append]
              rw [hemb]
              change (binaryNatCode 1).length +
                  afterTag.length <= bits.length at htagLength
              omega

theorem canonicalProofBudget_tag2
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (2, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.binaryLength + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_canonical_length_le htag
  simp only [decodeCompactProof] at hdecode
  rw [htag] at hdecode
  cases hsequent : decodeCompactSequent fuel afterTag with
  | none => simp [hsequent] at hdecode
  | some sequentResult =>
      rcases sequentResult with ⟨Gamma, afterSequent⟩
      simp [hsequent] at hdecode
      rcases hdecode with ⟨rfl, rfl⟩
      have hsequentLength :=
        decodeCompactSequent_canonical_length_le hsequent
      change (binaryNatCode 2).length +
          afterTag.length <= bits.length at htagLength
      simp only [CheckedPAProofTree.binaryLength,
        CheckedPAProofTree.binaryCode, List.length_append]
      omega

end FoundationCompactProofCanonicalDecodeLengthBase
