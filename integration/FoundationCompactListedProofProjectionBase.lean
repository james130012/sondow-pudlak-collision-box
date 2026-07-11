import integration.FoundationCompactListedCertificateVerifier

/-!
# Projection of list-preserving proof decoding: base rules
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedProofProjectionBase

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactListedProofDecoder

def ListedProofProjectionBudget (fuel : Nat) : Prop :=
  forall {bits suffix listedTree},
    decodeCompactListedProof fuel bits = some (listedTree, suffix) ->
      decodeCompactProof fuel bits = some (listedTree.toChecked, suffix)

theorem listedProofProjection_tag0
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {listedTree : ListedCheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (0, afterTag))
    (hdecode : decodeCompactListedProof (fuel + 1) bits =
      some (listedTree, suffix)) :
    decodeCompactProof (fuel + 1) bits =
      some (listedTree.toChecked, suffix) := by
  simp only [decodeCompactListedProof] at hdecode
  rw [htag] at hdecode
  cases hsequent : decodeCompactSequentList fuel afterTag with
  | none => simp [hsequent] at hdecode
  | some sequentResult =>
      rcases sequentResult with ⟨Gamma, afterSequent⟩
      cases hformula : decodeCompactFormula 0 fuel afterSequent with
      | none => simp [hsequent, hformula] at hdecode
      | some formulaResult =>
          rcases formulaResult with ⟨formula, afterFormula⟩
          simp [hsequent, hformula] at hdecode
          rcases hdecode with ⟨rfl, rfl⟩
          have hcheckedSequent := decodeCompactSequentList_toFinset hsequent
          simp [decodeCompactProof, htag, hcheckedSequent, hformula,
            ListedCheckedPAProofTree.toChecked]

theorem listedProofProjection_tag1
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {listedTree : ListedCheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (1, afterTag))
    (hdecode : decodeCompactListedProof (fuel + 1) bits =
      some (listedTree, suffix)) :
    decodeCompactProof (fuel + 1) bits =
      some (listedTree.toChecked, suffix) := by
  simp only [decodeCompactListedProof] at hdecode
  rw [htag] at hdecode
  cases hsequent : decodeCompactSequentList fuel afterTag with
  | none => simp [hsequent] at hdecode
  | some sequentResult =>
      rcases sequentResult with ⟨Gamma, afterSequent⟩
      cases hformula : decodeCompactFormula 0 fuel afterSequent with
      | none => simp [hsequent, hformula] at hdecode
      | some formulaResult =>
          rcases formulaResult with ⟨formula, afterFormula⟩
          cases hsentence : propositionToSentence formula with
          | none => simp [hsequent, hformula, hsentence] at hdecode
          | some sentence =>
              simp [hsequent, hformula, hsentence] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              have hcheckedSequent :=
                decodeCompactSequentList_toFinset hsequent
              simp [decodeCompactProof, htag, hcheckedSequent, hformula,
                hsentence, ListedCheckedPAProofTree.toChecked]

theorem listedProofProjection_tag2
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {listedTree : ListedCheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (2, afterTag))
    (hdecode : decodeCompactListedProof (fuel + 1) bits =
      some (listedTree, suffix)) :
    decodeCompactProof (fuel + 1) bits =
      some (listedTree.toChecked, suffix) := by
  simp only [decodeCompactListedProof] at hdecode
  rw [htag] at hdecode
  cases hsequent : decodeCompactSequentList fuel afterTag with
  | none => simp [hsequent] at hdecode
  | some sequentResult =>
      rcases sequentResult with ⟨Gamma, afterSequent⟩
      simp [hsequent] at hdecode
      rcases hdecode with ⟨rfl, rfl⟩
      have hcheckedSequent := decodeCompactSequentList_toFinset hsequent
      simp [decodeCompactProof, htag, hcheckedSequent,
        ListedCheckedPAProofTree.toChecked]

end FoundationCompactListedProofProjectionBase
