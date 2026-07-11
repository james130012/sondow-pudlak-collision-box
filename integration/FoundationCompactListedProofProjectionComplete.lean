import integration.FoundationCompactListedProofProjection

/-!
# Complete projection of list-preserving compact proof decoding
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedProofProjectionComplete

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactListedProofDecoder
open FoundationCompactListedProofProjectionBase
open FoundationCompactListedProofProjection

theorem listedProofProjection_tag7
    {fuel : Nat} (hrec : ListedProofProjectionBudget fuel)
    {bits afterTag suffix : List Bool}
    {listedTree : ListedCheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (7, afterTag))
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
      cases hpremise : decodeCompactListedProof fuel afterSequent with
      | none => simp [hsequent, hpremise] at hdecode
      | some premiseResult =>
          rcases premiseResult with ⟨premise, afterPremise⟩
          simp [hsequent, hpremise] at hdecode
          rcases hdecode with ⟨rfl, rfl⟩
          have hcheckedSequent :=
            decodeCompactSequentList_toFinset hsequent
          have hcheckedPremise := hrec hpremise
          simp [decodeCompactProof, htag, hcheckedSequent,
            hcheckedPremise, ListedCheckedPAProofTree.toChecked]

theorem listedProofProjection_tag8
    {fuel : Nat} (hrec : ListedProofProjectionBudget fuel)
    {bits afterTag suffix : List Bool}
    {listedTree : ListedCheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (8, afterTag))
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
      cases hpremise : decodeCompactListedProof fuel afterSequent with
      | none => simp [hsequent, hpremise] at hdecode
      | some premiseResult =>
          rcases premiseResult with ⟨premise, afterPremise⟩
          simp [hsequent, hpremise] at hdecode
          rcases hdecode with ⟨rfl, rfl⟩
          have hcheckedSequent :=
            decodeCompactSequentList_toFinset hsequent
          have hcheckedPremise := hrec hpremise
          simp [decodeCompactProof, htag, hcheckedSequent,
            hcheckedPremise, ListedCheckedPAProofTree.toChecked]

theorem listedProofProjection_tag9
    {fuel : Nat} (hrec : ListedProofProjectionBudget fuel)
    {bits afterTag suffix : List Bool}
    {listedTree : ListedCheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (9, afterTag))
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
          cases hleft : decodeCompactListedProof fuel afterFormula with
          | none => simp [hsequent, hformula, hleft] at hdecode
          | some leftResult =>
              rcases leftResult with ⟨left, afterLeft⟩
              cases hright : decodeCompactListedProof fuel afterLeft with
              | none =>
                  simp [hsequent, hformula, hleft, hright] at hdecode
              | some rightResult =>
                  rcases rightResult with ⟨right, afterRight⟩
                  simp [hsequent, hformula, hleft, hright] at hdecode
                  rcases hdecode with ⟨rfl, rfl⟩
                  have hcheckedSequent :=
                    decodeCompactSequentList_toFinset hsequent
                  have hcheckedLeft := hrec hleft
                  have hcheckedRight := hrec hright
                  simp [decodeCompactProof, htag, hcheckedSequent,
                    hformula, hcheckedLeft, hcheckedRight,
                    ListedCheckedPAProofTree.toChecked]

theorem decodeCompactListedProof_toChecked
    {fuel : Nat} : ListedProofProjectionBudget fuel := by
  induction fuel with
  | zero =>
      intro bits suffix listedTree hdecode
      simp [decodeCompactListedProof] at hdecode
  | succ fuel ih =>
      intro bits suffix listedTree hdecode
      cases htag : decodeBinaryNat bits with
      | none => simp [decodeCompactListedProof, htag] at hdecode
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          cases tag with
          | zero => exact listedProofProjection_tag0 htag hdecode
          | succ tag =>
              cases tag with
              | zero => exact listedProofProjection_tag1 htag hdecode
              | succ tag =>
                  cases tag with
                  | zero => exact listedProofProjection_tag2 htag hdecode
                  | succ tag =>
                      cases tag with
                      | zero => exact listedProofProjection_tag3 ih htag hdecode
                      | succ tag =>
                          cases tag with
                          | zero => exact listedProofProjection_tag4 ih htag hdecode
                          | succ tag =>
                              cases tag with
                              | zero => exact listedProofProjection_tag5 ih htag hdecode
                              | succ tag =>
                                  cases tag with
                                  | zero => exact listedProofProjection_tag6 ih htag hdecode
                                  | succ tag =>
                                      cases tag with
                                      | zero => exact listedProofProjection_tag7 ih htag hdecode
                                      | succ tag =>
                                          cases tag with
                                          | zero =>
                                              exact listedProofProjection_tag8 ih htag hdecode
                                          | succ tag =>
                                              cases tag with
                                              | zero =>
                                                  exact listedProofProjection_tag9 ih htag hdecode
                                              | succ tag =>
                                                  simp [decodeCompactListedProof,
                                                    htag] at hdecode

#print axioms decodeCompactListedProof_toChecked

end FoundationCompactListedProofProjectionComplete
