import integration.FoundationCompactListedProofProjectionBase

/-!
# Projection of list-preserving proof decoding: rules 3--6
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedProofProjection

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactListedProofDecoder
open FoundationCompactListedProofProjectionBase

theorem listedProofProjection_tag3
    {fuel : Nat} (hrec : ListedProofProjectionBudget fuel)
    {bits afterTag suffix : List Bool}
    {listedTree : ListedCheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (3, afterTag))
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
              cases hleft :
                  decodeCompactListedProof fuel afterRightFormula with
              | none =>
                  simp [hsequent, hleftFormula, hrightFormula, hleft]
                    at hdecode
              | some leftResult =>
                  rcases leftResult with ⟨left, afterLeft⟩
                  cases hright : decodeCompactListedProof fuel afterLeft with
                  | none =>
                      simp [hsequent, hleftFormula, hrightFormula, hleft,
                        hright] at hdecode
                  | some rightResult =>
                      rcases rightResult with ⟨right, afterRight⟩
                      simp [hsequent, hleftFormula, hrightFormula, hleft,
                        hright] at hdecode
                      rcases hdecode with ⟨rfl, rfl⟩
                      have hcheckedSequent :=
                        decodeCompactSequentList_toFinset hsequent
                      have hcheckedLeft := hrec hleft
                      have hcheckedRight := hrec hright
                      simp [decodeCompactProof, htag, hcheckedSequent,
                        hleftFormula, hrightFormula, hcheckedLeft,
                        hcheckedRight, ListedCheckedPAProofTree.toChecked]

theorem listedProofProjection_tag4
    {fuel : Nat} (hrec : ListedProofProjectionBudget fuel)
    {bits afterTag suffix : List Bool}
    {listedTree : ListedCheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (4, afterTag))
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
              cases hpremise :
                  decodeCompactListedProof fuel afterRightFormula with
              | none =>
                  simp [hsequent, hleftFormula, hrightFormula, hpremise]
                    at hdecode
              | some premiseResult =>
                  rcases premiseResult with ⟨premise, afterPremise⟩
                  simp [hsequent, hleftFormula, hrightFormula, hpremise]
                    at hdecode
                  rcases hdecode with ⟨rfl, rfl⟩
                  have hcheckedSequent :=
                    decodeCompactSequentList_toFinset hsequent
                  have hcheckedPremise := hrec hpremise
                  simp [decodeCompactProof, htag, hcheckedSequent,
                    hleftFormula, hrightFormula, hcheckedPremise,
                    ListedCheckedPAProofTree.toChecked]

theorem listedProofProjection_tag5
    {fuel : Nat} (hrec : ListedProofProjectionBudget fuel)
    {bits afterTag suffix : List Bool}
    {listedTree : ListedCheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (5, afterTag))
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
      cases hformula : decodeCompactFormula 1 fuel afterSequent with
      | none => simp [hsequent, hformula] at hdecode
      | some formulaResult =>
          rcases formulaResult with ⟨formula, afterFormula⟩
          cases hpremise : decodeCompactListedProof fuel afterFormula with
          | none => simp [hsequent, hformula, hpremise] at hdecode
          | some premiseResult =>
              rcases premiseResult with ⟨premise, afterPremise⟩
              simp [hsequent, hformula, hpremise] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              have hcheckedSequent :=
                decodeCompactSequentList_toFinset hsequent
              have hcheckedPremise := hrec hpremise
              simp [decodeCompactProof, htag, hcheckedSequent, hformula,
                hcheckedPremise, ListedCheckedPAProofTree.toChecked]

theorem listedProofProjection_tag6
    {fuel : Nat} (hrec : ListedProofProjectionBudget fuel)
    {bits afterTag suffix : List Bool}
    {listedTree : ListedCheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (6, afterTag))
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
      cases hformula : decodeCompactFormula 1 fuel afterSequent with
      | none => simp [hsequent, hformula] at hdecode
      | some formulaResult =>
          rcases formulaResult with ⟨formula, afterFormula⟩
          cases hwitness : decodeCompactTerm 0 fuel afterFormula with
          | none => simp [hsequent, hformula, hwitness] at hdecode
          | some witnessResult =>
              rcases witnessResult with ⟨witness, afterWitness⟩
              cases hpremise : decodeCompactListedProof fuel afterWitness with
              | none =>
                  simp [hsequent, hformula, hwitness, hpremise] at hdecode
              | some premiseResult =>
                  rcases premiseResult with ⟨premise, afterPremise⟩
                  simp [hsequent, hformula, hwitness, hpremise] at hdecode
                  rcases hdecode with ⟨rfl, rfl⟩
                  have hcheckedSequent :=
                    decodeCompactSequentList_toFinset hsequent
                  have hcheckedPremise := hrec hpremise
                  simp [decodeCompactProof, htag, hcheckedSequent, hformula,
                    hwitness, hcheckedPremise,
                    ListedCheckedPAProofTree.toChecked]

end FoundationCompactListedProofProjection
