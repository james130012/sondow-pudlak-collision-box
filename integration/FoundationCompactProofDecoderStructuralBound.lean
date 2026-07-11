import integration.FoundationCompactVerifierStructuralBound

/-!
# Structural bound for the complete compact proof decoder

The ten rule cases are kept as small independent lemmas so that the final
fuel induction remains cheap to elaborate on modest hardware.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactProofDecoderStructuralBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAProofVerifier
open FoundationCompactVerifierStructuralBound

theorem proofBudget_tag3
    {fuel : Nat} (hrec : CompactProofBudget fuel)
    {bits afterTag suffix : List Bool} {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (3, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.parseWeight + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_consumes_two htag
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
                        decodeCompactSequent_symbolCount_le hsequent
                      have hleftFormulaLength :=
                        decodeCompactFormula_symbolCount_le hleftFormula
                      have hrightFormulaLength :=
                        decodeCompactFormula_symbolCount_le hrightFormula
                      have hleftLength := hrec hleft
                      have hrightLength := hrec hright
                      simp only [CheckedPAProofTree.parseWeight]
                      omega

theorem proofBudget_tag4
    {fuel : Nat} (hrec : CompactProofBudget fuel)
    {bits afterTag suffix : List Bool} {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (4, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.parseWeight + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_consumes_two htag
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
                    decodeCompactSequent_symbolCount_le hsequent
                  have hleftFormulaLength :=
                    decodeCompactFormula_symbolCount_le hleftFormula
                  have hrightFormulaLength :=
                    decodeCompactFormula_symbolCount_le hrightFormula
                  have hpremiseLength := hrec hpremise
                  simp only [CheckedPAProofTree.parseWeight]
                  omega

theorem proofBudget_tag5
    {fuel : Nat} (hrec : CompactProofBudget fuel)
    {bits afterTag suffix : List Bool} {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (5, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.parseWeight + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_consumes_two htag
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
                decodeCompactSequent_symbolCount_le hsequent
              have hformulaLength :=
                decodeCompactFormula_symbolCount_le hformula
              have hpremiseLength := hrec hpremise
              simp only [CheckedPAProofTree.parseWeight]
              omega

theorem proofBudget_tag6
    {fuel : Nat} (hrec : CompactProofBudget fuel)
    {bits afterTag suffix : List Bool} {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (6, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.parseWeight + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_consumes_two htag
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
                    decodeCompactSequent_symbolCount_le hsequent
                  have hformulaLength :=
                    decodeCompactFormula_symbolCount_le hformula
                  have hwitnessLength :=
                    decodeCompactTerm_symbolCount_le hwitness
                  have hpremiseLength := hrec hpremise
                  simp only [CheckedPAProofTree.parseWeight]
                  omega

theorem proofBudget_tag7
    {fuel : Nat} (hrec : CompactProofBudget fuel)
    {bits afterTag suffix : List Bool} {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (7, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.parseWeight + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_consumes_two htag
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
            decodeCompactSequent_symbolCount_le hsequent
          have hpremiseLength := hrec hpremise
          simp only [CheckedPAProofTree.parseWeight]
          omega

theorem proofBudget_tag8
    {fuel : Nat} (hrec : CompactProofBudget fuel)
    {bits afterTag suffix : List Bool} {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (8, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.parseWeight + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_consumes_two htag
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
            decodeCompactSequent_symbolCount_le hsequent
          have hpremiseLength := hrec hpremise
          simp only [CheckedPAProofTree.parseWeight]
          omega

theorem proofBudget_tag9
    {fuel : Nat} (hrec : CompactProofBudget fuel)
    {bits afterTag suffix : List Bool} {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (9, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.parseWeight + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_consumes_two htag
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
                    decodeCompactSequent_symbolCount_le hsequent
                  have hformulaLength :=
                    decodeCompactFormula_symbolCount_le hformula
                  have hleftLength := hrec hleft
                  have hrightLength := hrec hright
                  simp only [CheckedPAProofTree.parseWeight]
                  omega

theorem decodeCompactProof_parseWeight_le
    {fuel : Nat} : CompactProofBudget fuel := by
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
          | zero => exact proofBudget_tag0 htag hdecode
          | succ tag =>
              cases tag with
              | zero => exact proofBudget_tag1 htag hdecode
              | succ tag =>
                  cases tag with
                  | zero => exact proofBudget_tag2 htag hdecode
                  | succ tag =>
                      cases tag with
                      | zero => exact proofBudget_tag3 ih htag hdecode
                      | succ tag =>
                          cases tag with
                          | zero => exact proofBudget_tag4 ih htag hdecode
                          | succ tag =>
                              cases tag with
                              | zero => exact proofBudget_tag5 ih htag hdecode
                              | succ tag =>
                                  cases tag with
                                  | zero => exact proofBudget_tag6 ih htag hdecode
                                  | succ tag =>
                                      cases tag with
                                      | zero => exact proofBudget_tag7 ih htag hdecode
                                      | succ tag =>
                                          cases tag with
                                          | zero =>
                                              exact proofBudget_tag8 ih htag hdecode
                                          | succ tag =>
                                              cases tag with
                                              | zero =>
                                                  exact proofBudget_tag9 ih htag hdecode
                                              | succ tag =>
                                                  simp [decodeCompactProof,
                                                    htag] at hdecode

end FoundationCompactProofDecoderStructuralBound
