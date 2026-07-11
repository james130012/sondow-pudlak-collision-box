import integration.FoundationCompactSyntaxTransformationCodeBounds
import integration.FoundationCompactListedProofDecoder

/-!
# Honest bit weight for list-preserving compact proof objects

The local verifier retains decoded sequent lists, including duplicates.  This
file charges every retained formula code and proves that successful decoding
cannot create more charged list data than a fixed multiple of the consumed
input bits.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedProofHonestWeight

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactVerifierStructuralBound
open FoundationCompactCanonicalDecodeLength
open FoundationCompactListedProofDecoder
open FoundationCompactVerifierFormulaListChecks
open FoundationCompactSyntaxTransformationBounds

theorem one_le_binaryFormulaCode_length
    {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    1 <= (binaryFormulaCode formula).length := by
  exact (one_le_formulaSymbolCount formula).trans
    (formulaSymbolCount_le_binaryFormulaCode_length formula)

theorem formulaListCodeWeight_le_four_codeSum
    (formulas : List LO.FirstOrder.ArithmeticProposition) :
    formulaListCodeWeight formulas <=
      4 * (formulas.map
        (fun formula => (binaryFormulaCode formula).length)).sum := by
  induction formulas with
  | nil => simp
  | cons formula formulas ih =>
      have hformula := one_le_binaryFormulaCode_length formula
      simp only [formulaListCodeWeight_cons, List.map_cons, List.sum_cons]
      omega

theorem formulaList_length_le_codeWeight
    (formulas : List LO.FirstOrder.ArithmeticProposition) :
    formulas.length <= formulaListCodeWeight formulas := by
  induction formulas with
  | nil => simp
  | cons formula formulas ih =>
      simp only [List.length_cons, formulaListCodeWeight_cons]
      omega

theorem decodeCompactFormula_eight_suffix_le
    {arity fuel : Nat} {bits suffix : List Bool}
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat arity}
    (hdecode : decodeCompactFormula arity fuel bits = some (formula, suffix)) :
    (binaryFormulaCode formula).length + 8 * suffix.length <=
      8 * bits.length := by
  have hcanonical := decodeCompactFormula_canonical_length_le hdecode
  have hscaled := Nat.mul_le_mul_left 8 hcanonical
  omega

theorem decodeCompactTerm_eight_suffix_le
    {arity fuel : Nat} {bits suffix : List Bool}
    {term : LO.FirstOrder.ArithmeticSemiterm Nat arity}
    (hdecode : decodeCompactTerm arity fuel bits = some (term, suffix)) :
    (binaryTermCode term).length + 8 * suffix.length <=
      8 * bits.length := by
  have hcanonical := decodeCompactTerm_canonical_length_le hdecode
  have hscaled := Nat.mul_le_mul_left 8 hcanonical
  omega

theorem decodeBinaryNat_one_add_eight_suffix_le
    {bits suffix : List Bool} {value : Nat}
    (hdecode : decodeBinaryNat bits = some (value, suffix)) :
    1 + 8 * suffix.length <= 8 * bits.length := by
  have hcanonical := decodeBinaryNat_canonical_length_le hdecode
  have hminimum := two_le_binaryNatCode_length value
  have hscaled := Nat.mul_le_mul_left 8 hcanonical
  omega

theorem decodeCompactSequentList_honestWeight_le :
    forall {fuel bits suffix Gamma},
      decodeCompactSequentList fuel bits = some (Gamma, suffix) ->
      formulaListCodeWeight Gamma + 8 * suffix.length <=
        8 * bits.length := by
  intro fuel bits suffix Gamma hdecode
  cases hcardinality : decodeBinaryNat bits with
  | none =>
      simp [decodeCompactSequentList, hcardinality] at hdecode
  | some cardinalityResult =>
      rcases cardinalityResult with ⟨cardinality, afterCardinality⟩
      cases hformulas :
          decodeManyVector (decodeCompactFormula 0 fuel) cardinality
            afterCardinality with
      | none =>
          simp [decodeCompactSequentList, hcardinality, hformulas] at hdecode
      | some formulasResult =>
          rcases formulasResult with ⟨formulas, afterFormulas⟩
          simp [decodeCompactSequentList, hcardinality, hformulas] at hdecode
          rcases hdecode with ⟨rfl, rfl⟩
          have hdecodedFormulas :=
            decodeManyVector_weight_le
              (decodeCompactFormula 0 fuel)
              (fun formula => (binaryFormulaCode formula).length)
              (fun h => decodeCompactFormula_canonical_length_le h)
              hformulas
          have hlistWeight :=
            formulaListCodeWeight_le_four_codeSum formulas.toList
          have hheader := decodeBinaryNat_canonical_length_le hcardinality
          have hdecodedScaled := Nat.mul_le_mul_left 8 hdecodedFormulas
          have hheaderScaled := Nat.mul_le_mul_left 8 hheader
          omega

def listedProofHonestBitWeight :
    ListedCheckedPAProofTree -> Nat
  | .closed Gamma formula =>
      1 + formulaListCodeWeight Gamma +
        (binaryFormulaCode formula).length
  | .axm Gamma sentence =>
      1 + formulaListCodeWeight Gamma +
        (binaryFormulaCode
          (Rewriting.emb sentence :
            LO.FirstOrder.ArithmeticProposition)).length
  | .verum Gamma =>
      1 + formulaListCodeWeight Gamma
  | .and Gamma leftFormula rightFormula left right =>
      1 + formulaListCodeWeight Gamma +
        (binaryFormulaCode leftFormula).length +
        (binaryFormulaCode rightFormula).length +
        listedProofHonestBitWeight left + listedProofHonestBitWeight right
  | .or Gamma leftFormula rightFormula premise =>
      1 + formulaListCodeWeight Gamma +
        (binaryFormulaCode leftFormula).length +
        (binaryFormulaCode rightFormula).length +
        listedProofHonestBitWeight premise
  | .all Gamma formula premise =>
      1 + formulaListCodeWeight Gamma +
        (binaryFormulaCode formula).length +
        listedProofHonestBitWeight premise
  | .exs Gamma formula witness premise =>
      1 + formulaListCodeWeight Gamma +
        (binaryFormulaCode formula).length +
        (binaryTermCode witness).length +
        listedProofHonestBitWeight premise
  | .wk Gamma premise =>
      1 + formulaListCodeWeight Gamma + listedProofHonestBitWeight premise
  | .shift Gamma premise =>
      1 + formulaListCodeWeight Gamma + listedProofHonestBitWeight premise
  | .cut Gamma formula left right =>
      1 + formulaListCodeWeight Gamma +
        (binaryFormulaCode formula).length +
        listedProofHonestBitWeight left + listedProofHonestBitWeight right

theorem conclusionList_codeWeight_le_honestBitWeight
    (tree : ListedCheckedPAProofTree) :
    formulaListCodeWeight tree.conclusionList <=
      listedProofHonestBitWeight tree := by
  cases tree <;>
    simp [ListedCheckedPAProofTree.conclusionList,
      listedProofHonestBitWeight] <;> omega

def ListedProofHonestWeightBudget (fuel : Nat) : Prop :=
  forall {bits suffix tree},
    decodeCompactListedProof fuel bits = some (tree, suffix) ->
      listedProofHonestBitWeight tree + 8 * suffix.length <= 8 * bits.length

theorem listedProofHonestWeight_tag0
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {tree : ListedCheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (0, afterTag))
    (hdecode : decodeCompactListedProof (fuel + 1) bits =
      some (tree, suffix)) :
    listedProofHonestBitWeight tree + 8 * suffix.length <= 8 * bits.length := by
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
          have htagWeight := decodeBinaryNat_one_add_eight_suffix_le htag
          have hsequentWeight :=
            decodeCompactSequentList_honestWeight_le hsequent
          have hformulaWeight := decodeCompactFormula_eight_suffix_le hformula
          simp only [listedProofHonestBitWeight]
          omega

theorem listedProofHonestWeight_tag1
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {tree : ListedCheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (1, afterTag))
    (hdecode : decodeCompactListedProof (fuel + 1) bits =
      some (tree, suffix)) :
    listedProofHonestBitWeight tree + 8 * suffix.length <= 8 * bits.length := by
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
              have hemb :
                  (Rewriting.emb sentence :
                    LO.FirstOrder.ArithmeticProposition) = formula := by
                unfold propositionToSentence at hsentence
                split at hsentence
                next hclosed =>
                  simp at hsentence
                  subst sentence
                  exact Semiformula.emb_toEmpty formula hclosed
                next hnotClosed => simp at hsentence
              have htagWeight := decodeBinaryNat_one_add_eight_suffix_le htag
              have hsequentWeight :=
                decodeCompactSequentList_honestWeight_le hsequent
              have hformulaWeight :=
                decodeCompactFormula_eight_suffix_le hformula
              simp only [listedProofHonestBitWeight]
              rw [hemb]
              omega

theorem listedProofHonestWeight_tag2
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {tree : ListedCheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (2, afterTag))
    (hdecode : decodeCompactListedProof (fuel + 1) bits =
      some (tree, suffix)) :
    listedProofHonestBitWeight tree + 8 * suffix.length <= 8 * bits.length := by
  simp only [decodeCompactListedProof] at hdecode
  rw [htag] at hdecode
  cases hsequent : decodeCompactSequentList fuel afterTag with
  | none => simp [hsequent] at hdecode
  | some sequentResult =>
      rcases sequentResult with ⟨Gamma, afterSequent⟩
      simp [hsequent] at hdecode
      rcases hdecode with ⟨rfl, rfl⟩
      have htagWeight := decodeBinaryNat_one_add_eight_suffix_le htag
      have hsequentWeight :=
        decodeCompactSequentList_honestWeight_le hsequent
      simp only [listedProofHonestBitWeight]
      omega

theorem listedProofHonestWeight_tag3
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {tree : ListedCheckedPAProofTree}
    (ih : ListedProofHonestWeightBudget fuel)
    (htag : decodeBinaryNat bits = some (3, afterTag))
    (hdecode : decodeCompactListedProof (fuel + 1) bits =
      some (tree, suffix)) :
    listedProofHonestBitWeight tree + 8 * suffix.length <= 8 * bits.length := by
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
              cases hleftProof :
                  decodeCompactListedProof fuel afterRightFormula with
              | none =>
                  simp [hsequent, hleftFormula, hrightFormula,
                    hleftProof] at hdecode
              | some leftProofResult =>
                  rcases leftProofResult with ⟨leftProof, afterLeftProof⟩
                  cases hrightProof :
                      decodeCompactListedProof fuel afterLeftProof with
                  | none =>
                      simp [hsequent, hleftFormula, hrightFormula,
                        hleftProof, hrightProof] at hdecode
                  | some rightProofResult =>
                      rcases rightProofResult with ⟨rightProof, finalSuffix⟩
                      simp [hsequent, hleftFormula, hrightFormula,
                        hleftProof, hrightProof] at hdecode
                      rcases hdecode with ⟨rfl, rfl⟩
                      have htagWeight :=
                        decodeBinaryNat_one_add_eight_suffix_le htag
                      have hsequentWeight :=
                        decodeCompactSequentList_honestWeight_le hsequent
                      have hleftFormulaWeight :=
                        decodeCompactFormula_eight_suffix_le hleftFormula
                      have hrightFormulaWeight :=
                        decodeCompactFormula_eight_suffix_le hrightFormula
                      have hleftProofWeight := ih hleftProof
                      have hrightProofWeight := ih hrightProof
                      simp only [listedProofHonestBitWeight]
                      omega

theorem listedProofHonestWeight_tag4
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {tree : ListedCheckedPAProofTree}
    (ih : ListedProofHonestWeightBudget fuel)
    (htag : decodeBinaryNat bits = some (4, afterTag))
    (hdecode : decodeCompactListedProof (fuel + 1) bits =
      some (tree, suffix)) :
    listedProofHonestBitWeight tree + 8 * suffix.length <= 8 * bits.length := by
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
                  simp [hsequent, hleftFormula, hrightFormula,
                    hpremise] at hdecode
              | some premiseResult =>
                  rcases premiseResult with ⟨premise, finalSuffix⟩
                  simp [hsequent, hleftFormula, hrightFormula,
                    hpremise] at hdecode
                  rcases hdecode with ⟨rfl, rfl⟩
                  have htagWeight :=
                    decodeBinaryNat_one_add_eight_suffix_le htag
                  have hsequentWeight :=
                    decodeCompactSequentList_honestWeight_le hsequent
                  have hleftFormulaWeight :=
                    decodeCompactFormula_eight_suffix_le hleftFormula
                  have hrightFormulaWeight :=
                    decodeCompactFormula_eight_suffix_le hrightFormula
                  have hpremiseWeight := ih hpremise
                  simp only [listedProofHonestBitWeight]
                  omega

theorem listedProofHonestWeight_tag5
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {tree : ListedCheckedPAProofTree}
    (ih : ListedProofHonestWeightBudget fuel)
    (htag : decodeBinaryNat bits = some (5, afterTag))
    (hdecode : decodeCompactListedProof (fuel + 1) bits =
      some (tree, suffix)) :
    listedProofHonestBitWeight tree + 8 * suffix.length <= 8 * bits.length := by
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
              rcases premiseResult with ⟨premise, finalSuffix⟩
              simp [hsequent, hformula, hpremise] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              have htagWeight :=
                decodeBinaryNat_one_add_eight_suffix_le htag
              have hsequentWeight :=
                decodeCompactSequentList_honestWeight_le hsequent
              have hformulaWeight :=
                decodeCompactFormula_eight_suffix_le hformula
              have hpremiseWeight := ih hpremise
              simp only [listedProofHonestBitWeight]
              omega

theorem listedProofHonestWeight_tag6
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {tree : ListedCheckedPAProofTree}
    (ih : ListedProofHonestWeightBudget fuel)
    (htag : decodeBinaryNat bits = some (6, afterTag))
    (hdecode : decodeCompactListedProof (fuel + 1) bits =
      some (tree, suffix)) :
    listedProofHonestBitWeight tree + 8 * suffix.length <= 8 * bits.length := by
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
                  rcases premiseResult with ⟨premise, finalSuffix⟩
                  simp [hsequent, hformula, hwitness, hpremise] at hdecode
                  rcases hdecode with ⟨rfl, rfl⟩
                  have htagWeight :=
                    decodeBinaryNat_one_add_eight_suffix_le htag
                  have hsequentWeight :=
                    decodeCompactSequentList_honestWeight_le hsequent
                  have hformulaWeight :=
                    decodeCompactFormula_eight_suffix_le hformula
                  have hwitnessWeight :=
                    decodeCompactTerm_eight_suffix_le hwitness
                  have hpremiseWeight := ih hpremise
                  simp only [listedProofHonestBitWeight]
                  omega

theorem listedProofHonestWeight_tag7
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {tree : ListedCheckedPAProofTree}
    (ih : ListedProofHonestWeightBudget fuel)
    (htag : decodeBinaryNat bits = some (7, afterTag))
    (hdecode : decodeCompactListedProof (fuel + 1) bits =
      some (tree, suffix)) :
    listedProofHonestBitWeight tree + 8 * suffix.length <= 8 * bits.length := by
  simp only [decodeCompactListedProof] at hdecode
  rw [htag] at hdecode
  cases hsequent : decodeCompactSequentList fuel afterTag with
  | none => simp [hsequent] at hdecode
  | some sequentResult =>
      rcases sequentResult with ⟨Gamma, afterSequent⟩
      cases hpremise : decodeCompactListedProof fuel afterSequent with
      | none => simp [hsequent, hpremise] at hdecode
      | some premiseResult =>
          rcases premiseResult with ⟨premise, finalSuffix⟩
          simp [hsequent, hpremise] at hdecode
          rcases hdecode with ⟨rfl, rfl⟩
          have htagWeight := decodeBinaryNat_one_add_eight_suffix_le htag
          have hsequentWeight :=
            decodeCompactSequentList_honestWeight_le hsequent
          have hpremiseWeight := ih hpremise
          simp only [listedProofHonestBitWeight]
          omega

theorem listedProofHonestWeight_tag8
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {tree : ListedCheckedPAProofTree}
    (ih : ListedProofHonestWeightBudget fuel)
    (htag : decodeBinaryNat bits = some (8, afterTag))
    (hdecode : decodeCompactListedProof (fuel + 1) bits =
      some (tree, suffix)) :
    listedProofHonestBitWeight tree + 8 * suffix.length <= 8 * bits.length := by
  simp only [decodeCompactListedProof] at hdecode
  rw [htag] at hdecode
  cases hsequent : decodeCompactSequentList fuel afterTag with
  | none => simp [hsequent] at hdecode
  | some sequentResult =>
      rcases sequentResult with ⟨Gamma, afterSequent⟩
      cases hpremise : decodeCompactListedProof fuel afterSequent with
      | none => simp [hsequent, hpremise] at hdecode
      | some premiseResult =>
          rcases premiseResult with ⟨premise, finalSuffix⟩
          simp [hsequent, hpremise] at hdecode
          rcases hdecode with ⟨rfl, rfl⟩
          have htagWeight := decodeBinaryNat_one_add_eight_suffix_le htag
          have hsequentWeight :=
            decodeCompactSequentList_honestWeight_le hsequent
          have hpremiseWeight := ih hpremise
          simp only [listedProofHonestBitWeight]
          omega

theorem listedProofHonestWeight_tag9
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {tree : ListedCheckedPAProofTree}
    (ih : ListedProofHonestWeightBudget fuel)
    (htag : decodeBinaryNat bits = some (9, afterTag))
    (hdecode : decodeCompactListedProof (fuel + 1) bits =
      some (tree, suffix)) :
    listedProofHonestBitWeight tree + 8 * suffix.length <= 8 * bits.length := by
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
          cases hleftProof : decodeCompactListedProof fuel afterFormula with
          | none => simp [hsequent, hformula, hleftProof] at hdecode
          | some leftProofResult =>
              rcases leftProofResult with ⟨leftProof, afterLeftProof⟩
              cases hrightProof :
                  decodeCompactListedProof fuel afterLeftProof with
              | none =>
                  simp [hsequent, hformula, hleftProof,
                    hrightProof] at hdecode
              | some rightProofResult =>
                  rcases rightProofResult with ⟨rightProof, finalSuffix⟩
                  simp [hsequent, hformula, hleftProof,
                    hrightProof] at hdecode
                  rcases hdecode with ⟨rfl, rfl⟩
                  have htagWeight :=
                    decodeBinaryNat_one_add_eight_suffix_le htag
                  have hsequentWeight :=
                    decodeCompactSequentList_honestWeight_le hsequent
                  have hformulaWeight :=
                    decodeCompactFormula_eight_suffix_le hformula
                  have hleftProofWeight := ih hleftProof
                  have hrightProofWeight := ih hrightProof
                  simp only [listedProofHonestBitWeight]
                  omega

theorem decodeCompactListedProof_honestWeight_le
    {fuel : Nat} : ListedProofHonestWeightBudget fuel := by
  induction fuel with
  | zero =>
      intro bits suffix tree hdecode
      simp [decodeCompactListedProof] at hdecode
  | succ fuel ih =>
      intro bits suffix tree hdecode
      cases htag : decodeBinaryNat bits with
      | none => simp [decodeCompactListedProof, htag] at hdecode
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          cases tag with
          | zero => exact listedProofHonestWeight_tag0 htag hdecode
          | succ tag =>
              cases tag with
              | zero => exact listedProofHonestWeight_tag1 htag hdecode
              | succ tag =>
                  cases tag with
                  | zero => exact listedProofHonestWeight_tag2 htag hdecode
                  | succ tag =>
                      cases tag with
                      | zero =>
                          exact listedProofHonestWeight_tag3 ih htag hdecode
                      | succ tag =>
                          cases tag with
                          | zero =>
                              exact listedProofHonestWeight_tag4 ih htag hdecode
                          | succ tag =>
                              cases tag with
                              | zero =>
                                  exact listedProofHonestWeight_tag5 ih htag hdecode
                              | succ tag =>
                                  cases tag with
                                  | zero =>
                                      exact listedProofHonestWeight_tag6 ih htag hdecode
                                  | succ tag =>
                                      cases tag with
                                      | zero =>
                                          exact listedProofHonestWeight_tag7 ih htag hdecode
                                      | succ tag =>
                                          cases tag with
                                          | zero =>
                                              exact listedProofHonestWeight_tag8 ih htag hdecode
                                          | succ tag =>
                                              cases tag with
                                              | zero =>
                                                  exact listedProofHonestWeight_tag9 ih htag hdecode
                                              | succ tag =>
                                                  simp [decodeCompactListedProof,
                                                    htag] at hdecode

#print axioms decodeCompactSequentList_honestWeight_le
#print axioms listedProofHonestWeight_tag0
#print axioms listedProofHonestWeight_tag1
#print axioms listedProofHonestWeight_tag2
#print axioms listedProofHonestWeight_tag3
#print axioms listedProofHonestWeight_tag4
#print axioms listedProofHonestWeight_tag5
#print axioms listedProofHonestWeight_tag6
#print axioms listedProofHonestWeight_tag7
#print axioms listedProofHonestWeight_tag8
#print axioms listedProofHonestWeight_tag9
#print axioms decodeCompactListedProof_honestWeight_le

end FoundationCompactListedProofHonestWeight
