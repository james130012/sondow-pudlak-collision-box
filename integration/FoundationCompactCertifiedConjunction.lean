import integration.FoundationCompactCertifiedModusPonens

/-!
# Explicit certified conjunction assembly

This file supplies the second bounded proof-assembly primitive used in the
quantitative Pudlak argument.  It composes two arbitrary full payloads accepted
by the public list-preserving verifier, reuses both decoded certificates, and
emits a canonical accepted proof of their conjunction.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCertifiedConjunction

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationComputableCompactPAProofEncoder
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactListedCertifiedVerifier
open FoundationCompactListedCertifiedEncoder
open FoundationCompactCertificateCanonicalDecodeLength
open FoundationCompactCanonicalDecodeLength
open FoundationCompactCertifiedModusPonens

def conjunctionSyntaxBudget
    (left right : LO.FirstOrder.ArithmeticProposition) : Nat :=
  (binaryFormulaCode left).length +
    (binaryFormulaCode right).length +
    (binaryFormulaCode (left ⋏ right)).length

theorem binarySequentCode_length_le_three_formula_budget
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (first second third : LO.FirstOrder.ArithmeticProposition)
    (hmem : ∀ formula ∈ Gamma,
      formula = first ∨ formula = second ∨ formula = third) :
    (binarySequentCode Gamma).length <=
      (binaryNatCode 3).length +
        3 * ((binaryFormulaCode first).length +
          (binaryFormulaCode second).length +
          (binaryFormulaCode third).length) := by
  let formulaBudget :=
    (binaryFormulaCode first).length +
      (binaryFormulaCode second).length +
      (binaryFormulaCode third).length
  have hsubset : Gamma ⊆ {first, second, third} := by
    intro formula hformula
    rcases hmem formula hformula with h | h | h <;> simp [h]
  have hcardSet :
      ({first, second, third} :
        Finset LO.FirstOrder.ArithmeticProposition).card <= 3 := by
    have hfirst := Finset.card_insert_le first {second, third}
    have hsecond := Finset.card_insert_le second {third}
    simp only [Finset.card_singleton] at hsecond
    omega
  have hcard : Gamma.card <= 3 :=
    (Finset.card_le_card hsubset).trans hcardSet
  have hheader := binaryNatCode_length_mono hcard
  have hformula
      (formula : LO.FirstOrder.ArithmeticProposition)
      (hformulaMem : formula ∈ Gamma) :
      (binaryFormulaCode formula).length <= formulaBudget := by
    rcases hmem formula hformulaMem with h | h | h <;>
      subst formula <;> simp [formulaBudget] <;> omega
  have hpayload :
      Gamma.sum (fun formula => (binaryFormulaCode formula).length) <=
        Gamma.card * formulaBudget := by
    simpa [nsmul_eq_mul] using
      Gamma.sum_le_card_nsmul
        (fun formula => (binaryFormulaCode formula).length)
        formulaBudget hformula
  have hpayloadBound :
      Gamma.sum (fun formula => (binaryFormulaCode formula).length) <=
        3 * formulaBudget :=
    hpayload.trans (Nat.mul_le_mul_right formulaBudget hcard)
  have hflat :
      (Gamma.toList.flatMap binaryFormulaCode).length =
        Gamma.sum (fun formula => (binaryFormulaCode formula).length) := by
    rw [List.length_flatMap]
    simp
  simp only [binarySequentCode, List.length_append, hflat]
  exact Nat.add_le_add hheader hpayloadBound

def checkedConjunctionTree
    (left right : LO.FirstOrder.ArithmeticProposition)
    (leftTree rightTree : CheckedPAProofTree) :
    CheckedPAProofTree :=
  .and {left ⋏ right} left right
    (.wk (insert left {left ⋏ right}) leftTree)
    (.wk (insert right {left ⋏ right}) rightTree)

def conjunctionCertificate
    (leftCertificate rightCertificate :
      StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .binary (.unary leftCertificate) (.unary rightCertificate)

@[simp] theorem checkedConjunctionTree_conclusion
    (left right : LO.FirstOrder.ArithmeticProposition)
    (leftTree rightTree : CheckedPAProofTree) :
    (checkedConjunctionTree left right leftTree rightTree).conclusion =
      {left ⋏ right} :=
  rfl

theorem checkedConjunctionCertificate_valid
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftTree rightTree : CheckedPAProofTree)
    (leftCertificate rightCertificate :
      StructuralValidityCertificate)
    (hleftConclusion : leftTree.conclusion = {left})
    (hrightConclusion : rightTree.conclusion = {right})
    (hleft : certificateValid leftTree leftCertificate)
    (hright : certificateValid rightTree rightCertificate) :
    certificateValid
      (checkedConjunctionTree left right leftTree rightTree)
      (conjunctionCertificate leftCertificate rightCertificate) := by
  simp [checkedConjunctionTree, conjunctionCertificate,
    CheckedPAProofTree.conclusion, certificateValid, hleft, hright]
  change leftTree.conclusion ⊆ _ ∧ rightTree.conclusion ⊆ _
  constructor
  · rw [hleftConclusion]
    simp
  · rw [hrightConclusion]
    simp

theorem conjunctionCertificate_code_length_le
    (leftCertificate rightCertificate :
      StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (conjunctionCertificate
        leftCertificate rightCertificate)).length <=
      (binaryStructuralValidityCertificateCode leftCertificate).length +
        (binaryStructuralValidityCertificateCode rightCertificate).length +
        48 := by
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  simp only [conjunctionCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

theorem checkedConjunctionTree_code_length_le
    (left right : LO.FirstOrder.ArithmeticProposition)
    (leftTree rightTree : CheckedPAProofTree) :
    (canonicalBinaryProofCode
      (checkedConjunctionTree left right leftTree rightTree)).length <=
      (canonicalBinaryProofCode leftTree).length +
        (canonicalBinaryProofCode rightTree).length + 96 +
        11 * conjunctionSyntaxBudget left right := by
  let conjunction := left ⋏ right
  let syntaxBudget := conjunctionSyntaxBudget left right
  have hbudget : syntaxBudget =
      (binaryFormulaCode left).length +
        (binaryFormulaCode right).length +
        (binaryFormulaCode conjunction).length := by
    rfl
  have hseq
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (hmem : ∀ candidate ∈ Gamma,
        candidate = left ∨ candidate = right ∨
          candidate = conjunction) :
      (canonicalBinarySequentCode Gamma).length <=
        (binaryNatCode 3).length + 3 * syntaxBudget := by
    rw [canonicalBinarySequentCode_length]
    simpa [hbudget] using
      binarySequentCode_length_le_three_formula_budget
        Gamma left right conjunction hmem
  have hseqRoot := hseq {conjunction} (by simp)
  have hseqLeft := hseq (insert left {conjunction}) (by simp)
  have hseqRight := hseq (insert right {conjunction}) (by simp)
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  have htag7 : (binaryNatCode 7).length <= 16 := by decide
  have hleft : (binaryFormulaCode left).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  have hright : (binaryFormulaCode right).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  simp only [checkedConjunctionTree,
    canonicalBinaryProofCode, List.length_append]
  dsimp only [conjunction] at hseqRoot hseqLeft hseqRight
  change _ <=
    (canonicalBinaryProofCode leftTree).length +
      (canonicalBinaryProofCode rightTree).length + 96 +
      11 * syntaxBudget
  omega

theorem checkedConjunctionCertifiedCode_length_le
    (left right : LO.FirstOrder.ArithmeticProposition)
    (leftTree rightTree : CheckedPAProofTree)
    (leftCertificate rightCertificate :
      StructuralValidityCertificate) :
    (canonicalBinaryCertifiedPAProofCode
      (checkedConjunctionTree left right leftTree rightTree)
      (conjunctionCertificate
        leftCertificate rightCertificate)).length <=
      (canonicalBinaryCertifiedPAProofCode
        leftTree leftCertificate).length +
      (canonicalBinaryCertifiedPAProofCode
        rightTree rightCertificate).length + 144 +
      11 * conjunctionSyntaxBudget left right := by
  have hproof := checkedConjunctionTree_code_length_le
    left right leftTree rightTree
  have hcertificate := conjunctionCertificate_code_length_le
    leftCertificate rightCertificate
  simp only [canonicalBinaryCertifiedPAProofCode,
    List.length_append] at hproof hcertificate ⊢
  omega

theorem acceptedCodes_conjunction_exists
    {left right : LO.FirstOrder.ArithmeticProposition}
    {leftCode rightCode : Nat}
    (hleft :
      listedCompactCertifiedPAProofVerifier leftCode
        (compactFormulaCode left) = true)
    (hright :
      listedCompactCertifiedPAProofVerifier rightCode
        (compactFormulaCode right) = true) :
    exists outputCode : Nat,
      listedCompactCertifiedPAProofVerifier outputCode
          (compactFormulaCode (left ⋏ right)) = true ∧
        packedPayloadLength outputCode <=
          packedPayloadLength leftCode +
            packedPayloadLength rightCode + 144 +
            11 * conjunctionSyntaxBudget left right := by
  rcases
      (listedCompactCertifiedPAProofVerifier_eq_true_iff _ _).mp hleft with
    ⟨leftListedTree, leftCertificate, decodedLeft,
      hleftDecode, hleftCertificate, hleftConclusion, hleftFormulaCode⟩
  have hdecodedLeft : decodedLeft = left :=
    compactFormulaCode_injective hleftFormulaCode
  subst decodedLeft
  rcases
      (listedCompactCertifiedPAProofVerifier_eq_true_iff _ _).mp hright with
    ⟨rightListedTree, rightCertificate, decodedRight,
      hrightDecode, hrightCertificate, hrightConclusion,
      hrightFormulaCode⟩
  have hdecodedRight : decodedRight = right :=
    compactFormulaCode_injective hrightFormulaCode
  subst decodedRight
  let leftTree := leftListedTree.toChecked
  let rightTree := rightListedTree.toChecked
  let outputTree := checkedConjunctionTree left right leftTree rightTree
  let outputCertificate :=
    conjunctionCertificate leftCertificate rightCertificate
  let outputCode :=
    canonicalPackedCertifiedPAProofCode outputTree outputCertificate
  have hleftCheckedCertificate :
      certificateValid leftTree leftCertificate :=
    (listedCertificateValid_toChecked_iff
      leftListedTree leftCertificate).mp hleftCertificate
  have hrightCheckedCertificate :
      certificateValid rightTree rightCertificate :=
    (listedCertificateValid_toChecked_iff
      rightListedTree rightCertificate).mp hrightCertificate
  have hleftCheckedConclusion : leftTree.conclusion = {left} := by
    change leftListedTree.toChecked.conclusion = {left}
    rw [ListedCheckedPAProofTree.toChecked_conclusion]
    exact hleftConclusion
  have hrightCheckedConclusion : rightTree.conclusion = {right} := by
    change rightListedTree.toChecked.conclusion = {right}
    rw [ListedCheckedPAProofTree.toChecked_conclusion]
    exact hrightConclusion
  have houtputCertificate :
      certificateValid outputTree outputCertificate :=
    checkedConjunctionCertificate_valid
      leftTree rightTree leftCertificate rightCertificate
      hleftCheckedConclusion hrightCheckedConclusion
      hleftCheckedCertificate hrightCheckedCertificate
  have hleftCheckedDecode :
      decodeCompactPackedCertifiedPAProof leftCode =
        some (leftTree, leftCertificate) :=
    decodeCompactPackedListedCertifiedPAProof_toChecked hleftDecode
  have hrightCheckedDecode :
      decodeCompactPackedCertifiedPAProof rightCode =
        some (rightTree, rightCertificate) :=
    decodeCompactPackedListedCertifiedPAProof_toChecked hrightDecode
  have hleftInputLength :
      (canonicalBinaryCertifiedPAProofCode
        leftTree leftCertificate).length <= packedPayloadLength leftCode := by
    rw [canonicalBinaryCertifiedPAProofCode_length]
    exact decodeCompactPackedCertifiedPAProof_binaryLength_le
      hleftCheckedDecode
  have hrightInputLength :
      (canonicalBinaryCertifiedPAProofCode
        rightTree rightCertificate).length <= packedPayloadLength rightCode := by
    rw [canonicalBinaryCertifiedPAProofCode_length]
    exact decodeCompactPackedCertifiedPAProof_binaryLength_le
      hrightCheckedDecode
  have houtputLength := checkedConjunctionCertifiedCode_length_le
    left right leftTree rightTree leftCertificate rightCertificate
  refine ⟨outputCode, ?_, ?_⟩
  · apply listedCompactCertifiedPAProofVerifier_eq_true_of_certifiedTree
      outputTree outputCertificate (left ⋏ right)
    · exact houtputCertificate
    · simp [outputTree]
  · calc
      packedPayloadLength outputCode =
          (canonicalBinaryCertifiedPAProofCode
            outputTree outputCertificate).length := by
        simp [outputCode]
      _ <=
          (canonicalBinaryCertifiedPAProofCode
            leftTree leftCertificate).length +
          (canonicalBinaryCertifiedPAProofCode
            rightTree rightCertificate).length + 144 +
          11 * conjunctionSyntaxBudget left right := by
        simpa [outputTree, outputCertificate] using houtputLength
      _ <= packedPayloadLength leftCode +
          packedPayloadLength rightCode + 144 +
          11 * conjunctionSyntaxBudget left right := by
        omega

#print axioms binarySequentCode_length_le_three_formula_budget
#print axioms checkedConjunctionCertificate_valid
#print axioms conjunctionCertificate_code_length_le
#print axioms checkedConjunctionTree_code_length_le
#print axioms checkedConjunctionCertifiedCode_length_le
#print axioms acceptedCodes_conjunction_exists

end FoundationCompactCertifiedConjunction
