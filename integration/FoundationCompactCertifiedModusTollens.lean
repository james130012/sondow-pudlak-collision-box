import integration.FoundationCompactPAQuantitativeCompilerCore

/-!
# Explicit certified modus tollens

From checked proofs of `P -> Q` and `not Q`, this module emits a real
five-node `Derivation2 PA` proof of `not P`.  Both the derivation and its
structural certificate are included in the public payload bound.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCertifiedModusTollens

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationComputableCompactPAProofEncoder
open FoundationCompactListedCertifiedVerifier
open FoundationCompactCertifiedModusPonens
open FoundationCompactCanonicalDecodeLength
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof

theorem binarySequentCode_length_le_seven_formula_budget
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (first second third fourth fifth sixth seventh :
      LO.FirstOrder.ArithmeticProposition)
    (hmem : ∀ formula ∈ Gamma,
      formula = first ∨ formula = second ∨ formula = third ∨
        formula = fourth ∨ formula = fifth ∨ formula = sixth ∨
        formula = seventh) :
    (binarySequentCode Gamma).length <=
      (binaryNatCode 7).length +
        7 * ((binaryFormulaCode first).length +
          (binaryFormulaCode second).length +
          (binaryFormulaCode third).length +
          (binaryFormulaCode fourth).length +
          (binaryFormulaCode fifth).length +
          (binaryFormulaCode sixth).length +
          (binaryFormulaCode seventh).length) := by
  let formulaBudget :=
    (binaryFormulaCode first).length +
      (binaryFormulaCode second).length +
      (binaryFormulaCode third).length +
      (binaryFormulaCode fourth).length +
      (binaryFormulaCode fifth).length +
      (binaryFormulaCode sixth).length +
      (binaryFormulaCode seventh).length
  have hsubset : Gamma ⊆
      {first, second, third, fourth, fifth, sixth, seventh} := by
    intro formula hformula
    rcases hmem formula hformula with h | h | h | h | h | h | h <;>
      simp [h]
  have hcardSet :
      ({first, second, third, fourth, fifth, sixth, seventh} :
        Finset LO.FirstOrder.ArithmeticProposition).card <= 7 := by
    have hfirst := Finset.card_insert_le first
      {second, third, fourth, fifth, sixth, seventh}
    have hsecond := Finset.card_insert_le second
      {third, fourth, fifth, sixth, seventh}
    have hthird := Finset.card_insert_le third
      {fourth, fifth, sixth, seventh}
    have hfourth := Finset.card_insert_le fourth {fifth, sixth, seventh}
    have hfifth := Finset.card_insert_le fifth {sixth, seventh}
    have hsixth := Finset.card_insert_le sixth {seventh}
    simp only [Finset.card_singleton] at hsixth
    omega
  have hcard : Gamma.card <= 7 :=
    (Finset.card_le_card hsubset).trans hcardSet
  have hheader := binaryNatCode_length_mono hcard
  have hformula
      (formula : LO.FirstOrder.ArithmeticProposition)
      (hformulaMem : formula ∈ Gamma) :
      (binaryFormulaCode formula).length <= formulaBudget := by
    rcases hmem formula hformulaMem with h | h | h | h | h | h | h <;>
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
        7 * formulaBudget :=
    hpayload.trans (Nat.mul_le_mul_right formulaBudget hcard)
  have hflat :
      (Gamma.toList.flatMap binaryFormulaCode).length =
        Gamma.sum (fun formula => (binaryFormulaCode formula).length) := by
    rw [List.length_flatMap]
    simp
  simp only [binarySequentCode, List.length_append, hflat]
  exact Nat.add_le_add hheader hpayloadBound

def modusTollensSyntaxBudget
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) : Nat :=
  (binaryFormulaCode antecedent).length +
    (binaryFormulaCode consequent).length +
    (binaryFormulaCode (antecedent 🡒 consequent)).length +
    (binaryFormulaCode (∼(antecedent 🡒 consequent))).length +
    (binaryFormulaCode (antecedent ⋏ (∼consequent))).length +
    (binaryFormulaCode (∼consequent)).length +
    (binaryFormulaCode (∼antecedent)).length

def modusTollensDerivation
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof :
      LO.FirstOrder.Derivation2 PA {antecedent 🡒 consequent})
    (negatedConsequentProof :
      LO.FirstOrder.Derivation2 PA {∼consequent}) :
    LO.FirstOrder.Derivation2 PA {∼antecedent} :=
  LO.FirstOrder.Derivation2.cut
    (φ := antecedent 🡒 consequent)
    (LO.FirstOrder.Derivation2.wk implicationProof (by simp))
    (LO.FirstOrder.Derivation2.and
      (φ := antecedent) (ψ := ∼consequent)
      (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        left
        simp [DeMorgan.imply])
      (LO.FirstOrder.Derivation2.closed _ antecedent (by simp) (by simp))
      (LO.FirstOrder.Derivation2.wk negatedConsequentProof (by simp)))

theorem modusTollensDerivation_binaryProofLength_le
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof :
      LO.FirstOrder.Derivation2 PA {antecedent 🡒 consequent})
    (negatedConsequentProof :
      LO.FirstOrder.Derivation2 PA {∼consequent}) :
    binaryProofLength
        (modusTollensDerivation implicationProof negatedConsequentProof) <=
      binaryProofLength implicationProof +
        binaryProofLength negatedConsequentProof + 192 +
        48 * modusTollensSyntaxBudget antecedent consequent := by
  let implication := antecedent 🡒 consequent
  let negatedImplication := ∼implication
  let conjunction := antecedent ⋏ (∼consequent)
  let negatedConsequent := ∼consequent
  let negatedAntecedent := ∼antecedent
  let syntaxBudget := modusTollensSyntaxBudget antecedent consequent
  have hbudget : syntaxBudget =
      (binaryFormulaCode antecedent).length +
        (binaryFormulaCode consequent).length +
        (binaryFormulaCode implication).length +
        (binaryFormulaCode negatedImplication).length +
        (binaryFormulaCode conjunction).length +
        (binaryFormulaCode negatedConsequent).length +
        (binaryFormulaCode negatedAntecedent).length := by
    rfl
  have hseq
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (hmem : ∀ candidate ∈ Gamma,
        candidate = antecedent ∨ candidate = consequent ∨
          candidate = implication ∨ candidate = negatedImplication ∨
          candidate = conjunction ∨ candidate = negatedConsequent ∨
          candidate = negatedAntecedent) :
      (binarySequentCode Gamma).length <=
        (binaryNatCode 7).length + 7 * syntaxBudget := by
    simpa [hbudget] using
      binarySequentCode_length_le_seven_formula_budget Gamma
        antecedent consequent implication negatedImplication
        conjunction negatedConsequent negatedAntecedent hmem
  have hseqFinal := hseq {negatedAntecedent} (by simp)
  have hseqImplication :=
    hseq (insert implication {negatedAntecedent}) (by simp)
  have hseqNegatedImplication :=
    hseq (insert negatedImplication {negatedAntecedent}) (by simp)
  have hseqAntecedent := hseq
    (insert antecedent (insert negatedImplication {negatedAntecedent}))
    (by simp)
  have hseqNegatedConsequent := hseq
    (insert negatedConsequent
      (insert negatedImplication {negatedAntecedent})) (by simp)
  have htag0 : (binaryNatCode 0).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  have htag7 : (binaryNatCode 7).length <= 16 := by decide
  have htag9 : (binaryNatCode 9).length <= 16 := by decide
  have hantecedent :
      (binaryFormulaCode antecedent).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  have himplication :
      (binaryFormulaCode implication).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  have hnegatedConsequent :
      (binaryFormulaCode negatedConsequent).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  simp only [modusTollensDerivation, binaryProofLength,
    binaryDerivationCode, List.length_append]
  dsimp only [implication, negatedImplication, conjunction,
    negatedConsequent, negatedAntecedent] at hseqFinal hseqImplication hseqNegatedImplication hseqAntecedent hseqNegatedConsequent himplication hantecedent hnegatedConsequent
  change _ <= (binaryDerivationCode implicationProof).length +
    (binaryDerivationCode negatedConsequentProof).length +
      192 + 48 * syntaxBudget
  omega

def modusTollensCertificate
    (implicationCertificate negatedConsequentCertificate :
      StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .binary (.unary implicationCertificate)
    (.binary .leaf (.unary negatedConsequentCertificate))

theorem modusTollensCertificate_valid
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof :
      LO.FirstOrder.Derivation2 PA {antecedent 🡒 consequent})
    (negatedConsequentProof :
      LO.FirstOrder.Derivation2 PA {∼consequent})
    (implicationCertificate negatedConsequentCertificate :
      StructuralValidityCertificate)
    (himplication : certificateValid
      (CheckedPAProofTree.ofDerivation implicationProof)
      implicationCertificate)
    (hnegatedConsequent : certificateValid
      (CheckedPAProofTree.ofDerivation negatedConsequentProof)
      negatedConsequentCertificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (modusTollensDerivation implicationProof negatedConsequentProof))
      (modusTollensCertificate
        implicationCertificate negatedConsequentCertificate) := by
  have himplicationConclusion :
      (CheckedPAProofTree.ofDerivation implicationProof).conclusion =
        {antecedent 🡒 consequent} :=
    CheckedPAProofTree.conclusion_ofDerivation implicationProof
  have hnegatedConsequentConclusion :
      (CheckedPAProofTree.ofDerivation negatedConsequentProof).conclusion =
        {∼consequent} :=
    CheckedPAProofTree.conclusion_ofDerivation negatedConsequentProof
  simp [modusTollensDerivation, modusTollensCertificate,
    CheckedPAProofTree.ofDerivation, CheckedPAProofTree.conclusion,
    certificateValid, himplication, hnegatedConsequent, DeMorgan.imply]
  constructor
  · change
      (CheckedPAProofTree.ofDerivation implicationProof).conclusion ⊆ _
    rw [himplicationConclusion]
    simp [LO.FirstOrder.Semiformula.imp_eq]
  · change
      (CheckedPAProofTree.ofDerivation negatedConsequentProof).conclusion ⊆ _
    rw [hnegatedConsequentConclusion]
    simp

theorem modusTollensCertificate_code_length_le
    (implicationCertificate negatedConsequentCertificate :
      StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (modusTollensCertificate implicationCertificate
        negatedConsequentCertificate)).length <=
      (binaryStructuralValidityCertificateCode
        implicationCertificate).length +
      (binaryStructuralValidityCertificateCode
        negatedConsequentCertificate).length + 80 := by
  have htag0 : (binaryNatCode 0).length <= 16 := by decide
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  simp only [modusTollensCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

def modusTollens
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof : CertifiedPAProof (antecedent 🡒 consequent))
    (negatedConsequentProof : CertifiedPAProof (∼consequent)) :
    CertifiedPAProof (∼antecedent) where
  derivation := modusTollensDerivation implicationProof.derivation
    negatedConsequentProof.derivation
  certificate := modusTollensCertificate implicationProof.certificate
    negatedConsequentProof.certificate
  certificate_valid := modusTollensCertificate_valid
    implicationProof.derivation negatedConsequentProof.derivation
    implicationProof.certificate negatedConsequentProof.certificate
    implicationProof.certificate_valid
    negatedConsequentProof.certificate_valid

theorem modusTollens_payloadLength_le
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof : CertifiedPAProof (antecedent 🡒 consequent))
    (negatedConsequentProof : CertifiedPAProof (∼consequent)) :
    (modusTollens implicationProof negatedConsequentProof).payloadLength <=
      implicationProof.payloadLength +
        negatedConsequentProof.payloadLength + 272 +
        48 * modusTollensSyntaxBudget antecedent consequent := by
  have hproof := modusTollensDerivation_binaryProofLength_le
    implicationProof.derivation negatedConsequentProof.derivation
  have hcertificate := modusTollensCertificate_code_length_le
    implicationProof.certificate negatedConsequentProof.certificate
  rw [CertifiedPAProof.payloadLength_eq,
    CertifiedPAProof.payloadLength_eq,
    CertifiedPAProof.payloadLength_eq]
  change
    binaryProofLength
        (modusTollensDerivation implicationProof.derivation
          negatedConsequentProof.derivation) +
      (binaryStructuralValidityCertificateCode
        (modusTollensCertificate implicationProof.certificate
          negatedConsequentProof.certificate)).length <= _
  omega

theorem modusTollens_verifier_eq_true
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof : CertifiedPAProof (antecedent 🡒 consequent))
    (negatedConsequentProof : CertifiedPAProof (∼consequent)) :
    listedCompactCertifiedPAProofVerifier
      (modusTollens implicationProof negatedConsequentProof).code
      (compactFormulaCode (∼antecedent)) = true :=
  (modusTollens implicationProof negatedConsequentProof).verifier_eq_true

#print axioms modusTollensDerivation_binaryProofLength_le
#print axioms modusTollensCertificate_valid
#print axioms modusTollens_payloadLength_le
#print axioms modusTollens_verifier_eq_true

end FoundationCompactCertifiedModusTollens
