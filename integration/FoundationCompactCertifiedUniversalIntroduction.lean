import integration.FoundationCompactPAQuantitativeCompilerCore
import integration.FoundationCompactCertifiedContextualModusPonens
import integration.FoundationCompactListedLocalCostPrimitives
import integration.FoundationCompactSyntaxTransformationCodeBounds
import integration.FoundationCompactCanonicalDecodeLength

/-!
# Explicit certified universal introduction

Given a real certified PA derivation of the eigenvariable-open body, this
module emits the corresponding universally quantified proof.  Both the
weakening node required by `Derivation2.all` and the universal node itself are
present in the proof tree and in the structural certificate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCertifiedUniversalIntroduction

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactCanonicalDecodeLength

def universalIntroductionPremiseContext
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    Finset LO.FirstOrder.ArithmeticProposition :=
  insert (Rewriting.free body)
    (({(∀⁰ body : LO.FirstOrder.ArithmeticProposition)} :
      Finset LO.FirstOrder.ArithmeticProposition).image Rewriting.shift)

def universalIntroductionDerivation
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bodyProof : LO.FirstOrder.Derivation2 PA
      {Rewriting.free body}) :
    LO.FirstOrder.Derivation2 PA
      {(∀⁰ body : LO.FirstOrder.ArithmeticProposition)} :=
  LO.FirstOrder.Derivation2.all (φ := body) (by simp)
    (LO.FirstOrder.Derivation2.wk bodyProof (by
      simp))

def universalIntroductionCertificate
    (bodyCertificate : StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .unary (.unary bodyCertificate)

theorem universalIntroductionCertificate_valid
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bodyProof : LO.FirstOrder.Derivation2 PA
      {Rewriting.free body})
    (bodyCertificate : StructuralValidityCertificate)
    (hvalid : certificateValid
      (CheckedPAProofTree.ofDerivation bodyProof) bodyCertificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (universalIntroductionDerivation body bodyProof))
      (universalIntroductionCertificate bodyCertificate) := by
  have hconclusion :=
    CheckedPAProofTree.conclusion_ofDerivation bodyProof
  simp [universalIntroductionDerivation,
    universalIntroductionCertificate,
    CheckedPAProofTree.ofDerivation,
    CheckedPAProofTree.conclusion, certificateValid, hvalid]
  change (CheckedPAProofTree.ofDerivation bodyProof).conclusion ⊆ _
  rw [hconclusion]
  simp

def universalIntroductionDerivationCost
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Nat :=
  (binaryNatCode 5).length +
    (binarySequentCode
      {(∀⁰ body : LO.FirstOrder.ArithmeticProposition)}).length +
    (binaryFormulaCode body).length +
    (binaryNatCode 7).length +
    (binarySequentCode
      (universalIntroductionPremiseContext body)).length

theorem universalIntroductionDerivation_binaryProofLength_eq
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bodyProof : LO.FirstOrder.Derivation2 PA
      {Rewriting.free body}) :
    binaryProofLength
        (universalIntroductionDerivation body bodyProof) =
      binaryProofLength bodyProof +
        universalIntroductionDerivationCost body := by
  simp only [universalIntroductionDerivation,
    universalIntroductionDerivationCost,
    universalIntroductionPremiseContext, binaryProofLength,
    binaryDerivationCode, List.length_append]
  omega

theorem universalIntroductionCertificate_code_length_le
    (bodyCertificate : StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (universalIntroductionCertificate bodyCertificate)).length <=
      (binaryStructuralValidityCertificateCode bodyCertificate).length +
        32 := by
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  simp only [universalIntroductionCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

def universalIntroduction
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bodyProof : CertifiedPAProof (Rewriting.free body)) :
    CertifiedPAProof (∀⁰ body) where
  derivation := universalIntroductionDerivation body bodyProof.derivation
  certificate := universalIntroductionCertificate bodyProof.certificate
  certificate_valid := universalIntroductionCertificate_valid
    body bodyProof.derivation bodyProof.certificate
      bodyProof.certificate_valid

def universalIntroductionFullAssemblyCost
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Nat :=
  universalIntroductionDerivationCost body + 32

theorem universalIntroduction_payloadLength_le
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bodyProof : CertifiedPAProof (Rewriting.free body)) :
    (universalIntroduction body bodyProof).payloadLength <=
      bodyProof.payloadLength +
        universalIntroductionFullAssemblyCost body := by
  have hproof := universalIntroductionDerivation_binaryProofLength_eq
    body bodyProof.derivation
  have hcertificate :=
    universalIntroductionCertificate_code_length_le
      bodyProof.certificate
  rw [CertifiedPAProof.payloadLength_eq,
    CertifiedPAProof.payloadLength_eq]
  change binaryProofLength
      (universalIntroductionDerivation body bodyProof.derivation) +
      (binaryStructuralValidityCertificateCode
        (universalIntroductionCertificate bodyProof.certificate)).length <= _
  unfold universalIntroductionFullAssemblyCost
  omega

def universalIntroductionFormulaCodeEnvelope (bodyCodeLength : Nat) : Nat :=
  4 * (bodyCodeLength + 8)

def universalIntroductionSequentCodeEnvelope (bodyCodeLength : Nat) : Nat :=
  (binaryNatCode 2).length +
    2 * universalIntroductionFormulaCodeEnvelope bodyCodeLength

theorem universalBinarySequentCode_length_le_uniform
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (cardBound formulaBound : Nat)
    (hcard : Gamma.card <= cardBound)
    (hformula : ∀ formula ∈ Gamma,
      (binaryFormulaCode formula).length <= formulaBound) :
    (binarySequentCode Gamma).length <=
      (binaryNatCode cardBound).length + cardBound * formulaBound := by
  have hheader := binaryNatCode_length_mono hcard
  have hpayload :
      Gamma.sum (fun formula => (binaryFormulaCode formula).length) <=
        Gamma.card * formulaBound := by
    simpa [nsmul_eq_mul] using
      Gamma.sum_le_card_nsmul
        (fun formula => (binaryFormulaCode formula).length)
        formulaBound hformula
  have hpayloadBound :
      Gamma.sum (fun formula => (binaryFormulaCode formula).length) <=
        cardBound * formulaBound :=
    hpayload.trans (Nat.mul_le_mul_right formulaBound hcard)
  have hflat :
      (Gamma.toList.flatMap binaryFormulaCode).length =
        Gamma.sum (fun formula =>
          (binaryFormulaCode formula).length) := by
    rw [List.length_flatMap]
    simp
  simp only [binarySequentCode, List.length_append, hflat]
  omega

theorem universalIntroductionFormulaCodes_le_envelope
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaCode (Rewriting.free body)).length <=
        universalIntroductionFormulaCodeEnvelope
          (binaryFormulaCode body).length ∧
      (binaryFormulaCode
        (∀⁰ body : LO.FirstOrder.ArithmeticProposition)).length <=
        universalIntroductionFormulaCodeEnvelope
          (binaryFormulaCode body).length ∧
      (binaryFormulaCode
        (Rewriting.shift
          (∀⁰ body : LO.FirstOrder.ArithmeticProposition))).length <=
        universalIntroductionFormulaCodeEnvelope
          (binaryFormulaCode body).length := by
  have hfree := binaryFormulaCode_free_length_le body
  have hall := binaryFormulaCode_all_length_le body
  have hshift := binaryFormulaCode_shift_length_le
    (∀⁰ body : LO.FirstOrder.ArithmeticProposition)
  unfold universalIntroductionFormulaCodeEnvelope
  omega

theorem universalIntroductionRootSequentCode_le_envelope
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binarySequentCode
      {(∀⁰ body : LO.FirstOrder.ArithmeticProposition)}).length <=
      universalIntroductionSequentCodeEnvelope
        (binaryFormulaCode body).length := by
  let formulaEnvelope := universalIntroductionFormulaCodeEnvelope
    (binaryFormulaCode body).length
  have hcodes := universalIntroductionFormulaCodes_le_envelope body
  have hformula : ∀ formula ∈
      ({(∀⁰ body : LO.FirstOrder.ArithmeticProposition)} :
        Finset LO.FirstOrder.ArithmeticProposition),
      (binaryFormulaCode formula).length <= formulaEnvelope := by
    intro formula hformula
    simp only [Finset.mem_singleton] at hformula
    subst formula
    exact hcodes.2.1
  have hsequent := universalBinarySequentCode_length_le_uniform
    ({(∀⁰ body : LO.FirstOrder.ArithmeticProposition)} :
      Finset LO.FirstOrder.ArithmeticProposition)
    2 formulaEnvelope (by simp) hformula
  simpa [universalIntroductionSequentCodeEnvelope, formulaEnvelope] using
    hsequent

theorem universalIntroductionPremiseSequentCode_le_envelope
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binarySequentCode
      (universalIntroductionPremiseContext body)).length <=
      universalIntroductionSequentCodeEnvelope
        (binaryFormulaCode body).length := by
  let formulaEnvelope := universalIntroductionFormulaCodeEnvelope
    (binaryFormulaCode body).length
  have hcodes := universalIntroductionFormulaCodes_le_envelope body
  have hformula : ∀ formula ∈
      universalIntroductionPremiseContext body,
      (binaryFormulaCode formula).length <= formulaEnvelope := by
    intro formula hformula
    have hcases : formula = Rewriting.free body ∨
        formula = Rewriting.shift
          (∀⁰ body : LO.FirstOrder.ArithmeticProposition) := by
      simpa [universalIntroductionPremiseContext] using hformula
    rcases hcases with rfl | rfl
    · exact hcodes.1
    · exact hcodes.2.2
  have hsequent := universalBinarySequentCode_length_le_uniform
    (universalIntroductionPremiseContext body)
    2 formulaEnvelope (by
      unfold universalIntroductionPremiseContext
      exact Finset.card_insert_le _ _ |>.trans (by simp)) hformula
  simpa [universalIntroductionSequentCodeEnvelope, formulaEnvelope] using
    hsequent

def universalIntroductionPayloadPolynomial (bodyCodeLength : Nat) : Nat :=
  64 + bodyCodeLength +
    2 * universalIntroductionSequentCodeEnvelope bodyCodeLength

theorem universalIntroductionFullAssemblyCost_le_polynomial
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    universalIntroductionFullAssemblyCost body <=
      universalIntroductionPayloadPolynomial
        (binaryFormulaCode body).length := by
  have hroot := universalIntroductionRootSequentCode_le_envelope body
  have hpremise :=
    universalIntroductionPremiseSequentCode_le_envelope body
  have htag5 : (binaryNatCode 5).length <= 16 := by decide
  have htag7 : (binaryNatCode 7).length <= 16 := by decide
  unfold universalIntroductionFullAssemblyCost
  unfold universalIntroductionDerivationCost
  unfold universalIntroductionPayloadPolynomial
  omega

theorem universalIntroduction_payloadLength_le_polynomial
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bodyProof : CertifiedPAProof (Rewriting.free body)) :
    (universalIntroduction body bodyProof).payloadLength <=
      bodyProof.payloadLength +
        universalIntroductionPayloadPolynomial
          (binaryFormulaCode body).length := by
  exact (universalIntroduction_payloadLength_le body bodyProof).trans
    (Nat.add_le_add_left
      (universalIntroductionFullAssemblyCost_le_polynomial body)
      bodyProof.payloadLength)

theorem universalIntroduction_verifier_eq_true
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bodyProof : CertifiedPAProof (Rewriting.free body)) :
    listedCompactCertifiedPAProofVerifier
      (universalIntroduction body bodyProof).code
      (compactFormulaCode (∀⁰ body)) = true :=
  (universalIntroduction body bodyProof).verifier_eq_true

#print axioms universalIntroductionCertificate_valid
#print axioms universalIntroduction_payloadLength_le
#print axioms universalIntroduction_payloadLength_le_polynomial
#print axioms universalIntroduction_verifier_eq_true

end FoundationCompactCertifiedUniversalIntroduction
