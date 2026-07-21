import integration.FoundationCompactCertifiedContextProof

/-!
# Certified universal introduction over a shifted finite context

The ordinary certified universal-introduction constructor starts from a
closed proof of the free body.  Nested bounded quantifiers need the stronger
contextual form: the outer valuation equalities remain available after the
new eigenvariable is introduced, with every formula shifted exactly once.

This module constructs the real `Derivation2 PA` tree, its matching structural
certificate, and an exact local full-payload charge.  It assumes no proof
existence and stores no proof-length premise.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCertifiedContextUniversalIntroduction

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedCertifiedVerifier
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

def contextualUniversalIntroductionPremiseContext
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    Finset LO.FirstOrder.ArithmeticProposition :=
  insert (Rewriting.free body)
    ((insert (∀⁰ body : LO.FirstOrder.ArithmeticProposition) Gamma).image
      Rewriting.shift)

def contextualUniversalIntroductionDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bodyProof : LO.FirstOrder.Derivation2 PA
      (insert (Rewriting.free body) (Gamma.image Rewriting.shift))) :
    LO.FirstOrder.Derivation2 PA
      (insert (∀⁰ body : LO.FirstOrder.ArithmeticProposition) Gamma) :=
  LO.FirstOrder.Derivation2.all (φ := body) (by simp)
    (LO.FirstOrder.Derivation2.wk bodyProof (by
      intro formula hformula
      simp only [Finset.mem_insert, Finset.mem_image] at hformula ⊢
      rcases hformula with hformula | hformula
      · exact Or.inl hformula
      · rcases hformula with ⟨source, hsource, rfl⟩
        right
        exact ⟨source, by simp [hsource], rfl⟩))

def contextualUniversalIntroductionCertificate
    (bodyCertificate : StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .unary (.unary bodyCertificate)

theorem contextualUniversalIntroductionCertificate_valid
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bodyProof : LO.FirstOrder.Derivation2 PA
      (insert (Rewriting.free body) (Gamma.image Rewriting.shift)))
    (bodyCertificate : StructuralValidityCertificate)
    (hvalid : certificateValid
      (CheckedPAProofTree.ofDerivation bodyProof) bodyCertificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (contextualUniversalIntroductionDerivation body bodyProof))
      (contextualUniversalIntroductionCertificate bodyCertificate) := by
  have hconclusion := CheckedPAProofTree.conclusion_ofDerivation bodyProof
  simp [contextualUniversalIntroductionDerivation,
    contextualUniversalIntroductionCertificate,
    CheckedPAProofTree.ofDerivation,
    CheckedPAProofTree.conclusion, certificateValid, hvalid]
  change (CheckedPAProofTree.ofDerivation bodyProof).conclusion ⊆ _
  rw [hconclusion]
  intro formula hformula
  simp only [Finset.mem_insert, Finset.mem_image] at hformula ⊢
  rcases hformula with hformula | hformula
  · exact Or.inl hformula
  · rcases hformula with ⟨source, hsource, rfl⟩
    right
    exact Or.inr ⟨source, hsource, rfl⟩

def contextualUniversalIntroduction
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bodyProof : CertifiedPAContextProof
      (Gamma.image Rewriting.shift) (Rewriting.free body)) :
    CertifiedPAContextProof Gamma
      (∀⁰ body : LO.FirstOrder.ArithmeticProposition) where
  derivation := contextualUniversalIntroductionDerivation
    body bodyProof.derivation
  certificate := contextualUniversalIntroductionCertificate
    bodyProof.certificate
  certificate_valid := contextualUniversalIntroductionCertificate_valid
    body bodyProof.derivation bodyProof.certificate
      bodyProof.certificate_valid

def contextualUniversalIntroductionDerivationCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Nat :=
  (binaryNatCode 5).length +
    (binarySequentCode
      (insert (∀⁰ body : LO.FirstOrder.ArithmeticProposition)
        Gamma)).length +
    (binaryFormulaCode body).length +
  (binaryNatCode 7).length +
    (binarySequentCode
      (contextualUniversalIntroductionPremiseContext Gamma body)).length

theorem contextualUniversalIntroductionDerivation_binaryProofLength_eq
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bodyProof : LO.FirstOrder.Derivation2 PA
      (insert (Rewriting.free body) (Gamma.image Rewriting.shift))) :
    binaryProofLength
        (contextualUniversalIntroductionDerivation body bodyProof) =
      binaryProofLength bodyProof +
        contextualUniversalIntroductionDerivationCost Gamma body := by
  simp only [contextualUniversalIntroductionDerivation,
    contextualUniversalIntroductionDerivationCost,
    contextualUniversalIntroductionPremiseContext,
    binaryProofLength, binaryDerivationCode, List.length_append]
  omega

theorem contextualUniversalIntroductionCertificate_code_length_le
    (bodyCertificate : StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (contextualUniversalIntroductionCertificate bodyCertificate)).length <=
      (binaryStructuralValidityCertificateCode bodyCertificate).length +
        32 := by
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  simp only [contextualUniversalIntroductionCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

def contextualUniversalIntroductionFullAssemblyCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Nat :=
  contextualUniversalIntroductionDerivationCost Gamma body + 32

theorem contextualUniversalIntroduction_payloadLength_le
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bodyProof : CertifiedPAContextProof
      (Gamma.image Rewriting.shift) (Rewriting.free body)) :
    (contextualUniversalIntroduction body bodyProof).payloadLength <=
      bodyProof.payloadLength +
        contextualUniversalIntroductionFullAssemblyCost Gamma body := by
  have hproof :=
    contextualUniversalIntroductionDerivation_binaryProofLength_eq
      body bodyProof.derivation
  have hcertificate :=
    contextualUniversalIntroductionCertificate_code_length_le
      bodyProof.certificate
  unfold CertifiedPAContextProof.payloadLength
  change binaryProofLength
      (contextualUniversalIntroductionDerivation body bodyProof.derivation) +
    (binaryStructuralValidityCertificateCode
      (contextualUniversalIntroductionCertificate
        bodyProof.certificate)).length <= _
  unfold contextualUniversalIntroductionFullAssemblyCost
  omega

theorem contextualUniversalIntroduction_certificate_valid
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bodyProof : CertifiedPAContextProof
      (Gamma.image Rewriting.shift) (Rewriting.free body)) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (contextualUniversalIntroduction body bodyProof).derivation)
      (contextualUniversalIntroduction body bodyProof).certificate :=
  (contextualUniversalIntroduction body bodyProof).certificate_valid

#print axioms contextualUniversalIntroductionCertificate_valid
#print axioms contextualUniversalIntroduction_payloadLength_le
#print axioms contextualUniversalIntroduction_certificate_valid

end FoundationCompactCertifiedContextUniversalIntroduction
