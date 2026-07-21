import integration.FoundationCompactCertifiedContextualModusPonens

/-!
# Certified PA proofs with a shared finite context

This module wraps real `Derivation2 PA (insert formula Gamma)` objects and
their structural certificates.  It supplies the contextual constructors
needed for finite case splits and formula replacement without treating a
local equality assumption as a global theorem.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCertifiedContextProof

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextualModusPonens

structure CertifiedPAContextProof
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition) where
  derivation : LO.FirstOrder.Derivation2 PA (insert formula Gamma)
  certificate : StructuralValidityCertificate
  certificate_valid : certificateValid
    (CheckedPAProofTree.ofDerivation derivation) certificate

namespace CertifiedPAContextProof

def payloadLength
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAContextProof Gamma formula) : Nat :=
  binaryProofLength proof.derivation +
    (binaryStructuralValidityCertificateCode proof.certificate).length

def cast
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {source target : LO.FirstOrder.ArithmeticProposition}
    (formulaEq : source = target)
    (proof : CertifiedPAContextProof Gamma source) :
    CertifiedPAContextProof Gamma target := by
  subst target
  exact proof

@[simp] theorem cast_payloadLength
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {source target : LO.FirstOrder.ArithmeticProposition}
    (formulaEq : source = target)
    (proof : CertifiedPAContextProof Gamma source) :
    (cast formulaEq proof).payloadLength = proof.payloadLength := by
  subst target
  rfl

def weakenCertified
    {formula : LO.FirstOrder.ArithmeticProposition}
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (proof : CertifiedPAProof formula) :
    CertifiedPAContextProof Gamma formula where
  derivation := LO.FirstOrder.Derivation2.wk proof.derivation (by simp)
  certificate := .unary proof.certificate
  certificate_valid := weakeningCertificate_valid
    proof.derivation proof.certificate (by simp) proof.certificate_valid

theorem weakenCertified_payloadLength_le
    {formula : LO.FirstOrder.ArithmeticProposition}
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (proof : CertifiedPAProof formula) :
    (weakenCertified Gamma proof).payloadLength <=
      proof.payloadLength +
        weakeningFullAssemblyCost (insert formula Gamma) := by
  have hbound := weakening_full_payload_le
    proof.derivation proof.certificate
      (show ({formula} : Finset LO.FirstOrder.ArithmeticProposition) ⊆
        insert formula Gamma by simp)
  rw [CertifiedPAProof.payloadLength_eq]
  simpa [payloadLength, weakenCertified] using hbound

def assumption
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (hnegated : ∼formula ∈ Gamma) :
    CertifiedPAContextProof Gamma formula where
  derivation := LO.FirstOrder.Derivation2.closed
    (insert formula Gamma) formula (by simp) (by simp [hnegated])
  certificate := .leaf
  certificate_valid := by
    simp [CheckedPAProofTree.ofDerivation, certificateValid, hnegated]

def assumptionFullPayloadCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition) : Nat :=
  (binaryNatCode 0).length +
    (binarySequentCode (insert formula Gamma)).length +
    (binaryFormulaCode formula).length +
    (binaryNatCode 0).length

theorem assumption_payloadLength_eq
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (hnegated : ∼formula ∈ Gamma) :
    (assumption Gamma formula hnegated).payloadLength =
      assumptionFullPayloadCost Gamma formula := by
  simp [payloadLength, assumption, assumptionFullPayloadCost,
    binaryProofLength, binaryDerivationCode,
    binaryStructuralValidityCertificateCode]
  omega

def modusPonens
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof : CertifiedPAContextProof Gamma
      (antecedent 🡒 consequent))
    (antecedentProof : CertifiedPAContextProof Gamma antecedent) :
    CertifiedPAContextProof Gamma consequent where
  derivation := contextualModusPonensDerivation
    implicationProof.derivation antecedentProof.derivation
  certificate := contextualModusPonensCertificate
    implicationProof.certificate antecedentProof.certificate
  certificate_valid := contextualModusPonensCertificate_valid
    implicationProof.derivation antecedentProof.derivation
    implicationProof.certificate antecedentProof.certificate
    implicationProof.certificate_valid antecedentProof.certificate_valid

theorem modusPonens_payloadLength_le
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof : CertifiedPAContextProof Gamma
      (antecedent 🡒 consequent))
    (antecedentProof : CertifiedPAContextProof Gamma antecedent) :
    (modusPonens implicationProof antecedentProof).payloadLength <=
      implicationProof.payloadLength + antecedentProof.payloadLength +
        contextualModusPonensFullAssemblyCost
          Gamma antecedent consequent := by
  simpa [payloadLength, modusPonens] using
    (contextualModusPonens_full_payload_le
      implicationProof.derivation antecedentProof.derivation
      implicationProof.certificate antecedentProof.certificate)

def equalitySymmetry
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (proof : CertifiedPAContextProof Gamma
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)) :
    CertifiedPAContextProof Gamma
      (“!!right = !!left” : LO.FirstOrder.ArithmeticProposition) :=
  modusPonens
    (weakenCertified Gamma (equalitySymmetryImplication left right)) proof

theorem equalitySymmetry_payloadLength_le
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (proof : CertifiedPAContextProof Gamma
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)) :
    (equalitySymmetry left right proof).payloadLength <=
      (equalitySymmetryImplication left right).payloadLength +
        weakeningFullAssemblyCost
          (insert
            (“!!left = !!right → !!right = !!left” :
              LO.FirstOrder.ArithmeticProposition) Gamma) +
        proof.payloadLength +
        contextualModusPonensFullAssemblyCost Gamma
          (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)
          (“!!right = !!left” : LO.FirstOrder.ArithmeticProposition) := by
  have hweakening := weakenCertified_payloadLength_le Gamma
    (equalitySymmetryImplication left right)
  have hmp := modusPonens_payloadLength_le
    (weakenCertified Gamma (equalitySymmetryImplication left right)) proof
  unfold equalitySymmetry
  omega

def modusTollensDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof : LO.FirstOrder.Derivation2 PA
      (insert (antecedent 🡒 consequent) Gamma))
    (negatedConsequentProof : LO.FirstOrder.Derivation2 PA
      (insert (∼consequent) Gamma)) :
    LO.FirstOrder.Derivation2 PA (insert (∼antecedent) Gamma) :=
  LO.FirstOrder.Derivation2.cut
    (φ := antecedent 🡒 consequent)
    (LO.FirstOrder.Derivation2.wk implicationProof (by simp))
    (LO.FirstOrder.Derivation2.and
      (φ := antecedent) (ψ := ∼consequent)
      (by
        simp only [Finset.mem_insert]
        left
        simp [DeMorgan.imply])
      (LO.FirstOrder.Derivation2.closed _ antecedent (by simp) (by simp))
      (LO.FirstOrder.Derivation2.wk negatedConsequentProof (by
        intro formula hformula
        simp only [Finset.mem_insert] at hformula ⊢
        rcases hformula with hformula | hformula
        · exact Or.inl hformula
        · exact Or.inr (Or.inr (Or.inr hformula)))))

def modusTollensCertificate
    (implicationCertificate negatedConsequentCertificate :
      StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .binary (.unary implicationCertificate)
    (.binary .leaf (.unary negatedConsequentCertificate))

theorem modusTollensCertificate_valid
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof : LO.FirstOrder.Derivation2 PA
      (insert (antecedent 🡒 consequent) Gamma))
    (negatedConsequentProof : LO.FirstOrder.Derivation2 PA
      (insert (∼consequent) Gamma))
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
  have himplicationConclusion :=
    CheckedPAProofTree.conclusion_ofDerivation implicationProof
  have hnegatedConsequentConclusion :=
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
    intro formula hformula
    simp only [Finset.mem_insert] at hformula ⊢
    rcases hformula with hformula | hformula
    · exact Or.inl hformula
    · exact Or.inr (Or.inr (Or.inr hformula))

def modusTollens
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof : CertifiedPAContextProof Gamma
      (antecedent 🡒 consequent))
    (negatedConsequentProof : CertifiedPAContextProof Gamma
      (∼consequent)) :
    CertifiedPAContextProof Gamma (∼antecedent) where
  derivation := modusTollensDerivation
    implicationProof.derivation negatedConsequentProof.derivation
  certificate := modusTollensCertificate
    implicationProof.certificate negatedConsequentProof.certificate
  certificate_valid := modusTollensCertificate_valid
    implicationProof.derivation negatedConsequentProof.derivation
    implicationProof.certificate negatedConsequentProof.certificate
    implicationProof.certificate_valid
    negatedConsequentProof.certificate_valid

def modusTollensDerivationCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) : Nat :=
  let implication := antecedent 🡒 consequent
  let negatedImplication := ∼implication
  let negatedConsequent := ∼consequent
  let negatedAntecedent := ∼antecedent
  (binaryNatCode 9).length +
      (binarySequentCode (insert negatedAntecedent Gamma)).length +
      (binaryFormulaCode implication).length +
    (binaryNatCode 7).length +
      (binarySequentCode
        (insert implication (insert negatedAntecedent Gamma))).length +
    (binaryNatCode 3).length +
      (binarySequentCode
        (insert negatedImplication
          (insert negatedAntecedent Gamma))).length +
      (binaryFormulaCode antecedent).length +
      (binaryFormulaCode negatedConsequent).length +
    (binaryNatCode 0).length +
      (binarySequentCode
        (insert antecedent
          (insert negatedImplication
            (insert negatedAntecedent Gamma)))).length +
      (binaryFormulaCode antecedent).length +
    (binaryNatCode 7).length +
      (binarySequentCode
        (insert negatedConsequent
          (insert negatedImplication
            (insert negatedAntecedent Gamma)))).length

theorem modusTollensDerivation_binaryProofLength_eq
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof : LO.FirstOrder.Derivation2 PA
      (insert (antecedent 🡒 consequent) Gamma))
    (negatedConsequentProof : LO.FirstOrder.Derivation2 PA
      (insert (∼consequent) Gamma)) :
    binaryProofLength
        (modusTollensDerivation implicationProof negatedConsequentProof) =
      binaryProofLength implicationProof +
        binaryProofLength negatedConsequentProof +
        modusTollensDerivationCost Gamma antecedent consequent := by
  simp only [modusTollensDerivation, modusTollensDerivationCost,
    binaryProofLength, binaryDerivationCode, List.length_append]
  omega

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

def modusTollensFullAssemblyCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) : Nat :=
  modusTollensDerivationCost Gamma antecedent consequent + 80

theorem modusTollens_payloadLength_le
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof : CertifiedPAContextProof Gamma
      (antecedent 🡒 consequent))
    (negatedConsequentProof : CertifiedPAContextProof Gamma
      (∼consequent)) :
    (modusTollens implicationProof negatedConsequentProof).payloadLength <=
      implicationProof.payloadLength +
        negatedConsequentProof.payloadLength +
        modusTollensFullAssemblyCost Gamma antecedent consequent := by
  have hproof := modusTollensDerivation_binaryProofLength_eq
    implicationProof.derivation negatedConsequentProof.derivation
  have hcertificate := modusTollensCertificate_code_length_le
    implicationProof.certificate negatedConsequentProof.certificate
  unfold payloadLength modusTollensFullAssemblyCost
  change binaryProofLength
      (modusTollensDerivation implicationProof.derivation
        negatedConsequentProof.derivation) +
    (binaryStructuralValidityCertificateCode
      (modusTollensCertificate implicationProof.certificate
        negatedConsequentProof.certificate)).length <= _
  omega

def conjunctionDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : LO.FirstOrder.Derivation2 PA (insert left Gamma))
    (rightProof : LO.FirstOrder.Derivation2 PA (insert right Gamma)) :
    LO.FirstOrder.Derivation2 PA (insert (left ⋏ right) Gamma) :=
  LO.FirstOrder.Derivation2.and
    (Γ := insert (left ⋏ right) Gamma) (φ := left) (ψ := right)
    (by simp)
    (LO.FirstOrder.Derivation2.wk leftProof (by simp))
    (LO.FirstOrder.Derivation2.wk rightProof (by simp))

def conjunctionCertificate
    (leftCertificate rightCertificate : StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .binary (.unary leftCertificate) (.unary rightCertificate)

theorem conjunctionCertificate_valid
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : LO.FirstOrder.Derivation2 PA (insert left Gamma))
    (rightProof : LO.FirstOrder.Derivation2 PA (insert right Gamma))
    (leftCertificate rightCertificate : StructuralValidityCertificate)
    (hleft : certificateValid
      (CheckedPAProofTree.ofDerivation leftProof) leftCertificate)
    (hright : certificateValid
      (CheckedPAProofTree.ofDerivation rightProof) rightCertificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (conjunctionDerivation leftProof rightProof))
      (conjunctionCertificate leftCertificate rightCertificate) := by
  have hleftConclusion :
      (CheckedPAProofTree.ofDerivation
        (LO.FirstOrder.Derivation2.wk leftProof
          (show insert left Gamma ⊆
            insert left (insert (left ⋏ right) Gamma) by simp))).conclusion =
        insert left (insert (left ⋏ right) Gamma) :=
    CheckedPAProofTree.conclusion_ofDerivation _
  have hrightConclusion :
      (CheckedPAProofTree.ofDerivation
        (LO.FirstOrder.Derivation2.wk rightProof
          (show insert right Gamma ⊆
            insert right (insert (left ⋏ right) Gamma) by simp))).conclusion =
        insert right (insert (left ⋏ right) Gamma) :=
    CheckedPAProofTree.conclusion_ofDerivation _
  simp [conjunctionDerivation, conjunctionCertificate,
    CheckedPAProofTree.ofDerivation, certificateValid,
    hleft, hright]
  exact ⟨hleftConclusion, hrightConclusion⟩

def conjunction
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : CertifiedPAContextProof Gamma left)
    (rightProof : CertifiedPAContextProof Gamma right) :
    CertifiedPAContextProof Gamma (left ⋏ right) where
  derivation := conjunctionDerivation
    leftProof.derivation rightProof.derivation
  certificate := conjunctionCertificate
    leftProof.certificate rightProof.certificate
  certificate_valid := conjunctionCertificate_valid
    leftProof.derivation rightProof.derivation
    leftProof.certificate rightProof.certificate
    leftProof.certificate_valid rightProof.certificate_valid

def conjunctionDerivationCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (left right : LO.FirstOrder.ArithmeticProposition) : Nat :=
  let conjunctionFormula := left ⋏ right
  (binaryNatCode 3).length +
      (binarySequentCode (insert conjunctionFormula Gamma)).length +
      (binaryFormulaCode left).length +
      (binaryFormulaCode right).length +
    (binaryNatCode 7).length +
      (binarySequentCode
        (insert left (insert conjunctionFormula Gamma))).length +
    (binaryNatCode 7).length +
      (binarySequentCode
        (insert right (insert conjunctionFormula Gamma))).length

theorem conjunctionDerivation_binaryProofLength_eq
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : LO.FirstOrder.Derivation2 PA (insert left Gamma))
    (rightProof : LO.FirstOrder.Derivation2 PA (insert right Gamma)) :
    binaryProofLength (conjunctionDerivation leftProof rightProof) =
      binaryProofLength leftProof + binaryProofLength rightProof +
        conjunctionDerivationCost Gamma left right := by
  simp only [conjunctionDerivation, conjunctionDerivationCost,
    binaryProofLength, binaryDerivationCode, List.length_append]
  omega

theorem conjunctionCertificate_code_length_le
    (leftCertificate rightCertificate : StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (conjunctionCertificate leftCertificate rightCertificate)).length <=
      (binaryStructuralValidityCertificateCode leftCertificate).length +
      (binaryStructuralValidityCertificateCode rightCertificate).length +
      48 := by
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  simp only [conjunctionCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

def conjunctionFullAssemblyCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (left right : LO.FirstOrder.ArithmeticProposition) : Nat :=
  conjunctionDerivationCost Gamma left right + 48

theorem conjunction_payloadLength_le
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftProof : CertifiedPAContextProof Gamma left)
    (rightProof : CertifiedPAContextProof Gamma right) :
    (conjunction leftProof rightProof).payloadLength <=
      leftProof.payloadLength + rightProof.payloadLength +
        conjunctionFullAssemblyCost Gamma left right := by
  have hproof := conjunctionDerivation_binaryProofLength_eq
    leftProof.derivation rightProof.derivation
  have hcertificate := conjunctionCertificate_code_length_le
    leftProof.certificate rightProof.certificate
  unfold payloadLength conjunctionFullAssemblyCost
  change binaryProofLength
      (conjunctionDerivation leftProof.derivation rightProof.derivation) +
    (binaryStructuralValidityCertificateCode
      (conjunctionCertificate leftProof.certificate
        rightProof.certificate)).length <= _
  omega

theorem dischargePremise_subset
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) :
    insert consequent
        ({∼antecedent} :
          Finset LO.FirstOrder.ArithmeticProposition) ⊆
      insert (∼antecedent)
        (insert consequent
          ({antecedent 🡒 consequent} :
            Finset LO.FirstOrder.ArithmeticProposition)) := by
  intro formula hformula
  simp only [Finset.mem_insert, Finset.mem_singleton] at hformula ⊢
  rcases hformula with hformula | hformula
  · exact Or.inr (Or.inl hformula)
  · exact Or.inl hformula

def dischargeDerivation
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (proof : LO.FirstOrder.Derivation2 PA
      (insert consequent {∼antecedent})) :
    LO.FirstOrder.Derivation2 PA {antecedent 🡒 consequent} :=
  LO.FirstOrder.Derivation2.or
    (φ := ∼antecedent) (ψ := consequent)
    (by simp [LO.FirstOrder.Semiformula.imp_eq])
    (LO.FirstOrder.Derivation2.wk proof
      (dischargePremise_subset antecedent consequent))

def dischargeCertificate
    (certificate : StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .unary (.unary certificate)

theorem dischargeCertificate_valid
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (proof : LO.FirstOrder.Derivation2 PA
      (insert consequent {∼antecedent}))
    (certificate : StructuralValidityCertificate)
    (hvalid : certificateValid
      (CheckedPAProofTree.ofDerivation proof) certificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (dischargeDerivation antecedent consequent proof))
      (dischargeCertificate certificate) := by
  have hweakeningConclusion :
      (CheckedPAProofTree.ofDerivation
        (LO.FirstOrder.Derivation2.wk proof
          (dischargePremise_subset antecedent consequent))).conclusion =
        insert (∼antecedent)
          (insert consequent {antecedent 🡒 consequent}) :=
    CheckedPAProofTree.conclusion_ofDerivation _
  simp [dischargeDerivation, dischargeCertificate,
    CheckedPAProofTree.ofDerivation, certificateValid,
    LO.FirstOrder.Semiformula.imp_eq, hvalid]
  exact ⟨hweakeningConclusion,
    dischargePremise_subset antecedent consequent⟩

def discharge
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (proof : CertifiedPAContextProof {∼antecedent} consequent) :
    CertifiedPAProof (antecedent 🡒 consequent) where
  derivation := dischargeDerivation antecedent consequent proof.derivation
  certificate := dischargeCertificate proof.certificate
  certificate_valid := dischargeCertificate_valid
    antecedent consequent proof.derivation proof.certificate
      proof.certificate_valid

def dischargeDerivationCost
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) : Nat :=
  let implication := antecedent 🡒 consequent
  (binaryNatCode 4).length +
      (binarySequentCode {implication}).length +
      (binaryFormulaCode (∼antecedent)).length +
      (binaryFormulaCode consequent).length +
    (binaryNatCode 7).length +
      (binarySequentCode
        (insert (∼antecedent) (insert consequent {implication}))).length

theorem dischargeDerivation_binaryProofLength_eq
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (proof : LO.FirstOrder.Derivation2 PA
      (insert consequent {∼antecedent})) :
    binaryProofLength
        (dischargeDerivation antecedent consequent proof) =
      binaryProofLength proof +
        dischargeDerivationCost antecedent consequent := by
  simp only [dischargeDerivation, dischargeDerivationCost,
    binaryProofLength, binaryDerivationCode, List.length_append]
  omega

theorem dischargeCertificate_code_length_le
    (certificate : StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (dischargeCertificate certificate)).length <=
      (binaryStructuralValidityCertificateCode certificate).length + 32 := by
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  simp only [dischargeCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

def dischargeFullAssemblyCost
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) : Nat :=
  dischargeDerivationCost antecedent consequent + 32

theorem discharge_payloadLength_le
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (proof : CertifiedPAContextProof {∼antecedent} consequent) :
    (discharge antecedent consequent proof).payloadLength <=
      proof.payloadLength +
        dischargeFullAssemblyCost antecedent consequent := by
  have hproof := dischargeDerivation_binaryProofLength_eq
    antecedent consequent proof.derivation
  have hcertificate := dischargeCertificate_code_length_le
    proof.certificate
  rw [CertifiedPAProof.payloadLength_eq]
  change binaryProofLength
      (dischargeDerivation antecedent consequent proof.derivation) +
    (binaryStructuralValidityCertificateCode
      (dischargeCertificate proof.certificate)).length <= _
  unfold payloadLength dischargeFullAssemblyCost
  omega

theorem discharge_verifier_eq_true
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (proof : CertifiedPAContextProof {∼antecedent} consequent) :
    listedCompactCertifiedPAProofVerifier
      (discharge antecedent consequent proof).code
      (compactFormulaCode (antecedent 🡒 consequent)) = true :=
  (discharge antecedent consequent proof).verifier_eq_true

#print axioms weakenCertified_payloadLength_le
#print axioms assumption_payloadLength_eq
#print axioms modusPonens_payloadLength_le
#print axioms equalitySymmetry_payloadLength_le
#print axioms modusTollensCertificate_valid
#print axioms modusTollens_payloadLength_le
#print axioms conjunctionCertificate_valid
#print axioms conjunction_payloadLength_le
#print axioms dischargeCertificate_valid
#print axioms discharge_payloadLength_le
#print axioms discharge_verifier_eq_true

end CertifiedPAContextProof

end FoundationCompactCertifiedContextProof
