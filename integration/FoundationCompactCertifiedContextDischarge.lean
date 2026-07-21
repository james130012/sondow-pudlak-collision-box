import integration.FoundationCompactCertifiedContextProof

/-!
# Certified implication discharge over a retained finite context

Nested bounded-universal compilation proves a body under both the finite
bound assumption and the shifted outer valuation context.  This constructor
discharges only the selected bound assumption and keeps every outer context
formula.  The emitted object is a real `Derivation2 PA` with a matching
structural certificate and an explicit local full-payload charge.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCertifiedContextDischarge

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

def contextualImplicationFormula
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) :
    LO.FirstOrder.ArithmeticProposition :=
  LO.Arrow.arrow antecedent consequent

theorem contextualDischargePremise_subset
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) :
    insert consequent (insert (∼antecedent) Gamma) ⊆
      insert (∼antecedent)
        (insert consequent
          (insert (contextualImplicationFormula antecedent consequent)
            Gamma)) := by
  intro formula hformula
  simp only [Finset.mem_insert] at hformula ⊢
  rcases hformula with hformula | hformula
  · exact Or.inr (Or.inl hformula)
  · rcases hformula with hformula | hformula
    · exact Or.inl hformula
    · exact Or.inr (Or.inr (Or.inr hformula))

def contextualDischargeDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (proof : LO.FirstOrder.Derivation2 PA
      (insert consequent (insert (∼antecedent) Gamma))) :
    LO.FirstOrder.Derivation2 PA
      (insert (contextualImplicationFormula antecedent consequent) Gamma) :=
  LO.FirstOrder.Derivation2.or
    (φ := ∼antecedent) (ψ := consequent)
    (by simp [contextualImplicationFormula,
      LO.FirstOrder.Semiformula.imp_eq])
    (LO.FirstOrder.Derivation2.wk proof
      (contextualDischargePremise_subset Gamma antecedent consequent))

def contextualDischargeCertificate
    (certificate : StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .unary (.unary certificate)

theorem contextualDischargeCertificate_valid
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (proof : LO.FirstOrder.Derivation2 PA
      (insert consequent (insert (∼antecedent) Gamma)))
    (certificate : StructuralValidityCertificate)
    (hvalid : certificateValid
      (CheckedPAProofTree.ofDerivation proof) certificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (contextualDischargeDerivation antecedent consequent proof))
      (contextualDischargeCertificate certificate) := by
  have hweakeningConclusion :
      (CheckedPAProofTree.ofDerivation
        (LO.FirstOrder.Derivation2.wk proof
          (contextualDischargePremise_subset
            Gamma antecedent consequent))).conclusion =
        insert (∼antecedent)
          (insert consequent
            (insert (contextualImplicationFormula antecedent consequent)
              Gamma)) :=
    CheckedPAProofTree.conclusion_ofDerivation _
  simp [contextualDischargeDerivation, contextualDischargeCertificate,
    CheckedPAProofTree.ofDerivation, certificateValid,
    contextualImplicationFormula, LO.FirstOrder.Semiformula.imp_eq, hvalid]
  exact ⟨hweakeningConclusion,
    contextualDischargePremise_subset Gamma antecedent consequent⟩

def contextualDischarge
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (proof : CertifiedPAContextProof
      (insert (∼antecedent) Gamma) consequent) :
    CertifiedPAContextProof Gamma
      (contextualImplicationFormula antecedent consequent) where
  derivation := contextualDischargeDerivation
    antecedent consequent proof.derivation
  certificate := contextualDischargeCertificate proof.certificate
  certificate_valid := contextualDischargeCertificate_valid
    antecedent consequent proof.derivation proof.certificate
      proof.certificate_valid

def contextualDischargePremiseContext
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) :
    Finset LO.FirstOrder.ArithmeticProposition :=
  insert (∼antecedent)
    (insert consequent
      (insert (contextualImplicationFormula antecedent consequent) Gamma))

def contextualDischargeDerivationCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) : Nat :=
  (binaryNatCode 4).length +
    (binarySequentCode
      (insert (contextualImplicationFormula antecedent consequent)
        Gamma)).length +
    (binaryFormulaCode (∼antecedent)).length +
    (binaryFormulaCode consequent).length +
  (binaryNatCode 7).length +
    (binarySequentCode
      (contextualDischargePremiseContext
        Gamma antecedent consequent)).length

theorem contextualDischargeDerivation_binaryProofLength_eq
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (proof : LO.FirstOrder.Derivation2 PA
      (insert consequent (insert (∼antecedent) Gamma))) :
    binaryProofLength
        (contextualDischargeDerivation antecedent consequent proof) =
      binaryProofLength proof +
        contextualDischargeDerivationCost
          Gamma antecedent consequent := by
  simp only [contextualDischargeDerivation,
    contextualDischargeDerivationCost,
    contextualDischargePremiseContext,
    contextualImplicationFormula,
    binaryProofLength, binaryDerivationCode, List.length_append]
  omega

theorem contextualDischargeCertificate_code_length_le
    (certificate : StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (contextualDischargeCertificate certificate)).length <=
      (binaryStructuralValidityCertificateCode certificate).length + 32 := by
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  simp only [contextualDischargeCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

def contextualDischargeFullAssemblyCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) : Nat :=
  contextualDischargeDerivationCost Gamma antecedent consequent + 32

theorem contextualDischarge_payloadLength_le
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (proof : CertifiedPAContextProof
      (insert (∼antecedent) Gamma) consequent) :
    (contextualDischarge antecedent consequent proof).payloadLength <=
      proof.payloadLength +
        contextualDischargeFullAssemblyCost
          Gamma antecedent consequent := by
  have hproof := contextualDischargeDerivation_binaryProofLength_eq
    antecedent consequent proof.derivation
  have hcertificate := contextualDischargeCertificate_code_length_le
    proof.certificate
  unfold CertifiedPAContextProof.payloadLength
  change binaryProofLength
      (contextualDischargeDerivation
        antecedent consequent proof.derivation) +
    (binaryStructuralValidityCertificateCode
      (contextualDischargeCertificate proof.certificate)).length <= _
  unfold contextualDischargeFullAssemblyCost
  omega

theorem contextualDischarge_certificate_valid
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (proof : CertifiedPAContextProof
      (insert (∼antecedent) Gamma) consequent) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (contextualDischarge antecedent consequent proof).derivation)
      (contextualDischarge antecedent consequent proof).certificate :=
  (contextualDischarge antecedent consequent proof).certificate_valid

#print axioms contextualDischargeCertificate_valid
#print axioms contextualDischarge_payloadLength_le
#print axioms contextualDischarge_certificate_valid

end FoundationCompactCertifiedContextDischarge
