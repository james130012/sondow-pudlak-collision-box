import integration.FoundationCompactPAQuantitativeCompilerCore

/-!
# Certified modus ponens under a shared finite context

The emitted tree is the same explicit five-node cut used by ordinary modus
ponens, but both premises may retain a common sequent context `Gamma`.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCertifiedContextualModusPonens

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationComputableCompactPAProofEncoder
open FoundationCompactPAQuantitativeCompilerCore

theorem weakeningCertificate_valid
    {Delta Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (proof : LO.FirstOrder.Derivation2 PA Delta)
    (certificate : StructuralValidityCertificate)
    (hsubset : Delta ⊆ Gamma)
    (hvalid : certificateValid
      (CheckedPAProofTree.ofDerivation proof) certificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (LO.FirstOrder.Derivation2.wk proof hsubset))
      (.unary certificate) := by
  simp only [CheckedPAProofTree.ofDerivation, certificateValid]
  constructor
  · change (CheckedPAProofTree.ofDerivation proof).conclusion ⊆ Gamma
    rw [CheckedPAProofTree.conclusion_ofDerivation proof]
    exact hsubset
  · exact hvalid

def weakeningFullAssemblyCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition) : Nat :=
  (binaryNatCode 7).length + (binarySequentCode Gamma).length + 16

theorem weakening_full_payload_le
    {Delta Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (proof : LO.FirstOrder.Derivation2 PA Delta)
    (certificate : StructuralValidityCertificate)
    (hsubset : Delta ⊆ Gamma) :
    binaryProofLength (LO.FirstOrder.Derivation2.wk proof hsubset) +
        (binaryStructuralValidityCertificateCode
          (.unary certificate)).length <=
      binaryProofLength proof +
        (binaryStructuralValidityCertificateCode certificate).length +
        weakeningFullAssemblyCost Gamma := by
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  simp only [binaryProofLength, binaryDerivationCode,
    binaryStructuralValidityCertificateCode, List.length_append]
  unfold weakeningFullAssemblyCost
  omega

def contextualModusPonensDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof : LO.FirstOrder.Derivation2 PA
      (insert (antecedent 🡒 consequent) Gamma))
    (antecedentProof : LO.FirstOrder.Derivation2 PA
      (insert antecedent Gamma)) :
    LO.FirstOrder.Derivation2 PA (insert consequent Gamma) :=
  LO.FirstOrder.Derivation2.cut
    (φ := antecedent 🡒 consequent)
    (LO.FirstOrder.Derivation2.wk implicationProof (by simp))
    (LO.FirstOrder.Derivation2.and
      (φ := antecedent) (ψ := ∼consequent)
      (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        left
        simp [DeMorgan.imply])
      (LO.FirstOrder.Derivation2.wk antecedentProof (by
        intro formula hformula
        simp only [Finset.mem_insert] at hformula ⊢
        rcases hformula with hformula | hformula
        · exact Or.inl hformula
        · exact Or.inr (Or.inr (Or.inr hformula))))
      (LO.FirstOrder.Derivation2.closed _ consequent (by simp) (by simp)))

def contextualModusPonensCertificate
    (implicationCertificate antecedentCertificate :
      StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .binary (.unary implicationCertificate)
    (.binary (.unary antecedentCertificate) .leaf)

theorem contextualModusPonensCertificate_valid
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof : LO.FirstOrder.Derivation2 PA
      (insert (antecedent 🡒 consequent) Gamma))
    (antecedentProof : LO.FirstOrder.Derivation2 PA
      (insert antecedent Gamma))
    (implicationCertificate antecedentCertificate :
      StructuralValidityCertificate)
    (himplication : certificateValid
      (CheckedPAProofTree.ofDerivation implicationProof)
      implicationCertificate)
    (hantecedent : certificateValid
      (CheckedPAProofTree.ofDerivation antecedentProof)
      antecedentCertificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (contextualModusPonensDerivation implicationProof antecedentProof))
      (contextualModusPonensCertificate
        implicationCertificate antecedentCertificate) := by
  have himplicationConclusion :=
    CheckedPAProofTree.conclusion_ofDerivation implicationProof
  have hantecedentConclusion :=
    CheckedPAProofTree.conclusion_ofDerivation antecedentProof
  simp [contextualModusPonensDerivation,
    contextualModusPonensCertificate, CheckedPAProofTree.ofDerivation,
    CheckedPAProofTree.conclusion, certificateValid, himplication,
    hantecedent, DeMorgan.imply]
  constructor
  · change
      (CheckedPAProofTree.ofDerivation implicationProof).conclusion ⊆ _
    rw [himplicationConclusion]
    simp [LO.FirstOrder.Semiformula.imp_eq]
  · change
      (CheckedPAProofTree.ofDerivation antecedentProof).conclusion ⊆ _
    rw [hantecedentConclusion]
    intro formula hformula
    simp only [Finset.mem_insert] at hformula ⊢
    rcases hformula with hformula | hformula
    · exact Or.inl hformula
    · exact Or.inr (Or.inr (Or.inr hformula))

def contextualModusPonensDerivationCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) : Nat :=
  let implication := antecedent 🡒 consequent
  let negatedImplication := ∼implication
  let negatedConsequent := ∼consequent
  (binaryNatCode 9).length +
      (binarySequentCode (insert consequent Gamma)).length +
      (binaryFormulaCode implication).length +
    (binaryNatCode 7).length +
      (binarySequentCode
        (insert implication (insert consequent Gamma))).length +
    (binaryNatCode 3).length +
      (binarySequentCode
        (insert negatedImplication (insert consequent Gamma))).length +
      (binaryFormulaCode antecedent).length +
      (binaryFormulaCode negatedConsequent).length +
    (binaryNatCode 7).length +
      (binarySequentCode
        (insert antecedent
          (insert negatedImplication (insert consequent Gamma)))).length +
    (binaryNatCode 0).length +
      (binarySequentCode
        (insert negatedConsequent
          (insert negatedImplication (insert consequent Gamma)))).length +
      (binaryFormulaCode consequent).length

theorem contextualModusPonensDerivation_binaryProofLength_eq
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof : LO.FirstOrder.Derivation2 PA
      (insert (antecedent 🡒 consequent) Gamma))
    (antecedentProof : LO.FirstOrder.Derivation2 PA
      (insert antecedent Gamma)) :
    binaryProofLength
        (contextualModusPonensDerivation implicationProof antecedentProof) =
      binaryProofLength implicationProof +
        binaryProofLength antecedentProof +
        contextualModusPonensDerivationCost Gamma antecedent consequent := by
  simp only [contextualModusPonensDerivation,
    contextualModusPonensDerivationCost, binaryProofLength,
    binaryDerivationCode, List.length_append]
  omega

theorem contextualModusPonensCertificate_code_length_le
    (implicationCertificate antecedentCertificate :
      StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (contextualModusPonensCertificate implicationCertificate
        antecedentCertificate)).length <=
      (binaryStructuralValidityCertificateCode
        implicationCertificate).length +
      (binaryStructuralValidityCertificateCode
        antecedentCertificate).length + 80 := by
  have htag0 : (binaryNatCode 0).length <= 16 := by decide
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  simp only [contextualModusPonensCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

def contextualModusPonensFullAssemblyCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) : Nat :=
  contextualModusPonensDerivationCost Gamma antecedent consequent + 80

theorem contextualModusPonens_full_payload_le
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {antecedent consequent : LO.FirstOrder.ArithmeticProposition}
    (implicationProof : LO.FirstOrder.Derivation2 PA
      (insert (antecedent 🡒 consequent) Gamma))
    (antecedentProof : LO.FirstOrder.Derivation2 PA
      (insert antecedent Gamma))
    (implicationCertificate antecedentCertificate :
      StructuralValidityCertificate) :
    binaryProofLength
        (contextualModusPonensDerivation implicationProof antecedentProof) +
        (binaryStructuralValidityCertificateCode
          (contextualModusPonensCertificate
            implicationCertificate antecedentCertificate)).length <=
      (binaryProofLength implicationProof +
          (binaryStructuralValidityCertificateCode
            implicationCertificate).length) +
        (binaryProofLength antecedentProof +
          (binaryStructuralValidityCertificateCode
            antecedentCertificate).length) +
        contextualModusPonensFullAssemblyCost Gamma antecedent consequent := by
  have hproof := contextualModusPonensDerivation_binaryProofLength_eq
    implicationProof antecedentProof
  have hcertificate := contextualModusPonensCertificate_code_length_le
    implicationCertificate antecedentCertificate
  unfold contextualModusPonensFullAssemblyCost
  omega

#print axioms contextualModusPonensCertificate_valid
#print axioms weakeningCertificate_valid
#print axioms weakening_full_payload_le
#print axioms contextualModusPonensDerivation_binaryProofLength_eq
#print axioms contextualModusPonensCertificate_code_length_le
#print axioms contextualModusPonens_full_payload_le

end FoundationCompactCertifiedContextualModusPonens
