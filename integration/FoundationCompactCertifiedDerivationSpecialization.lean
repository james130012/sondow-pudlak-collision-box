import integration.FoundationCompactDerivationSpecialization
import integration.FoundationCompactListedCertifiedEncoder

/-!
# Certified specialization on the public full-payload coordinate

The proof tree alone is not the final length measure.  This file supplies the
matching structural certificate, packs proof and certificate together, and
proves acceptance by the public list-preserving verifier with a cubic bound
on the complete payload.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCertifiedDerivationSpecialization

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationComputableCompactPAProofEncoder
open FoundationCompactListedCertifiedVerifier
open FoundationCompactListedCertifiedEncoder
open FoundationCompactDerivationSpecialization

/-- Choose one certificate for a concrete derivation.  For a fixed base
derivation this is one fixed finite object, not a varying length assumption. -/
noncomputable def certificateOfDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (derivation : LO.FirstOrder.Derivation2 PA Gamma) :
    StructuralValidityCertificate :=
  Classical.choose <| exists_certificateValid
    (CheckedPAProofTree.ofDerivation derivation)
    (structurallyValid_ofDerivation derivation)

theorem certificateOfDerivation_valid
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (derivation : LO.FirstOrder.Derivation2 PA Gamma) :
    certificateValid (CheckedPAProofTree.ofDerivation derivation)
      (certificateOfDerivation derivation) :=
  Classical.choose_spec <| exists_certificateValid
    (CheckedPAProofTree.ofDerivation derivation)
    (structurallyValid_ofDerivation derivation)

/-- Certificate shape matching `cut(wk(base), exs(closed))`. -/
def specializeCertificate
    (baseCertificate : StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .binary (.unary baseCertificate) (.unary .leaf)

theorem specializeCertificate_valid
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (base : LO.FirstOrder.Derivation2 PA {∀⁰ formula})
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (baseCertificate : StructuralValidityCertificate)
    (hbase : certificateValid (CheckedPAProofTree.ofDerivation base)
      baseCertificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (specializeDerivation base witness))
      (specializeCertificate baseCertificate) := by
  have hbaseConclusion :
      (CheckedPAProofTree.ofDerivation base).conclusion = {∀⁰ formula} :=
    CheckedPAProofTree.conclusion_ofDerivation base
  simp [specializeDerivation, specializeCertificate,
    CheckedPAProofTree.ofDerivation, CheckedPAProofTree.conclusion,
    certificateValid, hbase]
  change (CheckedPAProofTree.ofDerivation base).conclusion ⊆
    insert (∀⁰ formula) {formula/[witness]}
  rw [hbaseConclusion]
  simp

theorem specializeCertificate_code_length_le
    (baseCertificate : StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (specializeCertificate baseCertificate)).length <=
      (binaryStructuralValidityCertificateCode baseCertificate).length + 64 := by
  have htag0 : (binaryNatCode 0).length <= 16 := by decide
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  simp only [specializeCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

def specializedTree
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (base : LO.FirstOrder.Derivation2 PA {∀⁰ formula})
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CheckedPAProofTree :=
  CheckedPAProofTree.ofDerivation (specializeDerivation base witness)

noncomputable def specializedCertificate
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (base : LO.FirstOrder.Derivation2 PA {∀⁰ formula}) :
    StructuralValidityCertificate :=
  specializeCertificate (certificateOfDerivation base)

noncomputable def specializedCertifiedCode
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (base : LO.FirstOrder.Derivation2 PA {∀⁰ formula})
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  canonicalPackedCertifiedPAProofCode
    (specializedTree base witness) (specializedCertificate base)

theorem specializedCertificate_valid
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (base : LO.FirstOrder.Derivation2 PA {∀⁰ formula})
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    certificateValid (specializedTree base witness)
      (specializedCertificate base) := by
  exact specializeCertificate_valid base witness
    (certificateOfDerivation base) (certificateOfDerivation_valid base)

/-- The actual public verifier accepts the complete specialized payload. -/
theorem specializedCertifiedCode_verifier_eq_true
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (base : LO.FirstOrder.Derivation2 PA {∀⁰ formula})
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier
      (specializedCertifiedCode base witness)
      (compactFormulaCode (formula/[witness])) = true := by
  apply listedCompactCertifiedPAProofVerifier_eq_true_of_certifiedTree
    (specializedTree base witness) (specializedCertificate base)
      (formula/[witness])
  · exact specializedCertificate_valid base witness
  · simp [specializedTree]

/-- Cubic bound on the same full proof-plus-certificate payload measured by
the public verifier. -/
theorem specializedCertifiedCode_payloadLength_le_cubic
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (base : LO.FirstOrder.Derivation2 PA {∀⁰ formula})
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    let scale := (binaryFormulaCode formula).length +
      (binaryTermCode witness).length + 1
    packedPayloadLength (specializedCertifiedCode base witness) <=
      binaryProofLength base +
        (binaryStructuralValidityCertificateCode
          (certificateOfDerivation base)).length + 192 +
        2048 * scale * scale * scale := by
  let scale := (binaryFormulaCode formula).length +
    (binaryTermCode witness).length + 1
  have hproof := specializeDerivation_binaryProofLength_le_cubic base witness
  change binaryProofLength (specializeDerivation base witness) <=
      binaryProofLength base + 128 +
        2048 * scale * scale * scale at hproof
  have hcertificate := specializeCertificate_code_length_le
    (certificateOfDerivation base)
  change (binaryStructuralValidityCertificateCode
      (specializedCertificate base)).length <=
      (binaryStructuralValidityCertificateCode
        (certificateOfDerivation base)).length + 64 at hcertificate
  change packedPayloadLength (specializedCertifiedCode base witness) <=
    binaryProofLength base +
      (binaryStructuralValidityCertificateCode
        (certificateOfDerivation base)).length + 192 +
      2048 * scale * scale * scale
  calc
    packedPayloadLength (specializedCertifiedCode base witness) =
        binaryProofLength (specializeDerivation base witness) +
          (binaryStructuralValidityCertificateCode
            (specializedCertificate base)).length := by
      simp [specializedCertifiedCode, specializedTree,
        canonicalBinaryCertifiedPAProofCode,
        canonicalBinaryProofCode_length, binaryProofLength]
    _ <= (binaryProofLength base + 128 +
            2048 * scale * scale * scale) +
          ((binaryStructuralValidityCertificateCode
            (certificateOfDerivation base)).length + 64) :=
      Nat.add_le_add hproof hcertificate
    _ = binaryProofLength base +
          (binaryStructuralValidityCertificateCode
            (certificateOfDerivation base)).length + 192 +
          2048 * scale * scale * scale := by omega

#print axioms certificateOfDerivation_valid
#print axioms specializeCertificate_valid
#print axioms specializeCertificate_code_length_le
#print axioms specializedCertifiedCode_verifier_eq_true
#print axioms specializedCertifiedCode_payloadLength_le_cubic

end FoundationCompactCertifiedDerivationSpecialization
