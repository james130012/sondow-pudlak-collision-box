import integration.FoundationCompactListedProofHonestWeight
import integration.FoundationCompactCertificateCanonicalDecodeLength
import integration.FoundationCompactListedCertifiedVerifier

/-!
# Honest bit weight for list-preserving certified proofs

This file combines the duplicate-preserving proof-tree charge with the full
canonical code length of the structural certificate.  Every successful joint
decode is therefore controlled by the bits that it actually consumes.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedCertifiedHonestWeight

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertificateCanonicalDecodeLength
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertifiedVerifier
open FoundationCompactListedProofHonestWeight

def structuralCertificateHonestBitWeight
    (certificate : StructuralValidityCertificate) : Nat :=
  8 * (binaryStructuralValidityCertificateCode certificate).length

def listedCertifiedDecodedDataHonestBitWeight
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) : Nat :=
  listedProofHonestBitWeight tree +
    structuralCertificateHonestBitWeight certificate

theorem structuralCertificateParseWeight_le_honestBitWeight
    (certificate : StructuralValidityCertificate) :
    structuralCertificateParseWeight certificate <=
      structuralCertificateHonestBitWeight certificate := by
  have hparse :=
    structuralCertificateParseWeight_le_binaryCode_length certificate
  simp only [structuralCertificateHonestBitWeight]
  omega

theorem decodeCompactListedCertifiedPAProof_honestWeight_le
    {fuel : Nat} {bits suffix : List Bool}
    {tree : ListedCheckedPAProofTree}
    {certificate : StructuralValidityCertificate}
    (hdecode : decodeCompactListedCertifiedPAProof fuel bits =
      some ((tree, certificate), suffix)) :
    listedCertifiedDecodedDataHonestBitWeight tree certificate +
        8 * suffix.length <= 8 * bits.length := by
  cases htree : decodeCompactListedProof fuel bits with
  | none =>
      simp [decodeCompactListedCertifiedPAProof, htree] at hdecode
  | some treeResult =>
      rcases treeResult with ⟨decodedTree, afterTree⟩
      cases hcertificate :
          decodeStructuralValidityCertificate fuel afterTree with
      | none =>
          simp [decodeCompactListedCertifiedPAProof, htree, hcertificate]
            at hdecode
      | some certificateResult =>
          rcases certificateResult with
            ⟨decodedCertificate, afterCertificate⟩
          simp [decodeCompactListedCertifiedPAProof, htree, hcertificate]
            at hdecode
          rcases hdecode with ⟨⟨rfl, rfl⟩, rfl⟩
          have htreeWeight :=
            decodeCompactListedProof_honestWeight_le htree
          have hcertificateLength :=
            decodeStructuralValidityCertificate_binaryLength_le hcertificate
          simp only [listedCertifiedDecodedDataHonestBitWeight,
            structuralCertificateHonestBitWeight]
          omega

theorem decodeCompactPackedListedCertifiedPAProof_honestWeight_le
    {code : Nat} {tree : ListedCheckedPAProofTree}
    {certificate : StructuralValidityCertificate}
    (hdecode : decodeCompactPackedListedCertifiedPAProof code =
      some (tree, certificate)) :
    listedCertifiedDecodedDataHonestBitWeight tree certificate <=
      8 * packedPayloadLength code := by
  simp only [decodeCompactPackedListedCertifiedPAProof] at hdecode
  cases hlast : code.bits.getLast? with
  | none => simp [hlast] at hdecode
  | some lastBit =>
      cases lastBit with
      | false => simp [hlast] at hdecode
      | true =>
          cases hproof :
              decodeCompactListedCertifiedPAProof
                (code.bits.length - 1 + 1) code.bits.dropLast with
          | none => simp [hproof] at hdecode
          | some proofResult =>
              rcases proofResult with ⟨decodedProof, suffix⟩
              cases suffix with
              | cons head tail => simp [hproof, hlast] at hdecode
              | nil =>
                  rcases decodedProof with
                    ⟨decodedTree, decodedCertificate⟩
                  simp [hproof, hlast] at hdecode
                  rcases hdecode with ⟨rfl, rfl⟩
                  have hweight :=
                    decodeCompactListedCertifiedPAProof_honestWeight_le hproof
                  have hpayloadLength :
                      code.bits.dropLast.length =
                        packedPayloadLength code := by
                    simp [packedPayloadLength, Nat.size_eq_bits_len]
                  simpa [hpayloadLength] using hweight

#print axioms structuralCertificateParseWeight_le_honestBitWeight
#print axioms decodeCompactListedCertifiedPAProof_honestWeight_le
#print axioms decodeCompactPackedListedCertifiedPAProof_honestWeight_le

end FoundationCompactListedCertifiedHonestWeight
