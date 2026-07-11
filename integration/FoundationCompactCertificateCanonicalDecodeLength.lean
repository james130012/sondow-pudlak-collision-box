import integration.FoundationCompactPAAxiomCertificateCanonicalDecodeLength

/-!
# Canonical decode length for complete certified PA proofs
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCertificateCanonicalDecodeLength

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAProofVerifier
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationCompactCanonicalDecodeLength
open FoundationCompactProofCanonicalDecodeLengthComplete
open FoundationCompactPAAxiomCertificateCanonicalDecodeLength

theorem decodeStructuralValidityCertificate_binaryLength_le :
    forall {fuel bits suffix certificate},
      decodeStructuralValidityCertificate fuel bits =
        some (certificate, suffix) ->
      (binaryStructuralValidityCertificateCode certificate).length +
          suffix.length <= bits.length := by
  intro fuel
  induction fuel with
  | zero =>
      intro bits suffix certificate hdecode
      simp [decodeStructuralValidityCertificate] at hdecode
  | succ fuel ih =>
      intro bits suffix certificate hdecode
      cases htag : decodeBinaryNat bits with
      | none =>
          simp [decodeStructuralValidityCertificate, htag] at hdecode
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          have htagLength := decodeBinaryNat_canonical_length_le htag
          cases tag with
          | zero =>
              simp [decodeStructuralValidityCertificate, htag] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              simp only [binaryStructuralValidityCertificateCode]
              exact htagLength
          | succ tag =>
              cases tag with
              | zero =>
                  cases haxiom : decodePAAxiomCertificate fuel afterTag with
                  | none =>
                      simp [decodeStructuralValidityCertificate, htag,
                        haxiom] at hdecode
                  | some axiomResult =>
                      rcases axiomResult with ⟨axiomCertificate, afterAxiom⟩
                      simp [decodeStructuralValidityCertificate, htag,
                        haxiom] at hdecode
                      rcases hdecode with ⟨rfl, rfl⟩
                      have haxiomLength :=
                        decodePAAxiomCertificate_binaryLength_le haxiom
                      change (binaryNatCode 1).length +
                          afterTag.length <= bits.length at htagLength
                      simp only [binaryStructuralValidityCertificateCode,
                        List.length_append]
                      omega
              | succ tag =>
                  cases tag with
                  | zero =>
                      cases hpremise :
                          decodeStructuralValidityCertificate fuel afterTag with
                      | none =>
                          simp [decodeStructuralValidityCertificate, htag,
                            hpremise] at hdecode
                      | some premiseResult =>
                          rcases premiseResult with ⟨premise, afterPremise⟩
                          simp [decodeStructuralValidityCertificate, htag,
                            hpremise] at hdecode
                          rcases hdecode with ⟨rfl, rfl⟩
                          have hpremiseLength := ih hpremise
                          change (binaryNatCode 2).length +
                              afterTag.length <= bits.length at htagLength
                          simp only [binaryStructuralValidityCertificateCode,
                            List.length_append]
                          omega
                  | succ tag =>
                      cases tag with
                      | zero =>
                          cases hleft :
                              decodeStructuralValidityCertificate fuel
                                afterTag with
                          | none =>
                              simp [decodeStructuralValidityCertificate, htag,
                                hleft] at hdecode
                          | some leftResult =>
                              rcases leftResult with ⟨left, afterLeft⟩
                              cases hright :
                                  decodeStructuralValidityCertificate fuel
                                    afterLeft with
                              | none =>
                                  simp [decodeStructuralValidityCertificate,
                                    htag, hleft, hright] at hdecode
                              | some rightResult =>
                                  rcases rightResult with ⟨right, afterRight⟩
                                  simp [decodeStructuralValidityCertificate,
                                    htag, hleft, hright] at hdecode
                                  rcases hdecode with ⟨rfl, rfl⟩
                                  have hleftLength := ih hleft
                                  have hrightLength := ih hright
                                  change (binaryNatCode 3).length +
                                      afterTag.length <= bits.length at htagLength
                                  simp only
                                    [binaryStructuralValidityCertificateCode,
                                      List.length_append]
                                  omega
                      | succ tag =>
                          simp [decodeStructuralValidityCertificate, htag]
                            at hdecode

theorem decodeCompactCertifiedPAProof_binaryLength_le
    {fuel : Nat} {bits suffix : List Bool}
    {tree : CheckedPAProofTree}
    {certificate : StructuralValidityCertificate}
    (hdecode : decodeCompactCertifiedPAProof fuel bits =
      some ((tree, certificate), suffix)) :
    (binaryCertifiedPAProofCode tree certificate).length + suffix.length <=
      bits.length := by
  cases hproof : decodeCompactProof fuel bits with
  | none => simp [decodeCompactCertifiedPAProof, hproof] at hdecode
  | some proofResult =>
      rcases proofResult with ⟨decodedTree, afterProof⟩
      cases hcertificate :
          decodeStructuralValidityCertificate fuel afterProof with
      | none =>
          simp [decodeCompactCertifiedPAProof, hproof, hcertificate] at hdecode
      | some certificateResult =>
          rcases certificateResult with
            ⟨decodedCertificate, afterCertificate⟩
          simp [decodeCompactCertifiedPAProof, hproof, hcertificate] at hdecode
          rcases hdecode with ⟨⟨rfl, rfl⟩, rfl⟩
          have hproofLength := decodeCompactProof_binaryLength_le hproof
          have hcertificateLength :=
            decodeStructuralValidityCertificate_binaryLength_le hcertificate
          simp only [CheckedPAProofTree.binaryLength] at hproofLength
          simp only [binaryCertifiedPAProofCode, List.length_append]
          omega

theorem decodeCompactPackedCertifiedPAProof_binaryLength_le
    {code : Nat} {tree : CheckedPAProofTree}
    {certificate : StructuralValidityCertificate}
    (hdecode : decodeCompactPackedCertifiedPAProof code =
      some (tree, certificate)) :
    (binaryCertifiedPAProofCode tree certificate).length <=
      packedPayloadLength code := by
  simp only [decodeCompactPackedCertifiedPAProof] at hdecode
  cases hlast : code.bits.getLast? with
  | none => simp [hlast] at hdecode
  | some lastBit =>
      cases lastBit with
      | false => simp [hlast] at hdecode
      | true =>
          cases hproof :
              decodeCompactCertifiedPAProof
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
                  have hlength :=
                    decodeCompactCertifiedPAProof_binaryLength_le hproof
                  have hpayloadLength :
                      code.bits.dropLast.length =
                        packedPayloadLength code := by
                    simp [packedPayloadLength, Nat.size_eq_bits_len]
                  simpa [hpayloadLength] using hlength

theorem compactCertifiedPAProofVerifier_canonical_length_bound
    {code formulaCode : Nat}
    (haccept : compactCertifiedPAProofVerifier code formulaCode = true) :
    exists (tree : CheckedPAProofTree)
        (certificate : StructuralValidityCertificate)
        (formula : LO.FirstOrder.ArithmeticProposition),
      decodeCompactPackedCertifiedPAProof code =
          some (tree, certificate) ∧
        certificateValid tree certificate ∧
        tree.conclusion = {formula} ∧
        compactFormulaCode formula = formulaCode ∧
        (binaryCertifiedPAProofCode tree certificate).length <=
          packedPayloadLength code ∧
        (binaryFormulaCode formula).length <=
          packedPayloadLength formulaCode := by
  rcases checks_of_compactCertifiedPAProofVerifier_eq_true haccept with
    ⟨tree, certificate, formula, hdecode, hcertificate,
      hconclusion, hformulaCode⟩
  refine ⟨tree, certificate, formula, hdecode, hcertificate,
    hconclusion, hformulaCode, ?_, ?_⟩
  · exact decodeCompactPackedCertifiedPAProof_binaryLength_le hdecode
  · subst formulaCode
    simp [compactFormulaCode, packedPayloadLength]

#print axioms decodeStructuralValidityCertificate_binaryLength_le
#print axioms decodeCompactPackedCertifiedPAProof_binaryLength_le
#print axioms compactCertifiedPAProofVerifier_canonical_length_bound

end FoundationCompactCertificateCanonicalDecodeLength
