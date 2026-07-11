import integration.FoundationCompactListedProofEncoder

/-!
# Complete canonical encoding for the list-preserving certified verifier
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedCertifiedEncoder

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactListedCertifiedVerifier
open FoundationCompactListedProofEncoder
open FoundationComputableCompactPAProofEncoder

@[simp] theorem toListed_conclusion_toFinset
    (tree : CheckedPAProofTree) :
    (toListed tree).conclusionList.toFinset = tree.conclusion := by
  rw [← ListedCheckedPAProofTree.toChecked_conclusion,
    toListed_toChecked]

theorem decodeCompactListedCertifiedPAProof_canonicalBinaryCode_append
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (fuel : Nat)
    (htree : tree.parseWeight < fuel)
    (hcertificate : structuralCertificateParseWeight certificate < fuel)
    (suffix : List Bool) :
    decodeCompactListedCertifiedPAProof fuel
        (canonicalBinaryCertifiedPAProofCode tree certificate ++ suffix) =
      some ((toListed tree, certificate), suffix) := by
  simp [decodeCompactListedCertifiedPAProof,
    canonicalBinaryCertifiedPAProofCode,
    decodeCompactListedProof_canonicalBinaryCode_append
      tree fuel htree,
    decodeStructuralValidityCertificate_binaryCode_append
      certificate fuel hcertificate]

@[simp] theorem decodeCompactPackedListedCertifiedPAProof_canonicalPackedCode
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    decodeCompactPackedListedCertifiedPAProof
        (canonicalPackedCertifiedPAProofCode tree certificate) =
      some (toListed tree, certificate) := by
  have htree :
      tree.parseWeight <
        (canonicalBinaryCertifiedPAProofCode tree certificate).length + 1 := by
    have hweight := tree.parseWeight_le_binaryLength
    rw [CheckedPAProofTree.binaryLength] at hweight
    have hcanonical := canonicalBinaryProofCode_length tree
    simp only [canonicalBinaryCertifiedPAProofCode, List.length_append]
    omega
  have hcertificate :
      structuralCertificateParseWeight certificate <
        (canonicalBinaryCertifiedPAProofCode tree certificate).length + 1 := by
    have hweight :=
      structuralCertificateParseWeight_le_binaryCode_length certificate
    simp only [canonicalBinaryCertifiedPAProofCode, List.length_append]
    omega
  have hdecode :
      decodeCompactListedCertifiedPAProof
          ((canonicalBinaryCertifiedPAProofCode tree certificate).length + 1)
          (canonicalBinaryCertifiedPAProofCode tree certificate) =
        some ((toListed tree, certificate), []) := by
    simpa using
      decodeCompactListedCertifiedPAProof_canonicalBinaryCode_append
        tree certificate
        ((canonicalBinaryCertifiedPAProofCode tree certificate).length + 1)
        htree hcertificate []
  simp [decodeCompactPackedListedCertifiedPAProof,
    canonicalPackedCertifiedPAProofCode, hdecode]

theorem listedCertifiedTree_checks
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (hcertificate : certificateValid tree certificate)
    (hconclusion : tree.conclusion = {formula}) :
    ListedCompactCertifiedPAProofChecks
      (canonicalPackedCertifiedPAProofCode tree certificate)
      (compactFormulaCode formula) := by
  refine ⟨toListed tree, certificate, formula, ?_, ?_, ?_, rfl⟩
  · exact decodeCompactPackedListedCertifiedPAProof_canonicalPackedCode
      tree certificate
  · apply (listedCertificateValid_toChecked_iff
      (toListed tree) certificate).2
    simpa using hcertificate
  · simpa using hconclusion

theorem listedCompactCertifiedPAProofVerifier_eq_true_of_certifiedTree
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (hcertificate : certificateValid tree certificate)
    (hconclusion : tree.conclusion = {formula}) :
    listedCompactCertifiedPAProofVerifier
      (canonicalPackedCertifiedPAProofCode tree certificate)
      (compactFormulaCode formula) = true := by
  exact (listedCompactCertifiedPAProofVerifier_eq_true_iff _ _).2
    (listedCertifiedTree_checks tree certificate formula
      hcertificate hconclusion)

theorem derivation_to_listedCompactCertifiedPAProofVerifier
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (derivation : LO.FirstOrder.Derivation2 PA Gamma)
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hconclusion : Gamma = {formula}) :
    exists (code : Nat) (certificate : StructuralValidityCertificate),
      packedPayloadLength code =
          (canonicalBinaryCertifiedPAProofCode
            (CheckedPAProofTree.ofDerivation derivation)
            certificate).length ∧
        listedCompactCertifiedPAProofVerifier code
          (compactFormulaCode formula) = true := by
  let tree := CheckedPAProofTree.ofDerivation derivation
  have hvalid : structurallyValid tree :=
    structurallyValid_ofDerivation derivation
  rcases exists_certificateValid tree hvalid with
    ⟨certificate, hcertificate⟩
  let code := canonicalPackedCertifiedPAProofCode tree certificate
  refine ⟨code, certificate, ?_, ?_⟩
  · simp [code, tree]
  · apply listedCompactCertifiedPAProofVerifier_eq_true_of_certifiedTree
      tree certificate formula hcertificate
    simpa [tree] using hconclusion

#print axioms decodeCompactPackedListedCertifiedPAProof_canonicalPackedCode
#print axioms listedCompactCertifiedPAProofVerifier_eq_true_of_certifiedTree
#print axioms derivation_to_listedCompactCertifiedPAProofVerifier

end FoundationCompactListedCertifiedEncoder
