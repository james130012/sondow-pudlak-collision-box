import integration.FoundationCompactListedLocalCostPrimitives

/-!
# Joint honest-weight bounds at an axiom node

These lemmas place the context, displayed candidate sentence, and complete PA
axiom certificate in the same local proof-plus-certificate bit coordinate.
They are the input-size bridge for the guarded axiom comparator.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedAxiomJointWeight

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedProofDecoder
open FoundationCompactVerifierFormulaListChecks
open FoundationCompactListedProofHonestWeight
open FoundationCompactListedLocalCostPrimitives

theorem axm_contextWeight_le_jointWeight
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) :
    formulaListCodeWeight Gamma <=
      listedLocalJointHonestBitWeight (.axm Gamma sentence)
        (.axiomCert certificate) := by
  simp only [listedLocalJointHonestBitWeight,
    listedProofHonestBitWeight,
    localStructuralCertificateHonestBitWeight]
  omega

theorem axm_sentenceCodeLength_le_jointWeight
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) :
    (binaryFormulaCode
        (Rewriting.emb sentence :
          LO.FirstOrder.ArithmeticProposition)).length <=
      listedLocalJointHonestBitWeight (.axm Gamma sentence)
        (.axiomCert certificate) := by
  simp only [listedLocalJointHonestBitWeight,
    listedProofHonestBitWeight,
    localStructuralCertificateHonestBitWeight]
  omega

theorem axm_axiomCertificateCodeLength_le_jointWeight
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) :
    (binaryPAAxiomCertificateCode certificate).length <=
      listedLocalJointHonestBitWeight (.axm Gamma sentence)
        (.axiomCert certificate) := by
  simp only [listedLocalJointHonestBitWeight,
    listedProofHonestBitWeight,
    localStructuralCertificateHonestBitWeight,
    binaryStructuralValidityCertificateCode,
    List.length_append]
  omega

theorem axm_comparatorInputWeight_le_twiceJointWeight
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) :
    (binaryPAAxiomCertificateCode certificate).length +
        (binaryFormulaCode
          (Rewriting.emb sentence :
            LO.FirstOrder.ArithmeticProposition)).length + 1 <=
      2 * listedLocalJointHonestBitWeight (.axm Gamma sentence)
        (.axiomCert certificate) + 1 := by
  have hcertificate := axm_axiomCertificateCodeLength_le_jointWeight
    Gamma sentence certificate
  have hsentence := axm_sentenceCodeLength_le_jointWeight
    Gamma sentence certificate
  omega

#print axioms axm_contextWeight_le_jointWeight
#print axioms axm_sentenceCodeLength_le_jointWeight
#print axioms axm_axiomCertificateCodeLength_le_jointWeight
#print axioms axm_comparatorInputWeight_le_twiceJointWeight

end FoundationCompactListedAxiomJointWeight
