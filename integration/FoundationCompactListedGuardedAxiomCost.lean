import integration.FoundationCompactListedAxiomJointWeight
import integration.FoundationCompactListedPublicCostSkeleton

/-!
# Parameter-free guarded axiom and public verifier cost endpoints

The guarded comparator is charged in the same proof-plus-certificate bit
coordinate used by the list-preserving verifier.  This discharges the sole
`haxm` premise in both the structural aggregation and public cost skeletons.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedGuardedAxiomCost

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAAxiomCertificate
open FoundationCompactVerifierFormulaListChecks
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactListedCertifiedVerifier
open FoundationCompactListedCertifiedDecoderCost
open FoundationCompactListedProofHonestWeight
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactListedAxiomJointWeight
open FoundationCompactSyntaxTransformationTrace
open FoundationCompactListedPublicCostSkeleton

theorem guardedAxiomSentenceEqTrace_cost_le_jointWeight
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) :
    (guardedAxiomSentenceEqTrace certificate sentence).2 <=
      guardedAxiomCostEnvelope
        (listedLocalJointHonestBitWeight (.axm Gamma sentence)
          (.axiomCert certificate)) := by
  let weight := listedLocalJointHonestBitWeight (.axm Gamma sentence)
    (.axiomCert certificate)
  change (guardedAxiomSentenceEqTrace certificate sentence).2 <=
    guardedAxiomCostEnvelope weight
  have hinputRaw := axm_comparatorInputWeight_le_twiceJointWeight
    Gamma sentence certificate
  have hinput :
      (binaryPAAxiomCertificateCode certificate).length +
          candidateSentenceCodeLength sentence + 1 <=
        2 * weight + 1 := by
    simpa only [candidateSentenceCodeLength, weight] using hinputRaw
  have hpow := Nat.pow_le_pow_left hinput 12
  have hscaled := Nat.mul_le_mul_left
    guardedAxiomSentenceEqTraceCoefficient hpow
  exact (guardedAxiomSentenceEqTrace_cost_le certificate sentence).trans (by
    simpa only [guardedAxiomCostEnvelope] using hscaled)

theorem axm_formulaMemTrace_cost_le_jointWeight
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) :
    (formulaMemTrace
      (Rewriting.emb sentence : LO.FirstOrder.ArithmeticProposition) Gamma).2 <=
      formulaCheckPolynomial
        (generatedFormulaWeightPolynomial
          (listedLocalJointHonestBitWeight (.axm Gamma sentence)
            (.axiomCert certificate))) := by
  let weight := listedLocalJointHonestBitWeight (.axm Gamma sentence)
    (.axiomCert certificate)
  have hsentence := axm_sentenceCodeLength_le_jointWeight
    Gamma sentence certificate
  have hcontext := axm_contextWeight_le_jointWeight
    Gamma sentence certificate
  have hinput :
      (binaryFormulaCode
          (Rewriting.emb sentence :
            LO.FirstOrder.ArithmeticProposition)).length +
          formulaListCodeWeight Gamma <=
        4 * weight + 32 := by
    dsimp only [weight] at hsentence hcontext ⊢
    omega
  have hgenerated := hinput.trans
    (linearGeneratedWeight_le_polynomial weight)
  exact (formulaMemTrace_cost_le_polynomial
    (Rewriting.emb sentence : LO.FirstOrder.ArithmeticProposition) Gamma).trans
      (formulaCheckPolynomial_mono hgenerated)

theorem guardedListedCertificateValidTrace_axm_cost_le
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) :
    (listedCertificateValidTrace (.axm Gamma sentence)
      (.axiomCert certificate)).2 <=
      perProofNodeFormulaCostPolynomial
        (listedLocalJointHonestBitWeight (.axm Gamma sentence)
          (.axiomCert certificate)) := by
  let weight := listedLocalJointHonestBitWeight (.axm Gamma sentence)
    (.axiomCert certificate)
  have hguard := guardedAxiomSentenceEqTrace_cost_le_jointWeight
    Gamma sentence certificate
  have hmem := axm_formulaMemTrace_cost_le_jointWeight
    Gamma sentence certificate
  simp only [listedCertificateValidTrace, traceAnd_cost]
  change _ <= perProofNodeFormulaCostPolynomial weight
  unfold perProofNodeFormulaCostPolynomial
  dsimp only [weight] at hguard hmem ⊢
  omega

theorem guardedListedCertificateValidTrace_jointCost_le
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    (listedCertificateValidTrace tree certificate).2 <=
      listedJointLocalCostPolynomial
        (listedLocalJointHonestBitWeight tree certificate) := by
  exact listedCertificateValidTrace_jointCost_le_polynomial_of_axm
    guardedListedCertificateValidTrace_axm_cost_le tree certificate

theorem guardedListedCompactCertifiedPAProofVerifierTrace_result
    (code formulaCode : Nat) :
    (listedCompactCertifiedPAProofVerifierTrace code formulaCode).1 =
      listedCompactCertifiedPAProofVerifier code formulaCode := by
  exact listedCompactCertifiedPAProofVerifierTrace_result code formulaCode

theorem guardedListedCompactCertifiedPAProofVerifierTrace_cost_le
    (code formulaCode : Nat) :
    (listedCompactCertifiedPAProofVerifierTrace code formulaCode).2 <=
      listedPublicVerifierCostPolynomial
        (Nat.size code + Nat.size formulaCode) := by
  exact listedCompactCertifiedPAProofVerifierTrace_cost_le_of_certificateTrace
    code formulaCode guardedListedCertificateValidTrace_jointCost_le

#print axioms guardedAxiomSentenceEqTrace_cost_le_jointWeight
#print axioms guardedListedCertificateValidTrace_axm_cost_le
#print axioms guardedListedCertificateValidTrace_jointCost_le
#print axioms guardedListedCompactCertifiedPAProofVerifierTrace_result
#print axioms guardedListedCompactCertifiedPAProofVerifierTrace_cost_le

end FoundationCompactListedGuardedAxiomCost
