import integration.FoundationCompactListedLocalCostPrimitives
import integration.FoundationCompactListedCertifiedHonestWeight
import integration.FoundationCompactPackedDecoderCostPotential

/-!
# Public verifier cost aggregation skeleton

This file aggregates the already costed packed decoders with a concrete local
certificate-check bound.  The current theorem keeps that local bound explicit;
the guarded axiom comparator must discharge it before the public endpoint is
called unconditional.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedPublicCostSkeleton

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAProofVerifier
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationCompactCanonicalDecodeLength
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactListedCertifiedVerifier
open FoundationCompactVerifierBitCostPrimitives
open FoundationCompactVerifierFormulaListChecks
open FoundationCompactListedCertifiedDecoderCost
open FoundationCompactDecoderCostPotential
open FoundationCompactPackedDecoderCostPotential
open FoundationCompactListedProofHonestWeight
open FoundationCompactListedCertifiedHonestWeight
open FoundationCompactListedLocalCostPrimitives

theorem listedLocalJointHonestBitWeight_eq
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    listedLocalJointHonestBitWeight tree certificate =
      listedCertifiedDecodedDataHonestBitWeight tree certificate :=
  rfl

theorem decodeCompactPackedListedCertifiedPAProof_localJointWeight_le
    {code : Nat} {tree : ListedCheckedPAProofTree}
    {certificate : StructuralValidityCertificate}
    (hdecode : decodeCompactPackedListedCertifiedPAProof code =
      some (tree, certificate)) :
    listedLocalJointHonestBitWeight tree certificate <=
      8 * packedPayloadLength code := by
  simpa [listedLocalJointHonestBitWeight_eq] using
    decodeCompactPackedListedCertifiedPAProof_honestWeight_le hdecode

theorem decodeCompactPackedFormula_binaryLength_le
    {code : Nat} {formula : LO.FirstOrder.ArithmeticProposition}
    (hdecode : decodeCompactPackedFormula code = some formula) :
    (binaryFormulaCode formula).length <= packedPayloadLength code := by
  simp only [decodeCompactPackedFormula] at hdecode
  cases hlast : code.bits.getLast? with
  | none => simp [hlast] at hdecode
  | some lastBit =>
      cases lastBit with
      | false => simp [hlast] at hdecode
      | true =>
          cases hformula :
              decodeCompactFormula 0
                (code.bits.length - 1 + 1) code.bits.dropLast with
          | none => simp [hformula, hlast] at hdecode
          | some formulaResult =>
              rcases formulaResult with ⟨decodedFormula, suffix⟩
              cases suffix with
              | cons head tail => simp [hformula, hlast] at hdecode
              | nil =>
                  simp [hformula, hlast] at hdecode
                  rcases hdecode with ⟨rfl⟩
                  have hlength :=
                    decodeCompactFormula_canonical_length_le hformula
                  have hpayload :
                      code.bits.dropLast.length = packedPayloadLength code := by
                    simp [packedPayloadLength, Nat.size_eq_bits_len]
                  simpa [hpayload] using hlength

theorem listedCertifiedPAProofLocalTrace_cost_le_of_certificateTrace
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (formulaCode : Nat)
    (hcertificate :
      (listedCertificateValidTrace tree certificate).2 <=
        listedJointLocalCostPolynomial
          (listedLocalJointHonestBitWeight tree certificate)) :
    (listedCertifiedPAProofLocalTrace
        tree certificate formula formulaCode).2 <=
      listedJointLocalCostPolynomial
          (listedLocalJointHonestBitWeight tree certificate) +
        formulaCheckPolynomial
          (formulaListCodeWeight tree.conclusionList +
            formulaListCodeWeight [formula]) +
        2 * Nat.size (compactFormulaCode formula) +
        Nat.size formulaCode + 4 := by
  have hset := formulaSetEqTrace_cost_le_polynomial
    tree.conclusionList [formula]
  have hnat := natEqTrace_cost_le
    (compactFormulaCode formula) formulaCode
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len] at hnat
  simp only [listedCertifiedPAProofLocalTrace, traceAnd_cost]
  omega

def listedPublicLocalCostPolynomial (inputSize : Nat) : Nat :=
  listedJointLocalCostPolynomial (8 * inputSize) +
    formulaCheckPolynomial (10 * inputSize + 3) +
    4 * inputSize + 16

def listedPublicVerifierCostPolynomial (inputSize : Nat) : Nat :=
  4 * decoderPotential inputSize +
    listedPublicLocalCostPolynomial inputSize + 1

theorem listedCertifiedPAProofLocalTrace_cost_le_inputSize
    (tree : ListedCheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (formulaCode inputSize : Nat)
    (hcertificate :
      (listedCertificateValidTrace tree certificate).2 <=
        listedJointLocalCostPolynomial
          (listedLocalJointHonestBitWeight tree certificate))
    (hjoint : listedLocalJointHonestBitWeight tree certificate <=
      8 * inputSize)
    (hformula : (binaryFormulaCode formula).length <= inputSize)
    (hformulaCode : Nat.size formulaCode <= inputSize) :
    (listedCertifiedPAProofLocalTrace
        tree certificate formula formulaCode).2 <=
      listedPublicLocalCostPolynomial inputSize := by
  have hlocal := listedCertifiedPAProofLocalTrace_cost_le_of_certificateTrace
    tree certificate formula formulaCode hcertificate
  have hjointCost := listedJointLocalCostPolynomial_mono hjoint
  have hconclusion := conclusionList_codeWeight_le_honestBitWeight tree
  have hproofJoint := listedProofHonestBitWeight_le_joint tree certificate
  have hconclusionInput :
      formulaListCodeWeight tree.conclusionList +
          formulaListCodeWeight [formula] <=
        10 * inputSize + 3 := by
    simp only [formulaListCodeWeight_cons, formulaListCodeWeight_nil]
    omega
  have hsetCost := formulaCheckPolynomial_mono hconclusionInput
  have hcompactSize := size_compactFormulaCode formula
  unfold listedPublicLocalCostPolynomial
  omega

theorem listedCompactCertifiedPAProofVerifierTrace_cost_le_of_certificateTrace
    (code formulaCode : Nat)
    (hcertificate : forall
      (tree : ListedCheckedPAProofTree)
      (certificate : StructuralValidityCertificate),
      (listedCertificateValidTrace tree certificate).2 <=
        listedJointLocalCostPolynomial
          (listedLocalJointHonestBitWeight tree certificate)) :
    (listedCompactCertifiedPAProofVerifierTrace code formulaCode).2 <=
      listedPublicVerifierCostPolynomial
        (Nat.size code + Nat.size formulaCode) := by
  let inputSize := Nat.size code + Nat.size formulaCode
  change (listedCompactCertifiedPAProofVerifierTrace code formulaCode).2 <=
    listedPublicVerifierCostPolynomial inputSize
  have hproofDecoder :=
    decodeCompactPackedListedCertifiedPAProofTrace_cost_le code
  have hformulaDecoder := decodeCompactPackedFormulaTrace_cost_le formulaCode
  have hproofPotentialMono := decoderPotential_mono
    (show Nat.size code <= inputSize by
      dsimp [inputSize]
      omega)
  have hformulaPotentialMono := decoderPotential_mono
    (show Nat.size formulaCode <= inputSize by
      dsimp [inputSize]
      omega)
  have hproofCost :
      (decodeCompactPackedListedCertifiedPAProofTrace code).2 <=
        2 * decoderPotential inputSize :=
    hproofDecoder.trans (Nat.mul_le_mul_left 2 hproofPotentialMono)
  have hformulaCost :
      (decodeCompactPackedFormulaTrace formulaCode).2 <=
        2 * decoderPotential inputSize :=
    hformulaDecoder.trans (Nat.mul_le_mul_left 2 hformulaPotentialMono)
  cases hproofResult :
      (decodeCompactPackedListedCertifiedPAProofTrace code).1 with
  | none =>
      simp [listedCompactCertifiedPAProofVerifierTrace, hproofResult]
      unfold listedPublicVerifierCostPolynomial
      omega
  | some decodedProof =>
      rcases decodedProof with ⟨tree, certificate⟩
      cases hformulaResult : (decodeCompactPackedFormulaTrace formulaCode).1 with
      | none =>
          simp [listedCompactCertifiedPAProofVerifierTrace,
            hproofResult, hformulaResult]
          unfold listedPublicVerifierCostPolynomial
          omega
      | some formula =>
          have hproofDecode :
              decodeCompactPackedListedCertifiedPAProof code =
                some (tree, certificate) := by
            rw [← decodeCompactPackedListedCertifiedPAProofTrace_result]
            exact hproofResult
          have hformulaDecode :
              decodeCompactPackedFormula formulaCode = some formula := by
            rw [← decodeCompactPackedFormulaTrace_result]
            exact hformulaResult
          have hjointRaw :=
            decodeCompactPackedListedCertifiedPAProof_localJointWeight_le
              hproofDecode
          have hproofPayload : packedPayloadLength code <= Nat.size code := by
            simp [packedPayloadLength]
          have hjoint :
              listedLocalJointHonestBitWeight tree certificate <=
                8 * inputSize := by
            have hscaled := Nat.mul_le_mul_left 8 hproofPayload
            dsimp [inputSize]
            omega
          have hformulaRaw :=
            decodeCompactPackedFormula_binaryLength_le hformulaDecode
          have hformulaPayload :
              packedPayloadLength formulaCode <= Nat.size formulaCode := by
            simp [packedPayloadLength]
          have hformula :
              (binaryFormulaCode formula).length <= inputSize := by
            dsimp [inputSize]
            omega
          have hformulaCodeSize : Nat.size formulaCode <= inputSize := by
            dsimp [inputSize]
            omega
          have hlocal := listedCertifiedPAProofLocalTrace_cost_le_inputSize
            tree certificate formula formulaCode inputSize
              (hcertificate tree certificate) hjoint hformula hformulaCodeSize
          simp [listedCompactCertifiedPAProofVerifierTrace,
            hproofResult, hformulaResult]
          unfold listedPublicVerifierCostPolynomial
          omega

#print axioms decodeCompactPackedListedCertifiedPAProof_localJointWeight_le
#print axioms decodeCompactPackedFormula_binaryLength_le
#print axioms listedCertifiedPAProofLocalTrace_cost_le_of_certificateTrace
#print axioms listedCertifiedPAProofLocalTrace_cost_le_inputSize
#print axioms listedCompactCertifiedPAProofVerifierTrace_cost_le_of_certificateTrace

end FoundationCompactListedPublicCostSkeleton
