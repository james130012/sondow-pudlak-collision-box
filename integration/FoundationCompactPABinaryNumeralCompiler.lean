import integration.FoundationCompactPAQuantitativeCompilerCore
import integration.FoundationCompactBinaryNumeralTerm

/-!
# Quantitative PA proofs over short binary numerals

This module connects the proof-producing core to the existing short binary
numeral syntax.  Every endpoint emits a real proof-plus-certificate payload
accepted by the public checker, and its bound is a fixed cubic polynomial in
`Nat.size n` through the explicit numeral-code bound.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABinaryNumeralCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationComputableCompactPAProofEncoder
open FoundationCompactListedCertifiedVerifier
open FoundationCompactListedCertifiedEncoder
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof

noncomputable def binaryNumeralSpecializationScaleBound
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (value : Nat) : Nat :=
  (binaryFormulaCode formula).length +
    (binaryTermCode arithmeticZeroTerm).length +
    binaryNumeralStepBudget * Nat.size value + 1

theorem specializationScale_binaryNumeralTerm_le
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (value : Nat) :
    specializationScale formula (binaryNumeralTerm value) <=
      binaryNumeralSpecializationScaleBound formula value := by
  have hterm := binaryNumeralTerm_code_length_le_size value
  simp only [specializationScale,
    binaryNumeralSpecializationScaleBound]
  omega

noncomputable def binaryNumeralSpecializationCostBound
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (value : Nat) : Nat :=
  192 +
    2048 * binaryNumeralSpecializationScaleBound formula value *
      binaryNumeralSpecializationScaleBound formula value *
      binaryNumeralSpecializationScaleBound formula value

theorem weightedCubic_mono {left right : Nat} (h : left <= right) :
    192 + 2048 * left * left * left <=
      192 + 2048 * right * right * right := by
  have hpow : left ^ 3 <= right ^ 3 := pow_le_pow_left' h 3
  have hmul : 2048 * left ^ 3 <= 2048 * right ^ 3 :=
    Nat.mul_le_mul_left 2048 hpow
  simpa [pow_succ, Nat.mul_assoc] using Nat.add_le_add_left hmul 192

theorem specializationCost_binaryNumeralTerm_le
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (value : Nat) :
    specializationCost formula (binaryNumeralTerm value) <=
      binaryNumeralSpecializationCostBound formula value := by
  have hscale := specializationScale_binaryNumeralTerm_le formula value
  simp only [specializationCost, binaryNumeralSpecializationCostBound]
  exact weightedCubic_mono hscale

theorem proveBinaryNumeralReflexivity_verifier_eq_true
    (value : Nat) :
    listedCompactCertifiedPAProofVerifier
      (proveEqualityReflexivity (binaryNumeralTerm value)).code
      (FoundationPudlakQuantitativeConditions.compactFormulaCode
        (“!!(binaryNumeralTerm value) = !!(binaryNumeralTerm value)” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  proveEqualityReflexivity_verifier_eq_true (binaryNumeralTerm value)

theorem proveBinaryNumeralReflexivity_payloadLength_le
    (value : Nat) :
    (proveEqualityReflexivity
      (binaryNumeralTerm value)).payloadLength <=
      equalityReflexivityAxiomProof.payloadLength +
        binaryNumeralSpecializationCostBound
          equalityReflexivityBody value := by
  have hproof := specialize_payloadLength_le_cost
    equalityReflexivityAxiomProof (binaryNumeralTerm value)
  have hcost := specializationCost_binaryNumeralTerm_le
    equalityReflexivityBody value
  exact hproof.trans (Nat.add_le_add_left hcost _)

theorem proveBinaryNumeralAddZero_verifier_eq_true
    (value : Nat) :
    listedCompactCertifiedPAProofVerifier
      (proveAddZero (binaryNumeralTerm value)).code
      (FoundationPudlakQuantitativeConditions.compactFormulaCode
        (“!!(binaryNumeralTerm value) + 0 = !!(binaryNumeralTerm value)” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  proveAddZero_verifier_eq_true (binaryNumeralTerm value)

theorem proveBinaryNumeralAddZero_payloadLength_le
    (value : Nat) :
    (proveAddZero (binaryNumeralTerm value)).payloadLength <=
      addZeroAxiomProof.payloadLength +
        binaryNumeralSpecializationCostBound addZeroBody value := by
  have hproof := specialize_payloadLength_le_cost
    addZeroAxiomProof (binaryNumeralTerm value)
  have hcost := specializationCost_binaryNumeralTerm_le addZeroBody value
  exact hproof.trans (Nat.add_le_add_left hcost _)

theorem proveBinaryNumeralMulZero_verifier_eq_true
    (value : Nat) :
    listedCompactCertifiedPAProofVerifier
      (proveMulZero (binaryNumeralTerm value)).code
      (FoundationPudlakQuantitativeConditions.compactFormulaCode
        (“!!(binaryNumeralTerm value) * 0 = 0” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  proveMulZero_verifier_eq_true (binaryNumeralTerm value)

theorem proveBinaryNumeralMulZero_payloadLength_le
    (value : Nat) :
    (proveMulZero (binaryNumeralTerm value)).payloadLength <=
      mulZeroAxiomProof.payloadLength +
        binaryNumeralSpecializationCostBound mulZeroBody value := by
  have hproof := specialize_payloadLength_le_cost
    mulZeroAxiomProof (binaryNumeralTerm value)
  have hcost := specializationCost_binaryNumeralTerm_le mulZeroBody value
  exact hproof.trans (Nat.add_le_add_left hcost _)

theorem proveBinaryNumeralMulOne_verifier_eq_true
    (value : Nat) :
    listedCompactCertifiedPAProofVerifier
      (proveMulOne (binaryNumeralTerm value)).code
      (FoundationPudlakQuantitativeConditions.compactFormulaCode
        (“!!(binaryNumeralTerm value) * 1 = !!(binaryNumeralTerm value)” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  proveMulOne_verifier_eq_true (binaryNumeralTerm value)

theorem proveBinaryNumeralMulOne_payloadLength_le
    (value : Nat) :
    (proveMulOne (binaryNumeralTerm value)).payloadLength <=
      mulOneAxiomProof.payloadLength +
        binaryNumeralSpecializationCostBound mulOneBody value := by
  have hproof := specialize_payloadLength_le_cost
    mulOneAxiomProof (binaryNumeralTerm value)
  have hcost := specializationCost_binaryNumeralTerm_le mulOneBody value
  exact hproof.trans (Nat.add_le_add_left hcost _)

#print axioms specializationCost_binaryNumeralTerm_le
#print axioms proveBinaryNumeralReflexivity_verifier_eq_true
#print axioms proveBinaryNumeralReflexivity_payloadLength_le
#print axioms proveBinaryNumeralAddZero_payloadLength_le

end FoundationCompactPABinaryNumeralCompiler
