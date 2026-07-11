import Foundation.FirstOrder.Bootstrapping.FixedPoint
import integration.FoundationCompactBinaryNumeralTerm
import integration.FoundationCompactCertifiedDerivationSpecialization
import integration.FoundationCompactDerivationSpecialization
import integration.FoundationCompactListedMinProofLength

/-!
# Quantitative specialization of Foundation's parameterized diagonal proof

For each fixed two-variable predicate, Foundation supplies one universal
diagonal proof.  This file converts that fixed proof once to the concrete PA
`Derivation2` calculus and specializes it with the explicit cubic compiler.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactParameterizedDiagonalSpecialization

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactDerivationSpecialization
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedCertifiedVerifier
open FoundationCompactListedMinProofLength
open FoundationCompactCertifiedDerivationSpecialization

/-- The one-bound-variable body of Foundation's parameterized fixed point. -/
def parameterizedDiagonalBody
    (predicate : LO.FirstOrder.ArithmeticSemisentence 2) :
    LO.FirstOrder.ArithmeticSemisentence 1 :=
  LO.FirstOrder.Arithmetic.parameterizedFixedpoint predicate 🡘
    predicate/[⌜LO.FirstOrder.Arithmetic.parameterizedFixedpoint predicate⌝, #0]

/-- Embed the closed-free-variable body into the public PA proposition syntax. -/
def embeddedParameterizedDiagonalBody
    (predicate : LO.FirstOrder.ArithmeticSemisentence 2) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  Rewriting.emb (parameterizedDiagonalBody predicate)

/-- The fixed universal diagonal proof, converted once to the concrete
`Derivation2` proof system used by the checker. -/
noncomputable def parameterizedDiagonalBaseDerivation
    (predicate : LO.FirstOrder.ArithmeticSemisentence 2) :
    LO.FirstOrder.Derivation2 PA
      {∀⁰ embeddedParameterizedDiagonalBody predicate} := by
  have hprovable :
      PA ⊢ ∀⁰ parameterizedDiagonalBody predicate := by
    simpa [parameterizedDiagonalBody] using
      (LO.FirstOrder.Arithmetic.parameterized_diagonal₁
        (T := PA) predicate)
  have hderivable : Nonempty
      (LO.FirstOrder.Derivation2 PA
        {(Rewriting.emb (∀⁰ parameterizedDiagonalBody predicate) :
          LO.FirstOrder.ArithmeticProposition)}) :=
    (LO.FirstOrder.provable_iff_derivable2 (T := PA)).mp hprovable
  simpa [embeddedParameterizedDiagonalBody] using Classical.choice hderivable

/-- Specialize the fixed diagonal proof at any closed arithmetic term. -/
def parameterizedDiagonalInstanceDerivation
    (predicate : LO.FirstOrder.ArithmeticSemisentence 2)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.Derivation2 PA
      {(embeddedParameterizedDiagonalBody predicate)/[witness]} :=
  specializeDerivation
    (parameterizedDiagonalBaseDerivation predicate) witness

theorem parameterizedDiagonalInstance_tree_valid
    (predicate : LO.FirstOrder.ArithmeticSemisentence 2)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (CheckedPAProofTree.ofDerivation
      (parameterizedDiagonalInstanceDerivation predicate witness)).Valid :=
  CheckedPAProofTree.valid_ofDerivation _

/-- The varying diagonal instance has an explicit cubic proof-code bound;
the fixed universal base proof contributes only a predicate-dependent constant. -/
theorem parameterizedDiagonalInstance_binaryProofLength_le_cubic
    (predicate : LO.FirstOrder.ArithmeticSemisentence 2)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    let formula := embeddedParameterizedDiagonalBody predicate
    let scale := (binaryFormulaCode formula).length +
      (binaryTermCode witness).length + 1
    binaryProofLength
        (parameterizedDiagonalInstanceDerivation predicate witness) <=
      binaryProofLength (parameterizedDiagonalBaseDerivation predicate) + 128 +
        2048 * scale * scale * scale := by
  simpa [parameterizedDiagonalInstanceDerivation] using
    specializeDerivation_binaryProofLength_le_cubic
      (parameterizedDiagonalBaseDerivation predicate) witness

/-- The concrete diagonal proof specialized at the short binary numeral for
`value`. -/
def parameterizedDiagonalNatInstanceDerivation
    (predicate : LO.FirstOrder.ArithmeticSemisentence 2)
    (value : Nat) :
    LO.FirstOrder.Derivation2 PA
      {(embeddedParameterizedDiagonalBody predicate)/[binaryNumeralTerm value]} :=
  parameterizedDiagonalInstanceDerivation predicate
    (binaryNumeralTerm value)

theorem parameterizedDiagonalNatInstance_tree_valid
    (predicate : LO.FirstOrder.ArithmeticSemisentence 2)
    (value : Nat) :
    (CheckedPAProofTree.ofDerivation
      (parameterizedDiagonalNatInstanceDerivation predicate value)).Valid :=
  CheckedPAProofTree.valid_ofDerivation _

/-- Formula-level quantitative diagonalization in the genuine binary input
length.  All coefficients are closed definitions once `predicate` is fixed. -/
theorem parameterizedDiagonalNatInstance_binaryProofLength_le_sizePolynomial
    (predicate : LO.FirstOrder.ArithmeticSemisentence 2)
    (value : Nat) :
    let formula := embeddedParameterizedDiagonalBody predicate
    let bitScale := (binaryFormulaCode formula).length +
      (binaryTermCode arithmeticZeroTerm).length +
      binaryNumeralStepBudget * Nat.size value + 1
    binaryProofLength
        (parameterizedDiagonalNatInstanceDerivation predicate value) <=
      binaryProofLength (parameterizedDiagonalBaseDerivation predicate) + 128 +
        2048 * bitScale * bitScale * bitScale := by
  let formula := embeddedParameterizedDiagonalBody predicate
  let actualScale := (binaryFormulaCode formula).length +
    (binaryTermCode (binaryNumeralTerm value)).length + 1
  let bitScale := (binaryFormulaCode formula).length +
    (binaryTermCode arithmeticZeroTerm).length +
    binaryNumeralStepBudget * Nat.size value + 1
  have hterm := binaryNumeralTerm_code_length_le_size value
  have hscale : actualScale <= bitScale := by
    simp only [actualScale, bitScale]
    omega
  have hscaleCube :
      actualScale * actualScale * actualScale <=
        bitScale * bitScale * bitScale :=
    Nat.mul_le_mul (Nat.mul_le_mul hscale hscale) hscale
  have hscaledCube :
      2048 * actualScale * actualScale * actualScale <=
        2048 * bitScale * bitScale * bitScale := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2048 hscaleCube
  have hgeneric :=
    parameterizedDiagonalInstance_binaryProofLength_le_cubic
      predicate (binaryNumeralTerm value)
  change binaryProofLength
      (parameterizedDiagonalNatInstanceDerivation predicate value) <=
    binaryProofLength (parameterizedDiagonalBaseDerivation predicate) + 128 +
      2048 * bitScale * bitScale * bitScale
  apply hgeneric.trans
  exact Nat.add_le_add_left hscaledCube
    (binaryProofLength (parameterizedDiagonalBaseDerivation predicate) + 128)

/-- Actual proof-plus-certificate code for the binary-numeral diagonal
instance, on the public verifier coordinate. -/
noncomputable def parameterizedDiagonalNatCertifiedCode
    (predicate : LO.FirstOrder.ArithmeticSemisentence 2)
    (value : Nat) : Nat :=
  specializedCertifiedCode
    (parameterizedDiagonalBaseDerivation predicate)
    (binaryNumeralTerm value)

theorem parameterizedDiagonalNatCertifiedCode_verifier_eq_true
    (predicate : LO.FirstOrder.ArithmeticSemisentence 2)
    (value : Nat) :
    listedCompactCertifiedPAProofVerifier
      (parameterizedDiagonalNatCertifiedCode predicate value)
      (FoundationPudlakQuantitativeConditions.compactFormulaCode
        ((embeddedParameterizedDiagonalBody predicate)/[binaryNumeralTerm value])) = true := by
  simpa [parameterizedDiagonalNatCertifiedCode] using
    specializedCertifiedCode_verifier_eq_true
      (parameterizedDiagonalBaseDerivation predicate)
      (binaryNumeralTerm value)

theorem parameterizedDiagonalNatCertifiedCode_proofOf
    (predicate : LO.FirstOrder.ArithmeticSemisentence 2)
    (value : Nat) :
    ListedCertifiedPAProofOf
      (parameterizedDiagonalNatCertifiedCode predicate value)
      ((embeddedParameterizedDiagonalBody predicate)/[binaryNumeralTerm value]) := by
  exact parameterizedDiagonalNatCertifiedCode_verifier_eq_true predicate value

/-- The complete public payload, including the structural certificate, has a
cubic bound in the genuine binary length of `value`. -/
theorem parameterizedDiagonalNatCertifiedCode_payloadLength_le_sizePolynomial
    (predicate : LO.FirstOrder.ArithmeticSemisentence 2)
    (value : Nat) :
    let formula := embeddedParameterizedDiagonalBody predicate
    let base := parameterizedDiagonalBaseDerivation predicate
    let bitScale := (binaryFormulaCode formula).length +
      (binaryTermCode arithmeticZeroTerm).length +
      binaryNumeralStepBudget * Nat.size value + 1
    packedPayloadLength
        (parameterizedDiagonalNatCertifiedCode predicate value) <=
      binaryProofLength base +
        (binaryStructuralValidityCertificateCode
          (certificateOfDerivation base)).length + 192 +
        2048 * bitScale * bitScale * bitScale := by
  let formula := embeddedParameterizedDiagonalBody predicate
  let base := parameterizedDiagonalBaseDerivation predicate
  let actualScale := (binaryFormulaCode formula).length +
    (binaryTermCode (binaryNumeralTerm value)).length + 1
  let bitScale := (binaryFormulaCode formula).length +
    (binaryTermCode arithmeticZeroTerm).length +
    binaryNumeralStepBudget * Nat.size value + 1
  have hterm := binaryNumeralTerm_code_length_le_size value
  have hscale : actualScale <= bitScale := by
    simp only [actualScale, bitScale]
    omega
  have hscaleCube :
      actualScale * actualScale * actualScale <=
        bitScale * bitScale * bitScale :=
    Nat.mul_le_mul (Nat.mul_le_mul hscale hscale) hscale
  have hscaledCube :
      2048 * actualScale * actualScale * actualScale <=
        2048 * bitScale * bitScale * bitScale := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2048 hscaleCube
  have hgeneric := specializedCertifiedCode_payloadLength_le_cubic
    base (binaryNumeralTerm value)
  change packedPayloadLength
      (parameterizedDiagonalNatCertifiedCode predicate value) <=
    binaryProofLength base +
      (binaryStructuralValidityCertificateCode
        (certificateOfDerivation base)).length + 192 +
      2048 * bitScale * bitScale * bitScale
  apply hgeneric.trans
  exact Nat.add_le_add_left hscaledCube
    (binaryProofLength base +
      (binaryStructuralValidityCertificateCode
        (certificateOfDerivation base)).length + 192)

/-- The exact minimum on the project's public full-payload coordinate inherits
the explicit diagonal-instance polynomial bound. -/
theorem minListedCertifiedPAProofPayloadLength_parameterizedDiagonal_le
    (predicate : LO.FirstOrder.ArithmeticSemisentence 2)
    (value : Nat) :
    let formula := embeddedParameterizedDiagonalBody predicate
    let base := parameterizedDiagonalBaseDerivation predicate
    let bitScale := (binaryFormulaCode formula).length +
      (binaryTermCode arithmeticZeroTerm).length +
      binaryNumeralStepBudget * Nat.size value + 1
    minListedCertifiedPAProofPayloadLength
        (formula/[binaryNumeralTerm value]) <=
      binaryProofLength base +
        (binaryStructuralValidityCertificateCode
          (certificateOfDerivation base)).length + 192 +
        2048 * bitScale * bitScale * bitScale := by
  exact (minListedCertifiedPAProofPayloadLength_le_of_accept
      (parameterizedDiagonalNatCertifiedCode_proofOf predicate value)).trans
    (parameterizedDiagonalNatCertifiedCode_payloadLength_le_sizePolynomial
      predicate value)

#print axioms parameterizedDiagonalBaseDerivation
#print axioms parameterizedDiagonalInstanceDerivation
#print axioms parameterizedDiagonalInstance_tree_valid
#print axioms parameterizedDiagonalInstance_binaryProofLength_le_cubic
#print axioms parameterizedDiagonalNatInstanceDerivation
#print axioms parameterizedDiagonalNatInstance_tree_valid
#print axioms parameterizedDiagonalNatInstance_binaryProofLength_le_sizePolynomial
#print axioms parameterizedDiagonalNatCertifiedCode_verifier_eq_true
#print axioms parameterizedDiagonalNatCertifiedCode_payloadLength_le_sizePolynomial
#print axioms parameterizedDiagonalNatCertifiedCode_proofOf
#print axioms minListedCertifiedPAProofPayloadLength_parameterizedDiagonal_le

end FoundationCompactParameterizedDiagonalSpecialization
