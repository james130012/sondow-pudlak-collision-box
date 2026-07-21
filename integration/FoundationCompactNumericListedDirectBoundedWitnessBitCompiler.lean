import integration.FoundationCompactNumericListedDirectBoundedWitnessBounds
import integration.FoundationCompactPABitMembershipTraceBudgetBounds

/-!
# One public bit-proof budget for the bounded direct witness
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBoundedWitnessBitCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectBoundedProofWitness
open FoundationCompactNumericListedDirectWitnessBounds
open FoundationCompactNumericListedDirectBoundedWitnessBounds
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitMembershipRuleCompilerBounds
open FoundationCompactPABitMembershipTraceBudgetBounds

def directBoundedWitnessUniformBitPayloadPolynomial
    (bound formulaCodeSize : Nat) : Nat :=
  let bitBudget :=
    directBoundedWitnessBitWeightPolynomial bound formulaCodeSize
  binaryBitTraceBudgetPayloadPolynomial bitBudget bitBudget

theorem directBoundedWitnessCoordinateLimit_le_bitWeightPolynomial
    (bound formulaCodeSize : Nat) :
    directBoundedWitnessCoordinateLimit bound <=
      directBoundedWitnessBitWeightPolynomial bound formulaCodeSize := by
  have hfactor : 1 <=
      directBoundedWitnessFuelLimit bound *
        compactNumericVerifierStepWitnessColumnCount := by
    unfold directBoundedWitnessFuelLimit
      directBoundedWitnessStreamWeight
      compactNumericVerifierPublicFuelWeightBound
      compactNumericDecodedTokenListWeightBound
      compactNumericVerifierStepWitnessColumnCount
    omega
  have hcoordinateWidth :
      directBoundedWitnessCoordinateLimit bound <=
        directBoundedWitnessTraceWidthLimit bound := by
    calc
      directBoundedWitnessCoordinateLimit bound =
          1 * directBoundedWitnessCoordinateLimit bound := by omega
      _ <=
          (directBoundedWitnessFuelLimit bound *
              compactNumericVerifierStepWitnessColumnCount) *
            directBoundedWitnessCoordinateLimit bound :=
        Nat.mul_le_mul_right
          (directBoundedWitnessCoordinateLimit bound) hfactor
      _ = directBoundedWitnessTraceWidthLimit bound := by
        unfold directBoundedWitnessTraceWidthLimit
        ring
  unfold directBoundedWitnessBitWeightPolynomial
  omega

theorem directBoundedWitnessField_size_le_publicBudget
    {bound formulaCode value : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode)
    (hmem : value ∈ directWitnessValues bounded.witness) :
    Nat.size value <=
      directBoundedWitnessBitWeightPolynomial
        bound (Nat.size formulaCode) := by
  exact (directWitnessField_size_le_bitWeight bounded.witness hmem).trans
    (directBoundedWitness_bitWeight_le bounded)

theorem proveBinaryBitLiteralAtShortNumerals_checked_directWitnessField
    {bound formulaCode index value : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode)
    (hindex : index <
      directBoundedWitnessBitWeightPolynomial
        bound (Nat.size formulaCode))
    (hmem : value ∈ directWitnessValues bounded.witness) :
    listedCompactCertifiedPAProofVerifier
        (proveBinaryBitLiteralAtShortNumeralsPolynomial
          value index).code
        (compactFormulaCode
          (binaryBitShortLiteralFormula
            (value.testBit index) index value)) = true /\
      (proveBinaryBitLiteralAtShortNumeralsPolynomial
        value index).payloadLength <=
        directBoundedWitnessUniformBitPayloadPolynomial
          bound (Nat.size formulaCode) := by
  let bitBudget := directBoundedWitnessBitWeightPolynomial
    bound (Nat.size formulaCode)
  have hvalue : Nat.size value <= bitBudget := by
    simpa only [bitBudget] using
      directBoundedWitnessField_size_le_publicBudget bounded hmem
  simpa only [directBoundedWitnessUniformBitPayloadPolynomial, bitBudget] using
    proveBinaryBitLiteralAtShortNumerals_checked_traceBudget
      (coordinateBound := bitBudget) (traceWidth := bitBudget)
      hindex hvalue

theorem proveBinaryBitLiteralAtShortNumerals_checked_directRowCoordinate
    {bound formulaCode index value : Nat}
    (hindex : index <
      directBoundedWitnessBitWeightPolynomial
        bound (Nat.size formulaCode))
    (hvalue : Nat.size value <=
      directBoundedWitnessCoordinateLimit bound) :
    listedCompactCertifiedPAProofVerifier
        (proveBinaryBitLiteralAtShortNumeralsPolynomial
          value index).code
        (compactFormulaCode
          (binaryBitShortLiteralFormula
            (value.testBit index) index value)) = true /\
      (proveBinaryBitLiteralAtShortNumeralsPolynomial
        value index).payloadLength <=
        directBoundedWitnessUniformBitPayloadPolynomial
          bound (Nat.size formulaCode) := by
  let bitBudget := directBoundedWitnessBitWeightPolynomial
    bound (Nat.size formulaCode)
  have hvaluePublic : Nat.size value <= bitBudget := by
    exact hvalue.trans
      (directBoundedWitnessCoordinateLimit_le_bitWeightPolynomial
        bound (Nat.size formulaCode))
  simpa only [directBoundedWitnessUniformBitPayloadPolynomial, bitBudget] using
    proveBinaryBitLiteralAtShortNumerals_checked_traceBudget
      (coordinateBound := bitBudget) (traceWidth := bitBudget)
      hindex hvaluePublic

#print axioms
  directBoundedWitnessCoordinateLimit_le_bitWeightPolynomial
#print axioms directBoundedWitnessField_size_le_publicBudget
#print axioms
  proveBinaryBitLiteralAtShortNumerals_checked_directWitnessField
#print axioms
  proveBinaryBitLiteralAtShortNumerals_checked_directRowCoordinate

end FoundationCompactNumericListedDirectBoundedWitnessBitCompiler
