import integration.FoundationCompactPABitMembershipRuleCompilerBounds

/-!
# Uniform bit-membership proof bounds inside a bounded trace

The exact bit compiler is charged against `Nat.size value + index + 1`.
This file absorbs both varying coordinates into one trace-level budget.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABitMembershipTraceBudgetBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitMembershipRuleCompilerBounds

theorem binaryBitRecursivePayloadPolynomial_mono
    {small large : Nat} (hbudget : small <= large) :
    binaryBitRecursivePayloadPolynomial small <=
      binaryBitRecursivePayloadPolynomial large := by
  unfold binaryBitRecursivePayloadPolynomial
  exact Nat.add_le_add
    (binaryBitBasePayloadCumulative_mono hbudget)
    (Nat.mul_le_mul hbudget
      (binaryBitRecursiveStepPayloadCumulative_mono hbudget))

def binaryBitTraceBudgetPayloadPolynomial
    (coordinateBound traceWidth : Nat) : Nat :=
  binaryBitRecursivePayloadPolynomial
    (coordinateBound + traceWidth + 1)

theorem binaryBitWorkBudget_le_traceBudget
    {index value coordinateBound traceWidth : Nat}
    (hindex : index < traceWidth)
    (hvalue : Nat.size value <= coordinateBound) :
    binaryBitWorkBudget index value <=
      coordinateBound + traceWidth + 1 := by
  unfold binaryBitWorkBudget
  omega

theorem binaryBitLiteralPayloadPolynomial_le_traceBudget
    {index value coordinateBound traceWidth : Nat}
    (hindex : index < traceWidth)
    (hvalue : Nat.size value <= coordinateBound) :
    binaryBitLiteralPayloadPolynomial index value <=
      binaryBitTraceBudgetPayloadPolynomial coordinateBound traceWidth := by
  unfold binaryBitLiteralPayloadPolynomial
  unfold binaryBitTraceBudgetPayloadPolynomial
  exact binaryBitRecursivePayloadPolynomial_mono
    (binaryBitWorkBudget_le_traceBudget hindex hvalue)

theorem proveBinaryBitLiteralAtShortNumerals_checked_traceBudget
    {index value coordinateBound traceWidth : Nat}
    (hindex : index < traceWidth)
    (hvalue : Nat.size value <= coordinateBound) :
    listedCompactCertifiedPAProofVerifier
        (proveBinaryBitLiteralAtShortNumeralsPolynomial
          value index).code
        (compactFormulaCode
          (binaryBitShortLiteralFormula
            (value.testBit index) index value)) = true /\
      (proveBinaryBitLiteralAtShortNumeralsPolynomial
        value index).payloadLength <=
        binaryBitTraceBudgetPayloadPolynomial coordinateBound traceWidth := by
  have hchecked :=
    proveBinaryBitLiteralAtShortNumerals_checked_polynomial index value
  exact ⟨hchecked.1, hchecked.2.trans
    (binaryBitLiteralPayloadPolynomial_le_traceBudget hindex hvalue)⟩

#print axioms binaryBitRecursivePayloadPolynomial_mono
#print axioms binaryBitWorkBudget_le_traceBudget
#print axioms binaryBitLiteralPayloadPolynomial_le_traceBudget
#print axioms proveBinaryBitLiteralAtShortNumerals_checked_traceBudget

end FoundationCompactPABitMembershipTraceBudgetBounds
