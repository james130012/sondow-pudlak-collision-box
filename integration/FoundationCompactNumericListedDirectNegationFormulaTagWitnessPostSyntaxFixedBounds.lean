import integration.FoundationCompactNumericListedDirectNegationFormulaTagAtomicFixedBounds
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-!
# Fixed post-substitution resources for negation-tag witnesses

After substituting the bounded witness, each parity branch is a closed
right-associated conjunction of three checked atomic certificates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 40000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNegationFormulaTagWitnessPostFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate
open FoundationCompactNumericListedDirectNegationFormulaTagAtomicFixedBounds

private abbrev tagZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation

def negationFormulaTagWitnessPostSyntaxPolynomial (bitBound : Nat) : Nat :=
  64 * (orderAtomicFormulaCodeEnvelope
    (negationFormulaTagAtomicTermCodePolynomial bitBound) + 1)

def negationFormulaTagWitnessPostFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (negationFormulaTagWitnessPostSyntaxPolynomial bitBound)
    (negationFormulaTagAtomicFixedPayloadPolynomial bitBound)
    (negationFormulaTagAtomicFixedPayloadPolynomial bitBound)
    (negationFormulaTagAtomicFixedPayloadPolynomial bitBound)

theorem threeAtomicConjunctionCode_le
    (formula1 formula2 formula3 : ValuationFormula)
    (bitBound : Nat)
    (h1 : (binaryFormulaCode formula1).length <=
      orderAtomicFormulaCodeEnvelope
        (negationFormulaTagAtomicTermCodePolynomial bitBound))
    (h2 : (binaryFormulaCode formula2).length <=
      orderAtomicFormulaCodeEnvelope
        (negationFormulaTagAtomicTermCodePolynomial bitBound))
    (h3 : (binaryFormulaCode formula3).length <=
      orderAtomicFormulaCodeEnvelope
        (negationFormulaTagAtomicTermCodePolynomial bitBound)) :
    (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <=
      negationFormulaTagWitnessPostSyntaxPolynomial bitBound := by
  have hinner :=
    binaryFormulaCode_and_length_le_local formula2 formula3
  have houter :=
    binaryFormulaCode_and_length_le_local formula1 (formula2 ⋏ formula3)
  have htag4 : (binaryNatCode 4).length <= 32 := by decide
  unfold negationFormulaTagWitnessPostSyntaxPolynomial
  omega

theorem evenPostFormula_code_le
    (tag mapped pair bitBound : Nat)
    (hpair : pair < 4)
    (htagSize : Nat.size tag <= bitBound)
    (hmappedSize : Nat.size mapped <= bitBound) :
    (binaryFormulaCode
      (“!!(shortBinaryNumeralTerm pair) < 4” ⋏
        (“!!(shortBinaryNumeralTerm tag) =
            2 * !!(shortBinaryNumeralTerm pair)” ⋏
          “!!(shortBinaryNumeralTerm mapped) =
            !!(shortBinaryNumeralTerm tag) + 1”))).length <=
      negationFormulaTagWitnessPostSyntaxPolynomial bitBound := by
  have hpairFormula := lessThanFormula_code_le_orderAtomic
    (shortBinaryNumeralTerm pair) (‘4’ : ValuationTerm)
    (negationFormulaTagAtomicTermCodePolynomial bitBound)
    (pairShortNumeralCode_le pair bitBound hpair) (tagFourCode_le bitBound)
  have hequalityFormula := equalityFormula_code_le_orderAtomic
    (shortBinaryNumeralTerm tag)
    (‘2 * !!(shortBinaryNumeralTerm pair)’ : ValuationTerm)
    (negationFormulaTagAtomicTermCodePolynomial bitBound)
    (tagShortNumeralCode_le tag bitBound htagSize)
    (tagMulTwoPairCode_le pair bitBound hpair)
  have hsuccessorFormula := equalityFormula_code_le_orderAtomic
    (shortBinaryNumeralTerm mapped)
    (‘!!(shortBinaryNumeralTerm tag) + 1’ : ValuationTerm)
    (negationFormulaTagAtomicTermCodePolynomial bitBound)
    (tagShortNumeralCode_le mapped bitBound hmappedSize)
    (tagShortAddOneCode_le tag bitBound htagSize)
  exact threeAtomicConjunctionCode_le _ _ _ bitBound hpairFormula
    hequalityFormula hsuccessorFormula

theorem oddPostFormula_code_le
    (tag mapped pair bitBound : Nat)
    (hpair : pair < 4)
    (htagSize : Nat.size tag <= bitBound)
    (hmappedSize : Nat.size mapped <= bitBound) :
    (binaryFormulaCode
      (“!!(shortBinaryNumeralTerm pair) < 4” ⋏
        (“!!(shortBinaryNumeralTerm tag) =
            2 * !!(shortBinaryNumeralTerm pair) + 1” ⋏
          “!!(shortBinaryNumeralTerm tag) =
            !!(shortBinaryNumeralTerm mapped) + 1”))).length <=
      negationFormulaTagWitnessPostSyntaxPolynomial bitBound := by
  have hpairFormula := lessThanFormula_code_le_orderAtomic
    (shortBinaryNumeralTerm pair) (‘4’ : ValuationTerm)
    (negationFormulaTagAtomicTermCodePolynomial bitBound)
    (pairShortNumeralCode_le pair bitBound hpair) (tagFourCode_le bitBound)
  have hequalityFormula := equalityFormula_code_le_orderAtomic
    (shortBinaryNumeralTerm tag)
    (‘2 * !!(shortBinaryNumeralTerm pair) + 1’ : ValuationTerm)
    (negationFormulaTagAtomicTermCodePolynomial bitBound)
    (tagShortNumeralCode_le tag bitBound htagSize)
    (tagMulTwoPairAddOneCode_le pair bitBound hpair)
  have hsuccessorFormula := equalityFormula_code_le_orderAtomic
    (shortBinaryNumeralTerm tag)
    (‘!!(shortBinaryNumeralTerm mapped) + 1’ : ValuationTerm)
    (negationFormulaTagAtomicTermCodePolynomial bitBound)
    (tagShortNumeralCode_le tag bitBound htagSize)
    (tagShortAddOneCode_le mapped bitBound hmappedSize)
  exact threeAtomicConjunctionCode_le _ _ _ bitBound hpairFormula
    hequalityFormula hsuccessorFormula

theorem evenPostFormula_closed (tag mapped pair : Nat) :
    (“!!(shortBinaryNumeralTerm pair) < 4” ⋏
      (“!!(shortBinaryNumeralTerm tag) =
          2 * !!(shortBinaryNumeralTerm pair)” ⋏
        “!!(shortBinaryNumeralTerm mapped) =
          !!(shortBinaryNumeralTerm tag) + 1”)).freeVariables = ∅ := by
  simp [shortBinaryNumeralTerm_freeVariables_eq_empty,
    LO.FirstOrder.Semiterm.Operator.operator]
  exact ⟨tagMulTwoPair_freeVariables_eq_empty pair,
    tagShortAddOne_freeVariables_eq_empty tag⟩

theorem oddPostFormula_closed (tag mapped pair : Nat) :
    (“!!(shortBinaryNumeralTerm pair) < 4” ⋏
      (“!!(shortBinaryNumeralTerm tag) =
          2 * !!(shortBinaryNumeralTerm pair) + 1” ⋏
        “!!(shortBinaryNumeralTerm tag) =
          !!(shortBinaryNumeralTerm mapped) + 1”)).freeVariables = ∅ := by
  simp [shortBinaryNumeralTerm_freeVariables_eq_empty,
    LO.FirstOrder.Semiterm.Operator.operator]
  exact ⟨tagMulTwoPairAddOne_freeVariables_eq_empty pair,
    tagShortAddOne_freeVariables_eq_empty mapped⟩

end FoundationCompactNumericListedDirectNegationFormulaTagWitnessPostFixedBounds
