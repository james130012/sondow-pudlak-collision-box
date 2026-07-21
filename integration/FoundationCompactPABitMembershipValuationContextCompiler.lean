import integration.FoundationCompactCertifiedContextConnectives
import integration.FoundationCompactPABitMembershipArgumentTransport
import integration.FoundationCompactPABitMembershipRuleCompilerBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactPAValuationTermCompiler

/-!
# Fast bit literals at arbitrary valuation terms

Positive bit facts are transported forward along checked term equalities.
Negative bit facts use the reverse positive implications and checked modus
tollens, so no separate negative transport principle is assumed.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABitMembershipValuationContextCompiler

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitMembershipRuleCompilerBounds
open FoundationCompactPABitMembershipArgumentTransport
open FoundationCompactPAEmbeddedPredicateFreeVariables

def binaryBitValuationContext
    (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm) :
    Finset LO.FirstOrder.ArithmeticProposition :=
  valuationContext
    (indexTerm.freeVariables ∪ valueTerm.freeVariables) valuation

def binaryBitAtValuationFormula
    (expected : Bool)
    (indexTerm valueTerm : ValuationTerm) : ValuationFormula :=
  binaryBitLiteralAtTerms expected indexTerm valueTerm

theorem binaryBitAtValuationFormula_freeVariables_subset
    (expected : Bool)
    (indexTerm valueTerm : ValuationTerm) :
    (binaryBitAtValuationFormula expected indexTerm valueTerm).freeVariables ⊆
      indexTerm.freeVariables ∪ valueTerm.freeVariables := by
  cases expected
  · simpa [binaryBitAtValuationFormula, binaryBitLiteralAtTerms,
      binaryBitAtomAtTerms] using
        (embeddedBinarySubstitution_freeVariables_subset
          bitDef.val indexTerm valueTerm)
  · exact embeddedBinarySubstitution_freeVariables_subset
      bitDef.val indexTerm valueTerm

noncomputable def compilePositiveBinaryBitAtValuation
    (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm)
    (hbit : (termValue valuation valueTerm).testBit
      (termValue valuation indexTerm) = true) :
    CertifiedPAContextProof
      (binaryBitValuationContext valuation indexTerm valueTerm)
      (binaryBitAtValuationFormula true indexTerm valueTerm) := by
  let index := termValue valuation indexTerm
  let value := termValue valuation valueTerm
  let shortIndex := shortBinaryNumeralTerm index
  let shortValue := shortBinaryNumeralTerm value
  let Gamma := binaryBitValuationContext valuation indexTerm valueTerm

  let sourceRaw := proveBinaryBitLiteralAtShortNumeralsPolynomial value index
  have hsourceFormula :
      binaryBitShortLiteralFormula (value.testBit index) index value =
        binaryBitLiteralAtTerms true shortIndex shortValue := by
    unfold binaryBitShortLiteralFormula
    rw [hbit]
  let source : CertifiedPAProof
      (binaryBitLiteralAtTerms true shortIndex shortValue) :=
    CertifiedPAProof.cast hsourceFormula sourceRaw
  let sourceInContext := CertifiedPAContextProof.weakenCertified Gamma source

  have hindexVariables : indexTerm.freeVariables ⊆
      indexTerm.freeVariables ∪ valueTerm.freeVariables :=
    Finset.subset_union_left
  have hvalueVariables : valueTerm.freeVariables ⊆
      indexTerm.freeVariables ∪ valueTerm.freeVariables :=
    Finset.subset_union_right
  let indexEqualityRaw := compileTermValueEquality valuation indexTerm
  let indexEquality := CertifiedPAContextProof.weakenContext indexEqualityRaw
    (valuationContext_mono valuation hindexVariables)
  let indexTransport := CertifiedPAContextProof.weakenCertified Gamma
    (binaryBitIndexTransportImplication
      shortIndex indexTerm shortValue)
  let indexTransportAfterEquality :=
    CertifiedPAContextProof.modusPonens indexTransport indexEquality
  let indexFact := CertifiedPAContextProof.modusPonens
    indexTransportAfterEquality sourceInContext

  let valueEqualityRaw := compileTermValueEquality valuation valueTerm
  let valueEquality := CertifiedPAContextProof.weakenContext valueEqualityRaw
    (valuationContext_mono valuation hvalueVariables)
  let valueTransport := CertifiedPAContextProof.weakenCertified Gamma
    (binaryBitValueTransportImplication
      indexTerm shortValue valueTerm)
  let valueTransportAfterEquality :=
    CertifiedPAContextProof.modusPonens valueTransport valueEquality
  let result := CertifiedPAContextProof.modusPonens
    valueTransportAfterEquality indexFact
  exact result

noncomputable def compileNegativeBinaryBitAtValuation
    (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm)
    (hbit : (termValue valuation valueTerm).testBit
      (termValue valuation indexTerm) = false) :
    CertifiedPAContextProof
      (binaryBitValuationContext valuation indexTerm valueTerm)
      (binaryBitAtValuationFormula false indexTerm valueTerm) := by
  let index := termValue valuation indexTerm
  let value := termValue valuation valueTerm
  let shortIndex := shortBinaryNumeralTerm index
  let shortValue := shortBinaryNumeralTerm value
  let Gamma := binaryBitValuationContext valuation indexTerm valueTerm

  let sourceRaw := proveBinaryBitLiteralAtShortNumeralsPolynomial value index
  have hsourceFormula :
      binaryBitShortLiteralFormula (value.testBit index) index value =
        binaryBitLiteralAtTerms false shortIndex shortValue := by
    unfold binaryBitShortLiteralFormula
    rw [hbit]
  let source : CertifiedPAProof
      (binaryBitLiteralAtTerms false shortIndex shortValue) :=
    CertifiedPAProof.cast hsourceFormula sourceRaw
  let sourceInContext := CertifiedPAContextProof.weakenCertified Gamma source

  have hindexVariables : indexTerm.freeVariables ⊆
      indexTerm.freeVariables ∪ valueTerm.freeVariables :=
    Finset.subset_union_left
  have hvalueVariables : valueTerm.freeVariables ⊆
      indexTerm.freeVariables ∪ valueTerm.freeVariables :=
    Finset.subset_union_right
  let indexEqualityRaw := compileTermValueEquality valuation indexTerm
  let indexEqualityForward := CertifiedPAContextProof.weakenContext
    indexEqualityRaw (valuationContext_mono valuation hindexVariables)
  let indexEqualityReverse := CertifiedPAContextProof.equalitySymmetry
    shortIndex indexTerm indexEqualityForward
  let reverseIndexTransport := CertifiedPAContextProof.weakenCertified Gamma
    (binaryBitIndexTransportImplication
      indexTerm shortIndex shortValue)
  let reverseIndexImplication := CertifiedPAContextProof.modusPonens
    reverseIndexTransport indexEqualityReverse
  let indexNegative := CertifiedPAContextProof.modusTollens
    reverseIndexImplication sourceInContext

  let valueEqualityRaw := compileTermValueEquality valuation valueTerm
  let valueEqualityForward := CertifiedPAContextProof.weakenContext
    valueEqualityRaw (valuationContext_mono valuation hvalueVariables)
  let valueEqualityReverse := CertifiedPAContextProof.equalitySymmetry
    shortValue valueTerm valueEqualityForward
  let reverseValueTransport := CertifiedPAContextProof.weakenCertified Gamma
    (binaryBitValueTransportImplication
      indexTerm valueTerm shortValue)
  let reverseValueImplication := CertifiedPAContextProof.modusPonens
    reverseValueTransport valueEqualityReverse
  let result := CertifiedPAContextProof.modusTollens
    reverseValueImplication indexNegative
  exact result

noncomputable def compileBinaryBitLiteralAtValuation
    (expected : Bool)
    (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm)
    (hbit : (termValue valuation valueTerm).testBit
      (termValue valuation indexTerm) = expected) :
    CertifiedPAContextProof
      (binaryBitValuationContext valuation indexTerm valueTerm)
      (binaryBitAtValuationFormula expected indexTerm valueTerm) := by
  cases expected with
  | false =>
      exact compileNegativeBinaryBitAtValuation
        valuation indexTerm valueTerm hbit
  | true =>
      exact compilePositiveBinaryBitAtValuation
        valuation indexTerm valueTerm hbit

#print axioms compilePositiveBinaryBitAtValuation
#print axioms compileNegativeBinaryBitAtValuation
#print axioms compileBinaryBitLiteralAtValuation

end FoundationCompactPABitMembershipValuationContextCompiler
