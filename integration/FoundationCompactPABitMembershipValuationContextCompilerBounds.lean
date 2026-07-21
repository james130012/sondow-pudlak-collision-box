import integration.FoundationCompactPABitMembershipValuationContextCompiler
import integration.FoundationCompactPABitMembershipRuleCompilerBounds
import integration.FoundationCompactPAValuationTermCompilerBounds

/-!
# Payload bounds for bit literals at valuation terms

The resources below follow the positive and negative compiler trees literally.
They have no proof, proof-length, or caller-supplied bound arguments.  The
short-numeral source is charged to `binaryBitLiteralPayloadPolynomial`; term
equalities use the valuation-term compiler resource; transport implications
use their three concrete specialization costs; and all contextual assembly
costs retain the actual encoded formulas and valuation context.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABitMembershipValuationContextCompilerBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitMembershipRuleCompilerBounds
open FoundationCompactPABitMembershipArgumentTransport
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerBounds
open FoundationCompactPABitMembershipValuationContextCompiler

/-! ## The short-numeral source used by the valuation compiler -/

theorem proveBinaryBitLiteralAtShortNumerals_payloadLength_le_polynomial
    (index value : Nat) :
    (proveBinaryBitLiteralAtShortNumeralsPolynomial
      value index).payloadLength <=
      binaryBitLiteralPayloadPolynomial index value :=
  proveBinaryBitLiteralAtShortNumeralsPolynomial_payloadLength_le index value

/-! ## Quantitative specialization for argument transport -/

def binaryBitIndexTransportPayloadResource
    (leftIndex rightIndex value :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  binaryBitIndexTransportUniversalProof.payloadLength +
    specializationCost binaryBitIndexTransportOuterBody leftIndex +
    specializationCost
      (binaryBitIndexTransportMiddleBody leftIndex) rightIndex +
    specializationCost
      (binaryBitIndexTransportInnerBody leftIndex rightIndex) value

theorem binaryBitIndexTransportImplication_payloadLength_le_resource
    (leftIndex rightIndex value :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryBitIndexTransportImplication
      leftIndex rightIndex value).payloadLength <=
        binaryBitIndexTransportPayloadResource
          leftIndex rightIndex value := by
  have hraw := specializeThriceWithCasts_payloadLength_le
    binaryBitIndexTransportUniversalProof
    leftIndex rightIndex value
    (binaryBitIndexTransportAfterFirst_formula leftIndex)
    (binaryBitIndexTransportAfterSecond_formula leftIndex rightIndex)
    (binaryBitIndexTransportFinal_formula leftIndex rightIndex value)
  simpa [binaryBitIndexTransportImplication,
    binaryBitIndexTransportPayloadResource] using hraw

def binaryBitValueTransportPayloadResource
    (index leftValue rightValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  binaryBitValueTransportUniversalProof.payloadLength +
    specializationCost binaryBitValueTransportOuterBody index +
    specializationCost
      (binaryBitValueTransportMiddleBody index) leftValue +
    specializationCost
      (binaryBitValueTransportInnerBody index leftValue) rightValue

theorem binaryBitValueTransportImplication_payloadLength_le_resource
    (index leftValue rightValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryBitValueTransportImplication
      index leftValue rightValue).payloadLength <=
        binaryBitValueTransportPayloadResource
          index leftValue rightValue := by
  have hraw := specializeThriceWithCasts_payloadLength_le
    binaryBitValueTransportUniversalProof
    index leftValue rightValue
    (binaryBitValueTransportAfterFirst_formula index)
    (binaryBitValueTransportAfterSecond_formula index leftValue)
    (binaryBitValueTransportFinal_formula index leftValue rightValue)
  simpa [binaryBitValueTransportImplication,
    binaryBitValueTransportPayloadResource] using hraw

def binaryBitEqualitySymmetryImplicationPayloadResource
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  equalitySymmetryAxiomProof.payloadLength +
    specializationCost equalitySymmetryOuterBody left +
    specializationCost (equalitySymmetryInnerBody left) right

theorem equalitySymmetryImplication_payloadLength_le_binaryBitResource
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (equalitySymmetryImplication left right).payloadLength <=
      binaryBitEqualitySymmetryImplicationPayloadResource left right := by
  simpa [binaryBitEqualitySymmetryImplicationPayloadResource] using
    (CertifiedPAProof.equalitySymmetryImplication_payloadLength_le
      left right)

/-! ## Formula coordinates -/

def binaryBitValuationSourceFormula
    (expected : Bool) (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm) : ValuationFormula :=
  binaryBitLiteralAtTerms expected
    (shortBinaryNumeralTerm (termValue valuation indexTerm))
    (shortBinaryNumeralTerm (termValue valuation valueTerm))

def binaryBitValuationSourceAtomFormula
    (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm) : ValuationFormula :=
  binaryBitAtomAtTerms
    (shortBinaryNumeralTerm (termValue valuation indexTerm))
    (shortBinaryNumeralTerm (termValue valuation valueTerm))

def binaryBitValuationIndexEqualityFormula
    (valuation : Nat -> Nat) (indexTerm : ValuationTerm) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm (termValue valuation indexTerm)) =
    !!indexTerm”

def binaryBitValuationIndexReverseEqualityFormula
    (valuation : Nat -> Nat) (indexTerm : ValuationTerm) :
    ValuationFormula :=
  “!!indexTerm =
    !!(shortBinaryNumeralTerm (termValue valuation indexTerm))”

def binaryBitValuationIndexAtomFormula
    (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm) : ValuationFormula :=
  binaryBitAtomAtTerms indexTerm
    (shortBinaryNumeralTerm (termValue valuation valueTerm))

def binaryBitValuationValueEqualityFormula
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm (termValue valuation valueTerm)) =
    !!valueTerm”

def binaryBitValuationValueReverseEqualityFormula
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm) :
    ValuationFormula :=
  “!!valueTerm =
    !!(shortBinaryNumeralTerm (termValue valuation valueTerm))”

def binaryBitValuationResultAtomFormula
    (indexTerm valueTerm : ValuationTerm) : ValuationFormula :=
  binaryBitAtomAtTerms indexTerm valueTerm

/-! ## Positive compiler -/

/-- Complete input-computable payload resource for the positive compiler. -/
def compilePositiveBinaryBitAtValuationPayloadResource
    (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm) : Nat :=
  let index := termValue valuation indexTerm
  let value := termValue valuation valueTerm
  let shortIndex := shortBinaryNumeralTerm index
  let shortValue := shortBinaryNumeralTerm value
  let Gamma := binaryBitValuationContext valuation indexTerm valueTerm
  let sourceFormula := binaryBitValuationSourceFormula true
    valuation indexTerm valueTerm
  let indexEqualityFormula := binaryBitValuationIndexEqualityFormula
    valuation indexTerm
  let indexFactFormula := binaryBitValuationIndexAtomFormula
    valuation indexTerm valueTerm
  let valueEqualityFormula := binaryBitValuationValueEqualityFormula
    valuation valueTerm
  let resultFormula := binaryBitValuationResultAtomFormula
    indexTerm valueTerm
  let indexTransportConsequent := sourceFormula 🡒 indexFactFormula
  let valueTransportConsequent := indexFactFormula 🡒 resultFormula
  binaryBitLiteralPayloadPolynomial index value +
    weakeningFullAssemblyCost (insert sourceFormula Gamma) +
    compileTermValueEqualityPayloadResource valuation indexTerm +
    weakeningFullAssemblyCost (insert indexEqualityFormula Gamma) +
    binaryBitIndexTransportPayloadResource
      shortIndex indexTerm shortValue +
    weakeningFullAssemblyCost
      (insert (indexEqualityFormula 🡒 indexTransportConsequent) Gamma) +
    contextualModusPonensFullAssemblyCost Gamma
      indexEqualityFormula indexTransportConsequent +
    contextualModusPonensFullAssemblyCost Gamma
      sourceFormula indexFactFormula +
    compileTermValueEqualityPayloadResource valuation valueTerm +
    weakeningFullAssemblyCost (insert valueEqualityFormula Gamma) +
    binaryBitValueTransportPayloadResource
      indexTerm shortValue valueTerm +
    weakeningFullAssemblyCost
      (insert (valueEqualityFormula 🡒 valueTransportConsequent) Gamma) +
    contextualModusPonensFullAssemblyCost Gamma
      valueEqualityFormula valueTransportConsequent +
    contextualModusPonensFullAssemblyCost Gamma
      indexFactFormula resultFormula

theorem compilePositiveBinaryBitAtValuation_payloadLength_le_resource
    (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm)
    (hbit : (termValue valuation valueTerm).testBit
      (termValue valuation indexTerm) = true) :
    (compilePositiveBinaryBitAtValuation
      valuation indexTerm valueTerm hbit).payloadLength <=
        compilePositiveBinaryBitAtValuationPayloadResource
          valuation indexTerm valueTerm := by
  let index := termValue valuation indexTerm
  let value := termValue valuation valueTerm
  let shortIndex := shortBinaryNumeralTerm index
  let shortValue := shortBinaryNumeralTerm value
  let Gamma := binaryBitValuationContext valuation indexTerm valueTerm
  let sourceFormula : ValuationFormula :=
    binaryBitValuationSourceFormula true valuation indexTerm valueTerm
  let indexEqualityFormula : ValuationFormula :=
    binaryBitValuationIndexEqualityFormula valuation indexTerm
  let indexFactFormula : ValuationFormula :=
    binaryBitValuationIndexAtomFormula valuation indexTerm valueTerm
  let valueEqualityFormula : ValuationFormula :=
    binaryBitValuationValueEqualityFormula valuation valueTerm
  let resultFormula : ValuationFormula :=
    binaryBitValuationResultAtomFormula indexTerm valueTerm
  let indexTransportConsequent := sourceFormula 🡒 indexFactFormula
  let valueTransportConsequent := indexFactFormula 🡒 resultFormula

  let sourceRaw := proveBinaryBitLiteralAtShortNumeralsPolynomial value index
  have hsourceFormula :
      binaryBitShortLiteralFormula (value.testBit index) index value =
        sourceFormula := by
    dsimp only [sourceFormula, binaryBitValuationSourceFormula,
      shortIndex, shortValue, index, value]
    unfold binaryBitShortLiteralFormula
    rw [hbit]
  let source : CertifiedPAProof sourceFormula :=
    CertifiedPAProof.cast hsourceFormula sourceRaw
  let sourceInContext : CertifiedPAContextProof Gamma sourceFormula :=
    CertifiedPAContextProof.weakenCertified Gamma source
  have hsource : source.payloadLength <=
      binaryBitLiteralPayloadPolynomial index value := by
    calc
      source.payloadLength = sourceRaw.payloadLength := by
        dsimp only [source]
        exact CertifiedPAProof.cast_payloadLength hsourceFormula sourceRaw
      _ <= binaryBitLiteralPayloadPolynomial index value :=
        proveBinaryBitLiteralAtShortNumerals_payloadLength_le_polynomial
          index value
  have hsourceInContext : sourceInContext.payloadLength <=
      binaryBitLiteralPayloadPolynomial index value +
        weakeningFullAssemblyCost (insert sourceFormula Gamma) := by
    calc
      sourceInContext.payloadLength <= source.payloadLength +
          weakeningFullAssemblyCost (insert sourceFormula Gamma) := by
        dsimp only [sourceInContext]
        exact CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma source
      _ <= binaryBitLiteralPayloadPolynomial index value +
          weakeningFullAssemblyCost (insert sourceFormula Gamma) :=
        Nat.add_le_add_right hsource _

  have hindexVariables : indexTerm.freeVariables ⊆
      indexTerm.freeVariables ∪ valueTerm.freeVariables :=
    Finset.subset_union_left
  let indexEqualityRaw := compileTermValueEquality valuation indexTerm
  let indexEquality : CertifiedPAContextProof Gamma indexEqualityFormula :=
    CertifiedPAContextProof.weakenContext indexEqualityRaw
      (valuationContext_mono valuation hindexVariables)
  have hindexEqualityRaw : indexEqualityRaw.payloadLength <=
      compileTermValueEqualityPayloadResource valuation indexTerm :=
    compileTermValueEquality_payloadLength_le_resource valuation indexTerm
  have hindexEquality : indexEquality.payloadLength <=
      compileTermValueEqualityPayloadResource valuation indexTerm +
        weakeningFullAssemblyCost
          (insert indexEqualityFormula Gamma) := by
    calc
      indexEquality.payloadLength <= indexEqualityRaw.payloadLength +
          weakeningFullAssemblyCost
            (insert indexEqualityFormula Gamma) := by
        dsimp only [indexEquality]
        exact CertifiedPAContextProof.weakenContext_payloadLength_le
          indexEqualityRaw
          (valuationContext_mono valuation hindexVariables)
      _ <= compileTermValueEqualityPayloadResource valuation indexTerm +
          weakeningFullAssemblyCost
            (insert indexEqualityFormula Gamma) :=
        Nat.add_le_add_right hindexEqualityRaw _

  let indexTransportClosed := binaryBitIndexTransportImplication
    shortIndex indexTerm shortValue
  let indexTransport : CertifiedPAContextProof Gamma
      (indexEqualityFormula 🡒 indexTransportConsequent) :=
    CertifiedPAContextProof.weakenCertified Gamma indexTransportClosed
  have hindexTransportClosed : indexTransportClosed.payloadLength <=
      binaryBitIndexTransportPayloadResource
        shortIndex indexTerm shortValue := by
    dsimp only [indexTransportClosed]
    exact binaryBitIndexTransportImplication_payloadLength_le_resource
      shortIndex indexTerm shortValue
  have hindexTransport : indexTransport.payloadLength <=
      binaryBitIndexTransportPayloadResource shortIndex indexTerm shortValue +
        weakeningFullAssemblyCost
          (insert (indexEqualityFormula 🡒 indexTransportConsequent)
            Gamma) := by
    calc
      indexTransport.payloadLength <= indexTransportClosed.payloadLength +
          weakeningFullAssemblyCost
            (insert (indexEqualityFormula 🡒 indexTransportConsequent)
              Gamma) := by
        dsimp only [indexTransport]
        exact CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma indexTransportClosed
      _ <= binaryBitIndexTransportPayloadResource
            shortIndex indexTerm shortValue +
          weakeningFullAssemblyCost
            (insert (indexEqualityFormula 🡒 indexTransportConsequent)
              Gamma) := Nat.add_le_add_right hindexTransportClosed _

  let indexTransportAfterEquality :=
    CertifiedPAContextProof.modusPonens indexTransport indexEquality
  have hindexTransportAfterEquality :
      indexTransportAfterEquality.payloadLength <=
        indexTransport.payloadLength + indexEquality.payloadLength +
          contextualModusPonensFullAssemblyCost Gamma
            indexEqualityFormula indexTransportConsequent := by
    dsimp only [indexTransportAfterEquality]
    exact CertifiedPAContextProof.modusPonens_payloadLength_le
      indexTransport indexEquality
  let indexFact := CertifiedPAContextProof.modusPonens
    indexTransportAfterEquality sourceInContext
  have hindexFact : indexFact.payloadLength <=
      indexTransportAfterEquality.payloadLength +
        sourceInContext.payloadLength +
        contextualModusPonensFullAssemblyCost Gamma
          sourceFormula indexFactFormula := by
    dsimp only [indexFact]
    exact CertifiedPAContextProof.modusPonens_payloadLength_le
      indexTransportAfterEquality sourceInContext

  have hvalueVariables : valueTerm.freeVariables ⊆
      indexTerm.freeVariables ∪ valueTerm.freeVariables :=
    Finset.subset_union_right
  let valueEqualityRaw := compileTermValueEquality valuation valueTerm
  let valueEquality : CertifiedPAContextProof Gamma valueEqualityFormula :=
    CertifiedPAContextProof.weakenContext valueEqualityRaw
      (valuationContext_mono valuation hvalueVariables)
  have hvalueEqualityRaw : valueEqualityRaw.payloadLength <=
      compileTermValueEqualityPayloadResource valuation valueTerm :=
    compileTermValueEquality_payloadLength_le_resource valuation valueTerm
  have hvalueEquality : valueEquality.payloadLength <=
      compileTermValueEqualityPayloadResource valuation valueTerm +
        weakeningFullAssemblyCost
          (insert valueEqualityFormula Gamma) := by
    calc
      valueEquality.payloadLength <= valueEqualityRaw.payloadLength +
          weakeningFullAssemblyCost
            (insert valueEqualityFormula Gamma) := by
        dsimp only [valueEquality]
        exact CertifiedPAContextProof.weakenContext_payloadLength_le
          valueEqualityRaw
          (valuationContext_mono valuation hvalueVariables)
      _ <= compileTermValueEqualityPayloadResource valuation valueTerm +
          weakeningFullAssemblyCost
            (insert valueEqualityFormula Gamma) :=
        Nat.add_le_add_right hvalueEqualityRaw _

  let valueTransportClosed := binaryBitValueTransportImplication
    indexTerm shortValue valueTerm
  let valueTransport : CertifiedPAContextProof Gamma
      (valueEqualityFormula 🡒 valueTransportConsequent) :=
    CertifiedPAContextProof.weakenCertified Gamma valueTransportClosed
  have hvalueTransportClosed : valueTransportClosed.payloadLength <=
      binaryBitValueTransportPayloadResource
        indexTerm shortValue valueTerm := by
    dsimp only [valueTransportClosed]
    exact binaryBitValueTransportImplication_payloadLength_le_resource
      indexTerm shortValue valueTerm
  have hvalueTransport : valueTransport.payloadLength <=
      binaryBitValueTransportPayloadResource indexTerm shortValue valueTerm +
        weakeningFullAssemblyCost
          (insert (valueEqualityFormula 🡒 valueTransportConsequent)
            Gamma) := by
    calc
      valueTransport.payloadLength <= valueTransportClosed.payloadLength +
          weakeningFullAssemblyCost
            (insert (valueEqualityFormula 🡒 valueTransportConsequent)
              Gamma) := by
        dsimp only [valueTransport]
        exact CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma valueTransportClosed
      _ <= binaryBitValueTransportPayloadResource
            indexTerm shortValue valueTerm +
          weakeningFullAssemblyCost
            (insert (valueEqualityFormula 🡒 valueTransportConsequent)
              Gamma) := Nat.add_le_add_right hvalueTransportClosed _

  let valueTransportAfterEquality :=
    CertifiedPAContextProof.modusPonens valueTransport valueEquality
  have hvalueTransportAfterEquality :
      valueTransportAfterEquality.payloadLength <=
        valueTransport.payloadLength + valueEquality.payloadLength +
          contextualModusPonensFullAssemblyCost Gamma
            valueEqualityFormula valueTransportConsequent := by
    dsimp only [valueTransportAfterEquality]
    exact CertifiedPAContextProof.modusPonens_payloadLength_le
      valueTransport valueEquality
  let result := CertifiedPAContextProof.modusPonens
    valueTransportAfterEquality indexFact
  have hresult : result.payloadLength <=
      valueTransportAfterEquality.payloadLength + indexFact.payloadLength +
        contextualModusPonensFullAssemblyCost Gamma
          indexFactFormula resultFormula := by
    dsimp only [result]
    exact CertifiedPAContextProof.modusPonens_payloadLength_le
      valueTransportAfterEquality indexFact
  have hcompiled :
      (compilePositiveBinaryBitAtValuation
        valuation indexTerm valueTerm hbit).payloadLength =
          result.payloadLength := by
    rfl
  rw [hcompiled]
  unfold compilePositiveBinaryBitAtValuationPayloadResource
  dsimp only [Gamma, index, value, shortIndex, shortValue,
    sourceFormula, indexEqualityFormula, indexFactFormula,
    valueEqualityFormula, resultFormula, indexTransportConsequent,
    valueTransportConsequent] at *
  omega

/-! ## Negative compiler -/

/-- Complete input-computable payload resource for the negative compiler. -/
def compileNegativeBinaryBitAtValuationPayloadResource
    (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm) : Nat :=
  let index := termValue valuation indexTerm
  let value := termValue valuation valueTerm
  let shortIndex := shortBinaryNumeralTerm index
  let shortValue := shortBinaryNumeralTerm value
  let Gamma := binaryBitValuationContext valuation indexTerm valueTerm
  let sourceFormula := binaryBitValuationSourceFormula false
    valuation indexTerm valueTerm
  let sourceAtom := binaryBitValuationSourceAtomFormula
    valuation indexTerm valueTerm
  let indexEqualityFormula := binaryBitValuationIndexEqualityFormula
    valuation indexTerm
  let indexReverseEqualityFormula :=
    binaryBitValuationIndexReverseEqualityFormula valuation indexTerm
  let indexAtom := binaryBitValuationIndexAtomFormula
    valuation indexTerm valueTerm
  let valueEqualityFormula := binaryBitValuationValueEqualityFormula
    valuation valueTerm
  let valueReverseEqualityFormula :=
    binaryBitValuationValueReverseEqualityFormula valuation valueTerm
  let resultAtom := binaryBitValuationResultAtomFormula
    indexTerm valueTerm
  let reverseIndexTransportConsequent := indexAtom 🡒 sourceAtom
  let reverseValueTransportConsequent := resultAtom 🡒 indexAtom
  binaryBitLiteralPayloadPolynomial index value +
    weakeningFullAssemblyCost (insert sourceFormula Gamma) +
    compileTermValueEqualityPayloadResource valuation indexTerm +
    weakeningFullAssemblyCost (insert indexEqualityFormula Gamma) +
    binaryBitEqualitySymmetryImplicationPayloadResource
      shortIndex indexTerm +
    weakeningFullAssemblyCost
      (insert (indexEqualityFormula 🡒 indexReverseEqualityFormula)
        Gamma) +
    contextualModusPonensFullAssemblyCost Gamma
      indexEqualityFormula indexReverseEqualityFormula +
    binaryBitIndexTransportPayloadResource
      indexTerm shortIndex shortValue +
    weakeningFullAssemblyCost
      (insert
        (indexReverseEqualityFormula 🡒 reverseIndexTransportConsequent)
        Gamma) +
    contextualModusPonensFullAssemblyCost Gamma
      indexReverseEqualityFormula reverseIndexTransportConsequent +
    modusTollensFullAssemblyCost Gamma indexAtom sourceAtom +
    compileTermValueEqualityPayloadResource valuation valueTerm +
    weakeningFullAssemblyCost (insert valueEqualityFormula Gamma) +
    binaryBitEqualitySymmetryImplicationPayloadResource
      shortValue valueTerm +
    weakeningFullAssemblyCost
      (insert (valueEqualityFormula 🡒 valueReverseEqualityFormula)
        Gamma) +
    contextualModusPonensFullAssemblyCost Gamma
      valueEqualityFormula valueReverseEqualityFormula +
    binaryBitValueTransportPayloadResource
      indexTerm valueTerm shortValue +
    weakeningFullAssemblyCost
      (insert
        (valueReverseEqualityFormula 🡒 reverseValueTransportConsequent)
        Gamma) +
    contextualModusPonensFullAssemblyCost Gamma
      valueReverseEqualityFormula reverseValueTransportConsequent +
    modusTollensFullAssemblyCost Gamma resultAtom indexAtom

theorem compileNegativeBinaryBitAtValuation_payloadLength_le_resource
    (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm)
    (hbit : (termValue valuation valueTerm).testBit
      (termValue valuation indexTerm) = false) :
    (compileNegativeBinaryBitAtValuation
      valuation indexTerm valueTerm hbit).payloadLength <=
        compileNegativeBinaryBitAtValuationPayloadResource
          valuation indexTerm valueTerm := by
  let index := termValue valuation indexTerm
  let value := termValue valuation valueTerm
  let shortIndex := shortBinaryNumeralTerm index
  let shortValue := shortBinaryNumeralTerm value
  let Gamma := binaryBitValuationContext valuation indexTerm valueTerm
  let sourceFormula : ValuationFormula :=
    binaryBitValuationSourceFormula false valuation indexTerm valueTerm
  let sourceAtom : ValuationFormula :=
    binaryBitValuationSourceAtomFormula valuation indexTerm valueTerm
  let indexEqualityFormula : ValuationFormula :=
    binaryBitValuationIndexEqualityFormula valuation indexTerm
  let indexReverseEqualityFormula : ValuationFormula :=
    binaryBitValuationIndexReverseEqualityFormula valuation indexTerm
  let indexAtom : ValuationFormula :=
    binaryBitValuationIndexAtomFormula valuation indexTerm valueTerm
  let valueEqualityFormula : ValuationFormula :=
    binaryBitValuationValueEqualityFormula valuation valueTerm
  let valueReverseEqualityFormula : ValuationFormula :=
    binaryBitValuationValueReverseEqualityFormula valuation valueTerm
  let resultAtom : ValuationFormula :=
    binaryBitValuationResultAtomFormula indexTerm valueTerm
  let reverseIndexTransportConsequent := indexAtom 🡒 sourceAtom
  let reverseValueTransportConsequent := resultAtom 🡒 indexAtom

  let sourceRaw := proveBinaryBitLiteralAtShortNumeralsPolynomial value index
  have hsourceFormula :
      binaryBitShortLiteralFormula (value.testBit index) index value =
        sourceFormula := by
    dsimp only [sourceFormula, binaryBitValuationSourceFormula,
      shortIndex, shortValue, index, value]
    unfold binaryBitShortLiteralFormula
    rw [hbit]
  let source : CertifiedPAProof sourceFormula :=
    CertifiedPAProof.cast hsourceFormula sourceRaw
  let sourceInContext : CertifiedPAContextProof Gamma sourceFormula :=
    CertifiedPAContextProof.weakenCertified Gamma source
  have hsource : source.payloadLength <=
      binaryBitLiteralPayloadPolynomial index value := by
    calc
      source.payloadLength = sourceRaw.payloadLength := by
        dsimp only [source]
        exact CertifiedPAProof.cast_payloadLength hsourceFormula sourceRaw
      _ <= binaryBitLiteralPayloadPolynomial index value :=
        proveBinaryBitLiteralAtShortNumerals_payloadLength_le_polynomial
          index value
  have hsourceInContext : sourceInContext.payloadLength <=
      binaryBitLiteralPayloadPolynomial index value +
        weakeningFullAssemblyCost (insert sourceFormula Gamma) := by
    calc
      sourceInContext.payloadLength <= source.payloadLength +
          weakeningFullAssemblyCost (insert sourceFormula Gamma) := by
        dsimp only [sourceInContext]
        exact CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma source
      _ <= binaryBitLiteralPayloadPolynomial index value +
          weakeningFullAssemblyCost (insert sourceFormula Gamma) :=
        Nat.add_le_add_right hsource _

  have hindexVariables : indexTerm.freeVariables ⊆
      indexTerm.freeVariables ∪ valueTerm.freeVariables :=
    Finset.subset_union_left
  let indexEqualityRaw := compileTermValueEquality valuation indexTerm
  let indexEqualityForward : CertifiedPAContextProof Gamma
      indexEqualityFormula :=
    CertifiedPAContextProof.weakenContext indexEqualityRaw
      (valuationContext_mono valuation hindexVariables)
  have hindexEqualityRaw : indexEqualityRaw.payloadLength <=
      compileTermValueEqualityPayloadResource valuation indexTerm :=
    compileTermValueEquality_payloadLength_le_resource valuation indexTerm
  have hindexEqualityForward : indexEqualityForward.payloadLength <=
      compileTermValueEqualityPayloadResource valuation indexTerm +
        weakeningFullAssemblyCost
          (insert indexEqualityFormula Gamma) := by
    calc
      indexEqualityForward.payloadLength <= indexEqualityRaw.payloadLength +
          weakeningFullAssemblyCost
            (insert indexEqualityFormula Gamma) := by
        dsimp only [indexEqualityForward]
        exact CertifiedPAContextProof.weakenContext_payloadLength_le
          indexEqualityRaw
          (valuationContext_mono valuation hindexVariables)
      _ <= compileTermValueEqualityPayloadResource valuation indexTerm +
          weakeningFullAssemblyCost
            (insert indexEqualityFormula Gamma) :=
        Nat.add_le_add_right hindexEqualityRaw _

  let indexEqualityReverse : CertifiedPAContextProof Gamma
      indexReverseEqualityFormula :=
    CertifiedPAContextProof.equalitySymmetry
      shortIndex indexTerm indexEqualityForward
  have hindexSymmetryImplication :
      (equalitySymmetryImplication
        shortIndex indexTerm).payloadLength <=
          binaryBitEqualitySymmetryImplicationPayloadResource
            shortIndex indexTerm :=
    equalitySymmetryImplication_payloadLength_le_binaryBitResource
      shortIndex indexTerm
  have hindexEqualityReverseConstructor :=
    CertifiedPAContextProof.equalitySymmetry_payloadLength_le
      shortIndex indexTerm indexEqualityForward
  have hindexEqualityReverse : indexEqualityReverse.payloadLength <=
      compileTermValueEqualityPayloadResource valuation indexTerm +
        weakeningFullAssemblyCost (insert indexEqualityFormula Gamma) +
        binaryBitEqualitySymmetryImplicationPayloadResource
          shortIndex indexTerm +
        weakeningFullAssemblyCost
          (insert (indexEqualityFormula 🡒 indexReverseEqualityFormula)
            Gamma) +
        contextualModusPonensFullAssemblyCost Gamma
          indexEqualityFormula indexReverseEqualityFormula := by
    dsimp only [indexEqualityReverse, indexEqualityFormula,
      indexReverseEqualityFormula,
      binaryBitValuationIndexEqualityFormula,
      binaryBitValuationIndexReverseEqualityFormula,
      shortIndex, index] at
      *
    omega

  let reverseIndexTransportClosed := binaryBitIndexTransportImplication
    indexTerm shortIndex shortValue
  let reverseIndexTransport : CertifiedPAContextProof Gamma
      (indexReverseEqualityFormula 🡒 reverseIndexTransportConsequent) :=
    CertifiedPAContextProof.weakenCertified Gamma
      reverseIndexTransportClosed
  have hreverseIndexTransportClosed :
      reverseIndexTransportClosed.payloadLength <=
        binaryBitIndexTransportPayloadResource
          indexTerm shortIndex shortValue := by
    dsimp only [reverseIndexTransportClosed]
    exact binaryBitIndexTransportImplication_payloadLength_le_resource
      indexTerm shortIndex shortValue
  have hreverseIndexTransport : reverseIndexTransport.payloadLength <=
      binaryBitIndexTransportPayloadResource
          indexTerm shortIndex shortValue +
        weakeningFullAssemblyCost
          (insert
            (indexReverseEqualityFormula 🡒
              reverseIndexTransportConsequent) Gamma) := by
    calc
      reverseIndexTransport.payloadLength <=
          reverseIndexTransportClosed.payloadLength +
            weakeningFullAssemblyCost
              (insert
                (indexReverseEqualityFormula 🡒
                  reverseIndexTransportConsequent) Gamma) := by
        dsimp only [reverseIndexTransport]
        exact CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma reverseIndexTransportClosed
      _ <= binaryBitIndexTransportPayloadResource
              indexTerm shortIndex shortValue +
            weakeningFullAssemblyCost
              (insert
                (indexReverseEqualityFormula 🡒
                  reverseIndexTransportConsequent) Gamma) :=
        Nat.add_le_add_right hreverseIndexTransportClosed _

  let reverseIndexImplication := CertifiedPAContextProof.modusPonens
    reverseIndexTransport indexEqualityReverse
  have hreverseIndexImplication : reverseIndexImplication.payloadLength <=
      reverseIndexTransport.payloadLength +
        indexEqualityReverse.payloadLength +
        contextualModusPonensFullAssemblyCost Gamma
          indexReverseEqualityFormula reverseIndexTransportConsequent := by
    dsimp only [reverseIndexImplication]
    exact CertifiedPAContextProof.modusPonens_payloadLength_le
      reverseIndexTransport indexEqualityReverse
  let indexNegative : CertifiedPAContextProof Gamma (∼indexAtom) :=
    CertifiedPAContextProof.modusTollens
      reverseIndexImplication sourceInContext
  have hindexNegative : indexNegative.payloadLength <=
      reverseIndexImplication.payloadLength + sourceInContext.payloadLength +
        modusTollensFullAssemblyCost Gamma indexAtom sourceAtom := by
    dsimp only [indexNegative]
    exact CertifiedPAContextProof.modusTollens_payloadLength_le
      reverseIndexImplication sourceInContext

  have hvalueVariables : valueTerm.freeVariables ⊆
      indexTerm.freeVariables ∪ valueTerm.freeVariables :=
    Finset.subset_union_right
  let valueEqualityRaw := compileTermValueEquality valuation valueTerm
  let valueEqualityForward : CertifiedPAContextProof Gamma
      valueEqualityFormula :=
    CertifiedPAContextProof.weakenContext valueEqualityRaw
      (valuationContext_mono valuation hvalueVariables)
  have hvalueEqualityRaw : valueEqualityRaw.payloadLength <=
      compileTermValueEqualityPayloadResource valuation valueTerm :=
    compileTermValueEquality_payloadLength_le_resource valuation valueTerm
  have hvalueEqualityForward : valueEqualityForward.payloadLength <=
      compileTermValueEqualityPayloadResource valuation valueTerm +
        weakeningFullAssemblyCost
          (insert valueEqualityFormula Gamma) := by
    calc
      valueEqualityForward.payloadLength <= valueEqualityRaw.payloadLength +
          weakeningFullAssemblyCost
            (insert valueEqualityFormula Gamma) := by
        dsimp only [valueEqualityForward]
        exact CertifiedPAContextProof.weakenContext_payloadLength_le
          valueEqualityRaw
          (valuationContext_mono valuation hvalueVariables)
      _ <= compileTermValueEqualityPayloadResource valuation valueTerm +
          weakeningFullAssemblyCost
            (insert valueEqualityFormula Gamma) :=
        Nat.add_le_add_right hvalueEqualityRaw _

  let valueEqualityReverse : CertifiedPAContextProof Gamma
      valueReverseEqualityFormula :=
    CertifiedPAContextProof.equalitySymmetry
      shortValue valueTerm valueEqualityForward
  have hvalueSymmetryImplication :
      (equalitySymmetryImplication
        shortValue valueTerm).payloadLength <=
          binaryBitEqualitySymmetryImplicationPayloadResource
            shortValue valueTerm :=
    equalitySymmetryImplication_payloadLength_le_binaryBitResource
      shortValue valueTerm
  have hvalueEqualityReverseConstructor :=
    CertifiedPAContextProof.equalitySymmetry_payloadLength_le
      shortValue valueTerm valueEqualityForward
  have hvalueEqualityReverse : valueEqualityReverse.payloadLength <=
      compileTermValueEqualityPayloadResource valuation valueTerm +
        weakeningFullAssemblyCost (insert valueEqualityFormula Gamma) +
        binaryBitEqualitySymmetryImplicationPayloadResource
          shortValue valueTerm +
        weakeningFullAssemblyCost
          (insert (valueEqualityFormula 🡒 valueReverseEqualityFormula)
            Gamma) +
        contextualModusPonensFullAssemblyCost Gamma
          valueEqualityFormula valueReverseEqualityFormula := by
    dsimp only [valueEqualityReverse, valueEqualityFormula,
      valueReverseEqualityFormula,
      binaryBitValuationValueEqualityFormula,
      binaryBitValuationValueReverseEqualityFormula,
      shortValue, value] at
      *
    omega

  let reverseValueTransportClosed := binaryBitValueTransportImplication
    indexTerm valueTerm shortValue
  let reverseValueTransport : CertifiedPAContextProof Gamma
      (valueReverseEqualityFormula 🡒 reverseValueTransportConsequent) :=
    CertifiedPAContextProof.weakenCertified Gamma
      reverseValueTransportClosed
  have hreverseValueTransportClosed :
      reverseValueTransportClosed.payloadLength <=
        binaryBitValueTransportPayloadResource
          indexTerm valueTerm shortValue := by
    dsimp only [reverseValueTransportClosed]
    exact binaryBitValueTransportImplication_payloadLength_le_resource
      indexTerm valueTerm shortValue
  have hreverseValueTransport : reverseValueTransport.payloadLength <=
      binaryBitValueTransportPayloadResource indexTerm valueTerm shortValue +
        weakeningFullAssemblyCost
          (insert
            (valueReverseEqualityFormula 🡒
              reverseValueTransportConsequent) Gamma) := by
    calc
      reverseValueTransport.payloadLength <=
          reverseValueTransportClosed.payloadLength +
            weakeningFullAssemblyCost
              (insert
                (valueReverseEqualityFormula 🡒
                  reverseValueTransportConsequent) Gamma) := by
        dsimp only [reverseValueTransport]
        exact CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma reverseValueTransportClosed
      _ <= binaryBitValueTransportPayloadResource
              indexTerm valueTerm shortValue +
            weakeningFullAssemblyCost
              (insert
                (valueReverseEqualityFormula 🡒
                  reverseValueTransportConsequent) Gamma) :=
        Nat.add_le_add_right hreverseValueTransportClosed _

  let reverseValueImplication := CertifiedPAContextProof.modusPonens
    reverseValueTransport valueEqualityReverse
  have hreverseValueImplication : reverseValueImplication.payloadLength <=
      reverseValueTransport.payloadLength +
        valueEqualityReverse.payloadLength +
        contextualModusPonensFullAssemblyCost Gamma
          valueReverseEqualityFormula reverseValueTransportConsequent := by
    dsimp only [reverseValueImplication]
    exact CertifiedPAContextProof.modusPonens_payloadLength_le
      reverseValueTransport valueEqualityReverse
  let result : CertifiedPAContextProof Gamma (∼resultAtom) :=
    CertifiedPAContextProof.modusTollens
      reverseValueImplication indexNegative
  have hresult : result.payloadLength <=
      reverseValueImplication.payloadLength + indexNegative.payloadLength +
        modusTollensFullAssemblyCost Gamma resultAtom indexAtom := by
    dsimp only [result]
    exact CertifiedPAContextProof.modusTollens_payloadLength_le
      reverseValueImplication indexNegative
  have hcompiled :
      (compileNegativeBinaryBitAtValuation
        valuation indexTerm valueTerm hbit).payloadLength =
          result.payloadLength := by
    rfl
  rw [hcompiled]
  unfold compileNegativeBinaryBitAtValuationPayloadResource
  dsimp only [Gamma, index, value, shortIndex, shortValue,
    sourceFormula, sourceAtom, indexEqualityFormula,
    indexReverseEqualityFormula, indexAtom, valueEqualityFormula,
    valueReverseEqualityFormula, resultAtom,
    reverseIndexTransportConsequent,
    reverseValueTransportConsequent] at *
  omega

/-! ## Boolean, polynomial, and finite-family endpoints -/

def compileBinaryBitLiteralAtValuationPayloadResource
    (expected : Bool) (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm) : Nat :=
  if expected then
    compilePositiveBinaryBitAtValuationPayloadResource
      valuation indexTerm valueTerm
  else
    compileNegativeBinaryBitAtValuationPayloadResource
      valuation indexTerm valueTerm

theorem compileBinaryBitLiteralAtValuation_payloadLength_le_resource
    (expected : Bool) (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm)
    (hbit : (termValue valuation valueTerm).testBit
      (termValue valuation indexTerm) = expected) :
    (compileBinaryBitLiteralAtValuation expected
      valuation indexTerm valueTerm hbit).payloadLength <=
        compileBinaryBitLiteralAtValuationPayloadResource expected
          valuation indexTerm valueTerm := by
  cases expected with
  | false =>
      change
        (compileNegativeBinaryBitAtValuation
          valuation indexTerm valueTerm hbit).payloadLength <= _
      simpa [compileBinaryBitLiteralAtValuationPayloadResource] using
        (compileNegativeBinaryBitAtValuation_payloadLength_le_resource
          valuation indexTerm valueTerm hbit)
  | true =>
      change
        (compilePositiveBinaryBitAtValuation
          valuation indexTerm valueTerm hbit).payloadLength <= _
      simpa [compileBinaryBitLiteralAtValuationPayloadResource] using
        (compilePositiveBinaryBitAtValuation_payloadLength_le_resource
          valuation indexTerm valueTerm hbit)

def binaryBitValuationCompilerPayloadPolynomial (resource : Nat) : Nat :=
  resource * resource + 2 * resource + 1

theorem binaryBitValuationResource_le_fixedPolynomial (resource : Nat) :
    resource <= binaryBitValuationCompilerPayloadPolynomial resource := by
  unfold binaryBitValuationCompilerPayloadPolynomial
  calc
    resource <= 2 * resource := by omega
    _ <= resource * resource + 2 * resource := Nat.le_add_left _ _
    _ <= resource * resource + 2 * resource + 1 := Nat.le_add_right _ _

theorem compileBinaryBitLiteralAtValuation_payloadLength_le_fixedPolynomial
    (expected : Bool) (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm)
    (hbit : (termValue valuation valueTerm).testBit
      (termValue valuation indexTerm) = expected) :
    (compileBinaryBitLiteralAtValuation expected
      valuation indexTerm valueTerm hbit).payloadLength <=
        binaryBitValuationCompilerPayloadPolynomial
          (compileBinaryBitLiteralAtValuationPayloadResource expected
            valuation indexTerm valueTerm) := by
  exact
    (compileBinaryBitLiteralAtValuation_payloadLength_le_resource
      expected valuation indexTerm valueTerm hbit).trans
        (binaryBitValuationResource_le_fixedPolynomial _)

def fixedBinaryBitTermFamilyPayloadResource
    {literalCount : Nat} (valuation : Nat -> Nat)
    (expected : Fin literalCount -> Bool)
    (indexTerms valueTerms : Fin literalCount -> ValuationTerm) : Nat :=
  Finset.univ.sum (fun index =>
    compileBinaryBitLiteralAtValuationPayloadResource (expected index)
      valuation (indexTerms index) (valueTerms index))

theorem
    compileBinaryBitLiteralAtValuation_payloadLength_le_fixedTermFamilyPolynomial
    {literalCount : Nat} (valuation : Nat -> Nat)
    (expected : Fin literalCount -> Bool)
    (indexTerms valueTerms : Fin literalCount -> ValuationTerm)
    (index : Fin literalCount)
    (hbit : (termValue valuation (valueTerms index)).testBit
      (termValue valuation (indexTerms index)) = expected index) :
    (compileBinaryBitLiteralAtValuation (expected index) valuation
      (indexTerms index) (valueTerms index) hbit).payloadLength <=
      binaryBitValuationCompilerPayloadPolynomial
        (fixedBinaryBitTermFamilyPayloadResource valuation expected
          indexTerms valueTerms) := by
  have hpayload :=
    compileBinaryBitLiteralAtValuation_payloadLength_le_resource
      (expected index) valuation (indexTerms index) (valueTerms index) hbit
  have hmember :
      compileBinaryBitLiteralAtValuationPayloadResource (expected index)
          valuation (indexTerms index) (valueTerms index) <=
        fixedBinaryBitTermFamilyPayloadResource valuation expected
          indexTerms valueTerms := by
    unfold fixedBinaryBitTermFamilyPayloadResource
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        (compileBinaryBitLiteralAtValuationPayloadResource
          (expected candidate) valuation
          (indexTerms candidate) (valueTerms candidate)))
      (Finset.mem_univ index)
  exact hpayload.trans
    (hmember.trans (binaryBitValuationResource_le_fixedPolynomial _))

#print axioms
  proveBinaryBitLiteralAtShortNumerals_payloadLength_le_polynomial
#print axioms binaryBitIndexTransportImplication_payloadLength_le_resource
#print axioms binaryBitValueTransportImplication_payloadLength_le_resource
#print axioms
  compilePositiveBinaryBitAtValuation_payloadLength_le_resource
#print axioms
  compileNegativeBinaryBitAtValuation_payloadLength_le_resource
#print axioms
  compileBinaryBitLiteralAtValuation_payloadLength_le_resource
#print axioms
  compileBinaryBitLiteralAtValuation_payloadLength_le_fixedPolynomial
#print axioms
  compileBinaryBitLiteralAtValuation_payloadLength_le_fixedTermFamilyPolynomial

end FoundationCompactPABitMembershipValuationContextCompilerBounds
