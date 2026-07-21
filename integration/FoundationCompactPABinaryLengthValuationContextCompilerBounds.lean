import integration.FoundationCompactPABinaryLengthValuationContextCompiler
import integration.FoundationCompactPABinaryLengthRuleCompilerBounds
import integration.FoundationCompactPAValuationTermCompilerBounds

/-!
# Payload bounds for binary-length graphs at valuation terms

The main resource follows the valuation compiler node for node.  A short
bridge below identifies the original recursive short-numeral proof used by
that compiler with the already bounded polynomial construction.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABinaryLengthValuationContextCompilerBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryLengthRuleCompiler
open FoundationCompactPABinaryLengthRuleCompilerBounds
open FoundationCompactPABinaryLengthValueTransport
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerBounds
open FoundationCompactPABinaryLengthValuationContextCompiler

/-! ## The bounded short-numeral proof is the original proof -/

theorem proveBinaryLengthAtRecursiveSizePolynomial_zero :
    proveBinaryLengthAtRecursiveSizePolynomial 0 =
      binaryLengthZeroRecursiveProof := by
  unfold proveBinaryLengthAtRecursiveSizePolynomial
    boundedBinaryLengthRecursiveProof
  rw [Nat.binaryRec'_zero]
  rfl

theorem proveBinaryLengthAtRecursiveSizePolynomial_bit
    (bit : Bool) (value : Nat)
    (hcanonical : value = 0 -> bit = true) :
    proveBinaryLengthAtRecursiveSizePolynomial (Nat.bit bit value) =
      binaryLengthBitStep bit value hcanonical
        (proveBinaryLengthAtRecursiveSizePolynomial value) := by
  unfold proveBinaryLengthAtRecursiveSizePolynomial
    boundedBinaryLengthRecursiveProof
  rw [Nat.binaryRec'_eq
    (motive := fun candidate =>
      PolynomiallyBoundedBinaryLengthRecursiveProof candidate)
    bit value hcanonical]
  rfl

theorem proveBinaryLengthAtRecursiveSize_eq_polynomial (value : Nat) :
    proveBinaryLengthAtRecursiveSize value =
      proveBinaryLengthAtRecursiveSizePolynomial value := by
  induction value using Nat.binaryRec' with
  | zero =>
      calc
        proveBinaryLengthAtRecursiveSize 0 =
            binaryLengthZeroRecursiveProof :=
          proveBinaryLengthAtRecursiveSize_zero
        _ = proveBinaryLengthAtRecursiveSizePolynomial 0 :=
          proveBinaryLengthAtRecursiveSizePolynomial_zero.symm
  | bit bit value hcanonical inductionHypothesis =>
      calc
        proveBinaryLengthAtRecursiveSize (Nat.bit bit value) =
            binaryLengthBitStep bit value hcanonical
              (proveBinaryLengthAtRecursiveSize value) :=
          proveBinaryLengthAtRecursiveSize_bit bit value hcanonical
        _ = binaryLengthBitStep bit value hcanonical
              (proveBinaryLengthAtRecursiveSizePolynomial value) := by
          rw [inductionHypothesis]
        _ = proveBinaryLengthAtRecursiveSizePolynomial
              (Nat.bit bit value) :=
          (proveBinaryLengthAtRecursiveSizePolynomial_bit
            bit value hcanonical).symm

theorem proveBinaryLengthAtShortNumerals_eq_polynomial (value : Nat) :
    proveBinaryLengthAtShortNumerals value =
      proveBinaryLengthAtShortNumeralsPolynomial value := by
  unfold proveBinaryLengthAtShortNumerals
    proveBinaryLengthAtShortNumeralsPolynomial
  rw [proveBinaryLengthAtRecursiveSize_eq_polynomial]

theorem proveBinaryLengthAtShortNumerals_payloadLength_le_polynomial
    (value : Nat) :
    (proveBinaryLengthAtShortNumerals value).payloadLength <=
      binaryLengthAtShortNumeralsPayloadPolynomial (Nat.size value) := by
  rw [proveBinaryLengthAtShortNumerals_eq_polynomial]
  exact proveBinaryLengthAtShortNumeralsPolynomial_payloadLength_le value

/-! ## Explicit value-argument transport cost -/

def binaryLengthValueTransportPayloadResource
    (size leftValue rightValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  binaryLengthValueTransportUniversalProof.payloadLength +
    specializationCost binaryLengthValueTransportOuterBody size +
    specializationCost
      (binaryLengthValueTransportMiddleBody size) leftValue +
    specializationCost
      (binaryLengthValueTransportInnerBody size leftValue) rightValue

theorem binaryLengthValueTransportImplication_payloadLength_le_resource
    (size leftValue rightValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryLengthValueTransportImplication
      size leftValue rightValue).payloadLength <=
        binaryLengthValueTransportPayloadResource
          size leftValue rightValue := by
  have hraw := specializeThriceWithCasts_payloadLength_le
    binaryLengthValueTransportUniversalProof
    size leftValue rightValue
    (binaryLengthValueTransportAfterFirst_formula size)
    (binaryLengthValueTransportAfterSecond_formula size leftValue)
    (binaryLengthValueTransportFinal_formula size leftValue rightValue)
  change
    (specializeThriceWithCasts
      binaryLengthValueTransportUniversalProof
      size leftValue rightValue
      (binaryLengthValueTransportAfterFirst_formula size)
      (binaryLengthValueTransportAfterSecond_formula size leftValue)
      (binaryLengthValueTransportFinal_formula
        size leftValue rightValue)).payloadLength <= _
  unfold binaryLengthValueTransportPayloadResource
  exact hraw

/-! ## Complete valuation-context resource -/

def binaryLengthValuationTermCodeEnvelope
    (valuation : Nat -> Nat) (sizeTerm valueTerm : ValuationTerm) : Nat :=
  (binaryTermCode
      (shortBinaryNumeralTerm (termValue valuation sizeTerm))).length +
    (binaryTermCode
      (shortBinaryNumeralTerm (termValue valuation valueTerm))).length +
    (binaryTermCode sizeTerm).length +
    (binaryTermCode valueTerm).length + 1

def binaryLengthValuationSourceFormula
    (valuation : Nat -> Nat) (sizeTerm valueTerm : ValuationTerm) :
    ValuationFormula :=
  “!lengthDef
      !!(shortBinaryNumeralTerm (termValue valuation sizeTerm))
      !!(shortBinaryNumeralTerm (termValue valuation valueTerm))”

def binaryLengthValuationSizeEqualityFormula
    (valuation : Nat -> Nat) (sizeTerm : ValuationTerm) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm (termValue valuation sizeTerm)) = !!sizeTerm”

def binaryLengthValuationSizeFactFormula
    (valuation : Nat -> Nat) (sizeTerm valueTerm : ValuationTerm) :
    ValuationFormula :=
  “!lengthDef !!sizeTerm
      !!(shortBinaryNumeralTerm (termValue valuation valueTerm))”

def binaryLengthValuationValueEqualityFormula
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm (termValue valuation valueTerm)) = !!valueTerm”

/-- Exact input-computable resource for the complete contextual compiler. -/
def compileBinaryLengthAtValuationPayloadResource
    (valuation : Nat -> Nat) (sizeTerm valueTerm : ValuationTerm) : Nat :=
  let Gamma := binaryLengthValuationContext valuation sizeTerm valueTerm
  let termBound := binaryLengthValuationTermCodeEnvelope
    valuation sizeTerm valueTerm
  let shortValue := shortBinaryNumeralTerm (termValue valuation valueTerm)
  let sourceFormula := binaryLengthValuationSourceFormula
    valuation sizeTerm valueTerm
  let sizeEqualityFormula := binaryLengthValuationSizeEqualityFormula
    valuation sizeTerm
  let sizeFactFormula := binaryLengthValuationSizeFactFormula
    valuation sizeTerm valueTerm
  let valueEqualityFormula := binaryLengthValuationValueEqualityFormula
    valuation valueTerm
  let resultFormula := binaryLengthAtValuationFormula sizeTerm valueTerm
  let sizeTransportConsequent := sourceFormula 🡒 sizeFactFormula
  let valueTransportConsequent := sizeFactFormula 🡒 resultFormula
  binaryLengthAtShortNumeralsPayloadPolynomial
      (Nat.size (termValue valuation valueTerm)) +
    weakeningFullAssemblyCost (insert sourceFormula Gamma) +
    compileTermValueEqualityPayloadResource valuation sizeTerm +
    weakeningFullAssemblyCost (insert sizeEqualityFormula Gamma) +
    binaryLengthTransportPayloadEnvelope termBound +
    weakeningFullAssemblyCost
      (insert (sizeEqualityFormula 🡒 sizeTransportConsequent) Gamma) +
    compileTermValueEqualityPayloadResource valuation valueTerm +
    weakeningFullAssemblyCost (insert valueEqualityFormula Gamma) +
    binaryLengthValueTransportPayloadResource
      sizeTerm shortValue valueTerm +
    weakeningFullAssemblyCost
      (insert (valueEqualityFormula 🡒 valueTransportConsequent) Gamma) +
    contextualModusPonensFullAssemblyCost Gamma
      sizeEqualityFormula sizeTransportConsequent +
    contextualModusPonensFullAssemblyCost Gamma
      sourceFormula sizeFactFormula +
    contextualModusPonensFullAssemblyCost Gamma
      valueEqualityFormula valueTransportConsequent +
    contextualModusPonensFullAssemblyCost Gamma
      sizeFactFormula resultFormula

theorem compileBinaryLengthAtValuation_payloadLength_le_resource
    (valuation : Nat -> Nat) (sizeTerm valueTerm : ValuationTerm)
    (hsize : termValue valuation sizeTerm =
      Nat.size (termValue valuation valueTerm)) :
    (compileBinaryLengthAtValuation
      valuation sizeTerm valueTerm hsize).payloadLength <=
        compileBinaryLengthAtValuationPayloadResource
          valuation sizeTerm valueTerm := by
  let size := termValue valuation sizeTerm
  let value := termValue valuation valueTerm
  let shortSize := shortBinaryNumeralTerm size
  let shortValue := shortBinaryNumeralTerm value
  let Gamma := binaryLengthValuationContext valuation sizeTerm valueTerm
  let termBound := binaryLengthValuationTermCodeEnvelope
    valuation sizeTerm valueTerm
  let sourceFormula : ValuationFormula :=
    binaryLengthValuationSourceFormula valuation sizeTerm valueTerm
  let sizeEqualityFormula : ValuationFormula :=
    binaryLengthValuationSizeEqualityFormula valuation sizeTerm
  let sizeFactFormula : ValuationFormula :=
    binaryLengthValuationSizeFactFormula valuation sizeTerm valueTerm
  let valueEqualityFormula : ValuationFormula :=
    binaryLengthValuationValueEqualityFormula valuation valueTerm
  let resultFormula : ValuationFormula :=
    binaryLengthAtValuationFormula sizeTerm valueTerm
  let sizeTransportConsequent := sourceFormula 🡒 sizeFactFormula
  let valueTransportConsequent := sizeFactFormula 🡒 resultFormula

  have hshortSizeCode :
      (binaryTermCode shortSize).length <= termBound := by
    dsimp only [shortSize, size, termBound,
      binaryLengthValuationTermCodeEnvelope]
    omega
  have hshortValueCode :
      (binaryTermCode shortValue).length <= termBound := by
    dsimp only [shortValue, value, termBound,
      binaryLengthValuationTermCodeEnvelope]
    omega
  have hsizeTermCode : (binaryTermCode sizeTerm).length <= termBound := by
    dsimp only [termBound, binaryLengthValuationTermCodeEnvelope]
    omega
  have hvalueTermCode : (binaryTermCode valueTerm).length <= termBound := by
    dsimp only [termBound, binaryLengthValuationTermCodeEnvelope]
    omega

  let sourceRaw := proveBinaryLengthAtShortNumerals value
  have hsourceFormula :
      binaryLengthShortNumeralFormula value = sourceFormula := by
    dsimp only [sourceFormula, binaryLengthValuationSourceFormula,
      shortSize, shortValue, size, value]
    rw [hsize]
    rfl
  let source : CertifiedPAProof sourceFormula :=
    CertifiedPAProof.cast hsourceFormula sourceRaw
  let sourceInContext : CertifiedPAContextProof Gamma sourceFormula :=
    CertifiedPAContextProof.weakenCertified Gamma source
  have hsource : source.payloadLength <=
      binaryLengthAtShortNumeralsPayloadPolynomial (Nat.size value) := by
    calc
      source.payloadLength = sourceRaw.payloadLength := by
        dsimp only [source]
        exact CertifiedPAProof.cast_payloadLength hsourceFormula sourceRaw
      _ <= binaryLengthAtShortNumeralsPayloadPolynomial (Nat.size value) :=
        proveBinaryLengthAtShortNumerals_payloadLength_le_polynomial value
  have hsourceInContext : sourceInContext.payloadLength <=
      binaryLengthAtShortNumeralsPayloadPolynomial (Nat.size value) +
        weakeningFullAssemblyCost (insert sourceFormula Gamma) := by
    calc
      sourceInContext.payloadLength <= source.payloadLength +
          weakeningFullAssemblyCost (insert sourceFormula Gamma) := by
        dsimp only [sourceInContext]
        exact CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma source
      _ <= binaryLengthAtShortNumeralsPayloadPolynomial (Nat.size value) +
          weakeningFullAssemblyCost (insert sourceFormula Gamma) :=
        Nat.add_le_add_right hsource _

  have hsizeVariables : sizeTerm.freeVariables ⊆
      sizeTerm.freeVariables ∪ valueTerm.freeVariables :=
    Finset.subset_union_left
  let sizeEqualityRaw := compileTermValueEquality valuation sizeTerm
  let sizeEquality : CertifiedPAContextProof Gamma sizeEqualityFormula :=
    CertifiedPAContextProof.weakenContext sizeEqualityRaw
      (valuationContext_mono valuation hsizeVariables)
  have hsizeEqualityRaw : sizeEqualityRaw.payloadLength <=
      compileTermValueEqualityPayloadResource valuation sizeTerm :=
    compileTermValueEquality_payloadLength_le_resource valuation sizeTerm
  have hsizeEquality : sizeEquality.payloadLength <=
      compileTermValueEqualityPayloadResource valuation sizeTerm +
        weakeningFullAssemblyCost (insert sizeEqualityFormula Gamma) := by
    calc
      sizeEquality.payloadLength <= sizeEqualityRaw.payloadLength +
          weakeningFullAssemblyCost
            (insert sizeEqualityFormula Gamma) := by
        dsimp only [sizeEquality]
        exact CertifiedPAContextProof.weakenContext_payloadLength_le
          sizeEqualityRaw
          (valuationContext_mono valuation hsizeVariables)
      _ <= compileTermValueEqualityPayloadResource valuation sizeTerm +
          weakeningFullAssemblyCost
            (insert sizeEqualityFormula Gamma) :=
        Nat.add_le_add_right hsizeEqualityRaw _

  let sizeTransportClosed := binaryLengthSizeTransportImplication
    shortSize sizeTerm shortValue
  let sizeTransport : CertifiedPAContextProof Gamma
      (sizeEqualityFormula 🡒 sizeTransportConsequent) :=
    CertifiedPAContextProof.weakenCertified Gamma sizeTransportClosed
  have hsizeTransportClosed : sizeTransportClosed.payloadLength <=
      binaryLengthTransportPayloadEnvelope termBound := by
    dsimp only [sizeTransportClosed]
    exact binaryLengthSizeTransportImplication_payloadLength_le_envelope
      shortSize sizeTerm shortValue termBound
      hshortSizeCode hsizeTermCode hshortValueCode
  have hsizeTransport : sizeTransport.payloadLength <=
      binaryLengthTransportPayloadEnvelope termBound +
        weakeningFullAssemblyCost
          (insert (sizeEqualityFormula 🡒 sizeTransportConsequent)
            Gamma) := by
    calc
      sizeTransport.payloadLength <= sizeTransportClosed.payloadLength +
          weakeningFullAssemblyCost
            (insert (sizeEqualityFormula 🡒 sizeTransportConsequent)
              Gamma) := by
        dsimp only [sizeTransport]
        exact CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma sizeTransportClosed
      _ <= binaryLengthTransportPayloadEnvelope termBound +
          weakeningFullAssemblyCost
            (insert (sizeEqualityFormula 🡒 sizeTransportConsequent)
              Gamma) := Nat.add_le_add_right hsizeTransportClosed _

  let sizeTransportAfterEquality :=
    CertifiedPAContextProof.modusPonens sizeTransport sizeEquality
  have hsizeTransportAfterEquality :
      sizeTransportAfterEquality.payloadLength <=
        sizeTransport.payloadLength + sizeEquality.payloadLength +
          contextualModusPonensFullAssemblyCost Gamma
            sizeEqualityFormula sizeTransportConsequent := by
    dsimp only [sizeTransportAfterEquality]
    exact CertifiedPAContextProof.modusPonens_payloadLength_le
      sizeTransport sizeEquality
  let sizeFact := CertifiedPAContextProof.modusPonens
    sizeTransportAfterEquality sourceInContext
  have hsizeFact : sizeFact.payloadLength <=
      sizeTransportAfterEquality.payloadLength + sourceInContext.payloadLength +
        contextualModusPonensFullAssemblyCost Gamma
          sourceFormula sizeFactFormula := by
    dsimp only [sizeFact]
    exact CertifiedPAContextProof.modusPonens_payloadLength_le
      sizeTransportAfterEquality sourceInContext

  have hvalueVariables : valueTerm.freeVariables ⊆
      sizeTerm.freeVariables ∪ valueTerm.freeVariables :=
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

  let valueTransportClosed := binaryLengthValueTransportImplication
    sizeTerm shortValue valueTerm
  let valueTransport : CertifiedPAContextProof Gamma
      (valueEqualityFormula 🡒 valueTransportConsequent) :=
    CertifiedPAContextProof.weakenCertified Gamma valueTransportClosed
  have hvalueTransportClosed : valueTransportClosed.payloadLength <=
      binaryLengthValueTransportPayloadResource
        sizeTerm shortValue valueTerm := by
    dsimp only [valueTransportClosed]
    exact binaryLengthValueTransportImplication_payloadLength_le_resource
      sizeTerm shortValue valueTerm
  have hvalueTransport : valueTransport.payloadLength <=
      binaryLengthValueTransportPayloadResource
          sizeTerm shortValue valueTerm +
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
      _ <= binaryLengthValueTransportPayloadResource
            sizeTerm shortValue valueTerm +
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
    valueTransportAfterEquality sizeFact
  have hresult : result.payloadLength <=
      valueTransportAfterEquality.payloadLength + sizeFact.payloadLength +
        contextualModusPonensFullAssemblyCost Gamma
          sizeFactFormula resultFormula := by
    dsimp only [result]
    exact CertifiedPAContextProof.modusPonens_payloadLength_le
      valueTransportAfterEquality sizeFact
  have hcompiled :
      (compileBinaryLengthAtValuation
        valuation sizeTerm valueTerm hsize).payloadLength =
          result.payloadLength := by
    rfl
  rw [hcompiled]
  unfold compileBinaryLengthAtValuationPayloadResource
  dsimp only [Gamma, termBound, sourceFormula, sizeEqualityFormula,
    sizeFactFormula, valueEqualityFormula, resultFormula,
    sizeTransportConsequent, valueTransportConsequent,
    shortValue, value] at *
  omega

/-! ## Fixed polynomial and finite-family endpoints -/

def binaryLengthValuationCompilerPayloadPolynomial (resource : Nat) : Nat :=
  resource * resource + 2 * resource + 1

theorem binaryLengthValuationResource_le_fixedPolynomial (resource : Nat) :
    resource <= binaryLengthValuationCompilerPayloadPolynomial resource := by
  unfold binaryLengthValuationCompilerPayloadPolynomial
  calc
    resource <= 2 * resource := by omega
    _ <= resource * resource + 2 * resource := Nat.le_add_left _ _
    _ <= resource * resource + 2 * resource + 1 := Nat.le_add_right _ _

theorem compileBinaryLengthAtValuation_payloadLength_le_fixedPolynomial
    (valuation : Nat -> Nat) (sizeTerm valueTerm : ValuationTerm)
    (hsize : termValue valuation sizeTerm =
      Nat.size (termValue valuation valueTerm)) :
    (compileBinaryLengthAtValuation
      valuation sizeTerm valueTerm hsize).payloadLength <=
      binaryLengthValuationCompilerPayloadPolynomial
        (compileBinaryLengthAtValuationPayloadResource
          valuation sizeTerm valueTerm) := by
  exact
    (compileBinaryLengthAtValuation_payloadLength_le_resource
      valuation sizeTerm valueTerm hsize).trans
        (binaryLengthValuationResource_le_fixedPolynomial _)

def fixedBinaryLengthTermFamilyPayloadResource
    {termCount : Nat} (valuation : Nat -> Nat)
    (sizeTerms valueTerms : Fin termCount -> ValuationTerm) : Nat :=
  Finset.univ.sum (fun index =>
    compileBinaryLengthAtValuationPayloadResource valuation
      (sizeTerms index) (valueTerms index))

theorem
    compileBinaryLengthAtValuation_payloadLength_le_fixedTermFamilyPolynomial
    {termCount : Nat} (valuation : Nat -> Nat)
    (sizeTerms valueTerms : Fin termCount -> ValuationTerm)
    (index : Fin termCount)
    (hsize : termValue valuation (sizeTerms index) =
      Nat.size (termValue valuation (valueTerms index))) :
    (compileBinaryLengthAtValuation valuation
      (sizeTerms index) (valueTerms index) hsize).payloadLength <=
      binaryLengthValuationCompilerPayloadPolynomial
        (fixedBinaryLengthTermFamilyPayloadResource
          valuation sizeTerms valueTerms) := by
  have hpayload :=
    compileBinaryLengthAtValuation_payloadLength_le_resource valuation
      (sizeTerms index) (valueTerms index) hsize
  have hmember :
      compileBinaryLengthAtValuationPayloadResource valuation
          (sizeTerms index) (valueTerms index) <=
        fixedBinaryLengthTermFamilyPayloadResource
          valuation sizeTerms valueTerms := by
    unfold fixedBinaryLengthTermFamilyPayloadResource
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        (compileBinaryLengthAtValuationPayloadResource valuation
          (sizeTerms candidate) (valueTerms candidate)))
      (Finset.mem_univ index)
  exact hpayload.trans
    (hmember.trans (binaryLengthValuationResource_le_fixedPolynomial _))

#print axioms proveBinaryLengthAtShortNumerals_payloadLength_le_polynomial
#print axioms
  binaryLengthValueTransportImplication_payloadLength_le_resource
#print axioms compileBinaryLengthAtValuation_payloadLength_le_resource
#print axioms compileBinaryLengthAtValuation_payloadLength_le_fixedPolynomial
#print axioms
  compileBinaryLengthAtValuation_payloadLength_le_fixedTermFamilyPolynomial

end FoundationCompactPABinaryLengthValuationContextCompilerBounds
