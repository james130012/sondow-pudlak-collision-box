import integration.FoundationCompactPAExponentialValuationContextCompiler
import integration.FoundationCompactPAValuationTermCompilerBounds

/-!
# Payload bounds for exponential graphs at valuation terms

The resource below follows the compiler literally: two checked term-value
equalities, three closed proofs weakened into the common valuation context,
and four contextual modus-ponens assemblies.  It is computed only from the
valuation and the two input terms.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAExponentialValuationContextCompilerBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExponentialShortNumeralCompiler
open FoundationCompactPAExponentialShortNumeralTransportBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerBounds
open FoundationCompactPAExponentialValuationContextCompiler

def exponentialValuationTermCodeEnvelope
    (valuation : Nat -> Nat) (valueTerm exponentTerm : ValuationTerm) : Nat :=
  (binaryTermCode
      (shortBinaryNumeralTerm (termValue valuation valueTerm))).length +
    (binaryTermCode
      (shortBinaryNumeralTerm (termValue valuation exponentTerm))).length +
    (binaryTermCode valueTerm).length +
    (binaryTermCode exponentTerm).length + 1

def exponentialValuationSourceFormula
    (valuation : Nat -> Nat) (valueTerm exponentTerm : ValuationTerm) :
    ValuationFormula :=
  “!expDef
      !!(shortBinaryNumeralTerm (termValue valuation valueTerm))
      !!(shortBinaryNumeralTerm (termValue valuation exponentTerm))”

def exponentialValuationValueEqualityFormula
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm (termValue valuation valueTerm)) =
    !!valueTerm”

def exponentialValuationValueFactFormula
    (valuation : Nat -> Nat) (valueTerm exponentTerm : ValuationTerm) :
    ValuationFormula :=
  “!expDef !!valueTerm
      !!(shortBinaryNumeralTerm (termValue valuation exponentTerm))”

def exponentialValuationExponentEqualityFormula
    (valuation : Nat -> Nat) (exponentTerm : ValuationTerm) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm (termValue valuation exponentTerm)) =
    !!exponentTerm”

/-- Exact input-computable resource for the complete contextual compiler. -/
def compileExponentialAtValuationPayloadResource
    (valuation : Nat -> Nat) (valueTerm exponentTerm : ValuationTerm) : Nat :=
  let Gamma := exponentialValuationContext valuation valueTerm exponentTerm
  let termBound := exponentialValuationTermCodeEnvelope
    valuation valueTerm exponentTerm
  let sourceFormula := exponentialValuationSourceFormula
    valuation valueTerm exponentTerm
  let valueEqualityFormula := exponentialValuationValueEqualityFormula
    valuation valueTerm
  let valueFactFormula := exponentialValuationValueFactFormula
    valuation valueTerm exponentTerm
  let exponentEqualityFormula :=
    exponentialValuationExponentEqualityFormula valuation exponentTerm
  let resultFormula := exponentialAtValuationFormula valueTerm exponentTerm
  let valueTransportConsequent := sourceFormula 🡒 valueFactFormula
  let exponentTransportConsequent := valueFactFormula 🡒 resultFormula
  exponentialPowerAtShortNumeralsPayloadPolynomial
      (termValue valuation exponentTerm) +
    weakeningFullAssemblyCost (insert sourceFormula Gamma) +
    compileTermValueEqualityPayloadResource valuation valueTerm +
    weakeningFullAssemblyCost (insert valueEqualityFormula Gamma) +
    exponentialValueTransportPayloadEnvelope termBound +
    weakeningFullAssemblyCost
      (insert (valueEqualityFormula 🡒 valueTransportConsequent) Gamma) +
    compileTermValueEqualityPayloadResource valuation exponentTerm +
    weakeningFullAssemblyCost (insert exponentEqualityFormula Gamma) +
    exponentialExponentTransportPayloadEnvelope termBound +
    weakeningFullAssemblyCost
      (insert (exponentEqualityFormula 🡒 exponentTransportConsequent) Gamma) +
    contextualModusPonensFullAssemblyCost Gamma
      valueEqualityFormula valueTransportConsequent +
    contextualModusPonensFullAssemblyCost Gamma
      sourceFormula valueFactFormula +
    contextualModusPonensFullAssemblyCost Gamma
      exponentEqualityFormula exponentTransportConsequent +
    contextualModusPonensFullAssemblyCost Gamma
      valueFactFormula resultFormula

theorem compileExponentialAtValuation_payloadLength_le_resource
    (valuation : Nat -> Nat) (valueTerm exponentTerm : ValuationTerm)
    (hvalue : termValue valuation valueTerm =
      2 ^ termValue valuation exponentTerm) :
    (compileExponentialAtValuation
      valuation valueTerm exponentTerm hvalue).payloadLength <=
        compileExponentialAtValuationPayloadResource
          valuation valueTerm exponentTerm := by
  let value := termValue valuation valueTerm
  let exponent := termValue valuation exponentTerm
  let shortValue := shortBinaryNumeralTerm value
  let shortExponent := shortBinaryNumeralTerm exponent
  let Gamma := exponentialValuationContext valuation valueTerm exponentTerm
  let termBound := exponentialValuationTermCodeEnvelope
    valuation valueTerm exponentTerm
  let sourceFormula : ValuationFormula :=
    exponentialValuationSourceFormula valuation valueTerm exponentTerm
  let valueEqualityFormula : ValuationFormula :=
    exponentialValuationValueEqualityFormula valuation valueTerm
  let valueFactFormula : ValuationFormula :=
    exponentialValuationValueFactFormula valuation valueTerm exponentTerm
  let exponentEqualityFormula : ValuationFormula :=
    exponentialValuationExponentEqualityFormula valuation exponentTerm
  let resultFormula : ValuationFormula :=
    exponentialAtValuationFormula valueTerm exponentTerm
  let valueTransportConsequent := sourceFormula 🡒 valueFactFormula
  let exponentTransportConsequent := valueFactFormula 🡒 resultFormula

  have hshortValueCode :
      (binaryTermCode shortValue).length <= termBound := by
    dsimp only [shortValue, value, termBound,
      exponentialValuationTermCodeEnvelope]
    omega
  have hshortExponentCode :
      (binaryTermCode shortExponent).length <= termBound := by
    dsimp only [shortExponent, exponent, termBound,
      exponentialValuationTermCodeEnvelope]
    omega
  have hvalueTermCode : (binaryTermCode valueTerm).length <= termBound := by
    dsimp only [termBound, exponentialValuationTermCodeEnvelope]
    omega
  have hexponentTermCode :
      (binaryTermCode exponentTerm).length <= termBound := by
    dsimp only [termBound, exponentialValuationTermCodeEnvelope]
    omega

  let sourceRaw := proveExponentialPowerAtShortNumerals exponent
  have hsourceFormula :
      exponentialShortNumeralFormula exponent = sourceFormula := by
    dsimp only [sourceFormula, exponentialValuationSourceFormula,
      shortValue, shortExponent, value, exponent]
    rw [hvalue]
    rfl
  let source : CertifiedPAProof sourceFormula :=
    CertifiedPAProof.cast hsourceFormula sourceRaw
  let sourceInContext : CertifiedPAContextProof Gamma sourceFormula :=
    CertifiedPAContextProof.weakenCertified Gamma source
  have hsource : source.payloadLength <=
      exponentialPowerAtShortNumeralsPayloadPolynomial exponent := by
    calc
      source.payloadLength = sourceRaw.payloadLength := by
        dsimp only [source]
        exact CertifiedPAProof.cast_payloadLength hsourceFormula sourceRaw
      _ <= exponentialPowerAtShortNumeralsPayloadPolynomial exponent :=
        proveExponentialPowerAtShortNumerals_payloadLength_le_polynomial
          exponent
  have hsourceInContext : sourceInContext.payloadLength <=
      exponentialPowerAtShortNumeralsPayloadPolynomial exponent +
        weakeningFullAssemblyCost (insert sourceFormula Gamma) := by
    calc
      sourceInContext.payloadLength <= source.payloadLength +
          weakeningFullAssemblyCost (insert sourceFormula Gamma) := by
        dsimp only [sourceInContext]
        exact CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma source
      _ <= exponentialPowerAtShortNumeralsPayloadPolynomial exponent +
          weakeningFullAssemblyCost (insert sourceFormula Gamma) :=
        Nat.add_le_add_right hsource _

  have hvalueVariables : valueTerm.freeVariables ⊆
      valueTerm.freeVariables ∪ exponentTerm.freeVariables :=
    Finset.subset_union_left
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

  let valueTransportClosed := exponentialValueTransportImplication
    shortValue valueTerm shortExponent
  let valueTransport : CertifiedPAContextProof Gamma
      (valueEqualityFormula 🡒 valueTransportConsequent) :=
    CertifiedPAContextProof.weakenCertified Gamma valueTransportClosed
  have hvalueTransportClosed : valueTransportClosed.payloadLength <=
      exponentialValueTransportPayloadEnvelope termBound := by
    dsimp only [valueTransportClosed]
    exact exponentialValueTransportImplication_payloadLength_le_envelope
      shortValue valueTerm shortExponent termBound
      hshortValueCode hvalueTermCode hshortExponentCode
  have hvalueTransport : valueTransport.payloadLength <=
      exponentialValueTransportPayloadEnvelope termBound +
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
      _ <= exponentialValueTransportPayloadEnvelope termBound +
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
  let valueFact := CertifiedPAContextProof.modusPonens
    valueTransportAfterEquality sourceInContext
  have hvalueFact : valueFact.payloadLength <=
      valueTransportAfterEquality.payloadLength +
        sourceInContext.payloadLength +
        contextualModusPonensFullAssemblyCost Gamma
          sourceFormula valueFactFormula := by
    dsimp only [valueFact]
    exact CertifiedPAContextProof.modusPonens_payloadLength_le
      valueTransportAfterEquality sourceInContext

  have hexponentVariables : exponentTerm.freeVariables ⊆
      valueTerm.freeVariables ∪ exponentTerm.freeVariables :=
    Finset.subset_union_right
  let exponentEqualityRaw := compileTermValueEquality valuation exponentTerm
  let exponentEquality : CertifiedPAContextProof Gamma
      exponentEqualityFormula :=
    CertifiedPAContextProof.weakenContext exponentEqualityRaw
      (valuationContext_mono valuation hexponentVariables)
  have hexponentEqualityRaw : exponentEqualityRaw.payloadLength <=
      compileTermValueEqualityPayloadResource valuation exponentTerm :=
    compileTermValueEquality_payloadLength_le_resource valuation exponentTerm
  have hexponentEquality : exponentEquality.payloadLength <=
      compileTermValueEqualityPayloadResource valuation exponentTerm +
        weakeningFullAssemblyCost
          (insert exponentEqualityFormula Gamma) := by
    calc
      exponentEquality.payloadLength <= exponentEqualityRaw.payloadLength +
          weakeningFullAssemblyCost
            (insert exponentEqualityFormula Gamma) := by
        dsimp only [exponentEquality]
        exact CertifiedPAContextProof.weakenContext_payloadLength_le
          exponentEqualityRaw
          (valuationContext_mono valuation hexponentVariables)
      _ <= compileTermValueEqualityPayloadResource valuation exponentTerm +
          weakeningFullAssemblyCost
            (insert exponentEqualityFormula Gamma) :=
        Nat.add_le_add_right hexponentEqualityRaw _

  let exponentTransportClosed := exponentialExponentTransportImplication
    valueTerm shortExponent exponentTerm
  let exponentTransport : CertifiedPAContextProof Gamma
      (exponentEqualityFormula 🡒 exponentTransportConsequent) :=
    CertifiedPAContextProof.weakenCertified Gamma exponentTransportClosed
  have hexponentTransportClosed : exponentTransportClosed.payloadLength <=
      exponentialExponentTransportPayloadEnvelope termBound := by
    dsimp only [exponentTransportClosed]
    exact exponentialExponentTransportImplication_payloadLength_le_envelope
      valueTerm shortExponent exponentTerm termBound
      hvalueTermCode hshortExponentCode hexponentTermCode
  have hexponentTransport : exponentTransport.payloadLength <=
      exponentialExponentTransportPayloadEnvelope termBound +
        weakeningFullAssemblyCost
          (insert (exponentEqualityFormula 🡒 exponentTransportConsequent)
            Gamma) := by
    calc
      exponentTransport.payloadLength <=
          exponentTransportClosed.payloadLength +
            weakeningFullAssemblyCost
              (insert
                (exponentEqualityFormula 🡒 exponentTransportConsequent)
                Gamma) := by
        dsimp only [exponentTransport]
        exact CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma exponentTransportClosed
      _ <= exponentialExponentTransportPayloadEnvelope termBound +
          weakeningFullAssemblyCost
            (insert (exponentEqualityFormula 🡒 exponentTransportConsequent)
              Gamma) := Nat.add_le_add_right hexponentTransportClosed _

  let exponentTransportAfterEquality :=
    CertifiedPAContextProof.modusPonens exponentTransport exponentEquality
  have hexponentTransportAfterEquality :
      exponentTransportAfterEquality.payloadLength <=
        exponentTransport.payloadLength + exponentEquality.payloadLength +
          contextualModusPonensFullAssemblyCost Gamma
            exponentEqualityFormula exponentTransportConsequent := by
    dsimp only [exponentTransportAfterEquality]
    exact CertifiedPAContextProof.modusPonens_payloadLength_le
      exponentTransport exponentEquality
  let result := CertifiedPAContextProof.modusPonens
    exponentTransportAfterEquality valueFact
  have hresult : result.payloadLength <=
      exponentTransportAfterEquality.payloadLength + valueFact.payloadLength +
        contextualModusPonensFullAssemblyCost Gamma
          valueFactFormula resultFormula := by
    dsimp only [result]
    exact CertifiedPAContextProof.modusPonens_payloadLength_le
      exponentTransportAfterEquality valueFact
  have hcompiled :
      (compileExponentialAtValuation
        valuation valueTerm exponentTerm hvalue).payloadLength =
          result.payloadLength := by
    rfl
  rw [hcompiled]
  unfold compileExponentialAtValuationPayloadResource
  dsimp only [Gamma, termBound, sourceFormula, valueEqualityFormula,
    valueFactFormula, exponentEqualityFormula, resultFormula,
    valueTransportConsequent, exponentTransportConsequent,
    value, exponent, shortValue, shortExponent] at *
  omega

/-! ## Fixed polynomial and finite-family endpoints -/

def exponentialValuationCompilerPayloadPolynomial (resource : Nat) : Nat :=
  resource * resource + 2 * resource + 1

theorem exponentialValuationResource_le_fixedPolynomial (resource : Nat) :
    resource <= exponentialValuationCompilerPayloadPolynomial resource := by
  unfold exponentialValuationCompilerPayloadPolynomial
  calc
    resource <= 2 * resource := by omega
    _ <= resource * resource + 2 * resource := Nat.le_add_left _ _
    _ <= resource * resource + 2 * resource + 1 := Nat.le_add_right _ _

theorem compileExponentialAtValuation_payloadLength_le_fixedPolynomial
    (valuation : Nat -> Nat) (valueTerm exponentTerm : ValuationTerm)
    (hvalue : termValue valuation valueTerm =
      2 ^ termValue valuation exponentTerm) :
    (compileExponentialAtValuation
      valuation valueTerm exponentTerm hvalue).payloadLength <=
      exponentialValuationCompilerPayloadPolynomial
        (compileExponentialAtValuationPayloadResource
          valuation valueTerm exponentTerm) := by
  exact
    (compileExponentialAtValuation_payloadLength_le_resource
      valuation valueTerm exponentTerm hvalue).trans
        (exponentialValuationResource_le_fixedPolynomial _)

def fixedExponentialTermFamilyPayloadResource
    {termCount : Nat} (valuation : Nat -> Nat)
    (valueTerms exponentTerms : Fin termCount -> ValuationTerm) : Nat :=
  Finset.univ.sum (fun index =>
    compileExponentialAtValuationPayloadResource valuation
      (valueTerms index) (exponentTerms index))

theorem
    compileExponentialAtValuation_payloadLength_le_fixedTermFamilyPolynomial
    {termCount : Nat} (valuation : Nat -> Nat)
    (valueTerms exponentTerms : Fin termCount -> ValuationTerm)
    (index : Fin termCount)
    (hvalue : termValue valuation (valueTerms index) =
      2 ^ termValue valuation (exponentTerms index)) :
    (compileExponentialAtValuation valuation
      (valueTerms index) (exponentTerms index) hvalue).payloadLength <=
      exponentialValuationCompilerPayloadPolynomial
        (fixedExponentialTermFamilyPayloadResource
          valuation valueTerms exponentTerms) := by
  have hpayload :=
    compileExponentialAtValuation_payloadLength_le_resource valuation
      (valueTerms index) (exponentTerms index) hvalue
  have hmember :
      compileExponentialAtValuationPayloadResource valuation
          (valueTerms index) (exponentTerms index) <=
        fixedExponentialTermFamilyPayloadResource
          valuation valueTerms exponentTerms := by
    unfold fixedExponentialTermFamilyPayloadResource
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        (compileExponentialAtValuationPayloadResource valuation
          (valueTerms candidate) (exponentTerms candidate)))
      (Finset.mem_univ index)
  exact hpayload.trans
    (hmember.trans (exponentialValuationResource_le_fixedPolynomial _))

#print axioms compileExponentialAtValuation_payloadLength_le_resource
#print axioms compileExponentialAtValuation_payloadLength_le_fixedPolynomial
#print axioms
  compileExponentialAtValuation_payloadLength_le_fixedTermFamilyPolynomial

end FoundationCompactPAExponentialValuationContextCompilerBounds
