import integration.FoundationCompactPABinaryLengthValuationContextCompilerBounds
import integration.FoundationCompactPAValuationTermCompilerPublicBounds

/-!
# Public resource for binary length at valuation terms

The exact compiler resource contains two term-value equality resources.  The
public endpoint below replaces both by the independently proved term
normalization and transport polynomials while preserving every connector and
fixed binary-length transport cost.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPABinaryLengthValuationContextCompilerPublicBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryLengthRuleCompilerBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPABinaryLengthValuationContextCompiler
open FoundationCompactPABinaryLengthValuationContextCompilerBounds

def compileBinaryLengthAtValuationPayloadPolynomial
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
    compileTermValueEqualityPayloadPolynomial valuation sizeTerm +
    weakeningFullAssemblyCost (insert sizeEqualityFormula Gamma) +
    binaryLengthTransportPayloadEnvelope termBound +
    weakeningFullAssemblyCost
      (insert (sizeEqualityFormula 🡒 sizeTransportConsequent) Gamma) +
    compileTermValueEqualityPayloadPolynomial valuation valueTerm +
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

theorem compileBinaryLengthAtValuationPayloadResource_le_publicPolynomial
    (valuation : Nat -> Nat) (sizeTerm valueTerm : ValuationTerm)
    (hsizeVars : sizeTerm.freeVariables ⊆ {0})
    (hvalueVars : valueTerm.freeVariables ⊆ {0}) :
    compileBinaryLengthAtValuationPayloadResource
        valuation sizeTerm valueTerm ≤
      compileBinaryLengthAtValuationPayloadPolynomial
        valuation sizeTerm valueTerm := by
  have hsize := compileTermValueEqualityPayloadResource_le_publicPolynomial
    valuation sizeTerm hsizeVars
  have hvalue := compileTermValueEqualityPayloadResource_le_publicPolynomial
    valuation valueTerm hvalueVars
  unfold compileBinaryLengthAtValuationPayloadResource
    compileBinaryLengthAtValuationPayloadPolynomial
  dsimp only
  omega

#print axioms
  compileBinaryLengthAtValuationPayloadResource_le_publicPolynomial

end FoundationCompactPABinaryLengthValuationContextCompilerPublicBounds
