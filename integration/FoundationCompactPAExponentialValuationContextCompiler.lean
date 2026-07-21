import integration.FoundationCompactCertifiedContextConnectives
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactPAExponentialShortNumeralTransportBounds
import integration.FoundationCompactPAValuationTermCompiler

/-!
# Fast exponential graphs at arbitrary valuation terms

The short-numeral exponential proof is transported along checked term-value
equalities to the exact compound terms occurring in a bounded formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAExponentialValuationContextCompiler

open FoundationCompactPAValuationTermCompiler
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAExponentialShortNumeralCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables

def exponentialValuationContext
    (valuation : Nat -> Nat)
    (valueTerm exponentTerm : ValuationTerm) :
    Finset LO.FirstOrder.ArithmeticProposition :=
  valuationContext
    (valueTerm.freeVariables ∪ exponentTerm.freeVariables) valuation

def exponentialAtValuationFormula
    (valueTerm exponentTerm : ValuationTerm) : ValuationFormula :=
  “!expDef !!valueTerm !!exponentTerm”

@[simp] theorem exponentialAtValuationFormula_freeVariables
    (valueTerm exponentTerm : ValuationTerm) :
    (exponentialAtValuationFormula valueTerm exponentTerm).freeVariables =
      valueTerm.freeVariables ∪ exponentTerm.freeVariables := by
  apply Finset.Subset.antisymm
  · exact embeddedBinarySubstitution_freeVariables_subset
      expDef.val valueTerm exponentTerm
  · intro index hindex
    rcases Finset.mem_union.mp hindex with hvalue | hexponent
    · simp [exponentialAtValuationFormula, expDef, exponentialDef,
        hvalue]
    · simp [exponentialAtValuationFormula, expDef, exponentialDef,
        hexponent]

noncomputable def compileExponentialAtValuation
    (valuation : Nat -> Nat)
    (valueTerm exponentTerm : ValuationTerm)
    (hvalue : termValue valuation valueTerm =
      2 ^ termValue valuation exponentTerm) :
    CertifiedPAContextProof
      (exponentialValuationContext valuation valueTerm exponentTerm)
      (exponentialAtValuationFormula valueTerm exponentTerm) := by
  let value := termValue valuation valueTerm
  let exponent := termValue valuation exponentTerm
  let shortValue := shortBinaryNumeralTerm value
  let shortExponent := shortBinaryNumeralTerm exponent
  let Gamma := exponentialValuationContext valuation valueTerm exponentTerm

  let sourceRaw := proveExponentialPowerAtShortNumerals exponent
  have hsourceFormula :
      exponentialShortNumeralFormula exponent =
        (“!expDef !!shortValue !!shortExponent” :
          LO.FirstOrder.ArithmeticProposition) := by
    dsimp only [shortValue, shortExponent, value, exponent]
    rw [hvalue]
    rfl
  let source : CertifiedPAProof
      (“!expDef !!shortValue !!shortExponent” :
        LO.FirstOrder.ArithmeticProposition) :=
    CertifiedPAProof.cast hsourceFormula sourceRaw
  let sourceInContext := CertifiedPAContextProof.weakenCertified Gamma source

  have hvalueVariables : valueTerm.freeVariables ⊆
      valueTerm.freeVariables ∪ exponentTerm.freeVariables :=
    Finset.subset_union_left
  have hexponentVariables : exponentTerm.freeVariables ⊆
      valueTerm.freeVariables ∪ exponentTerm.freeVariables :=
    Finset.subset_union_right
  let valueEqualityRaw := compileTermValueEquality valuation valueTerm
  let valueEquality := CertifiedPAContextProof.weakenContext valueEqualityRaw
    (valuationContext_mono valuation hvalueVariables)
  let valueTransport := CertifiedPAContextProof.weakenCertified Gamma
    (exponentialValueTransportImplication
      shortValue valueTerm shortExponent)
  let valueTransportAfterEquality :=
    CertifiedPAContextProof.modusPonens valueTransport valueEquality
  let valueFact := CertifiedPAContextProof.modusPonens
    valueTransportAfterEquality sourceInContext

  let exponentEqualityRaw := compileTermValueEquality valuation exponentTerm
  let exponentEquality := CertifiedPAContextProof.weakenContext
    exponentEqualityRaw
    (valuationContext_mono valuation hexponentVariables)
  let exponentTransport := CertifiedPAContextProof.weakenCertified Gamma
    (exponentialExponentTransportImplication
      valueTerm shortExponent exponentTerm)
  let exponentTransportAfterEquality :=
    CertifiedPAContextProof.modusPonens exponentTransport exponentEquality
  let result := CertifiedPAContextProof.modusPonens
    exponentTransportAfterEquality valueFact
  exact result

#print axioms compileExponentialAtValuation

end FoundationCompactPAExponentialValuationContextCompiler
