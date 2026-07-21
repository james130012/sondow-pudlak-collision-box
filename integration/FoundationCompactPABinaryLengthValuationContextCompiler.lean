import integration.FoundationCompactCertifiedContextConnectives
import integration.FoundationCompactPABinaryLengthValueTransport
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactPAValuationTermCompiler

/-!
# Fast binary-length graphs at arbitrary valuation terms

The checked short-numeral length proof is transported along proved term-value
equalities to the exact compound terms occurring in a bounded formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABinaryLengthValuationContextCompiler

open FoundationCompactPAValuationTermCompiler
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPABinaryLengthRuleCompiler
open FoundationCompactPABinaryLengthValueTransport
open FoundationCompactPAEmbeddedPredicateFreeVariables

def binaryLengthValuationContext
    (valuation : Nat -> Nat)
    (sizeTerm valueTerm : ValuationTerm) :
    Finset LO.FirstOrder.ArithmeticProposition :=
  valuationContext
    (sizeTerm.freeVariables ∪ valueTerm.freeVariables) valuation

def binaryLengthAtValuationFormula
    (sizeTerm valueTerm : ValuationTerm) : ValuationFormula :=
  “!lengthDef !!sizeTerm !!valueTerm”

@[simp] theorem binaryLengthAtValuationFormula_freeVariables
    (sizeTerm valueTerm : ValuationTerm) :
    (binaryLengthAtValuationFormula sizeTerm valueTerm).freeVariables =
      sizeTerm.freeVariables ∪ valueTerm.freeVariables := by
  apply Finset.Subset.antisymm
  · exact embeddedBinarySubstitution_freeVariables_subset
      lengthDef.val sizeTerm valueTerm
  · intro index hindex
    rcases Finset.mem_union.mp hindex with hsize | hvalue
    · simp [binaryLengthAtValuationFormula, lengthDef, hsize]
    · simp [binaryLengthAtValuationFormula, lengthDef, hvalue]

noncomputable def compileBinaryLengthAtValuation
    (valuation : Nat -> Nat)
    (sizeTerm valueTerm : ValuationTerm)
    (hsize : termValue valuation sizeTerm =
      Nat.size (termValue valuation valueTerm)) :
    CertifiedPAContextProof
      (binaryLengthValuationContext valuation sizeTerm valueTerm)
      (binaryLengthAtValuationFormula sizeTerm valueTerm) := by
  let size := termValue valuation sizeTerm
  let value := termValue valuation valueTerm
  let shortSize := shortBinaryNumeralTerm size
  let shortValue := shortBinaryNumeralTerm value
  let Gamma := binaryLengthValuationContext valuation sizeTerm valueTerm

  let sourceRaw := proveBinaryLengthAtShortNumerals value
  have hsourceFormula :
      binaryLengthShortNumeralFormula value =
        (“!lengthDef !!shortSize !!shortValue” :
          LO.FirstOrder.ArithmeticProposition) := by
    dsimp only [shortSize, shortValue, size, value]
    rw [hsize]
    rfl
  let source : CertifiedPAProof
      (“!lengthDef !!shortSize !!shortValue” :
        LO.FirstOrder.ArithmeticProposition) :=
    CertifiedPAProof.cast hsourceFormula sourceRaw
  let sourceInContext := CertifiedPAContextProof.weakenCertified Gamma source

  have hsizeVariables : sizeTerm.freeVariables ⊆
      sizeTerm.freeVariables ∪ valueTerm.freeVariables :=
    Finset.subset_union_left
  have hvalueVariables : valueTerm.freeVariables ⊆
      sizeTerm.freeVariables ∪ valueTerm.freeVariables :=
    Finset.subset_union_right
  let sizeEqualityRaw := compileTermValueEquality valuation sizeTerm
  let sizeEquality := CertifiedPAContextProof.weakenContext sizeEqualityRaw
    (valuationContext_mono valuation hsizeVariables)
  let sizeTransport := CertifiedPAContextProof.weakenCertified Gamma
    (binaryLengthSizeTransportImplication
      shortSize sizeTerm shortValue)
  let sizeTransportAfterEquality :=
    CertifiedPAContextProof.modusPonens sizeTransport sizeEquality
  let sizeFact := CertifiedPAContextProof.modusPonens
    sizeTransportAfterEquality sourceInContext

  let valueEqualityRaw := compileTermValueEquality valuation valueTerm
  let valueEquality := CertifiedPAContextProof.weakenContext valueEqualityRaw
    (valuationContext_mono valuation hvalueVariables)
  let valueTransport := CertifiedPAContextProof.weakenCertified Gamma
    (binaryLengthValueTransportImplication
      sizeTerm shortValue valueTerm)
  let valueTransportAfterEquality :=
    CertifiedPAContextProof.modusPonens valueTransport valueEquality
  let result := CertifiedPAContextProof.modusPonens
    valueTransportAfterEquality sizeFact
  exact result

#print axioms compileBinaryLengthAtValuation

end FoundationCompactPABinaryLengthValuationContextCompiler
