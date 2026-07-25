import integration.FoundationCompactNumericListedDirectNegationFormulaTagAtomicFixedBounds
import integration.FoundationCompactPAHybridDisjunctionGeneralContextBounds

/-!
# Fixed disjunction resource for the large negation tag branch

The certificate for `8 <= tag` selects either the equality atom `8 = tag` or
the strict atom `8 < tag`.  Both atoms and the disjunction assembly are charged
to fixed functions of the common numeral bit bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 160000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNegationFormulaTagEightLeFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate
open FoundationCompactNumericListedDirectNegationFormulaTagAtomicFixedBounds

private abbrev tagZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation

def negationFormulaTagEightLeSyntaxPolynomial (bitBound : Nat) : Nat :=
  8 * (orderAtomicFormulaCodeEnvelope
    (negationFormulaTagAtomicTermCodePolynomial bitBound) + 1)

def negationFormulaTagEightLeFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (negationFormulaTagEightLeSyntaxPolynomial bitBound)
    (negationFormulaTagAtomicFixedPayloadPolynomial bitBound)

private theorem tagEightCode_le (bitBound : Nat) :
    (binaryTermCode (‘8’ : ValuationTerm)).length <=
      negationFormulaTagAtomicTermCodePolynomial bitBound := by
  unfold negationFormulaTagAtomicTermCodePolynomial
  dsimp only
  omega

private theorem tagShortNumeralCode_le
    (tag bitBound : Nat) (htagSize : Nat.size tag <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm tag)).length <=
      negationFormulaTagAtomicTermCodePolynomial bitBound := by
  have hraw :=
    binaryNumeralTerm_code_length_le_envelope tag bitBound htagSize
  unfold negationFormulaTagAtomicTermCodePolynomial
  dsimp only
  omega

theorem eightLeTagCertificate_structuralPayloadBound_le_fixed
    (tag bitBound : Nat) (htag : 8 <= tag)
    (htagSize : Nat.size tag <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (eightLeTagCertificate tag htag) <=
      negationFormulaTagEightLeFixedPayloadPolynomial bitBound := by
  let equalityFormula : ValuationFormula :=
    “8 = !!(shortBinaryNumeralTerm tag)”
  let strictFormula : ValuationFormula :=
    “8 < !!(shortBinaryNumeralTerm tag)”
  let targetFormula := equalityFormula ⋎ strictFormula
  let syntaxResource := negationFormulaTagEightLeSyntaxPolynomial bitBound
  let atomResource := negationFormulaTagAtomicFixedPayloadPolynomial bitBound
  have heightCode :
      (binaryTermCode (‘8’ : ValuationTerm)).length <=
        negationFormulaTagAtomicTermCodePolynomial bitBound :=
    tagEightCode_le bitBound
  have htagCode :
      (binaryTermCode (shortBinaryNumeralTerm tag)).length <=
        negationFormulaTagAtomicTermCodePolynomial bitBound :=
    tagShortNumeralCode_le tag bitBound htagSize
  have hequalityCodeRaw := equalityFormula_code_le_orderAtomic
    (‘8’ : ValuationTerm) (shortBinaryNumeralTerm tag)
    (negationFormulaTagAtomicTermCodePolynomial bitBound)
    heightCode htagCode
  have hstrictCodeRaw := lessThanFormula_code_le_orderAtomic
    (‘8’ : ValuationTerm) (shortBinaryNumeralTerm tag)
    (negationFormulaTagAtomicTermCodePolynomial bitBound)
    heightCode htagCode
  have htargetCodeRaw :=
    FoundationCompactListedLocalCostPrimitives.binaryFormulaCode_or_length_le
      equalityFormula strictFormula
  have hsyntaxPositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold negationFormulaTagEightLeSyntaxPolynomial
    omega
  have hequalityCode :
      (binaryFormulaCode equalityFormula).length <= syntaxResource := by
    dsimp only [equalityFormula, syntaxResource] at *
    unfold negationFormulaTagEightLeSyntaxPolynomial
    omega
  have hstrictCode :
      (binaryFormulaCode strictFormula).length <= syntaxResource := by
    dsimp only [strictFormula, syntaxResource] at *
    unfold negationFormulaTagEightLeSyntaxPolynomial
    omega
  have htargetCode :
      (binaryFormulaCode targetFormula).length <= syntaxResource := by
    dsimp only [targetFormula, equalityFormula, strictFormula]
      at htargetCodeRaw ⊢
    dsimp only [syntaxResource]
    unfold negationFormulaTagEightLeSyntaxPolynomial
    omega
  have htargetClosed : targetFormula.freeVariables = ∅ := by
    dsimp only [targetFormula, equalityFormula, strictFormula]
    simp [shortBinaryNumeralTerm_freeVariables_eq_empty,
      LO.FirstOrder.Semiterm.Operator.operator]
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext targetFormula.freeVariables tagZeroValuation) <=
        syntaxResource := by
    rw [htargetClosed]
    simp [valuationContext,
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum]
  have hequalityActualFixed :
      compilePositiveRelationPayloadResource tagZeroValuation Language.Eq.eq
          ![(‘8’ : ValuationTerm), shortBinaryNumeralTerm tag] <=
        atomResource := by
    exact eightTagEqualityPayloadResource_le_fixed tag bitBound htagSize
  have hstrictActualFixed :
      compilePositiveRelationPayloadResource tagZeroValuation
          Language.ORing.Rel.lt
          ![(‘8’ : ValuationTerm), shortBinaryNumeralTerm tag] <=
        atomResource := by
    exact eightTagStrictPayloadResource_le_fixed tag bitBound htagSize
  by_cases heq : 8 = tag
  · have hassembly :=
      transparentHybridDisjunctionLeftPayloadEnvelope_le_general
        tagZeroValuation equalityFormula strictFormula atomResource
        syntaxResource hsyntaxPositive hcontext hequalityCode hstrictCode
        htargetCode
    have hfixed :=
      (transparentHybridDisjunctionLeftPayloadEnvelope_mono
        tagZeroValuation equalityFormula strictFormula
        hequalityActualFixed).trans hassembly
    simp only [eightLeTagCertificate]
    rw [dif_pos heq]
    simp only [hybridFormulaStructuralPayloadBound]
    change transparentHybridDisjunctionLeftPayloadEnvelope tagZeroValuation
      equalityFormula strictFormula
      (compilePositiveRelationPayloadResource tagZeroValuation Language.Eq.eq
        ![(‘8’ : ValuationTerm), shortBinaryNumeralTerm tag]) <=
      hybridDisjunctionGeneralPayloadEnvelope syntaxResource atomResource
    exact hfixed
  · have hassembly :=
      transparentHybridDisjunctionRightPayloadEnvelope_le_general
        tagZeroValuation equalityFormula strictFormula atomResource
        syntaxResource hsyntaxPositive hcontext hequalityCode hstrictCode
        htargetCode
    have hfixed :=
      (transparentHybridDisjunctionRightPayloadEnvelope_mono
        tagZeroValuation equalityFormula strictFormula
        hstrictActualFixed).trans hassembly
    simp only [eightLeTagCertificate]
    rw [dif_neg heq]
    simp only [hybridFormulaStructuralPayloadBound]
    change transparentHybridDisjunctionRightPayloadEnvelope tagZeroValuation
      equalityFormula strictFormula
      (compilePositiveRelationPayloadResource tagZeroValuation
        Language.ORing.Rel.lt
        ![(‘8’ : ValuationTerm), shortBinaryNumeralTerm tag]) <=
      hybridDisjunctionGeneralPayloadEnvelope syntaxResource atomResource
    exact hfixed

#print axioms eightLeTagCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectNegationFormulaTagEightLeFixedBounds
