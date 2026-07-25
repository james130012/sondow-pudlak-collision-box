import integration.FoundationCompactNumericListedDirectNegationFormulaTagPublicBounds
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactPABinaryNumeralAdditionBounds

/-!
# Fixed closed-formula syntax for the negation tag graph

The original two-coordinate Delta-zero formula is instantiated by closed short
binary numerals.  Its complete code and closedness are derived directly from
that substitution.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNegationFormulaTagFormulaFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate

def compactNegationFormulaTagClosedTerms
    (tag mapped : Nat) : Fin 2 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tag, shortBinaryNumeralTerm mapped]

def compactNegationFormulaTagFullFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 2 :=
    Rewriting.emb (ξ := Nat) compactNegationFormulaTagGraphDef.val
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0
    (binaryNumeralTermCodeEnvelope bitBound) (binaryFormulaCode source).length

theorem compactNegationFormulaTagClosedFormula_code_length_le_fixed
    (tag mapped bitBound : Nat)
    (htagSize : Nat.size tag <= bitBound)
    (hmappedSize : Nat.size mapped <= bitBound) :
    (binaryFormulaCode
      (compactNegationFormulaTagClosedFormula tag mapped)).length <=
      compactNegationFormulaTagFullFormulaCodePolynomial bitBound := by
  let terms := compactNegationFormulaTagClosedTerms tag mapped
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 2 :=
    Rewriting.emb (ξ := Nat) compactNegationFormulaTagGraphDef.val
  have hterms : ∀ coordinate,
      (binaryTermCode (terms coordinate)).length <=
        binaryNumeralTermCodeEnvelope bitBound := by
    intro coordinate
    fin_cases coordinate
    · exact binaryNumeralTerm_code_length_le_envelope tag bitBound htagSize
    · exact binaryNumeralTerm_code_length_le_envelope mapped bitBound
        hmappedSize
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 (binaryNumeralTermCodeEnvelope bitBound)
      (binaryFormulaCode source).length terms source hterms le_rfl
  unfold compactNegationFormulaTagClosedFormula
    compactNegationFormulaTagFullFormulaCodePolynomial
  simpa only [sourceSubstitutionQpow, terms, source,
    compactNegationFormulaTagClosedTerms] using hraw

theorem compactNegationFormulaTagClosedFormula_closed
    (tag mapped : Nat) :
    (compactNegationFormulaTagClosedFormula tag mapped).freeVariables = ∅ := by
  unfold compactNegationFormulaTagClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

#print axioms compactNegationFormulaTagClosedFormula_code_length_le_fixed
#print axioms compactNegationFormulaTagClosedFormula_closed

end FoundationCompactNumericListedDirectNegationFormulaTagFormulaFixedBounds
