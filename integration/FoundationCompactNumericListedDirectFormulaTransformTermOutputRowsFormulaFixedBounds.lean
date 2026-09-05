import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Fixed complete syntax for formula-transform term output rows

The original thirty-three-coordinate Delta-zero formula is instantiated by
closed short binary numerals. One explicit environment-wide bit bound controls
the complete formula code.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 80000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFormulaFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate

def compactFormulaTransformTermOutputRowsClosedTerms
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) :
    Fin 33 -> ValuationTerm :=
  compactFormulaTransformTermOutputRowsOuterTerms tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount

def compactFormulaTransformTermOutputRowsFullFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 33 :=
    Rewriting.emb (ξ := Nat)
      compactFormulaTransformTermOutputRowsDef.val
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0
    (binaryNumeralTermCodeEnvelope bitBound) (binaryFormulaCode source).length

theorem
    compactFormulaTransformTermOutputRowsClosedFormula_code_length_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount bitBound : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (henvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <= bitBound) :
    (binaryFormulaCode
      (compactFormulaTransformTermOutputRowsClosedFormula tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount)).length <=
      compactFormulaTransformTermOutputRowsFullFormulaCodePolynomial
        bitBound := by
  let terms :=
    compactFormulaTransformTermOutputRowsClosedTerms tokenTable width
      tokenCount current next mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 33 :=
    Rewriting.emb (ξ := Nat)
      compactFormulaTransformTermOutputRowsDef.val
  have hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <=
        binaryNumeralTermCodeEnvelope bitBound := by
    intro coordinate
    have hsize := henvironmentSize coordinate
    fin_cases coordinate <;>
      simp [terms, compactFormulaTransformTermOutputRowsClosedTerms,
        compactFormulaTransformTermOutputRowsOuterTerms,
        compactFormulaTransformTermOutputRowsEnvironment] at hsize ⊢ <;>
      exact binaryNumeralTerm_code_length_le_envelope _ bitBound hsize
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 (binaryNumeralTermCodeEnvelope bitBound)
      (binaryFormulaCode source).length terms source hterms le_rfl
  unfold compactFormulaTransformTermOutputRowsClosedFormula
    compactFormulaTransformTermOutputRowsFullFormulaCodePolynomial
  simpa only [sourceSubstitutionQpow, terms, source,
    compactFormulaTransformTermOutputRowsClosedTerms] using hraw

theorem compactFormulaTransformTermOutputRowsClosedFormula_closed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) :
    (compactFormulaTransformTermOutputRowsClosedFormula tokenTable width
      tokenCount current next mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount).freeVariables = ∅ := by
  unfold compactFormulaTransformTermOutputRowsClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

#print axioms
  compactFormulaTransformTermOutputRowsClosedFormula_code_length_le_fixed
#print axioms compactFormulaTransformTermOutputRowsClosedFormula_closed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFormulaFixedBounds
