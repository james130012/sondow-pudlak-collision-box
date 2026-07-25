import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Fixed complete syntax for formula-transform formula output rows

The original twenty-nine-coordinate Delta-zero formula is instantiated by
closed short binary numerals.  One explicit environment-wide bit bound controls
the complete formula code.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 80000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsFormulaFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRows
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate

def compactFormulaTransformFormulaOutputRowsClosedTerms
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat) :
    Fin 29 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm current.start,
    shortBinaryNumeralTerm current.finish,
    shortBinaryNumeralTerm current.parserFinish,
    shortBinaryNumeralTerm current.parserTokensFinish,
    shortBinaryNumeralTerm current.parserTasksFinish,
    shortBinaryNumeralTerm current.parserTokensBoundary,
    shortBinaryNumeralTerm current.parserTokensCount,
    shortBinaryNumeralTerm current.parserTasksBoundary,
    shortBinaryNumeralTerm current.parserTasksCount,
    shortBinaryNumeralTerm current.outputBoundary,
    shortBinaryNumeralTerm current.outputCount,
    shortBinaryNumeralTerm next.start,
    shortBinaryNumeralTerm next.finish,
    shortBinaryNumeralTerm next.parserFinish,
    shortBinaryNumeralTerm next.parserTokensFinish,
    shortBinaryNumeralTerm next.parserTasksFinish,
    shortBinaryNumeralTerm next.parserTokensBoundary,
    shortBinaryNumeralTerm next.parserTokensCount,
    shortBinaryNumeralTerm next.parserTasksBoundary,
    shortBinaryNumeralTerm next.parserTasksCount,
    shortBinaryNumeralTerm next.outputBoundary,
    shortBinaryNumeralTerm next.outputCount,
    shortBinaryNumeralTerm mode,
    shortBinaryNumeralTerm tag,
    shortBinaryNumeralTerm consumedCount,
    shortBinaryNumeralTerm mappedHead]

def compactFormulaTransformFormulaOutputRowsFullFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 29 :=
    Rewriting.emb (ξ := Nat)
      compactFormulaTransformFormulaOutputRowsDef.val
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0
    (binaryNumeralTermCodeEnvelope bitBound) (binaryFormulaCode source).length

theorem
    compactFormulaTransformFormulaOutputRowsClosedFormula_code_length_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead bitBound : Nat)
    (henvironmentSize : ∀ coordinate,
      Nat.size
        (compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
          tokenCount current next mode tag consumedCount mappedHead
          coordinate) <= bitBound) :
    (binaryFormulaCode
      (compactFormulaTransformFormulaOutputRowsClosedFormula tokenTable width
        tokenCount current next mode tag consumedCount mappedHead)).length <=
      compactFormulaTransformFormulaOutputRowsFullFormulaCodePolynomial
        bitBound := by
  let terms :=
    compactFormulaTransformFormulaOutputRowsClosedTerms tokenTable width
      tokenCount current next mode tag consumedCount mappedHead
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 29 :=
    Rewriting.emb (ξ := Nat)
      compactFormulaTransformFormulaOutputRowsDef.val
  have hterms : ∀ coordinate,
      (binaryTermCode (terms coordinate)).length <=
        binaryNumeralTermCodeEnvelope bitBound := by
    intro coordinate
    have hsize := henvironmentSize coordinate
    fin_cases coordinate <;>
      simp [terms, compactFormulaTransformFormulaOutputRowsClosedTerms,
        compactFormulaTransformFormulaOutputRowsEnvironment] at hsize ⊢ <;>
      exact binaryNumeralTerm_code_length_le_envelope _ bitBound hsize
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 (binaryNumeralTermCodeEnvelope bitBound)
      (binaryFormulaCode source).length terms source hterms le_rfl
  unfold compactFormulaTransformFormulaOutputRowsClosedFormula
    compactFormulaTransformFormulaOutputRowsFullFormulaCodePolynomial
  simpa only [sourceSubstitutionQpow, terms, source,
    compactFormulaTransformFormulaOutputRowsClosedTerms] using hraw

theorem compactFormulaTransformFormulaOutputRowsClosedFormula_closed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat) :
    (compactFormulaTransformFormulaOutputRowsClosedFormula tokenTable width
      tokenCount current next mode tag consumedCount
      mappedHead).freeVariables = ∅ := by
  unfold compactFormulaTransformFormulaOutputRowsClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

#print axioms
  compactFormulaTransformFormulaOutputRowsClosedFormula_code_length_le_fixed
#print axioms compactFormulaTransformFormulaOutputRowsClosedFormula_closed

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsFormulaFixedBounds
