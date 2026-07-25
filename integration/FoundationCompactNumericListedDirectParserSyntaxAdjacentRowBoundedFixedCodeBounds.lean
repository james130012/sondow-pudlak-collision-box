import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSyntax
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Fixed code bounds for the bounded adjacent-row raw terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedFixedCodeBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSyntaxBase
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSubstitution

def compactParserSyntaxAdjacentRowBoundedRawTerminalFixedCodeEnvelope
    (bitBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 27
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      compactParserSyntaxAdjacentRowBoundedSourceRawTerminal).length

theorem compactParserSyntaxAdjacentRowBoundedSourceTerms_code_length_le
    (tokenTable width tokenCount stateBoundary stateCount index valueBound
      bitBound : Nat)
    (htokenTable : Nat.size tokenTable <= bitBound)
    (hwidth : Nat.size width <= bitBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hstateBoundary : Nat.size stateBoundary <= bitBound)
    (hstateCount : Nat.size stateCount <= bitBound)
    (hindex : Nat.size index <= bitBound)
    (hvalueBound : Nat.size valueBound <= bitBound) :
    forall coordinate,
      (binaryTermCode
        (compactParserSyntaxAdjacentRowBoundedSourceTerms tokenTable width
          tokenCount stateBoundary stateCount index valueBound coordinate)).length
        <= binaryNumeralTermCodeEnvelope bitBound := by
  intro coordinate
  fin_cases coordinate
  · exact binaryNumeralTerm_code_length_le_envelope tokenTable bitBound
      htokenTable
  · exact binaryNumeralTerm_code_length_le_envelope width bitBound hwidth
  · exact binaryNumeralTerm_code_length_le_envelope tokenCount bitBound
      htokenCount
  · exact binaryNumeralTerm_code_length_le_envelope stateBoundary bitBound
      hstateBoundary
  · exact binaryNumeralTerm_code_length_le_envelope stateCount bitBound
      hstateCount
  · exact binaryNumeralTerm_code_length_le_envelope index bitBound hindex
  · exact binaryNumeralTerm_code_length_le_envelope valueBound bitBound
      hvalueBound

theorem compactParserSyntaxAdjacentRowBoundedRawTerminal_code_length_le_fixed
    (tokenTable width tokenCount stateBoundary stateCount index valueBound
      bitBound : Nat)
    (htokenTable : Nat.size tokenTable <= bitBound)
    (hwidth : Nat.size width <= bitBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hstateBoundary : Nat.size stateBoundary <= bitBound)
    (hstateCount : Nat.size stateCount <= bitBound)
    (hindex : Nat.size index <= bitBound)
    (hvalueBound : Nat.size valueBound <= bitBound) :
    (binaryFormulaCode
      (compactParserSyntaxAdjacentRowBoundedRawTerminal tokenTable width
        tokenCount stateBoundary stateCount index valueBound)).length <=
      compactParserSyntaxAdjacentRowBoundedRawTerminalFixedCodeEnvelope
        bitBound := by
  rw [← compactParserSyntaxAdjacentRowBoundedSourceRawTerminal_rewriting
    tokenTable width tokenCount stateBoundary stateCount index valueBound]
  exact
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      27 (binaryNumeralTermCodeEnvelope bitBound)
      (binaryFormulaCode
        compactParserSyntaxAdjacentRowBoundedSourceRawTerminal).length
      (compactParserSyntaxAdjacentRowBoundedSourceTerms tokenTable width
        tokenCount stateBoundary stateCount index valueBound)
      compactParserSyntaxAdjacentRowBoundedSourceRawTerminal
      (compactParserSyntaxAdjacentRowBoundedSourceTerms_code_length_le
        tokenTable width tokenCount stateBoundary stateCount index valueBound
        bitBound htokenTable hwidth htokenCount hstateBoundary hstateCount
        hindex hvalueBound)
      le_rfl

theorem compactParserSyntaxAdjacentRowBoundedRawTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat) :
    (compactParserSyntaxAdjacentRowBoundedRawTerminal tokenTable width tokenCount
      stateBoundary stateCount index valueBound).freeVariables = ∅ := by
  unfold compactParserSyntaxAdjacentRowBoundedRawTerminal
  apply Finset.subset_empty.mp
  simp only [LO.FirstOrder.Semiformula.freeVariables_and]
  apply Finset.union_subset
  · apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate <;>
      simp [sourceSubstitutionLift_freeVariables_eq,
        shortBinaryNumeralTerm_freeVariables_eq_empty]
  · apply Finset.union_subset
    · apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
      intro coordinate
      fin_cases coordinate <;>
        simp [sourceSubstitutionLift_freeVariables_eq,
          shortBinaryNumeralTerm_freeVariables_eq_empty]
    · apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
      intro coordinate
      fin_cases coordinate <;>
        simp [sourceSubstitutionLift_freeVariables_eq,
          shortBinaryNumeralTerm_freeVariables_eq_empty]

theorem compactParserSyntaxAdjacentRowBoundedRawTerminal_context_eq_zero
    (tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat)
    (valuation : Nat -> Nat) :
    formulaCodeSum
      (valuationContext
        (compactParserSyntaxAdjacentRowBoundedRawTerminal tokenTable width
          tokenCount stateBoundary stateCount index valueBound).freeVariables
        valuation) = 0 := by
  rw [compactParserSyntaxAdjacentRowBoundedRawTerminal_freeVariables_eq_empty]
  simp [valuationContext, formulaCodeSum]

def compactParserSyntaxAdjacentRowBoundedFullyFixedPayloadPolynomial
    (index tokenCount valueBound numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 27 0 valueBound
    (compactParserSyntaxAdjacentRowBoundedRawTerminalFixedCodeEnvelope bitBound)
    (compactParserSyntaxAdjacentRowTerminalFullyFixedPayloadPolynomial index
      tokenCount numericBound bitBound)

#print axioms
  compactParserSyntaxAdjacentRowBoundedRawTerminal_code_length_le_fixed
#print axioms
  compactParserSyntaxAdjacentRowBoundedRawTerminal_freeVariables_eq_empty
#print axioms
  compactParserSyntaxAdjacentRowBoundedRawTerminal_context_eq_zero

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedFixedCodeBounds
