import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexSyntax
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds

/-!
# Fixed syntax bounds for one open-index bounded sequent row
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexFixedCodeBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexSyntax

def compactSequentFormulaStepRowBoundedAtValuationIndexPublicTermCodeEnvelope
    (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (&0 : ValuationTerm)).length

def compactSequentFormulaStepRowBoundedAtValuationIndexRawBodyFixedCodeEnvelope
    (bitBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 18
    (compactSequentFormulaStepRowBoundedAtValuationIndexPublicTermCodeEnvelope
      bitBound)
    (binaryFormulaCode
      compactSequentFormulaStepRowBoundedDirectSourceRawTerminal).length

theorem
    compactSequentFormulaStepRowBoundedAtValuationIndexPublicTerms_code_length_le
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueBound bitBound : Nat)
    (htokenTable : Nat.size tokenTable <= bitBound)
    (hwidth : Nat.size width <= bitBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hsuffixBoundary : Nat.size suffixBoundary <= bitBound)
    (hsuffixCount : Nat.size suffixCount <= bitBound)
    (hvalueBoundary : Nat.size valueBoundary <= bitBound)
    (hvalueCount : Nat.size valueCount <= bitBound)
    (hvalueBound : Nat.size valueBound <= bitBound) :
    forall coordinate,
      (binaryTermCode
        (compactSequentFormulaStepRowBoundedAtValuationIndexPublicTerms
          tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount valueBound (&0 : ValuationTerm) coordinate)).length <=
        compactSequentFormulaStepRowBoundedAtValuationIndexPublicTermCodeEnvelope
          bitBound := by
  intro coordinate
  fin_cases coordinate
  · exact (binaryNumeralTerm_code_length_le_envelope tokenTable bitBound
      htokenTable).trans (Nat.le_add_right _ _)
  · exact (binaryNumeralTerm_code_length_le_envelope width bitBound
      hwidth).trans (Nat.le_add_right _ _)
  · exact (binaryNumeralTerm_code_length_le_envelope tokenCount bitBound
      htokenCount).trans (Nat.le_add_right _ _)
  · exact (binaryNumeralTerm_code_length_le_envelope suffixBoundary bitBound
      hsuffixBoundary).trans (Nat.le_add_right _ _)
  · exact (binaryNumeralTerm_code_length_le_envelope suffixCount bitBound
      hsuffixCount).trans (Nat.le_add_right _ _)
  · exact (binaryNumeralTerm_code_length_le_envelope valueBoundary bitBound
      hvalueBoundary).trans (Nat.le_add_right _ _)
  · exact (binaryNumeralTerm_code_length_le_envelope valueCount bitBound
      hvalueCount).trans (Nat.le_add_right _ _)
  · unfold
      compactSequentFormulaStepRowBoundedAtValuationIndexPublicTermCodeEnvelope
    exact Nat.le_add_left _ _
  · exact (binaryNumeralTerm_code_length_le_envelope valueBound bitBound
      hvalueBound).trans (Nat.le_add_right _ _)

theorem
    compactSequentFormulaStepRowBoundedAtValuationIndexRawBody_code_length_le_fixed
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueBound bitBound : Nat)
    (htokenTable : Nat.size tokenTable <= bitBound)
    (hwidth : Nat.size width <= bitBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hsuffixBoundary : Nat.size suffixBoundary <= bitBound)
    (hsuffixCount : Nat.size suffixCount <= bitBound)
    (hvalueBoundary : Nat.size valueBoundary <= bitBound)
    (hvalueCount : Nat.size valueCount <= bitBound)
    (hvalueBound : Nat.size valueBound <= bitBound) :
    (binaryFormulaCode
      (compactSequentFormulaStepRowBoundedAtOpenIndexRawBody tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount)).length <=
      compactSequentFormulaStepRowBoundedAtValuationIndexRawBodyFixedCodeEnvelope
        bitBound := by
  unfold compactSequentFormulaStepRowBoundedAtOpenIndexRawBody
  rw [←
    compactSequentFormulaStepRowBoundedAtValuationIndexSourceRawTerminal_rewriting
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueBound (&0 : ValuationTerm)]
  exact
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      18
      (compactSequentFormulaStepRowBoundedAtValuationIndexPublicTermCodeEnvelope
        bitBound)
      (binaryFormulaCode
        compactSequentFormulaStepRowBoundedDirectSourceRawTerminal).length
      (compactSequentFormulaStepRowBoundedAtValuationIndexPublicTerms tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        valueBound (&0 : ValuationTerm))
      compactSequentFormulaStepRowBoundedDirectSourceRawTerminal
      (compactSequentFormulaStepRowBoundedAtValuationIndexPublicTerms_code_length_le
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount valueBound bitBound htokenTable hwidth htokenCount
        hsuffixBoundary hsuffixCount hvalueBoundary hvalueCount hvalueBound)
      le_rfl

#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexRawBody_code_length_le_fixed

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexFixedCodeBounds
