import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
import integration.FoundationCompactSyntaxTransformationCodeBounds

/-! # Fixed code bound for the adjacent-row universal body -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedUniversalBodyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax

def compactParserSyntaxAdjacentRowsBoundedUniversalBodyTermCodePolynomial
    (bitBound : Nat) : Nat :=
  3 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 1)).length + 1

def compactParserSyntaxAdjacentRowsBoundedUniversalBodyCodePolynomial
    (bitBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0
    (compactParserSyntaxAdjacentRowsBoundedUniversalBodyTermCodePolynomial
      bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactParserSyntaxAdjacentRowBoundedDef.val)).length

private theorem shiftedShortNumeral_code_length_le_adjacentBody
    (value bitBound : Nat) (hsize : Nat.size value <= bitBound) :
    (binaryTermCode
      (Rew.bShift (shortBinaryNumeralTerm value) :
        ArithmeticSemiterm Nat 1)).length <=
      compactParserSyntaxAdjacentRowsBoundedUniversalBodyTermCodePolynomial
        bitBound := by
  have hshort := binaryNumeralTerm_code_length_le_envelope value bitBound hsize
  have hsymbols := termSymbolCount_le_binaryTermCode_length
    (shortBinaryNumeralTerm value : ValuationTerm)
  have hshift := binaryTermCode_bShift_length_le_add_symbols
    (shortBinaryNumeralTerm value : ValuationTerm)
  unfold compactParserSyntaxAdjacentRowsBoundedUniversalBodyTermCodePolynomial
  omega

theorem compactParserSyntaxAdjacentRowsBoundedUniversalBody_code_length_le_fixed
    (tokenTable width tokenCount stateBoundary stateCount valueBound bitBound :
      Nat)
    (htokenTable : Nat.size tokenTable <= bitBound)
    (hwidth : Nat.size width <= bitBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hstateBoundary : Nat.size stateBoundary <= bitBound)
    (hstateCount : Nat.size stateCount <= bitBound)
    (hvalueBound : Nat.size valueBound <= bitBound) :
    (binaryFormulaCode
      (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
        tokenCount stateBoundary stateCount valueBound)).length <=
      compactParserSyntaxAdjacentRowsBoundedUniversalBodyCodePolynomial
        bitBound := by
  let terms : Fin 7 -> ArithmeticSemiterm Nat 1 :=
    ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
      Rew.bShift (shortBinaryNumeralTerm width),
      Rew.bShift (shortBinaryNumeralTerm tokenCount),
      Rew.bShift (shortBinaryNumeralTerm stateBoundary),
      Rew.bShift (shortBinaryNumeralTerm stateCount),
      (#0 : ArithmeticSemiterm Nat 1),
      Rew.bShift (shortBinaryNumeralTerm valueBound)]
  let source : ArithmeticSemiformula Nat 7 :=
    Rewriting.emb (ξ := Nat) compactParserSyntaxAdjacentRowBoundedDef.val
  have hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <=
        compactParserSyntaxAdjacentRowsBoundedUniversalBodyTermCodePolynomial
          bitBound := by
    intro coordinate
    fin_cases coordinate
    · exact shiftedShortNumeral_code_length_le_adjacentBody tokenTable bitBound
        htokenTable
    · exact shiftedShortNumeral_code_length_le_adjacentBody width bitBound
        hwidth
    · exact shiftedShortNumeral_code_length_le_adjacentBody tokenCount bitBound
        htokenCount
    · exact shiftedShortNumeral_code_length_le_adjacentBody stateBoundary
        bitBound hstateBoundary
    · exact shiftedShortNumeral_code_length_le_adjacentBody stateCount bitBound
        hstateCount
    · change (binaryTermCode (#0 : ArithmeticSemiterm Nat 1)).length <= _
      unfold compactParserSyntaxAdjacentRowsBoundedUniversalBodyTermCodePolynomial
      omega
    · exact shiftedShortNumeral_code_length_le_adjacentBody valueBound bitBound
        hvalueBound
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0
      (compactParserSyntaxAdjacentRowsBoundedUniversalBodyTermCodePolynomial
        bitBound)
      (binaryFormulaCode source).length terms source hterms le_rfl
  unfold compactParserSyntaxAdjacentRowsBoundedUniversalBody
    compactParserSyntaxAdjacentRowsBoundedUniversalBodyCodePolynomial
  simpa only [sourceSubstitutionQpow, terms, source] using hraw

#print axioms
  compactParserSyntaxAdjacentRowsBoundedUniversalBody_code_length_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedUniversalBodyFixedBounds
