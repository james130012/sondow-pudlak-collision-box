import integration.FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransport
import integration.FoundationCompactNumericListedDirectParserSyntaxExactFuelFixedBounds

/-! # Fixed term-code bounds for parser task-one transport -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 350000

namespace FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransportFixedTerms

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserSyntaxExactFuelFixedBounds
open FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransport

def compactParserSyntaxExactTaskOneTransportTermCodePolynomial
    (numericBound : Nat) : Nat :=
  boundedWitnessNumeralTermCodeEnvelope numericBound +
    compactParserSyntaxExactStateCountTermFixedCodePolynomial numericBound +
    (binaryTermCode compactParserSyntaxExactNativeOneTerm).length + 1

theorem compactParserSyntaxExactTaskOneTransportPublicTerms_code_le_fixed
    (tokenTable width tokenCount stateBoundary inputBoundary inputCount
      expectedBoundary expectedCount tableWidth valueBound numericBound : Nat)
    (htokenTable : tokenTable <= numericBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateBoundary : stateBoundary <= numericBound)
    (hinputBoundary : inputBoundary <= numericBound)
    (hinputCount : inputCount <= numericBound)
    (hexpectedBoundary : expectedBoundary <= numericBound)
    (hexpectedCount : expectedCount <= numericBound)
    (htableWidth : tableWidth <= numericBound)
    (hvalueBound : valueBound <= numericBound)
    (hnumericPositive : 1 <= numericBound) :
    ∀ coordinate,
      (binaryTermCode
        (compactParserSyntaxExactTaskOneTransportPublicTerms tokenTable width
          tokenCount stateBoundary inputBoundary inputCount expectedBoundary
          expectedCount tableWidth valueBound coordinate)).length <=
        compactParserSyntaxExactTaskOneTransportTermCodePolynomial
          numericBound := by
  have hshort (value : Nat) (hvalue : value <= numericBound) :
      (binaryTermCode (shortBinaryNumeralTerm value)).length <=
        compactParserSyntaxExactTaskOneTransportTermCodePolynomial
          numericBound := by
    have hraw := shortBinaryNumeralTerm_code_length_le_bound value numericBound
      hvalue
    unfold compactParserSyntaxExactTaskOneTransportTermCodePolynomial
    omega
  have hexact :
      (binaryTermCode (compactParserSyntaxExactStateCountTerm inputCount)).length <=
        compactParserSyntaxExactTaskOneTransportTermCodePolynomial
          numericBound := by
    have hraw := compactParserSyntaxExactStateCountTerm_code_length_le_fixed
      inputCount numericBound hinputCount
    unfold compactParserSyntaxExactTaskOneTransportTermCodePolynomial
    omega
  have hnative :
      (binaryTermCode compactParserSyntaxExactNativeOneTerm).length <=
        compactParserSyntaxExactTaskOneTransportTermCodePolynomial
          numericBound := by
    unfold compactParserSyntaxExactTaskOneTransportTermCodePolynomial
    omega
  intro coordinate
  fin_cases coordinate
  · exact hshort tokenTable htokenTable
  · exact hshort width hwidth
  · exact hshort tokenCount htokenCount
  · exact hshort stateBoundary hstateBoundary
  · change (binaryTermCode
        (‘!!(compactParserSyntaxExactFuelTerm inputCount) + 1’ :
          ValuationTerm)).length <= _
    simpa only [compactParserSyntaxExactStateCountTerm] using hexact
  · exact hshort inputBoundary hinputBoundary
  · exact hshort inputCount hinputCount
  · exact hshort expectedBoundary hexpectedBoundary
  · exact hshort expectedCount hexpectedCount
  · exact hshort 1 hnumericPositive
  · exact hnative
  · exact hshort 0 (Nat.zero_le _)
  · exact hshort 0 (Nat.zero_le _)
  · exact hshort tableWidth htableWidth
  · exact hshort valueBound hvalueBound

#print axioms
  compactParserSyntaxExactTaskOneTransportPublicTerms_code_le_fixed

end FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransportFixedTerms
