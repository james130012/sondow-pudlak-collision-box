import integration.FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransport
import integration.FoundationCompactNumericListedDirectParserSyntaxExactFuelFixedBounds

/-! # Fixed term-code and payload bounds for exact state-count transport -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransportFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserSyntaxExactFuelFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransport

def compactParserSyntaxExactStateCountTransportTermCodePolynomial
    (numericBound : Nat) : Nat :=
  boundedWitnessNumeralTermCodeEnvelope numericBound +
    compactParserSyntaxExactStateCountTermFixedCodePolynomial numericBound

theorem compactParserSyntaxExactStateCountTransportPublicTerms_code_le_fixed
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound numericBound : Nat)
    (htokenTable : tokenTable <= numericBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateBoundary : stateBoundary <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hinputBoundary : inputBoundary <= numericBound)
    (hinputCount : inputCount <= numericBound)
    (hexpectedBoundary : expectedBoundary <= numericBound)
    (hexpectedCount : expectedCount <= numericBound)
    (htaskKind : taskKind <= numericBound)
    (htaskBinderArity : taskBinderArity <= numericBound)
    (htaskRepeatCount : taskRepeatCount <= numericBound)
    (htableWidth : tableWidth <= numericBound)
    (hvalueBound : valueBound <= numericBound) :
    ∀ coordinate,
      (binaryTermCode
        (compactParserSyntaxExactStateCountTransportPublicTerms tokenTable
          width tokenCount stateBoundary stateCount inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount tableWidth valueBound coordinate)).length <=
        compactParserSyntaxExactStateCountTransportTermCodePolynomial
          numericBound := by
  have hshort (value : Nat) (hvalue : value <= numericBound) :
      (binaryTermCode (shortBinaryNumeralTerm value)).length <=
        compactParserSyntaxExactStateCountTransportTermCodePolynomial
          numericBound := by
    have hraw := shortBinaryNumeralTerm_code_length_le_bound value numericBound
      hvalue
    unfold compactParserSyntaxExactStateCountTransportTermCodePolynomial
    omega
  have hexact :
      (binaryTermCode (compactParserSyntaxExactStateCountTerm inputCount)).length <=
        compactParserSyntaxExactStateCountTransportTermCodePolynomial
          numericBound := by
    have hraw := compactParserSyntaxExactStateCountTerm_code_length_le_fixed
      inputCount numericBound hinputCount
    unfold compactParserSyntaxExactStateCountTransportTermCodePolynomial
    omega
  intro coordinate
  fin_cases coordinate
  · exact hshort tokenTable htokenTable
  · exact hshort width hwidth
  · exact hshort tokenCount htokenCount
  · exact hshort stateBoundary hstateBoundary
  · exact hshort stateCount hstateCount
  · change (binaryTermCode
        (‘!!(compactParserSyntaxExactFuelTerm inputCount) + 1’ :
          ValuationTerm)).length <= _
    simpa only [compactParserSyntaxExactStateCountTerm] using hexact
  · exact hshort inputBoundary hinputBoundary
  · exact hshort inputCount hinputCount
  · exact hshort expectedBoundary hexpectedBoundary
  · exact hshort expectedCount hexpectedCount
  · exact hshort taskKind htaskKind
  · exact hshort taskBinderArity htaskBinderArity
  · exact hshort taskRepeatCount htaskRepeatCount
  · exact hshort tableWidth htableWidth
  · exact hshort valueBound hvalueBound

#print axioms
  compactParserSyntaxExactStateCountTransportPublicTerms_code_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransportFixedBounds
