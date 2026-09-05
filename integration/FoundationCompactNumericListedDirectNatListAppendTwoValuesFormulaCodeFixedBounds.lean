import integration.FoundationCompactNumericListedDirectNatListAppendTwoValuesTermFixedBounds
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds

/-! # Fixed formula code for appending two exact values -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 180000

namespace FoundationCompactNumericListedDirectNatListAppendTwoValuesFormulaFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectNatListAppendTwoValues
open FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate

def appendTwoExactFullFormulaCodePolynomial (bitBound : Nat) : Nat :=
  let termCode := appendTwoExactTermCodePolynomial bitBound
  let source : ArithmeticSemiformula Nat 12 :=
    Rewriting.emb (ξ := Nat) compactAdditiveNatListAppendTwoValuesDef.val
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0 termCode
    (binaryFormulaCode source).length

theorem
    compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula_code_length_le_fixed
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount bitBound : Nat)
    (firstTerm secondTerm : ValuationTerm)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (hsourceFinishSize : Nat.size sourceFinish <= bitBound)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound)
    (htargetFinishSize : Nat.size targetFinish <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (htargetCountSize : Nat.size targetCount <= bitBound)
    (hfirstCode : (binaryTermCode firstTerm).length <=
      appendTwoExactTermCodePolynomial bitBound)
    (hsecondCode : (binaryTermCode secondTerm).length <=
      appendTwoExactTermCodePolynomial bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
        tokenTable width tokenCount sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount firstTerm
        secondTerm)).length <=
      appendTwoExactFullFormulaCodePolynomial bitBound := by
  let terms := appendTwoAtValuationValuesTerms tokenTable width tokenCount
    sourceStart sourceFinish sourceCount targetStart targetFinish targetBoundary
    targetCount firstTerm secondTerm
  let termCode := appendTwoExactTermCodePolynomial bitBound
  let source : ArithmeticSemiformula Nat 12 :=
    Rewriting.emb (ξ := Nat) compactAdditiveNatListAppendTwoValuesDef.val
  have hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · simpa [terms, termCode, appendTwoAtValuationValuesTerms] using
        appendTwoShortNumeralCode_le tokenTable bitBound htableSize
    · simpa [terms, termCode, appendTwoAtValuationValuesTerms] using
        appendTwoShortNumeralCode_le width bitBound hwidthSize
    · simpa [terms, termCode, appendTwoAtValuationValuesTerms] using
        appendTwoShortNumeralCode_le tokenCount bitBound htokenCountSize
    · simpa [terms, termCode, appendTwoAtValuationValuesTerms] using
        appendTwoShortNumeralCode_le sourceStart bitBound hsourceStartSize
    · simpa [terms, termCode, appendTwoAtValuationValuesTerms] using
        appendTwoShortNumeralCode_le sourceFinish bitBound hsourceFinishSize
    · simpa [terms, termCode, appendTwoAtValuationValuesTerms] using
        appendTwoShortNumeralCode_le sourceCount bitBound hsourceCountSize
    · simpa [terms, termCode, appendTwoAtValuationValuesTerms] using
        appendTwoShortNumeralCode_le targetStart bitBound htargetStartSize
    · simpa [terms, termCode, appendTwoAtValuationValuesTerms] using
        appendTwoShortNumeralCode_le targetFinish bitBound htargetFinishSize
    · simpa [terms, termCode, appendTwoAtValuationValuesTerms] using
        appendTwoShortNumeralCode_le targetBoundary bitBound
          htargetBoundarySize
    · simpa [terms, termCode, appendTwoAtValuationValuesTerms] using
        appendTwoShortNumeralCode_le targetCount bitBound htargetCountSize
    · simpa [terms, termCode, appendTwoAtValuationValuesTerms] using hfirstCode
    · simpa [terms, termCode, appendTwoAtValuationValuesTerms] using hsecondCode
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 termCode (binaryFormulaCode source).length terms source hterms le_rfl
  unfold compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula
    appendTwoExactFullFormulaCodePolynomial
  simpa only [sourceSubstitutionQpow, terms, termCode, source,
    appendTwoAtValuationValuesTerms] using hraw

#print axioms
  compactAdditiveNatListAppendTwoValuesAtValuationValuesFormula_code_length_le_fixed

end FoundationCompactNumericListedDirectNatListAppendTwoValuesFormulaFixedBounds
