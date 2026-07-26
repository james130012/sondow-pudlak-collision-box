import integration.FoundationCompactNumericListedDirectParserSyntaxAllClosureSpecializationFixedBounds
import integration.FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransportFixedTerms

/-! # Fixed payload bound for parser task-one transport -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransportFixedPayload

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransport
open FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransport
open FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransportFixedTerms

def compactParserSyntaxExactTaskOneTransportFixedPayloadPolynomial
    (numericBound : Nat) : Nat :=
  allClosureSpecializationFixedPayloadBound 15
    compactParserSyntaxExactTaskOneTransportProof.payloadLength
    (compactParserSyntaxExactTaskOneTransportTermCodePolynomial numericBound)

theorem compactParserSyntaxExactTaskOneTransportPublicProof_payload_le_fixed
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
    (compactParserSyntaxExactTaskOneTransportPublicProof tokenTable width
      tokenCount stateBoundary inputBoundary inputCount expectedBoundary
      expectedCount tableWidth valueBound).payloadLength <=
        compactParserSyntaxExactTaskOneTransportFixedPayloadPolynomial
          numericBound := by
  let publicTerms := compactParserSyntaxExactTaskOneTransportPublicTerms
    tokenTable width tokenCount stateBoundary inputBoundary inputCount
    expectedBoundary expectedCount tableWidth valueBound
  let baseProof : CertifiedPAProof
      (∀⁰* compactParserSyntaxExactTaskOneTransportBodyNat) :=
    CertifiedPAProof.cast
      compactParserSyntaxExactTaskOneTransportClosure_alignment.symm
      compactParserSyntaxExactTaskOneTransportProof
  have hbase : baseProof.payloadLength <=
      compactParserSyntaxExactTaskOneTransportProof.payloadLength := by
    dsimp only [baseProof]
    rw [CertifiedPAProof.cast_payloadLength]
  have hterms : ∀ coordinate,
      (binaryTermCode (publicTerms coordinate)).length <=
        compactParserSyntaxExactTaskOneTransportTermCodePolynomial
          numericBound := by
    exact compactParserSyntaxExactTaskOneTransportPublicTerms_code_le_fixed
      tokenTable width tokenCount stateBoundary inputBoundary inputCount
      expectedBoundary expectedCount tableWidth valueBound numericBound
      htokenTable hwidth htokenCount hstateBoundary hinputBoundary hinputCount
      hexpectedBoundary hexpectedCount htableWidth hvalueBound hnumericPositive
  have hspecialized := specializeAllClosure_payloadLength_le_fixed
    compactParserSyntaxExactTaskOneTransportBodyNat baseProof publicTerms
    compactParserSyntaxExactTaskOneTransportProof.payloadLength
    (compactParserSyntaxExactTaskOneTransportTermCodePolynomial numericBound)
    hbase hterms
  unfold compactParserSyntaxExactTaskOneTransportPublicProof
  rw [CertifiedPAProof.cast_payloadLength]
  simpa only [publicTerms, baseProof,
    compactParserSyntaxExactTaskOneTransportFixedPayloadPolynomial] using
      hspecialized

#print axioms
  compactParserSyntaxExactTaskOneTransportPublicProof_payload_le_fixed

end FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransportFixedPayload
