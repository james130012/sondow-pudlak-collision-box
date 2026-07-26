import integration.FoundationCompactNumericListedDirectParserSyntaxAllClosureSpecializationFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransportFixedBounds

/-! # Fixed payload bound for exact state-count transport -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransportFixedPayload

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransport
open FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransportFixedBounds

def compactParserSyntaxExactStateCountTransportFixedPayloadPolynomial
    (numericBound : Nat) : Nat :=
  allClosureSpecializationFixedPayloadBound 15
    compactParserSyntaxExactStateCountTransportProof.payloadLength
    (compactParserSyntaxExactStateCountTransportTermCodePolynomial numericBound)

theorem compactParserSyntaxExactStateCountTransportPublicProof_payload_le_fixed
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
    (compactParserSyntaxExactStateCountTransportPublicProof tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound).payloadLength <=
        compactParserSyntaxExactStateCountTransportFixedPayloadPolynomial
          numericBound := by
  let publicTerms := compactParserSyntaxExactStateCountTransportPublicTerms
    tokenTable width tokenCount stateBoundary stateCount inputBoundary
    inputCount expectedBoundary expectedCount taskKind taskBinderArity
    taskRepeatCount tableWidth valueBound
  let baseProof : CertifiedPAProof
      (∀⁰* compactParserSyntaxExactStateCountTransportBodyNat) :=
    CertifiedPAProof.cast
      compactParserSyntaxExactStateCountTransportClosure_alignment.symm
      compactParserSyntaxExactStateCountTransportProof
  have hbase : baseProof.payloadLength <=
      compactParserSyntaxExactStateCountTransportProof.payloadLength := by
    dsimp only [baseProof]
    rw [CertifiedPAProof.cast_payloadLength]
  have hterms : ∀ coordinate,
      (binaryTermCode (publicTerms coordinate)).length <=
        compactParserSyntaxExactStateCountTransportTermCodePolynomial
          numericBound := by
    exact compactParserSyntaxExactStateCountTransportPublicTerms_code_le_fixed
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound numericBound htokenTable hwidth
      htokenCount hstateBoundary hstateCount hinputBoundary hinputCount
      hexpectedBoundary hexpectedCount htaskKind htaskBinderArity
      htaskRepeatCount htableWidth hvalueBound
  have hspecialized := specializeAllClosure_payloadLength_le_fixed
    compactParserSyntaxExactStateCountTransportBodyNat baseProof publicTerms
    compactParserSyntaxExactStateCountTransportProof.payloadLength
    (compactParserSyntaxExactStateCountTransportTermCodePolynomial numericBound)
    hbase hterms
  unfold compactParserSyntaxExactStateCountTransportPublicProof
  rw [CertifiedPAProof.cast_payloadLength]
  simpa only [publicTerms, baseProof,
    compactParserSyntaxExactStateCountTransportFixedPayloadPolynomial] using
      hspecialized

#print axioms
  compactParserSyntaxExactStateCountTransportPublicProof_payload_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransportFixedPayload
