import integration.FoundationCompactNumericListedDirectNatListConsRowsTailTerminalLeafTypes

/-! # Atomic-row leaf for one natural-list cons tail terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 220000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailTerminalAtomicLeafBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectAtomicRowEqualityExplicitHybridCertificate
open FoundationCompactNumericListedDirectAtomicRowEqualityFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailAtomicRowCodeBound
open FoundationCompactNumericListedDirectNatListConsRowsTailCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalSemanticBounds

structure NatListConsRowsTailAtomicLeafBounds
    {tokenTable width tokenCount sourceBoundary targetBoundary index : Nat}
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index)
    (numericBound bitBound : Nat) : Prop where
  payload :
    hybridFormulaStructuralPayloadBound
        (consRowsTailAtomicRowCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data) <=
      compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound
  code :
    (binaryFormulaCode
      (consRowsTailAtomicRowFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data)).length <=
      compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound

theorem buildNatListConsRowsTailAtomicLeafBounds
    {tokenTable width tokenCount sourceBoundary targetBoundary index : Nat}
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index)
    (numericBound bitBound : Nat)
    (facts : NatListConsRowsTailFixedFacts data numericBound bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    NatListConsRowsTailAtomicLeafBounds data numericBound bitBound := by
  let valuation := consRowsTailValuation index
  have hpayload :=
    natListConsRowsTailAtomicRowCertificatePayloadAtTerms_le_fixed valuation
      tokenTable width tokenCount data.sourceLeft data.sourceRight
      data.targetLeft data.targetRight numericBound bitBound facts.width_le
      facts.tokenCount_le facts.sourceLeft_le facts.sourceRight_le
      facts.targetLeft_le facts.targetRight_le htokenTableSize hnumericSize
      (consRowsTailAtomicRowAtTerms tokenTable width tokenCount sourceBoundary
        targetBoundary index data)
  have hcode := natListConsRowsTailAtomicRowCode_le_fixed valuation tokenTable
    width tokenCount data.sourceLeft data.sourceRight data.targetLeft
    data.targetRight numericBound bitBound facts.width_le facts.tokenCount_le
    facts.sourceLeft_le facts.sourceRight_le facts.targetLeft_le
    facts.targetRight_le htokenTableSize hnumericSize data.atomic_row_eq
  have hcertificateEq :
      compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate valuation
          (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm data.sourceLeft)
          (shortBinaryNumeralTerm data.sourceRight)
          (shortBinaryNumeralTerm data.targetLeft)
          (shortBinaryNumeralTerm data.targetRight)
          (consRowsTailAtomicRowAtTerms tokenTable width tokenCount
            sourceBoundary targetBoundary index data) =
        consRowsTailAtomicRowCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data := by
    rfl
  refine {
    payload := ?_
    code := ?_ }
  · rw [← hcertificateEq]
    exact hpayload
  · simpa only [valuation, consRowsTailAtomicRowFormula] using hcode

#print axioms buildNatListConsRowsTailAtomicLeafBounds

end FoundationCompactNumericListedDirectNatListConsRowsTailTerminalAtomicLeafBounds
