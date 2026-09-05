import integration.FoundationCompactNumericListedDirectNatListConsRowsTailTerminalSemanticBounds

/-! # Result interfaces for natural-list cons tail terminal leaves -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section
set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailTerminalLeafTypes

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectAtomicRowEqualityFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailEntryFixedBounds

structure NatListConsRowsTailLeafBounds
    {tokenTable width tokenCount sourceBoundary targetBoundary index : Nat}
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index)
    (numericBound bitBound : Nat) : Prop where
  sourceLeftPayload :
    hybridFormulaStructuralPayloadBound
        (consRowsTailSourceLeftCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data) <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound
  sourceLeftCode :
    (binaryFormulaCode
      (consRowsTailSourceLeftFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data)).length <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound
  sourceRightPayload :
    hybridFormulaStructuralPayloadBound
        (consRowsTailSourceRightCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data) <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound
  sourceRightCode :
    (binaryFormulaCode
      (consRowsTailSourceRightFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data)).length <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound
  targetLeftPayload :
    hybridFormulaStructuralPayloadBound
        (consRowsTailTargetLeftCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data) <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound
  targetLeftCode :
    (binaryFormulaCode
      (consRowsTailTargetLeftFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data)).length <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound
  targetRightPayload :
    hybridFormulaStructuralPayloadBound
        (consRowsTailTargetRightCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data) <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound
  targetRightCode :
    (binaryFormulaCode
      (consRowsTailTargetRightFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data)).length <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound
  atomicRowPayload :
    hybridFormulaStructuralPayloadBound
        (consRowsTailAtomicRowCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data) <=
      compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound
  atomicRowCode :
    (binaryFormulaCode
      (consRowsTailAtomicRowFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data)).length <=
      compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound

end FoundationCompactNumericListedDirectNatListConsRowsTailTerminalLeafTypes
