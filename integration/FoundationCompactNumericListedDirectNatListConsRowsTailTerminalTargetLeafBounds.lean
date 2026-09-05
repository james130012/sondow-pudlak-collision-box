import integration.FoundationCompactNumericListedDirectNatListConsRowsTailTerminalLeafTypes

/-! # Target entry leaves for one natural-list cons tail terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 260000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailTerminalTargetLeafBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailEntryCodeBound
open FoundationCompactNumericListedDirectNatListConsRowsTailEntryFixedBounds
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalSemanticBounds

structure NatListConsRowsTailTargetLeafBounds
    {tokenTable width tokenCount sourceBoundary targetBoundary index : Nat}
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index)
    (numericBound bitBound : Nat) : Prop where
  leftPayload :
    hybridFormulaStructuralPayloadBound
        (consRowsTailTargetLeftCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data) <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound
  leftCode :
    (binaryFormulaCode
      (consRowsTailTargetLeftFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data)).length <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound
  rightPayload :
    hybridFormulaStructuralPayloadBound
        (consRowsTailTargetRightCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data) <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound
  rightCode :
    (binaryFormulaCode
      (consRowsTailTargetRightFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data)).length <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound

theorem buildNatListConsRowsTailTargetLeafBounds
    {tokenTable width tokenCount sourceBoundary targetBoundary index : Nat}
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index)
    (numericBound bitBound : Nat)
    (facts : NatListConsRowsTailFixedFacts data numericBound bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    NatListConsRowsTailTargetLeafBounds data numericBound bitBound := by
  let valuation := consRowsTailValuation index
  have hleftEntry : CompactFixedWidthEntry targetBoundary tokenCount
      (termValue valuation consRowsTailSuccessorTerm) data.targetLeft :=
    consRowsTailTargetLeftEntry tokenTable width tokenCount sourceBoundary
      targetBoundary index data
  have hrightEntry : CompactFixedWidthEntry targetBoundary tokenCount
      (termValue valuation consRowsTailSecondSuccessorTerm) data.targetRight :=
    consRowsTailTargetRightEntry tokenTable width tokenCount sourceBoundary
      targetBoundary index data
  have hleftPayload :=
    natListConsRowsTailEntryCertificatePayloadAtTerms_le_fixed valuation
      targetBoundary tokenCount data.targetLeft numericBound bitBound
      consRowsTailSuccessorTerm facts.tokenCount_le (by
        simpa only [valuation, termValue_consRowsTailSuccessorTerm] using
          facts.successor_le) facts.valuation_zero_le htargetBoundarySize
      facts.tokenCount_size (by
        simpa only [valuation, termValue_consRowsTailSuccessorTerm] using
          facts.successor_size) facts.targetLeft_size
      consRowsTailSuccessorTerm_code_length_le
      consRowsTailSuccessorTerm_freeVariables_subset
      (consRowsTailTargetLeftEntryAtTerms tokenTable width tokenCount
        sourceBoundary targetBoundary index data)
  have hleftCode := natListConsRowsTailEntryCode_le_fixed valuation
    targetBoundary tokenCount data.targetLeft numericBound bitBound
    consRowsTailSuccessorTerm facts.tokenCount_le (by
      simpa only [valuation, termValue_consRowsTailSuccessorTerm] using
        facts.successor_le) facts.valuation_zero_le htargetBoundarySize
    facts.tokenCount_size (by
      simpa only [valuation, termValue_consRowsTailSuccessorTerm] using
        facts.successor_size) facts.targetLeft_size
    consRowsTailSuccessorTerm_code_length_le
    consRowsTailSuccessorTerm_freeVariables_subset hleftEntry
  have hrightPayload :=
    natListConsRowsTailEntryCertificatePayloadAtTerms_le_fixed valuation
      targetBoundary tokenCount data.targetRight numericBound bitBound
      consRowsTailSecondSuccessorTerm facts.tokenCount_le (by
        simpa only [valuation, termValue_consRowsTailSecondSuccessorTerm] using
          facts.secondSuccessor_le) facts.valuation_zero_le htargetBoundarySize
      facts.tokenCount_size (by
        simpa only [valuation, termValue_consRowsTailSecondSuccessorTerm] using
          facts.secondSuccessor_size) facts.targetRight_size
      consRowsTailSecondSuccessorTerm_code_length_le
      consRowsTailSecondSuccessorTerm_freeVariables_subset
      (consRowsTailTargetRightEntryAtTerms tokenTable width tokenCount
        sourceBoundary targetBoundary index data)
  have hrightCode := natListConsRowsTailEntryCode_le_fixed valuation
    targetBoundary tokenCount data.targetRight numericBound bitBound
    consRowsTailSecondSuccessorTerm facts.tokenCount_le (by
      simpa only [valuation, termValue_consRowsTailSecondSuccessorTerm] using
        facts.secondSuccessor_le) facts.valuation_zero_le htargetBoundarySize
    facts.tokenCount_size (by
      simpa only [valuation, termValue_consRowsTailSecondSuccessorTerm] using
        facts.secondSuccessor_size) facts.targetRight_size
    consRowsTailSecondSuccessorTerm_code_length_le
    consRowsTailSecondSuccessorTerm_freeVariables_subset hrightEntry
  have hleftCertificateEq :
      compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
          (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount) consRowsTailSuccessorTerm
          (shortBinaryNumeralTerm data.targetLeft)
          (consRowsTailTargetLeftEntryAtTerms tokenTable width tokenCount
            sourceBoundary targetBoundary index data) =
        consRowsTailTargetLeftCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data := by
    rfl
  have hrightCertificateEq :
      compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
          (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount)
          consRowsTailSecondSuccessorTerm
          (shortBinaryNumeralTerm data.targetRight)
          (consRowsTailTargetRightEntryAtTerms tokenTable width tokenCount
            sourceBoundary targetBoundary index data) =
        consRowsTailTargetRightCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data := by
    rfl
  refine {
    leftPayload := ?_
    leftCode := ?_
    rightPayload := ?_
    rightCode := ?_ }
  · rw [← hleftCertificateEq]
    exact hleftPayload
  · simpa only [valuation, consRowsTailTargetLeftFormula] using hleftCode
  · rw [← hrightCertificateEq]
    exact hrightPayload
  · simpa only [valuation, consRowsTailTargetRightFormula] using hrightCode

#print axioms buildNatListConsRowsTailTargetLeafBounds

end FoundationCompactNumericListedDirectNatListConsRowsTailTerminalTargetLeafBounds
