import integration.FoundationCompactNumericListedDirectNatListConsRowsTailTerminalLeafTypes

/-! # Source entry leaves for one natural-list cons tail terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 260000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailTerminalSourceLeafBounds

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

structure NatListConsRowsTailSourceLeafBounds
    {tokenTable width tokenCount sourceBoundary targetBoundary index : Nat}
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index)
    (numericBound bitBound : Nat) : Prop where
  leftPayload :
    hybridFormulaStructuralPayloadBound
        (consRowsTailSourceLeftCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data) <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound
  leftCode :
    (binaryFormulaCode
      (consRowsTailSourceLeftFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data)).length <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound
  rightPayload :
    hybridFormulaStructuralPayloadBound
        (consRowsTailSourceRightCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data) <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound
  rightCode :
    (binaryFormulaCode
      (consRowsTailSourceRightFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data)).length <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound

theorem buildNatListConsRowsTailSourceLeafBounds
    {tokenTable width tokenCount sourceBoundary targetBoundary index : Nat}
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index)
    (numericBound bitBound : Nat)
    (facts : NatListConsRowsTailFixedFacts data numericBound bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound) :
    NatListConsRowsTailSourceLeafBounds data numericBound bitBound := by
  let valuation := consRowsTailValuation index
  have hleftEntry : CompactFixedWidthEntry sourceBoundary tokenCount
      (termValue valuation consRowsTailIndexTerm) data.sourceLeft :=
    consRowsTailSourceLeftEntry tokenTable width tokenCount sourceBoundary
      targetBoundary index data
  have hrightEntry : CompactFixedWidthEntry sourceBoundary tokenCount
      (termValue valuation consRowsTailSuccessorTerm) data.sourceRight :=
    consRowsTailSourceRightEntry tokenTable width tokenCount sourceBoundary
      targetBoundary index data
  have hleftPayload :=
    natListConsRowsTailEntryCertificatePayloadAtTerms_le_fixed valuation
      sourceBoundary
      tokenCount data.sourceLeft numericBound bitBound consRowsTailIndexTerm
      facts.tokenCount_le (by
        simpa only [valuation, termValue_consRowsTailIndexTerm] using
          facts.index_le) facts.valuation_zero_le hsourceBoundarySize
      facts.tokenCount_size (by
        simpa only [valuation, termValue_consRowsTailIndexTerm] using
          facts.index_size) facts.sourceLeft_size
      consRowsTailIndexTerm_code_length_le
      consRowsTailIndexTerm_freeVariables_subset
      (consRowsTailSourceLeftEntryAtTerms tokenTable width tokenCount
        sourceBoundary targetBoundary index data)
  have hleftCode := natListConsRowsTailEntryCode_le_fixed valuation
    sourceBoundary tokenCount data.sourceLeft numericBound bitBound
    consRowsTailIndexTerm facts.tokenCount_le (by
      simpa only [valuation, termValue_consRowsTailIndexTerm] using
        facts.index_le) facts.valuation_zero_le hsourceBoundarySize
    facts.tokenCount_size (by
      simpa only [valuation, termValue_consRowsTailIndexTerm] using
        facts.index_size) facts.sourceLeft_size
    consRowsTailIndexTerm_code_length_le
    consRowsTailIndexTerm_freeVariables_subset hleftEntry
  have hrightPayload :=
    natListConsRowsTailEntryCertificatePayloadAtTerms_le_fixed valuation
      sourceBoundary
      tokenCount data.sourceRight numericBound bitBound consRowsTailSuccessorTerm
      facts.tokenCount_le (by
        simpa only [valuation, termValue_consRowsTailSuccessorTerm] using
          facts.successor_le) facts.valuation_zero_le hsourceBoundarySize
      facts.tokenCount_size (by
        simpa only [valuation, termValue_consRowsTailSuccessorTerm] using
          facts.successor_size) facts.sourceRight_size
      consRowsTailSuccessorTerm_code_length_le
      consRowsTailSuccessorTerm_freeVariables_subset
      (consRowsTailSourceRightEntryAtTerms tokenTable width tokenCount
        sourceBoundary targetBoundary index data)
  have hrightCode := natListConsRowsTailEntryCode_le_fixed valuation
    sourceBoundary tokenCount data.sourceRight numericBound bitBound
    consRowsTailSuccessorTerm facts.tokenCount_le (by
      simpa only [valuation, termValue_consRowsTailSuccessorTerm] using
        facts.successor_le) facts.valuation_zero_le hsourceBoundarySize
    facts.tokenCount_size (by
      simpa only [valuation, termValue_consRowsTailSuccessorTerm] using
        facts.successor_size) facts.sourceRight_size
    consRowsTailSuccessorTerm_code_length_le
    consRowsTailSuccessorTerm_freeVariables_subset hrightEntry
  have hleftCertificateEq :
      compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
          (shortBinaryNumeralTerm sourceBoundary)
          (shortBinaryNumeralTerm tokenCount) consRowsTailIndexTerm
          (shortBinaryNumeralTerm data.sourceLeft)
          (consRowsTailSourceLeftEntryAtTerms tokenTable width tokenCount
            sourceBoundary targetBoundary index data) =
        consRowsTailSourceLeftCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data := by
    rfl
  have hrightCertificateEq :
      compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
          (shortBinaryNumeralTerm sourceBoundary)
          (shortBinaryNumeralTerm tokenCount) consRowsTailSuccessorTerm
          (shortBinaryNumeralTerm data.sourceRight)
          (consRowsTailSourceRightEntryAtTerms tokenTable width tokenCount
            sourceBoundary targetBoundary index data) =
        consRowsTailSourceRightCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data := by
    rfl
  refine {
    leftPayload := ?_
    leftCode := ?_
    rightPayload := ?_
    rightCode := ?_ }
  · rw [← hleftCertificateEq]
    exact hleftPayload
  · simpa only [valuation, consRowsTailSourceLeftFormula] using hleftCode
  · rw [← hrightCertificateEq]
    exact hrightPayload
  · simpa only [valuation, consRowsTailSourceRightFormula] using hrightCode

#print axioms buildNatListConsRowsTailSourceLeafBounds

end FoundationCompactNumericListedDirectNatListConsRowsTailTerminalSourceLeafBounds
