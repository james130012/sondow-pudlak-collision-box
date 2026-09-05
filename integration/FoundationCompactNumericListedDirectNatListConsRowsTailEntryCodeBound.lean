import integration.FoundationCompactNumericListedDirectNatListConsRowsTailEntryCoordinateBound

/-! # Formula-code projection for a fixed natural-list cons tail entry -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 240000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailEntryCodeBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryOpenIndexTermUniformCeilingBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListConsRowsTailEntryFixedBounds
open FoundationCompactNumericListedDirectNatListConsRowsTailEntryCoordinateBound

theorem natListConsRowsTailEntryCertificatePayloadAtTerms_le_fixed
    (valuation : Nat -> Nat)
    (boundary tokenCount value numericBound bitBound : Nat)
    (indexTerm : ValuationTerm)
    (htokenCount : tokenCount <= numericBound)
    (hindexValue : termValue valuation indexTerm <= numericBound)
    (hvaluation : valuation 0 <= numericBound)
    (hboundarySize : Nat.size boundary <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <=
      natListConsRowsTailOpenIndexTermCodeBound)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hentry : CompactFixedWidthEntry
      (termValue valuation (shortBinaryNumeralTerm boundary))
      (termValue valuation (shortBinaryNumeralTerm tokenCount))
      (termValue valuation indexTerm)
      (termValue valuation (shortBinaryNumeralTerm value))) :
    hybridFormulaStructuralPayloadBound
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
          (shortBinaryNumeralTerm boundary)
          (shortBinaryNumeralTerm tokenCount) indexTerm
          (shortBinaryNumeralTerm value) hentry) <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound := by
  let certificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm boundary) (shortBinaryNumeralTerm tokenCount)
      indexTerm (shortBinaryNumeralTerm value) hentry
  have hopen :
      hybridFormulaStructuralPayloadBound certificate <=
        compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
          valuation (shortBinaryNumeralTerm boundary)
          (shortBinaryNumeralTerm tokenCount) indexTerm
          (shortBinaryNumeralTerm value) := by
    dsimp only [certificate]
    exact
      compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
        valuation (shortBinaryNumeralTerm boundary)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm value)
        (shortBinaryNumeralTerm_freeVariables_eq_empty boundary)
        (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
        hindexVariables (shortBinaryNumeralTerm_freeVariables_eq_empty value)
        hentry
  have hfixed := natListConsRowsTailEntryPayload_le_fixed valuation boundary
    tokenCount value numericBound bitBound indexTerm htokenCount hindexValue
    hvaluation hboundarySize htokenCountSize hindexSize hvalueSize hindexCode
    hindexVariables
  simpa only [certificate] using hopen.trans hfixed

theorem natListConsRowsTailEntryCertificatePayload_le_fixed
    (valuation : Nat -> Nat)
    (boundary tokenCount value numericBound bitBound : Nat)
    (indexTerm : ValuationTerm)
    (htokenCount : tokenCount <= numericBound)
    (hindexValue : termValue valuation indexTerm <= numericBound)
    (hvaluation : valuation 0 <= numericBound)
    (hboundarySize : Nat.size boundary <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <=
      natListConsRowsTailOpenIndexTermCodeBound)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hentry : CompactFixedWidthEntry boundary tokenCount
      (termValue valuation indexTerm) value) :
    hybridFormulaStructuralPayloadBound
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
          (shortBinaryNumeralTerm boundary)
          (shortBinaryNumeralTerm tokenCount) indexTerm
          (shortBinaryNumeralTerm value) (by
            simpa only [termValue_shortBinaryNumeralTerm] using hentry)) <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound :=
  natListConsRowsTailEntryCertificatePayloadAtTerms_le_fixed valuation boundary
    tokenCount value numericBound bitBound indexTerm htokenCount hindexValue
    hvaluation hboundarySize htokenCountSize hindexSize hvalueSize hindexCode
    hindexVariables (by
      simpa only [termValue_shortBinaryNumeralTerm] using hentry)

theorem natListConsRowsTailEntryCode_le_fixed
    (valuation : Nat -> Nat)
    (boundary tokenCount value numericBound bitBound : Nat)
    (indexTerm : ValuationTerm)
    (htokenCount : tokenCount <= numericBound)
    (hindexValue : termValue valuation indexTerm <= numericBound)
    (hvaluation : valuation 0 <= numericBound)
    (hboundarySize : Nat.size boundary <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <=
      natListConsRowsTailOpenIndexTermCodeBound)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hentry : CompactFixedWidthEntry boundary tokenCount
      (termValue valuation indexTerm) value) :
    (binaryFormulaCode
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm boundary)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm value))).length <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound := by
  let certificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm boundary) (shortBinaryNumeralTerm tokenCount)
      indexTerm (shortBinaryNumeralTerm value) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hentry)
  have hpayload := natListConsRowsTailEntryCertificatePayload_le_fixed
    valuation boundary tokenCount value numericBound bitBound indexTerm
    htokenCount hindexValue hvaluation hboundarySize htokenCountSize hindexSize
    hvalueSize hindexCode hindexVariables hentry
  have hcode :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      certificate
  simpa only [certificate] using hcode.trans hpayload

#print axioms natListConsRowsTailEntryCertificatePayloadAtTerms_le_fixed
#print axioms natListConsRowsTailEntryCertificatePayload_le_fixed
#print axioms natListConsRowsTailEntryCode_le_fixed

end FoundationCompactNumericListedDirectNatListConsRowsTailEntryCodeBound
