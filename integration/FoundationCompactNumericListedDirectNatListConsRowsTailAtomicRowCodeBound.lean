import integration.FoundationCompactNumericListedDirectNatListConsRowsTailAtomicRowFixedBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-! # Formula-code bound for the natural-list cons tail atomic row -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 240000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailAtomicRowCodeBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectAtomicRowEqualityExplicitHybridCertificate
open FoundationCompactNumericListedDirectAtomicRowEqualityFixedPolynomialBounds
open FoundationCompactNumericListedDirectAtomicRowEqualityPublicBounds
open FoundationCompactNumericListedDirectNatListConsRowsTailAtomicRowFixedBounds

theorem natListConsRowsTailAtomicRowCertificatePayloadAtTerms_le_fixed
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount sourceLeft sourceRight targetLeft targetRight
      numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceLeft : sourceLeft <= numericBound)
    (hsourceRight : sourceRight <= numericBound)
    (htargetLeft : targetLeft <= numericBound)
    (htargetRight : targetRight <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hrow : CompactAdditiveAtomicRowEq
      (termValue valuation (shortBinaryNumeralTerm tokenTable))
      (termValue valuation (shortBinaryNumeralTerm width))
      (termValue valuation (shortBinaryNumeralTerm tokenCount))
      (termValue valuation (shortBinaryNumeralTerm sourceLeft))
      (termValue valuation (shortBinaryNumeralTerm sourceRight))
      (termValue valuation (shortBinaryNumeralTerm targetLeft))
      (termValue valuation (shortBinaryNumeralTerm targetRight))) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate
          valuation (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm sourceLeft)
          (shortBinaryNumeralTerm sourceRight)
          (shortBinaryNumeralTerm targetLeft)
          (shortBinaryNumeralTerm targetRight) hrow) <=
      compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound := by
  let certificate :=
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm sourceLeft)
      (shortBinaryNumeralTerm sourceRight)
      (shortBinaryNumeralTerm targetLeft)
      (shortBinaryNumeralTerm targetRight) hrow
  have hopen : hybridFormulaStructuralPayloadBound certificate <=
      compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm sourceLeft)
        (shortBinaryNumeralTerm sourceRight)
        (shortBinaryNumeralTerm targetLeft)
        (shortBinaryNumeralTerm targetRight) := by
    dsimp only [certificate]
    exact
      compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_of_closed
        valuation (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm sourceLeft)
        (shortBinaryNumeralTerm sourceRight)
        (shortBinaryNumeralTerm targetLeft)
        (shortBinaryNumeralTerm targetRight)
        (shortBinaryNumeralTerm_freeVariables_eq_empty _)
        (shortBinaryNumeralTerm_freeVariables_eq_empty _)
        (shortBinaryNumeralTerm_freeVariables_eq_empty _)
        (shortBinaryNumeralTerm_freeVariables_eq_empty _) hrow
  have hfixed := natListConsRowsTailAtomicRowPayload_le_fixed valuation
    tokenTable width tokenCount sourceLeft sourceRight targetLeft targetRight
    numericBound bitBound hwidth htokenCount hsourceLeft hsourceRight
    htargetLeft htargetRight htokenTableSize hnumericSize
  simpa only [certificate] using hopen.trans hfixed

theorem natListConsRowsTailAtomicRowCertificatePayload_le_fixed
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount sourceLeft sourceRight targetLeft targetRight
      numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceLeft : sourceLeft <= numericBound)
    (hsourceRight : sourceRight <= numericBound)
    (htargetLeft : targetLeft <= numericBound)
    (htargetRight : targetRight <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hrow : CompactAdditiveAtomicRowEq tokenTable width tokenCount sourceLeft
      sourceRight targetLeft targetRight) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate
          valuation (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm sourceLeft)
          (shortBinaryNumeralTerm sourceRight)
          (shortBinaryNumeralTerm targetLeft)
          (shortBinaryNumeralTerm targetRight) (by
            simpa only [termValue_shortBinaryNumeralTerm] using hrow)) <=
      compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound :=
  natListConsRowsTailAtomicRowCertificatePayloadAtTerms_le_fixed valuation
    tokenTable width tokenCount sourceLeft sourceRight targetLeft targetRight
    numericBound bitBound hwidth htokenCount hsourceLeft hsourceRight
    htargetLeft htargetRight htokenTableSize hnumericSize (by
      simpa only [termValue_shortBinaryNumeralTerm] using hrow)

theorem natListConsRowsTailAtomicRowCode_le_fixed
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount sourceLeft sourceRight targetLeft targetRight
      numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceLeft : sourceLeft <= numericBound)
    (hsourceRight : sourceRight <= numericBound)
    (htargetLeft : targetLeft <= numericBound)
    (htargetRight : targetRight <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hrow : CompactAdditiveAtomicRowEq tokenTable width tokenCount sourceLeft
      sourceRight targetLeft targetRight) :
    (binaryFormulaCode
      (compactAdditiveAtomicRowEqAtValuationFormula
        (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm sourceLeft)
        (shortBinaryNumeralTerm sourceRight)
        (shortBinaryNumeralTerm targetLeft)
        (shortBinaryNumeralTerm targetRight))).length <=
      compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound := by
  let certificate :=
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm sourceLeft)
      (shortBinaryNumeralTerm sourceRight)
      (shortBinaryNumeralTerm targetLeft)
      (shortBinaryNumeralTerm targetRight) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hrow)
  have hpayload := natListConsRowsTailAtomicRowCertificatePayload_le_fixed
    valuation tokenTable width tokenCount sourceLeft sourceRight targetLeft
    targetRight numericBound bitBound hwidth htokenCount hsourceLeft
    hsourceRight htargetLeft htargetRight htokenTableSize hnumericSize hrow
  have hcode :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      certificate
  simpa only [certificate] using hcode.trans hpayload

#print axioms natListConsRowsTailAtomicRowCertificatePayloadAtTerms_le_fixed
#print axioms natListConsRowsTailAtomicRowCertificatePayload_le_fixed
#print axioms natListConsRowsTailAtomicRowCode_le_fixed

end FoundationCompactNumericListedDirectNatListConsRowsTailAtomicRowCodeBound
