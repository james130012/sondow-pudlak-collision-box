import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawBranchesFullyFixedBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds

/-!
# Fully fixed zero-count output-row branch

The original `FromData.zero` certificate is assembled from the fixed count
equality, the fixed zero equality, and the genuine fully fixed same-rows
certificate.  Every connective is paid from the complete closed formula budget.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 220000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsZeroBranchFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRows
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsFormulaFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAtomicFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsMappedRowsFullyFixedBounds
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds

private abbrev zeroBranchValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate.zeroValuation

def outputRowsZeroBranchFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource := outputRowsMappedOuterSyntaxPolynomial bitBound
  let zeroPairResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound)
      (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
  let casesResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource zeroPairResource
  hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound) casesResource

theorem
    compactFormulaTransformFormulaOutputRowsZeroBranchCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : consumedCount = 0)
    (hsame : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
      current next)
    (henvironmentSize : ∀ coordinate,
      Nat.size
        (compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
          tokenCount current next mode tag consumedCount mappedHead
          coordinate) <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hcurrentOutputCountBound : current.outputCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead (.zero hcount hconsumed hsame)) <=
      outputRowsZeroBranchFixedPayloadPolynomial numericBound bitBound := by
  let countFormula := outputRowsCountFormula current next consumedCount
  let zeroGuard :=
    nativeEqFormula (shortBinaryNumeralTerm consumedCount)
      (‘0’ : ValuationTerm)
  let sameFormula :=
    compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
      current.outputBoundary current.outputCount next.outputBoundary
      next.outputCount
  let zeroFormula := zeroGuard ⋏ sameFormula
  let positiveFormula :=
    outputRowsPositiveCaseFormula tokenTable width tokenCount current next mode
      tag consumedCount mappedHead
  let casesFormula := zeroFormula ⋎ positiveFormula
  let fullFormula := countFormula ⋏ casesFormula
  let syntaxResource := outputRowsMappedOuterSyntaxPolynomial bitBound
  let countResource :=
    outputRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let zeroResource :=
    outputRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let sameResource :=
    sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound
  let zeroPairResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource zeroResource
      sameResource
  let casesResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource zeroPairResource
  have hfullAlignment :
      fullFormula =
        compactFormulaTransformFormulaOutputRowsExplicitFormula tokenTable width
          tokenCount current next mode tag consumedCount mappedHead := by
    dsimp only [fullFormula, casesFormula, positiveFormula, zeroFormula,
      sameFormula, zeroGuard, countFormula]
    unfold outputRowsCountFormula outputRowsPositiveCaseFormula
      outputRowsPositiveBodyFormula outputRowsRawCaseFormula
      outputRowsSameFourCaseFormula outputRowsMappedCaseFormula
      outputRowsMappedTailFormula
      compactFormulaTransformFormulaOutputRowsExplicitFormula
    rfl
  have hfullClosed : fullFormula.freeVariables = ∅ := by
    rw [hfullAlignment,
      ← compactFormulaTransformFormulaOutputRowsClosedFormula_alignment]
    exact compactFormulaTransformFormulaOutputRowsClosedFormula_closed
      tokenTable width tokenCount current next mode tag consumedCount mappedHead
  have hfullCode :
      (binaryFormulaCode fullFormula).length <= syntaxResource := by
    have hraw :=
      compactFormulaTransformFormulaOutputRowsClosedFormula_code_length_le_fixed
        tokenTable width tokenCount current next mode tag consumedCount
        mappedHead bitBound henvironmentSize
    rw [hfullAlignment,
      ← compactFormulaTransformFormulaOutputRowsClosedFormula_alignment]
    dsimp only [syntaxResource]
    unfold outputRowsMappedOuterSyntaxPolynomial
    omega
  have hsyntaxPositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold outputRowsMappedOuterSyntaxPolynomial
    omega
  have hcountClosed :=
    conjunction_left_closed_outputRows countFormula casesFormula hfullClosed
  have hcasesClosed :=
    conjunction_right_closed_outputRows countFormula casesFormula hfullClosed
  have hzeroFormulaClosed :=
    disjunction_left_closed_outputRows zeroFormula positiveFormula hcasesClosed
  have hpositiveClosed :=
    disjunction_right_closed_outputRows zeroFormula positiveFormula hcasesClosed
  have hzeroGuardClosed :=
    conjunction_left_closed_outputRows zeroGuard sameFormula
      hzeroFormulaClosed
  have hsameClosed :=
    conjunction_right_closed_outputRows zeroGuard sameFormula
      hzeroFormulaClosed
  have hcountCode :=
    (binaryFormulaCode_and_left_le_outputRows countFormula casesFormula).trans
      hfullCode
  have hcasesCode :=
    (binaryFormulaCode_and_right_le_outputRows countFormula casesFormula).trans
      hfullCode
  have hzeroFormulaCode :=
    (binaryFormulaCode_or_left_le_outputRows zeroFormula positiveFormula).trans
      hcasesCode
  have hpositiveCode :=
    (binaryFormulaCode_or_right_le_outputRows zeroFormula positiveFormula).trans
      hcasesCode
  have hzeroGuardCode :=
    (binaryFormulaCode_and_left_le_outputRows zeroGuard sameFormula).trans
      hzeroFormulaCode
  have hsameCode :=
    (binaryFormulaCode_and_right_le_outputRows zeroGuard sameFormula).trans
      hzeroFormulaCode
  have htableSize : Nat.size tokenTable <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (0 : Fin 29)
  have hcurrentParserTokensCountSize :
      Nat.size current.parserTokensCount <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (9 : Fin 29)
  have hcurrentOutputBoundarySize :
      Nat.size current.outputBoundary <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (12 : Fin 29)
  have hconsumedCountSize : Nat.size consumedCount <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (27 : Fin 29)
  have hnextParserTokensCountSize :
      Nat.size next.parserTokensCount <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (20 : Fin 29)
  have hnextOutputBoundarySize :
      Nat.size next.outputBoundary <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (23 : Fin 29)
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let zeroCertificate :=
    consumedCountZeroCertificate consumedCount hconsumed
  let sameCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hsame
  let zeroPairCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction zeroCertificate
      sameCertificate
  let casesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := positiveFormula) zeroPairCertificate
  have hcountResource :
      hybridFormulaStructuralPayloadBound countCertificate <= countResource := by
    exact consumedCountEqualityCertificate_structuralPayloadBound_le_fixed
      current next consumedCount bitBound hcount
      hcurrentParserTokensCountSize hconsumedCountSize
      hnextParserTokensCountSize
  have hzeroResource :
      hybridFormulaStructuralPayloadBound zeroCertificate <= zeroResource := by
    exact consumedCountZeroCertificate_structuralPayloadBound_le_fixed
      consumedCount bitBound hconsumed hconsumedCountSize
  have hsameTransparent :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hsame
  have hsameFixed :=
    compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_fullyFixed tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount numericBound bitBound hsame
      hwidthBound htokenCountBound hcurrentOutputCountBound htableSize
      hcurrentOutputBoundarySize hnextOutputBoundarySize hnumericSize
  have hsameResource :
      hybridFormulaStructuralPayloadBound sameCertificate <= sameResource :=
    hsameTransparent.trans hsameFixed
  have hzeroPairRaw := transparentHybridConjunctionPayloadBound_le
    zeroCertificate sameCertificate zeroResource sameResource hzeroResource
    hsameResource
  have hzeroPairAssembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      zeroBranchValuation zeroGuard sameFormula zeroResource sameResource
      syntaxResource hsyntaxPositive hzeroGuardClosed hsameClosed
      hzeroGuardCode hsameCode hzeroFormulaCode
  have hzeroPairResource :
      hybridFormulaStructuralPayloadBound zeroPairCertificate <=
        zeroPairResource :=
    hzeroPairRaw.trans hzeroPairAssembly
  have hcasesRaw := transparentHybridDisjunctionLeftPayloadBound_le
    (right := positiveFormula) zeroPairCertificate zeroPairResource
    hzeroPairResource
  have hcasesAssembly :=
    transparentHybridDisjunctionLeftPayloadEnvelope_le_closedGeneral_outputRows
      zeroBranchValuation zeroFormula positiveFormula zeroPairResource
      syntaxResource hsyntaxPositive hzeroFormulaClosed hpositiveClosed
      hzeroFormulaCode hpositiveCode hcasesCode
  have hcasesResource :
      hybridFormulaStructuralPayloadBound casesCertificate <= casesResource :=
    hcasesRaw.trans hcasesAssembly
  have houterRaw := transparentHybridConjunctionPayloadBound_le
    countCertificate casesCertificate countResource casesResource
    hcountResource hcasesResource
  have houterAssembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      zeroBranchValuation countFormula casesFormula countResource casesResource
      syntaxResource hsyntaxPositive hcountClosed hcasesClosed hcountCode
      hcasesCode hfullCode
  have hfixed := houterRaw.trans houterAssembly
  convert hfixed using 1 <;>
    (try simp only [
      compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData,
      outputRowsZeroBranchFixedPayloadPolynomial, countCertificate,
      zeroCertificate, sameCertificate, zeroPairCertificate, casesCertificate,
      syntaxResource, countResource, zeroResource, sameResource,
      zeroPairResource, casesResource]) <;>
    (try (congr 1 <;> apply proof_irrel_heq))

#print axioms
  compactFormulaTransformFormulaOutputRowsZeroBranchCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsZeroBranchFullyFixedBounds
