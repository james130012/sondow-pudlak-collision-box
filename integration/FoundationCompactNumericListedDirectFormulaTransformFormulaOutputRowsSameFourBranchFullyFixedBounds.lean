import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsZeroBranchFullyFixedBounds

/-!
# Fully fixed same-four output-row branch

The original `FromData.sameFour` certificate is assembled from a fixed
`mode = 4` equality and the genuine fully fixed same-rows certificate.  The
complete selected path is charged from the closed twenty-nine-coordinate
formula budget.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 240000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsSameFourBranchFullyFixedBounds

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

private abbrev sameFourValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate.zeroValuation

def outputRowsSameFourBranchFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource := outputRowsMappedOuterSyntaxPolynomial bitBound
  let samePairResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound)
      (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
  let sameSelectedResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource samePairResource
  let positiveBodyResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource sameSelectedResource
  let positiveResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (outputRowsNativeLeFixedPayloadPolynomial bitBound)
      positiveBodyResource
  let casesResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource positiveResource
  hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound) casesResource

theorem
    compactFormulaTransformFormulaOutputRowsSameFourBranchCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 4)
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
          mappedHead (.sameFour hcount hconsumed hmode hsame)) <=
      outputRowsSameFourBranchFixedPayloadPolynomial numericBound bitBound := by
  let countFormula := outputRowsCountFormula current next consumedCount
  let zeroFormula :=
    outputRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount
  let positiveGuard :=
    nativeLeFormula (‘1’ : ValuationTerm)
      (shortBinaryNumeralTerm consumedCount)
  let rawFormula :=
    outputRowsRawCaseFormula tokenTable width tokenCount current next mode
      consumedCount
  let modeFormula :=
    nativeEqFormula (shortBinaryNumeralTerm mode) (‘4’ : ValuationTerm)
  let rowsFormula :=
    compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
      current.outputBoundary current.outputCount next.outputBoundary
      next.outputCount
  let sameFormula := modeFormula ⋏ rowsFormula
  let mappedFormula :=
    outputRowsMappedCaseFormula tokenTable width tokenCount current next mode
      tag consumedCount mappedHead
  let sameMappedFormula := sameFormula ⋎ mappedFormula
  let positiveBodyFormula := rawFormula ⋎ sameMappedFormula
  let positiveFormula := positiveGuard ⋏ positiveBodyFormula
  let casesFormula := zeroFormula ⋎ positiveFormula
  let fullFormula := countFormula ⋏ casesFormula
  let syntaxResource := outputRowsMappedOuterSyntaxPolynomial bitBound
  let countResource :=
    outputRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let positiveGuardResource :=
    outputRowsNativeLeFixedPayloadPolynomial bitBound
  let modeResource :=
    outputRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let rowsResource :=
    sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound
  let samePairResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource modeResource
      rowsResource
  let sameSelectedResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource samePairResource
  let positiveBodyResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource sameSelectedResource
  let positiveResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      positiveGuardResource positiveBodyResource
  let casesResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource positiveResource
  have hfullAlignment :
      fullFormula =
        compactFormulaTransformFormulaOutputRowsExplicitFormula tokenTable width
          tokenCount current next mode tag consumedCount mappedHead := by
    dsimp only [fullFormula, casesFormula, positiveFormula,
      positiveBodyFormula, sameMappedFormula, mappedFormula, sameFormula,
      rowsFormula, modeFormula, rawFormula, positiveGuard, zeroFormula,
      countFormula]
    unfold outputRowsCountFormula outputRowsZeroCaseFormula
      outputRowsRawCaseFormula outputRowsMappedCaseFormula
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
  have hzeroClosed :=
    disjunction_left_closed_outputRows zeroFormula positiveFormula hcasesClosed
  have hpositiveClosed :=
    disjunction_right_closed_outputRows zeroFormula positiveFormula hcasesClosed
  have hguardClosed :=
    conjunction_left_closed_outputRows positiveGuard positiveBodyFormula
      hpositiveClosed
  have hpositiveBodyClosed :=
    conjunction_right_closed_outputRows positiveGuard positiveBodyFormula
      hpositiveClosed
  have hrawClosed :=
    disjunction_left_closed_outputRows rawFormula sameMappedFormula
      hpositiveBodyClosed
  have hsameMappedClosed :=
    disjunction_right_closed_outputRows rawFormula sameMappedFormula
      hpositiveBodyClosed
  have hsameClosed :=
    disjunction_left_closed_outputRows sameFormula mappedFormula
      hsameMappedClosed
  have hmappedClosed :=
    disjunction_right_closed_outputRows sameFormula mappedFormula
      hsameMappedClosed
  have hmodeClosed :=
    conjunction_left_closed_outputRows modeFormula rowsFormula hsameClosed
  have hrowsClosed :=
    conjunction_right_closed_outputRows modeFormula rowsFormula hsameClosed
  have hcountCode :=
    (binaryFormulaCode_and_left_le_outputRows countFormula casesFormula).trans
      hfullCode
  have hcasesCode :=
    (binaryFormulaCode_and_right_le_outputRows countFormula casesFormula).trans
      hfullCode
  have hzeroCode :=
    (binaryFormulaCode_or_left_le_outputRows zeroFormula positiveFormula).trans
      hcasesCode
  have hpositiveCode :=
    (binaryFormulaCode_or_right_le_outputRows zeroFormula positiveFormula).trans
      hcasesCode
  have hguardCode :=
    (binaryFormulaCode_and_left_le_outputRows positiveGuard
      positiveBodyFormula).trans hpositiveCode
  have hpositiveBodyCode :=
    (binaryFormulaCode_and_right_le_outputRows positiveGuard
      positiveBodyFormula).trans hpositiveCode
  have hrawCode :=
    (binaryFormulaCode_or_left_le_outputRows rawFormula
      sameMappedFormula).trans hpositiveBodyCode
  have hsameMappedCode :=
    (binaryFormulaCode_or_right_le_outputRows rawFormula
      sameMappedFormula).trans hpositiveBodyCode
  have hsameCode :=
    (binaryFormulaCode_or_left_le_outputRows sameFormula mappedFormula).trans
      hsameMappedCode
  have hmappedCode :=
    (binaryFormulaCode_or_right_le_outputRows sameFormula mappedFormula).trans
      hsameMappedCode
  have hmodeCode :=
    (binaryFormulaCode_and_left_le_outputRows modeFormula rowsFormula).trans
      hsameCode
  have hrowsCode :=
    (binaryFormulaCode_and_right_le_outputRows modeFormula rowsFormula).trans
      hsameCode
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
  have hnextParserTokensCountSize :
      Nat.size next.parserTokensCount <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (20 : Fin 29)
  have hnextOutputBoundarySize :
      Nat.size next.outputBoundary <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (23 : Fin 29)
  have hmodeSize : Nat.size mode <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (25 : Fin 29)
  have hconsumedCountSize : Nat.size consumedCount <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (27 : Fin 29)
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let modeCertificate :=
    modeNativeEqualityCertificate mode (‘4’ : ValuationTerm) 4
      (termValue_arithmeticFour sameFourValuation) hmode
  let rowsCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hsame
  let samePairCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction modeCertificate
      rowsCertificate
  let sameSelectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := mappedFormula) samePairCertificate
  let positiveBodyCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := rawFormula) sameSelectedCertificate
  let positiveCertificateFull :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      positiveCertificate positiveBodyCertificate
  let casesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := zeroFormula) positiveCertificateFull
  have hcountResource :
      hybridFormulaStructuralPayloadBound countCertificate <= countResource := by
    exact consumedCountEqualityCertificate_structuralPayloadBound_le_fixed
      current next consumedCount bitBound hcount
      hcurrentParserTokensCountSize hconsumedCountSize
      hnextParserTokensCountSize
  have hpositiveGuardResource :
      hybridFormulaStructuralPayloadBound positiveCertificate <=
        positiveGuardResource := by
    exact consumedCountPositiveCertificate_structuralPayloadBound_le_fixed
      consumedCount bitBound hconsumed hconsumedCountSize
  have hmodeResource :
      hybridFormulaStructuralPayloadBound modeCertificate <= modeResource := by
    exact modeNativeEqualityCertificate_structuralPayloadBound_le_fixed mode
      (‘4’ : ValuationTerm) 4 bitBound
      (termValue_arithmeticFour sameFourValuation) hmode hmodeSize
      (outputRowsModeLiteral_closed _
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (outputRowsModeLiteralCode_le _ bitBound
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hrowsTransparent :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hsame
  have hrowsFixed :=
    compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_fullyFixed tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount numericBound bitBound hsame
      hwidthBound htokenCountBound hcurrentOutputCountBound htableSize
      hcurrentOutputBoundarySize hnextOutputBoundarySize hnumericSize
  have hrowsResource :
      hybridFormulaStructuralPayloadBound rowsCertificate <= rowsResource :=
    hrowsTransparent.trans hrowsFixed
  have hsamePairRaw := transparentHybridConjunctionPayloadBound_le
    modeCertificate rowsCertificate modeResource rowsResource hmodeResource
    hrowsResource
  have hsamePairAssembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      sameFourValuation modeFormula rowsFormula modeResource rowsResource
      syntaxResource hsyntaxPositive hmodeClosed hrowsClosed hmodeCode
      hrowsCode hsameCode
  have hsamePairResource :
      hybridFormulaStructuralPayloadBound samePairCertificate <=
        samePairResource :=
    hsamePairRaw.trans hsamePairAssembly
  have hsameSelectedRaw := transparentHybridDisjunctionLeftPayloadBound_le
    (right := mappedFormula) samePairCertificate samePairResource
    hsamePairResource
  have hsameSelectedAssembly :=
    transparentHybridDisjunctionLeftPayloadEnvelope_le_closedGeneral_outputRows
      sameFourValuation sameFormula mappedFormula samePairResource
      syntaxResource hsyntaxPositive hsameClosed hmappedClosed hsameCode
      hmappedCode hsameMappedCode
  have hsameSelectedResource :
      hybridFormulaStructuralPayloadBound sameSelectedCertificate <=
        sameSelectedResource :=
    hsameSelectedRaw.trans hsameSelectedAssembly
  have hpositiveBodyRaw := transparentHybridDisjunctionRightPayloadBound_le
    (left := rawFormula) sameSelectedCertificate sameSelectedResource
    hsameSelectedResource
  have hpositiveBodyAssembly :=
    transparentHybridDisjunctionRightPayloadEnvelope_le_closedGeneral_outputRows
      sameFourValuation rawFormula sameMappedFormula sameSelectedResource
      syntaxResource hsyntaxPositive hrawClosed hsameMappedClosed hrawCode
      hsameMappedCode hpositiveBodyCode
  have hpositiveBodyResource :
      hybridFormulaStructuralPayloadBound positiveBodyCertificate <=
        positiveBodyResource :=
    hpositiveBodyRaw.trans hpositiveBodyAssembly
  have hpositiveRaw := transparentHybridConjunctionPayloadBound_le
    positiveCertificate positiveBodyCertificate positiveGuardResource
    positiveBodyResource hpositiveGuardResource hpositiveBodyResource
  have hpositiveAssembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      sameFourValuation positiveGuard positiveBodyFormula
      positiveGuardResource positiveBodyResource syntaxResource
      hsyntaxPositive hguardClosed hpositiveBodyClosed hguardCode
      hpositiveBodyCode hpositiveCode
  have hpositiveResource :
      hybridFormulaStructuralPayloadBound positiveCertificateFull <=
        positiveResource :=
    hpositiveRaw.trans hpositiveAssembly
  have hcasesRaw := transparentHybridDisjunctionRightPayloadBound_le
    (left := zeroFormula) positiveCertificateFull positiveResource
    hpositiveResource
  have hcasesAssembly :=
    transparentHybridDisjunctionRightPayloadEnvelope_le_closedGeneral_outputRows
      sameFourValuation zeroFormula positiveFormula positiveResource
      syntaxResource hsyntaxPositive hzeroClosed hpositiveClosed hzeroCode
      hpositiveCode hcasesCode
  have hcasesResource :
      hybridFormulaStructuralPayloadBound casesCertificate <= casesResource :=
    hcasesRaw.trans hcasesAssembly
  have houterRaw := transparentHybridConjunctionPayloadBound_le
    countCertificate casesCertificate countResource casesResource
    hcountResource hcasesResource
  have houterAssembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      sameFourValuation countFormula casesFormula countResource casesResource
      syntaxResource hsyntaxPositive hcountClosed hcasesClosed hcountCode
      hcasesCode hfullCode
  have hfixed := houterRaw.trans houterAssembly
  convert hfixed using 1 <;>
    (try simp only [
      compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData,
      outputRowsSameFourBranchFixedPayloadPolynomial, countCertificate,
      positiveCertificate, modeCertificate, rowsCertificate,
      samePairCertificate, sameSelectedCertificate, positiveBodyCertificate,
      positiveCertificateFull, casesCertificate, syntaxResource,
      countResource, positiveGuardResource, modeResource, rowsResource,
      samePairResource, sameSelectedResource, positiveBodyResource,
      positiveResource, casesResource]) <;>
    (try (congr 1 <;> apply proof_irrel_heq))

#print axioms
  compactFormulaTransformFormulaOutputRowsSameFourBranchCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsSameFourBranchFullyFixedBounds
