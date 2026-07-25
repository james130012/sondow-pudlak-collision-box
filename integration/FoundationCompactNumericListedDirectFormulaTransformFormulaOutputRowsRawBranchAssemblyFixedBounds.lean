import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixFullyFixedBounds

/-!
# Fully fixed outer assembly for raw output-row branches

This module combines an already fixed raw-mode certificate with the genuine
append-source-prefix certificate and pays every connective in the complete
formula-transform output-row formula from one closed syntax budget.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 220000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawBranchAssemblyFixedBounds

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
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefix
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixFullyFixedBounds

private abbrev rawBranchZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate.zeroValuation

def outputRowsRawBranchFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource := outputRowsMappedOuterSyntaxPolynomial bitBound
  let rawPairResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (outputRowsRawModeFixedPayloadPolynomial bitBound)
      (appendSourcePrefixFullyFixedPayloadPolynomial numericBound bitBound)
  let positiveBodyResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource rawPairResource
  let positiveResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (outputRowsNativeLeFixedPayloadPolynomial bitBound)
      positiveBodyResource
  let casesResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource positiveResource
  hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound) casesResource

noncomputable def outputRowsRawSelectedFixedCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (modeCertificate :
      CheckedHybridValuationBoundedFormulaCertificate rawBranchZeroValuation
        (rawModeFormula (shortBinaryNumeralTerm mode)))
    (sourceCertificate :
      CheckedHybridValuationBoundedFormulaCertificate rawBranchZeroValuation
        (compactAdditiveNatListAppendSourcePrefixClosedFormula tokenTable width
          tokenCount current.parserFinish current.finish current.outputCount
          current.start current.parserTokensFinish current.parserTokensCount
          consumedCount next.parserFinish next.finish next.outputCount)) :
    CheckedHybridValuationBoundedFormulaCertificate rawBranchZeroValuation
      (compactFormulaTransformFormulaOutputRowsExplicitFormula tokenTable width
        tokenCount current next mode tag consumedCount mappedHead) :=
  .conjunction
    (consumedCountEqualityCertificate current next consumedCount hcount)
    (.disjunctionRight
      (.conjunction
        (consumedCountPositiveCertificate consumedCount hconsumed)
        (.disjunctionLeft (.conjunction modeCertificate sourceCertificate))))

theorem outputRowsRawSelectedFixedCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hsource : CompactFormulaTransformOutputRawPrefixRows tokenTable width
      tokenCount current next consumedCount)
    (modeCertificate :
      CheckedHybridValuationBoundedFormulaCertificate rawBranchZeroValuation
        (rawModeFormula (shortBinaryNumeralTerm mode)))
    (hmodeCertificate :
      hybridFormulaStructuralPayloadBound modeCertificate <=
        outputRowsRawModeFixedPayloadPolynomial bitBound)
    (henvironmentSize : ∀ coordinate,
      Nat.size
        (compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
          tokenCount current next mode tag consumedCount mappedHead
          coordinate) <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (outputRowsRawSelectedFixedCertificate tokenTable width tokenCount
          current next mode tag consumedCount mappedHead hcount hconsumed
          modeCertificate
          (compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount current.start current.parserTokensFinish
            current.parserTokensCount consumedCount next.parserFinish
            next.finish next.outputCount hsource)) <=
      outputRowsRawBranchFixedPayloadPolynomial numericBound bitBound := by
  let countFormula := outputRowsCountFormula current next consumedCount
  let zeroFormula :=
    outputRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount
  let positiveGuard :=
    nativeLeFormula (‘1’ : ValuationTerm)
      (shortBinaryNumeralTerm consumedCount)
  let modeFormula := rawModeFormula (shortBinaryNumeralTerm mode)
  let sourceFormula :=
    compactAdditiveNatListAppendSourcePrefixClosedFormula tokenTable width
      tokenCount current.parserFinish current.finish current.outputCount
      current.start current.parserTokensFinish current.parserTokensCount
      consumedCount next.parserFinish next.finish next.outputCount
  let rawFormula := modeFormula ⋏ sourceFormula
  let sameFormula :=
    outputRowsSameFourCaseFormula tokenTable width tokenCount current next mode
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
  let modeResource := outputRowsRawModeFixedPayloadPolynomial bitBound
  let sourceResource :=
    appendSourcePrefixFullyFixedPayloadPolynomial numericBound bitBound
  let rawPairResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource modeResource
      sourceResource
  let positiveBodyResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource rawPairResource
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
      rawFormula, sourceFormula, modeFormula, positiveGuard, zeroFormula,
      countFormula]
    unfold outputRowsCountFormula outputRowsZeroCaseFormula
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
  have hmodeClosed :=
    conjunction_left_closed_outputRows modeFormula sourceFormula hrawClosed
  have hsourceClosed :=
    conjunction_right_closed_outputRows modeFormula sourceFormula hrawClosed
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
  have hmodeCode :=
    (binaryFormulaCode_and_left_le_outputRows modeFormula sourceFormula).trans
      hrawCode
  have hsourceCode :=
    (binaryFormulaCode_and_right_le_outputRows modeFormula sourceFormula).trans
      hrawCode
  have hnextParserTokensCountSize :
      Nat.size next.parserTokensCount <= bitBound := by
    have hraw := henvironmentSize (20 : Fin 29)
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using hraw
  have htableSize : Nat.size tokenTable <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (0 : Fin 29)
  have hwidthSize : Nat.size width <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (1 : Fin 29)
  have htokenCountSize : Nat.size tokenCount <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (2 : Fin 29)
  have hcurrentStartSize : Nat.size current.start <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (3 : Fin 29)
  have hcurrentFinishSize : Nat.size current.finish <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (4 : Fin 29)
  have hcurrentParserFinishSize :
      Nat.size current.parserFinish <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (5 : Fin 29)
  have hcurrentParserTokensFinishSize :
      Nat.size current.parserTokensFinish <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (6 : Fin 29)
  have hcurrentParserTokensCountSize :
      Nat.size current.parserTokensCount <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (9 : Fin 29)
  have hcurrentOutputCountSize :
      Nat.size current.outputCount <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (13 : Fin 29)
  have hnextFinishSize : Nat.size next.finish <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (15 : Fin 29)
  have hnextParserFinishSize :
      Nat.size next.parserFinish <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (16 : Fin 29)
  have hnextOutputCountSize : Nat.size next.outputCount <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (24 : Fin 29)
  have hconsumedCountSize : Nat.size consumedCount <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (27 : Fin 29)
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let sourceCertificate :=
    compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hsource
  let rawPairCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction modeCertificate
      sourceCertificate
  let positiveBodyCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := sameMappedFormula) rawPairCertificate
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
  have hsourceTransparent :=
    compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hsource
  have hsourceFixed :=
    compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount numericBound bitBound hsource htableSize hwidthSize
      htokenCountSize hcurrentParserFinishSize hcurrentFinishSize
      hcurrentOutputCountSize hcurrentStartSize
      hcurrentParserTokensFinishSize hcurrentParserTokensCountSize
      hconsumedCountSize hnextParserFinishSize hnextFinishSize
      hnextOutputCountSize hwidthBound htokenCountBound hnumericSize
  have hsourceResource :
      hybridFormulaStructuralPayloadBound sourceCertificate <= sourceResource :=
    hsourceTransparent.trans hsourceFixed
  have hrawPairRaw := transparentHybridConjunctionPayloadBound_le
    modeCertificate sourceCertificate modeResource sourceResource
    hmodeCertificate hsourceResource
  have hrawPairAssembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      rawBranchZeroValuation modeFormula sourceFormula modeResource
      sourceResource syntaxResource hsyntaxPositive hmodeClosed hsourceClosed
      hmodeCode hsourceCode hrawCode
  have hrawPairResource :
      hybridFormulaStructuralPayloadBound rawPairCertificate <=
        rawPairResource :=
    hrawPairRaw.trans hrawPairAssembly
  have hpositiveBodyRaw :=
    transparentHybridDisjunctionLeftPayloadBound_le
      (right := sameMappedFormula) rawPairCertificate rawPairResource
      hrawPairResource
  have hpositiveBodyAssembly :=
    transparentHybridDisjunctionLeftPayloadEnvelope_le_closedGeneral_outputRows
      rawBranchZeroValuation rawFormula sameMappedFormula rawPairResource
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
      rawBranchZeroValuation positiveGuard positiveBodyFormula
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
      rawBranchZeroValuation zeroFormula positiveFormula positiveResource
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
      rawBranchZeroValuation countFormula casesFormula countResource
      casesResource syntaxResource hsyntaxPositive hcountClosed hcasesClosed
      hcountCode hcasesCode hfullCode
  have hfixed := houterRaw.trans houterAssembly
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        countCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := zeroFormula)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            positiveCertificate
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              (right := sameMappedFormula)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                modeCertificate sourceCertificate))))) <= _
  unfold outputRowsRawBranchFixedPayloadPolynomial
  simpa only [syntaxResource, countResource, positiveGuardResource,
    modeResource, sourceResource, rawPairResource, positiveBodyResource,
    positiveResource, casesResource, rawPairCertificate,
    positiveBodyCertificate, positiveCertificateFull, casesCertificate]
    using hfixed

#print axioms
  outputRowsRawSelectedFixedCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawBranchAssemblyFixedBounds
