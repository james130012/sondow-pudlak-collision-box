import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPositiveOuterFixedCore
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixFullyFixedBounds
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds

/-! # Fully fixed raw-prefix branch under term-output mode five -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 220000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFiveRawFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOuterSyntaxFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterSyntaxFacts
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPositiveOuterFixedCore
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixFullyFixedBounds

private abbrev modeFiveRawValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsModeFiveRawFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource := termRowsOuterSyntaxPolynomial bitBound
  let rawResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termOutputDoubleFailureFixedPayloadPolynomial bitBound)
    (appendSourcePrefixFullyFixedPayloadPolynomial numericBound bitBound)
  let middleResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    rawResource
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    middleResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termRowsPositiveAtomicFixedPayloadPolynomial bitBound) internalResource
  let modesResource := sixRightDisjunctionPathFourPayloadEnvelope syntaxResource
    modeResource
  termRowsPositiveOuterFixedPayloadPolynomial modesResource bitBound

theorem
    compactFormulaTransformTermOutputRowsModeFiveRawBranch_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 5)
    (failure : DoubleFailureCheckedData consumedCount tag)
    (hrows : CompactFormulaTransformOutputRawPrefixRows tokenTable width
      tokenCount current next consumedCount)
    (henvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.modeFiveRaw hcount hconsumed hmode failure hrows)) <=
      termRowsModeFiveRawFixedPayloadPolynomial numericBound bitBound := by
  let syntaxResource := termRowsOuterSyntaxPolynomial bitBound
  let modeZeroFormula := termRowsModeZeroFormula tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount
  let modeOneFormula := termRowsModeOneFormula tokenTable width tokenCount
    current next mode tag argument consumedCount
  let modeTwoFormula := termRowsModeTwoFormula tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount
  let modeFourFormula := termRowsModeFourFormula tokenTable width tokenCount
    current next mode tag argument consumedCount
  let modeFiveFormula := termRowsModeFiveFormula tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessCount
  let otherFormula := termRowsOtherFormula tokenTable width tokenCount current
    next mode consumedCount
  let modeEqFormula := nativeEqFormula (shortBinaryNumeralTerm mode)
    (‘5’ : ValuationTerm)
  let capturedFormula :=
    termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
      termRowsCapturedFormula tokenTable width tokenCount current next
        binderArity argument
  let residualFormula :=
    termRowsResidualGuardFormula consumedCount tag argument witnessCount ⋏
      compactFormulaTransformTermResidualExistsFormula tokenTable width
        tokenCount current next argument witnessCount
  let failureFormula := doubleFailureFormula
    (shortBinaryNumeralTerm consumedCount) (shortBinaryNumeralTerm tag)
  let rowsFormula := termRowsRawPrefixFormula tokenTable width tokenCount
    current next consumedCount
  let rawFormula := failureFormula ⋏ rowsFormula
  let middleFormula := residualFormula ⋎ rawFormula
  let internalFormula := capturedFormula ⋎ middleFormula
  let failureResource := termOutputDoubleFailureFixedPayloadPolynomial bitBound
  let rowsResource := appendSourcePrefixFullyFixedPayloadPolynomial numericBound
    bitBound
  let atomicResource := termRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let rawResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    failureResource rowsResource
  let middleResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    rawResource
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    middleResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource internalResource
  let modesResource := sixRightDisjunctionPathFourPayloadEnvelope syntaxResource
    modeResource
  have facts := termRowsModeZeroOuterSyntaxFacts tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount bitBound
    witnessStart witnessFinish witnessCount henvironmentSize
  have htailOneClosed := termRowsDisjunction_right_closed modeZeroFormula
    (modeOneFormula ⋎ (modeTwoFormula ⋎
      (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))))
    facts.modesDecomposedClosed
  have htailOneCode :=
    (termRowsDisjunction_right_code_le modeZeroFormula
      (modeOneFormula ⋎ (modeTwoFormula ⋎
        (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))))).trans
      facts.modesDecomposedCode
  have htailTwoClosed := termRowsDisjunction_right_closed modeOneFormula
    (modeTwoFormula ⋎ (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula)))
    htailOneClosed
  have htailTwoCode :=
    (termRowsDisjunction_right_code_le modeOneFormula
      (modeTwoFormula ⋎ (modeFourFormula ⋎
        (modeFiveFormula ⋎ otherFormula)))).trans htailOneCode
  have htailThreeClosed := termRowsDisjunction_right_closed modeTwoFormula
    (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula)) htailTwoClosed
  have htailThreeCode :=
    (termRowsDisjunction_right_code_le modeTwoFormula
      (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))).trans htailTwoCode
  have htailFourClosed := termRowsDisjunction_right_closed modeFourFormula
    (modeFiveFormula ⋎ otherFormula) htailThreeClosed
  have htailFourCode :=
    (termRowsDisjunction_right_code_le modeFourFormula
      (modeFiveFormula ⋎ otherFormula)).trans htailThreeCode
  have hmodeFiveClosed := termRowsDisjunction_left_closed modeFiveFormula
    otherFormula htailFourClosed
  have hmodeFiveCode :=
    (termRowsDisjunction_left_code_le modeFiveFormula otherFormula).trans
      htailFourCode
  have hmodeFiveDecomposition :
      modeFiveFormula = modeEqFormula ⋏ internalFormula := by
    dsimp only [modeFiveFormula, modeEqFormula, internalFormula,
      capturedFormula, middleFormula, residualFormula, rawFormula,
      failureFormula, rowsFormula]
    unfold termRowsModeFiveFormula
    rfl
  have hmodeFiveDecomposedClosed :
      (modeEqFormula ⋏ internalFormula).freeVariables = ∅ := by
    simpa only [hmodeFiveDecomposition] using hmodeFiveClosed
  have hmodeFiveDecomposedCode :
      (binaryFormulaCode (modeEqFormula ⋏ internalFormula)).length <=
        syntaxResource := by
    simpa only [hmodeFiveDecomposition] using hmodeFiveCode
  have hmodeEqClosed := termRowsConjunction_left_closed modeEqFormula
    internalFormula hmodeFiveDecomposedClosed
  have hinternalClosed := termRowsConjunction_right_closed modeEqFormula
    internalFormula hmodeFiveDecomposedClosed
  have hmodeEqCode :=
    (termRowsConjunction_left_code_le modeEqFormula internalFormula).trans
      hmodeFiveDecomposedCode
  have hinternalCode :=
    (termRowsConjunction_right_code_le modeEqFormula internalFormula).trans
      hmodeFiveDecomposedCode
  have hcapturedClosed := termRowsDisjunction_left_closed capturedFormula
    middleFormula hinternalClosed
  have hmiddleClosed := termRowsDisjunction_right_closed capturedFormula
    middleFormula hinternalClosed
  have hcapturedCode :=
    (termRowsDisjunction_left_code_le capturedFormula middleFormula).trans
      hinternalCode
  have hmiddleCode :=
    (termRowsDisjunction_right_code_le capturedFormula middleFormula).trans
      hinternalCode
  have hresidualClosed := termRowsDisjunction_left_closed residualFormula
    rawFormula hmiddleClosed
  have hrawClosed := termRowsDisjunction_right_closed residualFormula rawFormula
    hmiddleClosed
  have hresidualCode :=
    (termRowsDisjunction_left_code_le residualFormula rawFormula).trans
      hmiddleCode
  have hrawCode :=
    (termRowsDisjunction_right_code_le residualFormula rawFormula).trans
      hmiddleCode
  have hfailureClosed := termRowsConjunction_left_closed failureFormula
    rowsFormula hrawClosed
  have hrowsClosed := termRowsConjunction_right_closed failureFormula
    rowsFormula hrawClosed
  have hfailureCode :=
    (termRowsConjunction_left_code_le failureFormula rowsFormula).trans hrawCode
  have hrowsCode :=
    (termRowsConjunction_right_code_le failureFormula rowsFormula).trans hrawCode
  have htableSize : Nat.size tokenTable <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (0 : Fin 33)
  have hwidthSize : Nat.size width <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (1 : Fin 33)
  have htokenCountSize : Nat.size tokenCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (2 : Fin 33)
  have hcurrentStartSize : Nat.size current.start <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (3 : Fin 33)
  have hcurrentFinishSize : Nat.size current.finish <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (4 : Fin 33)
  have hcurrentParserFinishSize : Nat.size current.parserFinish <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (5 : Fin 33)
  have hcurrentParserTokensFinishSize : Nat.size current.parserTokensFinish <=
      bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (6 : Fin 33)
  have hcurrentParserTokensCountSize :
      Nat.size current.parserTokensCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (9 : Fin 33)
  have hcurrentOutputCountSize : Nat.size current.outputCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (13 : Fin 33)
  have hnextFinishSize : Nat.size next.finish <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (15 : Fin 33)
  have hnextParserFinishSize : Nat.size next.parserFinish <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (16 : Fin 33)
  have hnextOutputCountSize : Nat.size next.outputCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (24 : Fin 33)
  have hmodeSize : Nat.size mode <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (25 : Fin 33)
  have htagSize : Nat.size tag <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (27 : Fin 33)
  have hconsumedSize : Nat.size consumedCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (29 : Fin 33)
  let modeCertificate := shortNumeralLiteralEqCertificate mode 5
    (‘5’ : ValuationTerm) (termValue_arithmeticFive modeFiveRawValuation) hmode
  let failureCertificate := doubleFailureCertificateFromData consumedCount tag
    failure
  let rowsCertificate :=
    compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hrows
  let rawCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      failureCertificate rowsCertificate
  let middleCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := residualFormula) rawCertificate
  let internalCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := capturedFormula) middleCertificate
  let modeFullCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction modeCertificate
      internalCertificate
  let tailFourCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := otherFormula) modeFullCertificate
  let tailThreeCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := modeFourFormula) tailFourCertificate
  let tailTwoCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := modeTwoFormula) tailThreeCertificate
  let tailOneCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := modeOneFormula) tailTwoCertificate
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := modeZeroFormula) tailOneCertificate
  have hmodeResource :
      hybridFormulaStructuralPayloadBound modeCertificate <= atomicResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_fixed mode 5
      (‘5’ : ValuationTerm) (termValue_arithmeticFive modeFiveRawValuation)
      hmode bitBound hmodeSize
      (termRowsLiteral_closed (‘5’ : ValuationTerm)
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      (termRowsLiteralCode_le (‘5’ : ValuationTerm) bitBound
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have hfailureResource :
      hybridFormulaStructuralPayloadBound failureCertificate <=
        failureResource :=
    (doubleFailureCertificateFromData_structuralPayloadBound_le_transparent
      consumedCount tag failure).trans
      ((doubleFailurePayloadEnvelopeFromData_le_publicFinite consumedCount tag
        failure).trans
        (doubleFailurePublicFinitePayloadEnvelope_le_fullyFixed consumedCount
          tag bitBound hconsumedSize htagSize))
  have hrowsTransparent :=
    compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hrows
  have hrowsFixed :=
    compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount numericBound bitBound hrows htableSize hwidthSize
      htokenCountSize hcurrentParserFinishSize hcurrentFinishSize
      hcurrentOutputCountSize hcurrentStartSize hcurrentParserTokensFinishSize
      hcurrentParserTokensCountSize hconsumedSize hnextParserFinishSize
      hnextFinishSize hnextOutputCountSize hwidthBound htokenCountBound
      hnumericSize
  have hrowsResource :
      hybridFormulaStructuralPayloadBound rowsCertificate <= rowsResource :=
    hrowsTransparent.trans hrowsFixed
  have hrawResource :
      hybridFormulaStructuralPayloadBound rawCertificate <= rawResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral failureCertificate
      rowsCertificate failureResource rowsResource syntaxResource
      hfailureResource hrowsResource facts.syntaxPositive hfailureClosed
      hrowsClosed hfailureCode hrowsCode hrawCode
  have hmiddleResource :
      hybridFormulaStructuralPayloadBound middleCertificate <= middleResource :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral rawCertificate
      rawResource syntaxResource hrawResource facts.syntaxPositive
      hresidualClosed hrawClosed hresidualCode hrawCode hmiddleCode
  have hinternalResource :
      hybridFormulaStructuralPayloadBound internalCertificate <=
        internalResource :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral middleCertificate
      middleResource syntaxResource hmiddleResource facts.syntaxPositive
      hcapturedClosed hmiddleClosed hcapturedCode hmiddleCode hinternalCode
  have hmodeFullResource :
      hybridFormulaStructuralPayloadBound modeFullCertificate <= modeResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral modeCertificate
      internalCertificate atomicResource internalResource syntaxResource
      hmodeResource hinternalResource facts.syntaxPositive hmodeEqClosed
      hinternalClosed hmodeEqCode hinternalCode hmodeFiveDecomposedCode
  have hmodesResource :
      hybridFormulaStructuralPayloadBound modesCertificate <= modesResource :=
    sixRightDisjunctionPathFourPayloadBound_le_closedGeneral modeZeroFormula
      modeOneFormula modeTwoFormula modeFourFormula modeFiveFormula otherFormula
      modeFullCertificate modeResource syntaxResource hmodeFullResource
      facts.syntaxPositive facts.modesDecomposedClosed facts.modesDecomposedCode
  have houter := termRowsPositiveOuterCertificate_structuralPayloadBound_le_fixed
    tokenTable width tokenCount current next mode binderArity tag argument
    consumedCount witnessStart witnessFinish witnessCount modesResource bitBound
    hcount hconsumed modesCertificate hmodesResource henvironmentSize
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (termRowsPositiveOuterCertificate tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount hcount hconsumed modesCertificate) <= _
  simpa only [termRowsModeFiveRawFixedPayloadPolynomial, syntaxResource,
    failureResource, rowsResource, atomicResource, rawResource, middleResource,
    internalResource, modeResource, modesResource] using houter

#print axioms
  compactFormulaTransformTermOutputRowsModeFiveRawBranch_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFiveRawFullyFixedBounds
