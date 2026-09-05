import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPositiveOuterFixedCore
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureTripleFixedBound
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixFullyFixedBounds
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds

/-! # Fully fixed raw-prefix branch under term-output mode two -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 220000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeTwoRawFullyFixedBounds

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
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureTripleFixedBound
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOuterSyntaxFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterSyntaxFacts
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPositiveOuterFixedCore
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixFullyFixedBounds

private abbrev modeTwoRawValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsModeTwoRawFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource := termRowsOuterSyntaxPolynomial bitBound
  let rawResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termOutputTripleFailureFixedPayloadPolynomial bitBound)
    (appendSourcePrefixFullyFixedPayloadPolynomial numericBound bitBound)
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    rawResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termRowsPositiveAtomicFixedPayloadPolynomial bitBound) internalResource
  let modesResource := sixRightDisjunctionPathTwoPayloadEnvelope syntaxResource
    modeResource
  termRowsPositiveOuterFixedPayloadPolynomial modesResource bitBound

theorem
    compactFormulaTransformTermOutputRowsModeTwoRawBranch_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 2)
    (failure : TripleFailureCheckedData consumedCount tag argument binderArity)
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
          (.modeTwoRaw hcount hconsumed hmode failure hrows)) <=
      termRowsModeTwoRawFixedPayloadPolynomial numericBound bitBound := by
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
    (‘2’ : ValuationTerm)
  let selectedFormula :=
    termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
      termRowsWitnessFormula tokenTable width tokenCount current next
        witnessStart witnessFinish witnessCount
  let failureFormula := tripleFailureFormula
    (shortBinaryNumeralTerm consumedCount) (shortBinaryNumeralTerm tag)
    (shortBinaryNumeralTerm argument) (shortBinaryNumeralTerm binderArity)
  let rowsFormula := termRowsRawPrefixFormula tokenTable width tokenCount
    current next consumedCount
  let rawFormula := failureFormula ⋏ rowsFormula
  let internalFormula := selectedFormula ⋎ rawFormula
  let failureResource := termOutputTripleFailureFixedPayloadPolynomial bitBound
  let rowsResource := appendSourcePrefixFullyFixedPayloadPolynomial numericBound
    bitBound
  let atomicResource := termRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let rawResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    failureResource rowsResource
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    rawResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource internalResource
  let modesResource := sixRightDisjunctionPathTwoPayloadEnvelope syntaxResource
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
  have hmodeTwoClosed := termRowsDisjunction_left_closed modeTwoFormula
    (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula)) htailTwoClosed
  have hmodeTwoCode :=
    (termRowsDisjunction_left_code_le modeTwoFormula
      (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))).trans htailTwoCode
  have hmodeTwoDecomposition :
      modeTwoFormula = modeEqFormula ⋏ internalFormula := by
    dsimp only [modeTwoFormula, modeEqFormula, internalFormula,
      selectedFormula, rawFormula, failureFormula, rowsFormula]
    unfold termRowsModeTwoFormula
    rfl
  have hmodeTwoDecomposedClosed :
      (modeEqFormula ⋏ internalFormula).freeVariables = ∅ := by
    simpa only [hmodeTwoDecomposition] using hmodeTwoClosed
  have hmodeTwoDecomposedCode :
      (binaryFormulaCode (modeEqFormula ⋏ internalFormula)).length <=
        syntaxResource := by
    simpa only [hmodeTwoDecomposition] using hmodeTwoCode
  have hmodeEqClosed := termRowsConjunction_left_closed modeEqFormula
    internalFormula hmodeTwoDecomposedClosed
  have hinternalClosed := termRowsConjunction_right_closed modeEqFormula
    internalFormula hmodeTwoDecomposedClosed
  have hmodeEqCode :=
    (termRowsConjunction_left_code_le modeEqFormula internalFormula).trans
      hmodeTwoDecomposedCode
  have hinternalCode :=
    (termRowsConjunction_right_code_le modeEqFormula internalFormula).trans
      hmodeTwoDecomposedCode
  have hselectedClosed := termRowsDisjunction_left_closed selectedFormula
    rawFormula hinternalClosed
  have hrawClosed := termRowsDisjunction_right_closed selectedFormula rawFormula
    hinternalClosed
  have hselectedCode :=
    (termRowsDisjunction_left_code_le selectedFormula rawFormula).trans
      hinternalCode
  have hrawCode :=
    (termRowsDisjunction_right_code_le selectedFormula rawFormula).trans
      hinternalCode
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
  have hbinderAritySize : Nat.size binderArity <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (26 : Fin 33)
  have htagSize : Nat.size tag <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (27 : Fin 33)
  have hargumentSize : Nat.size argument <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (28 : Fin 33)
  have hconsumedSize : Nat.size consumedCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (29 : Fin 33)
  let modeCertificate := shortNumeralLiteralEqCertificate mode 2
    (‘2’ : ValuationTerm) (termValue_arithmeticTwo modeTwoRawValuation) hmode
  let failureCertificate := tripleFailureCertificateFromData consumedCount tag
    argument binderArity failure
  let rowsCertificate :=
    compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hrows
  let rawCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      failureCertificate rowsCertificate
  let internalCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := selectedFormula) rawCertificate
  let modeFullCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction modeCertificate
      internalCertificate
  let tailTwoCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))
      modeFullCertificate
  let tailOneCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := modeOneFormula) tailTwoCertificate
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := modeZeroFormula) tailOneCertificate
  have hmodeResource :
      hybridFormulaStructuralPayloadBound modeCertificate <= atomicResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_fixed mode 2
      (‘2’ : ValuationTerm) (termValue_arithmeticTwo modeTwoRawValuation) hmode
      bitBound hmodeSize
      (termRowsLiteral_closed (‘2’ : ValuationTerm)
        (Or.inr (Or.inr (Or.inl rfl))))
      (termRowsLiteralCode_le (‘2’ : ValuationTerm) bitBound
        (Or.inr (Or.inr (Or.inl rfl))))
  have hfailureResource :
      hybridFormulaStructuralPayloadBound failureCertificate <=
        failureResource :=
    (tripleFailureCertificateFromData_structuralPayloadBound_le_transparent
      consumedCount tag argument binderArity failure).trans
      ((tripleFailurePayloadEnvelopeFromData_le_publicFinite consumedCount tag
        argument binderArity failure).trans
        (tripleFailurePublicFinitePayloadEnvelope_le_fullyFixed consumedCount
          tag argument binderArity bitBound hconsumedSize htagSize
          hargumentSize hbinderAritySize))
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
  have hinternalResource :
      hybridFormulaStructuralPayloadBound internalCertificate <=
        internalResource :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral rawCertificate
      rawResource syntaxResource hrawResource facts.syntaxPositive
      hselectedClosed hrawClosed hselectedCode hrawCode hinternalCode
  have hmodeFullResource :
      hybridFormulaStructuralPayloadBound modeFullCertificate <= modeResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral modeCertificate
      internalCertificate atomicResource internalResource syntaxResource
      hmodeResource hinternalResource facts.syntaxPositive hmodeEqClosed
      hinternalClosed hmodeEqCode hinternalCode hmodeTwoDecomposedCode
  have hmodesResource :
      hybridFormulaStructuralPayloadBound modesCertificate <= modesResource :=
    sixRightDisjunctionPathTwoPayloadBound_le_closedGeneral modeZeroFormula
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
  simpa only [termRowsModeTwoRawFixedPayloadPolynomial, syntaxResource,
    failureResource, rowsResource, atomicResource, rawResource,
    internalResource, modeResource, modesResource] using houter

#print axioms
  compactFormulaTransformTermOutputRowsModeTwoRawBranch_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeTwoRawFullyFixedBounds
