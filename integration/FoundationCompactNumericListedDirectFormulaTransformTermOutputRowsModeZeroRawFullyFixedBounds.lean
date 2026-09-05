import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterFixedCore
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureTripleFixedBound
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixFullyFixedBounds
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds

/-! # Fully fixed raw-prefix branch under term-output mode zero -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 220000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroRawFullyFixedBounds

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
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterFixedCore
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixFullyFixedBounds

private abbrev modeZeroRawValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsModeZeroRawFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource := termRowsOuterSyntaxPolynomial bitBound
  let shiftRowsResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource (termOutputDoubleFailureFixedPayloadPolynomial bitBound)
    (appendSourcePrefixFullyFixedPayloadPolynomial numericBound bitBound)
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource (termOutputTripleFailureFixedPayloadPolynomial bitBound)
    shiftRowsResource
  let middleResource := hybridDisjunctionGeneralPayloadEnvelope
    syntaxResource selectedResource
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope
    syntaxResource middleResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termRowsPositiveAtomicFixedPayloadPolynomial bitBound) internalResource
  termRowsModeZeroOuterFixedPayloadPolynomial modeResource bitBound

theorem
    compactFormulaTransformTermOutputRowsModeZeroRawBranch_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 0)
    (lowerFailure : TripleFailureCheckedData consumedCount tag argument
      binderArity)
    (shiftFailure : DoubleFailureCheckedData consumedCount tag)
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
          (.modeZeroRaw hcount hconsumed hmode lowerFailure shiftFailure
            hrows)) <=
      termRowsModeZeroRawFixedPayloadPolynomial numericBound bitBound := by
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
    (‘0’ : ValuationTerm)
  let lowerPairFormula :=
    termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
      termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current next
  let lowerFailureFormula := tripleFailureFormula
    (shortBinaryNumeralTerm consumedCount) (shortBinaryNumeralTerm tag)
    (shortBinaryNumeralTerm argument) (shortBinaryNumeralTerm binderArity)
  let shiftedPairFormula := lowerFailureFormula ⋏
    (termRowsGuardOneTagFormula consumedCount tag ⋏
      termRowsAppendTwoShiftedFormula tokenTable width tokenCount current next
        argument)
  let shiftFailureFormula := doubleFailureFormula
    (shortBinaryNumeralTerm consumedCount) (shortBinaryNumeralTerm tag)
  let rowsFormula := termRowsRawPrefixFormula tokenTable width tokenCount
    current next consumedCount
  let shiftRowsFormula := shiftFailureFormula ⋏ rowsFormula
  let rawPairFormula := lowerFailureFormula ⋏ shiftRowsFormula
  let tailFormula := shiftedPairFormula ⋎ rawPairFormula
  let internalFormula := lowerPairFormula ⋎ tailFormula
  let lowerFailureResource := termOutputTripleFailureFixedPayloadPolynomial
    bitBound
  let shiftFailureResource := termOutputDoubleFailureFixedPayloadPolynomial
    bitBound
  let rowsResource := appendSourcePrefixFullyFixedPayloadPolynomial
    numericBound bitBound
  let atomicResource := termRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let shiftRowsResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource shiftFailureResource rowsResource
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource lowerFailureResource shiftRowsResource
  let middleResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    selectedResource
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope
    syntaxResource middleResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource internalResource
  have facts := termRowsModeZeroOuterSyntaxFacts tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount bitBound
    witnessStart witnessFinish witnessCount henvironmentSize
  have hmodeZeroClosed := termRowsDisjunction_left_closed modeZeroFormula
    (modeOneFormula ⋎ (modeTwoFormula ⋎
      (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))))
    facts.modesDecomposedClosed
  have hmodeZeroCode :=
    (termRowsDisjunction_left_code_le modeZeroFormula
      (modeOneFormula ⋎ (modeTwoFormula ⋎
        (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))))).trans
      facts.modesDecomposedCode
  have hmodeZeroDecomposition :
      modeZeroFormula = modeEqFormula ⋏ internalFormula := by
    dsimp only [modeZeroFormula, modeEqFormula, internalFormula,
      lowerPairFormula, tailFormula, shiftedPairFormula, rawPairFormula,
      lowerFailureFormula, shiftRowsFormula, shiftFailureFormula, rowsFormula]
    unfold termRowsModeZeroFormula
    rfl
  have hmodeZeroDecomposedClosed :
      (modeEqFormula ⋏ internalFormula).freeVariables = ∅ := by
    simpa only [hmodeZeroDecomposition] using hmodeZeroClosed
  have hmodeZeroDecomposedCode :
      (binaryFormulaCode (modeEqFormula ⋏ internalFormula)).length <=
        syntaxResource := by
    simpa only [hmodeZeroDecomposition] using hmodeZeroCode
  have hmodeEqClosed := termRowsConjunction_left_closed modeEqFormula
    internalFormula hmodeZeroDecomposedClosed
  have hinternalClosed := termRowsConjunction_right_closed modeEqFormula
    internalFormula hmodeZeroDecomposedClosed
  have hmodeEqCode :=
    (termRowsConjunction_left_code_le modeEqFormula internalFormula).trans
      hmodeZeroDecomposedCode
  have hinternalCode :=
    (termRowsConjunction_right_code_le modeEqFormula internalFormula).trans
      hmodeZeroDecomposedCode
  have hlowerPairClosed := termRowsDisjunction_left_closed lowerPairFormula
    tailFormula hinternalClosed
  have htailClosed := termRowsDisjunction_right_closed lowerPairFormula
    tailFormula hinternalClosed
  have hlowerPairCode :=
    (termRowsDisjunction_left_code_le lowerPairFormula tailFormula).trans
      hinternalCode
  have htailCode :=
    (termRowsDisjunction_right_code_le lowerPairFormula tailFormula).trans
      hinternalCode
  have hshiftedPairClosed := termRowsDisjunction_left_closed shiftedPairFormula
    rawPairFormula htailClosed
  have hrawPairClosed := termRowsDisjunction_right_closed shiftedPairFormula
    rawPairFormula htailClosed
  have hshiftedPairCode :=
    (termRowsDisjunction_left_code_le shiftedPairFormula rawPairFormula).trans
      htailCode
  have hrawPairCode :=
    (termRowsDisjunction_right_code_le shiftedPairFormula rawPairFormula).trans
      htailCode
  have hlowerFailureClosed := termRowsConjunction_left_closed
    lowerFailureFormula shiftRowsFormula hrawPairClosed
  have hshiftRowsClosed := termRowsConjunction_right_closed
    lowerFailureFormula shiftRowsFormula hrawPairClosed
  have hlowerFailureCode :=
    (termRowsConjunction_left_code_le lowerFailureFormula shiftRowsFormula).trans
      hrawPairCode
  have hshiftRowsCode :=
    (termRowsConjunction_right_code_le lowerFailureFormula shiftRowsFormula).trans
      hrawPairCode
  have hshiftFailureClosed := termRowsConjunction_left_closed
    shiftFailureFormula rowsFormula hshiftRowsClosed
  have hrowsClosed := termRowsConjunction_right_closed shiftFailureFormula
    rowsFormula hshiftRowsClosed
  have hshiftFailureCode :=
    (termRowsConjunction_left_code_le shiftFailureFormula rowsFormula).trans
      hshiftRowsCode
  have hrowsCode :=
    (termRowsConjunction_right_code_le shiftFailureFormula rowsFormula).trans
      hshiftRowsCode
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
  let modeCertificate := shortNumeralLiteralEqCertificate mode 0
    (‘0’ : ValuationTerm) (termValue_arithmeticZero modeZeroRawValuation) hmode
  let lowerFailureCertificate := tripleFailureCertificateFromData consumedCount
    tag argument binderArity lowerFailure
  let shiftFailureCertificate := doubleFailureCertificateFromData consumedCount
    tag shiftFailure
  let rowsCertificate :=
    compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hrows
  let shiftRowsCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      shiftFailureCertificate rowsCertificate
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      lowerFailureCertificate shiftRowsCertificate
  let middleCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := shiftedPairFormula) selectedCertificate
  let internalCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := lowerPairFormula) middleCertificate
  let modeFullCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction modeCertificate
      internalCertificate
  have hmodeResource :
      hybridFormulaStructuralPayloadBound modeCertificate <= atomicResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_fixed mode 0
      (‘0’ : ValuationTerm) (termValue_arithmeticZero modeZeroRawValuation)
      hmode bitBound hmodeSize
      (termRowsLiteral_closed (‘0’ : ValuationTerm) (Or.inl rfl))
      (termRowsLiteralCode_le (‘0’ : ValuationTerm) bitBound (Or.inl rfl))
  have hlowerFailureResource :
      hybridFormulaStructuralPayloadBound lowerFailureCertificate <=
        lowerFailureResource :=
    (tripleFailureCertificateFromData_structuralPayloadBound_le_transparent
      consumedCount tag argument binderArity lowerFailure).trans
      ((tripleFailurePayloadEnvelopeFromData_le_publicFinite consumedCount tag
        argument binderArity lowerFailure).trans
        (tripleFailurePublicFinitePayloadEnvelope_le_fullyFixed consumedCount
          tag argument binderArity bitBound hconsumedSize htagSize
          hargumentSize hbinderAritySize))
  have hshiftFailureResource :
      hybridFormulaStructuralPayloadBound shiftFailureCertificate <=
        shiftFailureResource :=
    (doubleFailureCertificateFromData_structuralPayloadBound_le_transparent
      consumedCount tag shiftFailure).trans
      ((doubleFailurePayloadEnvelopeFromData_le_publicFinite consumedCount tag
        shiftFailure).trans
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
  have hshiftRowsResource :
      hybridFormulaStructuralPayloadBound shiftRowsCertificate <=
        shiftRowsResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral
      shiftFailureCertificate rowsCertificate shiftFailureResource rowsResource
      syntaxResource hshiftFailureResource hrowsResource facts.syntaxPositive
      hshiftFailureClosed hrowsClosed hshiftFailureCode hrowsCode
      hshiftRowsCode
  have hselectedResource :
      hybridFormulaStructuralPayloadBound selectedCertificate <=
        selectedResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral
      lowerFailureCertificate shiftRowsCertificate lowerFailureResource
      shiftRowsResource syntaxResource hlowerFailureResource
      hshiftRowsResource facts.syntaxPositive hlowerFailureClosed
      hshiftRowsClosed hlowerFailureCode hshiftRowsCode hrawPairCode
  have hmiddleResource :
      hybridFormulaStructuralPayloadBound middleCertificate <= middleResource :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      selectedCertificate selectedResource syntaxResource hselectedResource
      facts.syntaxPositive hshiftedPairClosed hrawPairClosed hshiftedPairCode
      hrawPairCode htailCode
  have hinternalResource :
      hybridFormulaStructuralPayloadBound internalCertificate <=
        internalResource :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral middleCertificate
      middleResource syntaxResource hmiddleResource facts.syntaxPositive
      hlowerPairClosed htailClosed hlowerPairCode htailCode hinternalCode
  have hmodeFullResource :
      hybridFormulaStructuralPayloadBound modeFullCertificate <= modeResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral modeCertificate
      internalCertificate atomicResource internalResource syntaxResource
      hmodeResource hinternalResource facts.syntaxPositive hmodeEqClosed
      hinternalClosed hmodeEqCode hinternalCode hmodeZeroDecomposedCode
  have houter :=
    termRowsModeZeroOuterCertificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount modeResource bitBound
      hcount hconsumed modeFullCertificate hmodeFullResource henvironmentSize
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (termRowsModeZeroOuterCertificate tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount hcount hconsumed modeFullCertificate) <= _
  simpa only [termRowsModeZeroRawFixedPayloadPolynomial, syntaxResource,
    lowerFailureResource, shiftFailureResource, rowsResource, atomicResource,
    shiftRowsResource, selectedResource, middleResource, internalResource,
    modeResource] using houter

#print axioms
  compactFormulaTransformTermOutputRowsModeZeroRawBranch_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroRawFullyFixedBounds
