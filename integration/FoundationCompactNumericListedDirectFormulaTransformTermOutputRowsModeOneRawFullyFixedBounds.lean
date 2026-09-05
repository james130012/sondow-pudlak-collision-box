import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPositiveOuterFixedCore
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixFullyFixedBounds
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds

/-! # Fully fixed raw-prefix branch under term-output mode one -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 220000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeOneRawFullyFixedBounds

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

private abbrev modeOneRawValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsModeOneRawFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource := termRowsOuterSyntaxPolynomial bitBound
  let rawResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termOutputDoubleFailureFixedPayloadPolynomial bitBound)
    (appendSourcePrefixFullyFixedPayloadPolynomial numericBound bitBound)
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    rawResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termRowsPositiveAtomicFixedPayloadPolynomial bitBound) internalResource
  let modesResource := sixRightDisjunctionPathOnePayloadEnvelope syntaxResource
    modeResource
  termRowsPositiveOuterFixedPayloadPolynomial modesResource bitBound

theorem
    compactFormulaTransformTermOutputRowsModeOneRawBranch_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 1)
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
          (.modeOneRaw hcount hconsumed hmode failure hrows)) <=
      termRowsModeOneRawFixedPayloadPolynomial numericBound bitBound := by
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
    (‘1’ : ValuationTerm)
  let selectedFormula := termRowsGuardOneTagFormula consumedCount tag ⋏
    termRowsAppendTwoShiftedFormula tokenTable width tokenCount current next
      argument
  let failureFormula := doubleFailureFormula
    (shortBinaryNumeralTerm consumedCount) (shortBinaryNumeralTerm tag)
  let rowsFormula := termRowsRawPrefixFormula tokenTable width tokenCount
    current next consumedCount
  let rawFormula := failureFormula ⋏ rowsFormula
  let internalFormula := selectedFormula ⋎ rawFormula
  let failureResource := termOutputDoubleFailureFixedPayloadPolynomial bitBound
  let rowsResource := appendSourcePrefixFullyFixedPayloadPolynomial
    numericBound bitBound
  let atomicResource := termRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let rawResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    failureResource rowsResource
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    rawResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource internalResource
  let modesResource := sixRightDisjunctionPathOnePayloadEnvelope syntaxResource
    modeResource
  have facts := termRowsModeZeroOuterSyntaxFacts tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount bitBound
    witnessStart witnessFinish witnessCount henvironmentSize
  have htailClosed := termRowsDisjunction_right_closed modeZeroFormula
    (modeOneFormula ⋎ (modeTwoFormula ⋎
      (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))))
    facts.modesDecomposedClosed
  have htailCode :=
    (termRowsDisjunction_right_code_le modeZeroFormula
      (modeOneFormula ⋎ (modeTwoFormula ⋎
        (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))))).trans
      facts.modesDecomposedCode
  have hmodeOneClosed := termRowsDisjunction_left_closed modeOneFormula
    (modeTwoFormula ⋎ (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula)))
    htailClosed
  have hmodeOneCode :=
    (termRowsDisjunction_left_code_le modeOneFormula
      (modeTwoFormula ⋎ (modeFourFormula ⋎
        (modeFiveFormula ⋎ otherFormula)))).trans htailCode
  have hmodeOneDecomposition :
      modeOneFormula = modeEqFormula ⋏ internalFormula := by
    dsimp only [modeOneFormula, modeEqFormula, internalFormula,
      selectedFormula, rawFormula, failureFormula, rowsFormula]
    unfold termRowsModeOneFormula
    rfl
  have hmodeOneDecomposedClosed :
      (modeEqFormula ⋏ internalFormula).freeVariables = ∅ := by
    simpa only [hmodeOneDecomposition] using hmodeOneClosed
  have hmodeOneDecomposedCode :
      (binaryFormulaCode (modeEqFormula ⋏ internalFormula)).length <=
        syntaxResource := by
    simpa only [hmodeOneDecomposition] using hmodeOneCode
  have hmodeEqClosed := termRowsConjunction_left_closed modeEqFormula
    internalFormula hmodeOneDecomposedClosed
  have hinternalClosed := termRowsConjunction_right_closed modeEqFormula
    internalFormula hmodeOneDecomposedClosed
  have hmodeEqCode :=
    (termRowsConjunction_left_code_le modeEqFormula internalFormula).trans
      hmodeOneDecomposedCode
  have hinternalCode :=
    (termRowsConjunction_right_code_le modeEqFormula internalFormula).trans
      hmodeOneDecomposedCode
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
  have htagSize : Nat.size tag <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (27 : Fin 33)
  have hconsumedSize : Nat.size consumedCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (29 : Fin 33)
  let modeCertificate := shortNumeralLiteralEqCertificate mode 1
    (‘1’ : ValuationTerm) (termValue_arithmeticOne modeOneRawValuation) hmode
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
  let internalCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := selectedFormula) rawCertificate
  let modeFullCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction modeCertificate
      internalCertificate
  let selectedPathCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := modeTwoFormula ⋎
        (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula)))
      modeFullCertificate
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := modeZeroFormula) selectedPathCertificate
  have hmodeResource :
      hybridFormulaStructuralPayloadBound modeCertificate <= atomicResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_fixed mode 1
      (‘1’ : ValuationTerm) (termValue_arithmeticOne modeOneRawValuation) hmode
      bitBound hmodeSize
      (termRowsLiteral_closed (‘1’ : ValuationTerm) (Or.inr (Or.inl rfl)))
      (termRowsLiteralCode_le (‘1’ : ValuationTerm) bitBound
        (Or.inr (Or.inl rfl)))
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
      hinternalClosed hmodeEqCode hinternalCode hmodeOneDecomposedCode
  have hmodesResource :
      hybridFormulaStructuralPayloadBound modesCertificate <= modesResource :=
    sixRightDisjunctionPathOnePayloadBound_le_closedGeneral modeZeroFormula
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
  simpa only [termRowsModeOneRawFixedPayloadPolynomial, syntaxResource,
    failureResource, rowsResource, atomicResource, rawResource,
    internalResource, modeResource, modesResource] using houter

#print axioms
  compactFormulaTransformTermOutputRowsModeOneRawBranch_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeOneRawFullyFixedBounds
