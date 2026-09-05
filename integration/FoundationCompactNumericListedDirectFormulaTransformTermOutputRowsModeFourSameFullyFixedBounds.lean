import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPositiveOuterFixedCore
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds

/-! # Fully fixed same-rows branch under term-output mode four -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 220000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFourSameFullyFixedBounds

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
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds

private abbrev modeFourSameValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsModeFourSameFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource := termRowsOuterSyntaxPolynomial bitBound
  let rawResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termOutputDoubleFailureFixedPayloadPolynomial bitBound)
    (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    rawResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termRowsPositiveAtomicFixedPayloadPolynomial bitBound) internalResource
  let modesResource := sixRightDisjunctionPathThreePayloadEnvelope
    syntaxResource modeResource
  termRowsPositiveOuterFixedPayloadPolynomial modesResource bitBound

theorem
    compactFormulaTransformTermOutputRowsModeFourSameBranch_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 4)
    (failure : DoubleFailureCheckedData consumedCount tag)
    (hrows : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
      current next)
    (henvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hcurrentOutputCountBound : current.outputCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.modeFourSame hcount hconsumed hmode failure hrows)) <=
      termRowsModeFourSameFixedPayloadPolynomial numericBound bitBound := by
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
    (‘4’ : ValuationTerm)
  let selectedFormula := termRowsGuardOneTagFormula consumedCount tag ⋏
    termRowsOneValueFormula tokenTable width tokenCount current next argument
  let failureFormula := doubleFailureFormula
    (shortBinaryNumeralTerm consumedCount) (shortBinaryNumeralTerm tag)
  let rowsFormula := termRowsSameFormula tokenTable width tokenCount current next
  let rawFormula := failureFormula ⋏ rowsFormula
  let internalFormula := selectedFormula ⋎ rawFormula
  let failureResource := termOutputDoubleFailureFixedPayloadPolynomial bitBound
  let rowsResource := sameRowsCompleteFullyFixedPayloadPolynomial numericBound
    bitBound
  let atomicResource := termRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let rawResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    failureResource rowsResource
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    rawResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource internalResource
  let modesResource := sixRightDisjunctionPathThreePayloadEnvelope
    syntaxResource modeResource
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
  have hmodeFourClosed := termRowsDisjunction_left_closed modeFourFormula
    (modeFiveFormula ⋎ otherFormula) htailThreeClosed
  have hmodeFourCode :=
    (termRowsDisjunction_left_code_le modeFourFormula
      (modeFiveFormula ⋎ otherFormula)).trans htailThreeCode
  have hmodeFourDecomposition :
      modeFourFormula = modeEqFormula ⋏ internalFormula := by
    dsimp only [modeFourFormula, modeEqFormula, internalFormula,
      selectedFormula, rawFormula, failureFormula, rowsFormula]
    unfold termRowsModeFourFormula
    rfl
  have hmodeFourDecomposedClosed :
      (modeEqFormula ⋏ internalFormula).freeVariables = ∅ := by
    simpa only [hmodeFourDecomposition] using hmodeFourClosed
  have hmodeFourDecomposedCode :
      (binaryFormulaCode (modeEqFormula ⋏ internalFormula)).length <=
        syntaxResource := by
    simpa only [hmodeFourDecomposition] using hmodeFourCode
  have hmodeEqClosed := termRowsConjunction_left_closed modeEqFormula
    internalFormula hmodeFourDecomposedClosed
  have hinternalClosed := termRowsConjunction_right_closed modeEqFormula
    internalFormula hmodeFourDecomposedClosed
  have hmodeEqCode :=
    (termRowsConjunction_left_code_le modeEqFormula internalFormula).trans
      hmodeFourDecomposedCode
  have hinternalCode :=
    (termRowsConjunction_right_code_le modeEqFormula internalFormula).trans
      hmodeFourDecomposedCode
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
  have htokenTableSize : Nat.size tokenTable <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (0 : Fin 33)
  have hcurrentOutputBoundarySize :
      Nat.size current.outputBoundary <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (12 : Fin 33)
  have hnextOutputBoundarySize : Nat.size next.outputBoundary <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (23 : Fin 33)
  have hmodeSize : Nat.size mode <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (25 : Fin 33)
  have htagSize : Nat.size tag <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (27 : Fin 33)
  have hconsumedSize : Nat.size consumedCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (29 : Fin 33)
  let modeCertificate := shortNumeralLiteralEqCertificate mode 4
    (‘4’ : ValuationTerm) (termValue_arithmeticFour modeFourSameValuation) hmode
  let failureCertificate := doubleFailureCertificateFromData consumedCount tag
    failure
  let rowsCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hrows
  let rawCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      failureCertificate rowsCertificate
  let internalCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := selectedFormula) rawCertificate
  let modeFullCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction modeCertificate
      internalCertificate
  let tailThreeCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := modeFiveFormula ⋎ otherFormula) modeFullCertificate
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
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_fixed mode 4
      (‘4’ : ValuationTerm) (termValue_arithmeticFour modeFourSameValuation)
      hmode bitBound hmodeSize
      (termRowsLiteral_closed (‘4’ : ValuationTerm)
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (termRowsLiteralCode_le (‘4’ : ValuationTerm) bitBound
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
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
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hrows
  have hrowsFixed :=
    compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_fullyFixed tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount numericBound bitBound hrows
      hwidthBound htokenCountBound hcurrentOutputCountBound htokenTableSize
      hcurrentOutputBoundarySize hnextOutputBoundarySize hnumericSize
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
      hinternalClosed hmodeEqCode hinternalCode hmodeFourDecomposedCode
  have hmodesResource :
      hybridFormulaStructuralPayloadBound modesCertificate <= modesResource :=
    sixRightDisjunctionPathThreePayloadBound_le_closedGeneral modeZeroFormula
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
  simpa only [termRowsModeFourSameFixedPayloadPolynomial, syntaxResource,
    failureResource, rowsResource, atomicResource, rawResource,
    internalResource, modeResource, modesResource] using houter

#print axioms
  compactFormulaTransformTermOutputRowsModeFourSameBranch_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFourSameFullyFixedBounds
