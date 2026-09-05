import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPositiveOuterFixedCore
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsComparisonGuardFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsResidualExistsFullyFixedBounds
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds

/-! # Fully fixed residual-witness branch under term-output mode five -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 260000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFiveResidualFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
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
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGuardFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOuterSyntaxFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterSyntaxFacts
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPositiveOuterFixedCore
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAppendCapturedFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsResidualExistsFullyFixedBounds

private abbrev modeFiveResidualValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsModeFiveResidualFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let branchBitBound := termRowsAdditiveBitBound bitBound
  let syntaxResource := termRowsOuterSyntaxPolynomial branchBitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource (termRowsThreeGuardFixedPayloadPolynomial branchBitBound)
    (termRowsResidualExistsFixedPayloadPolynomial numericBound branchBitBound)
  let middleResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    selectedResource
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    middleResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termRowsPositiveAtomicFixedPayloadPolynomial branchBitBound)
    internalResource
  let modesResource := sixRightDisjunctionPathFourPayloadEnvelope syntaxResource
    modeResource
  termRowsPositiveOuterFixedPayloadPolynomial modesResource branchBitBound

theorem
    compactFormulaTransformTermOutputRowsModeFiveResidualBranch_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount residual numericBound
      bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 5)
    (hguard : consumedCount = 2 ∧ tag = 1 ∧ witnessCount <= argument)
    (hresidual : residual <= argument)
    (hequality : argument = witnessCount + residual)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 1 residual)
    (henvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnextOutputCountBound : next.outputCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.modeFiveResidual hcount hconsumed hmode hguard residual hresidual
            hequality hrows)) <=
      termRowsModeFiveResidualFixedPayloadPolynomial numericBound bitBound := by
  let branchBitBound := termRowsAdditiveBitBound bitBound
  let syntaxResource := termRowsOuterSyntaxPolynomial branchBitBound
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
  let guardFormula := termRowsResidualGuardFormula consumedCount tag argument
    witnessCount
  let residualExistsFormula :=
    compactFormulaTransformTermResidualExistsFormula tokenTable width
      tokenCount current next argument witnessCount
  let selectedFormula := guardFormula ⋏ residualExistsFormula
  let rawFormula := doubleFailureFormula
      (shortBinaryNumeralTerm consumedCount) (shortBinaryNumeralTerm tag) ⋏
    termRowsRawPrefixFormula tokenTable width tokenCount current next
      consumedCount
  let middleFormula := selectedFormula ⋎ rawFormula
  let internalFormula := capturedFormula ⋎ middleFormula
  let guardResource := termRowsThreeGuardFixedPayloadPolynomial branchBitBound
  let residualResource := termRowsResidualExistsFixedPayloadPolynomial
    numericBound branchBitBound
  let atomicResource := termRowsPositiveAtomicFixedPayloadPolynomial
    branchBitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource guardResource residualResource
  let middleResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    selectedResource
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    middleResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource internalResource
  let modesResource := sixRightDisjunctionPathFourPayloadEnvelope syntaxResource
    modeResource
  have henvironmentLarge : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <=
        branchBitBound := by
    intro coordinate
    exact (henvironmentSize coordinate).trans (by
      unfold branchBitBound termRowsAdditiveBitBound
      omega)
  have facts := termRowsModeZeroOuterSyntaxFacts tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount branchBitBound
    witnessStart witnessFinish witnessCount henvironmentLarge
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
      capturedFormula, middleFormula, selectedFormula, guardFormula,
      residualExistsFormula, rawFormula]
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
  have hselectedClosed := termRowsDisjunction_left_closed selectedFormula
    rawFormula hmiddleClosed
  have hrawClosed := termRowsDisjunction_right_closed selectedFormula rawFormula
    hmiddleClosed
  have hselectedCode :=
    (termRowsDisjunction_left_code_le selectedFormula rawFormula).trans
      hmiddleCode
  have hrawCode :=
    (termRowsDisjunction_right_code_le selectedFormula rawFormula).trans
      hmiddleCode
  have hguardClosed := termRowsConjunction_left_closed guardFormula
    residualExistsFormula hselectedClosed
  have hresidualExistsClosed := termRowsConjunction_right_closed guardFormula
    residualExistsFormula hselectedClosed
  have hguardCode :=
    (termRowsConjunction_left_code_le guardFormula residualExistsFormula).trans
      hselectedCode
  have hresidualExistsCode :=
    (termRowsConjunction_right_code_le guardFormula residualExistsFormula).trans
      hselectedCode
  have htableSize : Nat.size tokenTable <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (0 : Fin 33)
  have hwidthSize : Nat.size width <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (1 : Fin 33)
  have htokenCountSize : Nat.size tokenCount <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (2 : Fin 33)
  have hcurrentFinishSize : Nat.size current.finish <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (4 : Fin 33)
  have hcurrentParserFinishSize : Nat.size current.parserFinish <=
      branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (5 : Fin 33)
  have hcurrentOutputCountSize : Nat.size current.outputCount <=
      branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (13 : Fin 33)
  have hnextFinishSize : Nat.size next.finish <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (15 : Fin 33)
  have hnextParserFinishSize : Nat.size next.parserFinish <=
      branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (16 : Fin 33)
  have hnextOutputBoundarySize : Nat.size next.outputBoundary <=
      branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (23 : Fin 33)
  have hnextOutputCountSize : Nat.size next.outputCount <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (24 : Fin 33)
  have hmodeSize : Nat.size mode <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (25 : Fin 33)
  have htagSize : Nat.size tag <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (27 : Fin 33)
  have hargumentSize : Nat.size argument <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (28 : Fin 33)
  have hconsumedSize : Nat.size consumedCount <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (29 : Fin 33)
  have hwitnessCountSize : Nat.size witnessCount <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (32 : Fin 33)
  have hbranchBitPositive : 1 <= branchBitBound := by
    unfold branchBitBound termRowsAdditiveBitBound
    omega
  have hnumericSizeLarge : Nat.size numericBound <= branchBitBound :=
    hnumericSize.trans (by
      unfold branchBitBound termRowsAdditiveBitBound
      omega)
  let modeCertificate := shortNumeralLiteralEqCertificate mode 5
    (‘5’ : ValuationTerm)
    (termValue_arithmeticFive modeFiveResidualValuation) hmode
  let guardCertificate := residualGuardCertificate consumedCount tag argument
    witnessCount hguard
  let residualCertificate :=
    compactFormulaTransformTermResidualExistsCertificate tokenTable width
      tokenCount current next argument witnessCount residual hresidual hequality
      hrows
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction guardCertificate
      residualCertificate
  let middleCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := rawFormula) selectedCertificate
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
      (‘5’ : ValuationTerm)
      (termValue_arithmeticFive modeFiveResidualValuation) hmode
      branchBitBound hmodeSize
      (termRowsLiteral_closed (‘5’ : ValuationTerm)
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      (termRowsLiteralCode_le (‘5’ : ValuationTerm) branchBitBound
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have hguardResource :
      hybridFormulaStructuralPayloadBound guardCertificate <= guardResource :=
    residualGuardCertificate_structuralPayloadBound_le_fixed consumedCount tag
      argument witnessCount branchBitBound hguard hconsumedSize htagSize
      hargumentSize hwitnessCountSize
  have hresidualResource :
      hybridFormulaStructuralPayloadBound residualCertificate <=
        residualResource :=
    compactFormulaTransformTermResidualExistsCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next argument witnessCount residual
      numericBound branchBitBound hresidual hequality hrows
      hresidualExistsClosed hresidualExistsCode htableSize hwidthSize
      htokenCountSize hcurrentParserFinishSize hcurrentFinishSize
      hcurrentOutputCountSize hnextParserFinishSize hnextFinishSize
      hnextOutputBoundarySize hnextOutputCountSize hargumentSize
      hwitnessCountSize hbranchBitPositive hwidthBound htokenCountBound
      hnextOutputCountBound hnumericSizeLarge
  have hselectedResource :
      hybridFormulaStructuralPayloadBound selectedCertificate <=
        selectedResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral guardCertificate
      residualCertificate guardResource residualResource syntaxResource
      hguardResource hresidualResource facts.syntaxPositive hguardClosed
      hresidualExistsClosed hguardCode hresidualExistsCode hselectedCode
  have hmiddleResource :
      hybridFormulaStructuralPayloadBound middleCertificate <= middleResource :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral
      selectedCertificate selectedResource syntaxResource hselectedResource
      facts.syntaxPositive hselectedClosed hrawClosed hselectedCode hrawCode
      hmiddleCode
  have hinternalResource :
      hybridFormulaStructuralPayloadBound internalCertificate <=
        internalResource :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      middleCertificate middleResource syntaxResource hmiddleResource
      facts.syntaxPositive hcapturedClosed hmiddleClosed hcapturedCode
      hmiddleCode hinternalCode
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
    consumedCount witnessStart witnessFinish witnessCount modesResource
    branchBitBound hcount hconsumed modesCertificate hmodesResource
    henvironmentLarge
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (termRowsPositiveOuterCertificate tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount hcount hconsumed modesCertificate) <= _
  simpa only [termRowsModeFiveResidualFixedPayloadPolynomial, branchBitBound,
    syntaxResource, guardResource, residualResource, atomicResource,
    selectedResource, middleResource, internalResource, modeResource,
    modesResource] using houter

#print axioms
  compactFormulaTransformTermOutputRowsModeFiveResidualBranch_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFiveResidualFullyFixedBounds
