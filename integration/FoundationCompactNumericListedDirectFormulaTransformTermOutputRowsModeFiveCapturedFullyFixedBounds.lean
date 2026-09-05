import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPositiveOuterFixedCore
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsComparisonGuardFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAppendCapturedFullyFixedBounds
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds

/-! # Fully fixed captured-variable branch under term-output mode five -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 230000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFiveCapturedFullyFixedBounds

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
open FoundationCompactNumericListedDirectNatListAppendTwoValuesFullyFixedBounds

private abbrev modeFiveCapturedValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsModeFiveCapturedFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let branchBitBound := termRowsAdditiveBitBound bitBound
  let syntaxResource := termRowsOuterSyntaxPolynomial branchBitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource (termRowsThreeGuardFixedPayloadPolynomial branchBitBound)
    (appendTwoFullyFixedPayloadPolynomial numericBound branchBitBound)
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope
    syntaxResource selectedResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termRowsPositiveAtomicFixedPayloadPolynomial branchBitBound)
    internalResource
  let modesResource := sixRightDisjunctionPathFourPayloadEnvelope syntaxResource
    modeResource
  termRowsPositiveOuterFixedPayloadPolynomial modesResource branchBitBound

theorem
    compactFormulaTransformTermOutputRowsModeFiveCapturedBranch_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 5)
    (hguard : consumedCount = 2 ∧ tag = 1 ∧ argument < witnessCount)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 0 (binderArity + argument))
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
          (.modeFiveCaptured hcount hconsumed hmode hguard hrows)) <=
      termRowsModeFiveCapturedFixedPayloadPolynomial numericBound bitBound := by
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
  let guardFormula := termRowsCapturedGuardFormula consumedCount tag argument
    witnessCount
  let rowsFormula := termRowsCapturedFormula tokenTable width tokenCount current
    next binderArity argument
  let selectedFormula := guardFormula ⋏ rowsFormula
  let residualFormula :=
    termRowsResidualGuardFormula consumedCount tag argument witnessCount ⋏
      compactFormulaTransformTermResidualExistsFormula tokenTable width
        tokenCount current next argument witnessCount
  let rawFormula := doubleFailureFormula
      (shortBinaryNumeralTerm consumedCount) (shortBinaryNumeralTerm tag) ⋏
    termRowsRawPrefixFormula tokenTable width tokenCount current next
      consumedCount
  let middleFormula := residualFormula ⋎ rawFormula
  let internalFormula := selectedFormula ⋎ middleFormula
  let guardResource := termRowsThreeGuardFixedPayloadPolynomial branchBitBound
  let rowsResource := appendTwoFullyFixedPayloadPolynomial numericBound
    branchBitBound
  let atomicResource := termRowsPositiveAtomicFixedPayloadPolynomial
    branchBitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource guardResource rowsResource
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope
    syntaxResource selectedResource
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
      selectedFormula, guardFormula, rowsFormula, middleFormula,
      residualFormula, rawFormula]
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
  have hselectedClosed := termRowsDisjunction_left_closed selectedFormula
    middleFormula hinternalClosed
  have hmiddleClosed := termRowsDisjunction_right_closed selectedFormula
    middleFormula hinternalClosed
  have hselectedCode :=
    (termRowsDisjunction_left_code_le selectedFormula middleFormula).trans
      hinternalCode
  have hmiddleCode :=
    (termRowsDisjunction_right_code_le selectedFormula middleFormula).trans
      hinternalCode
  have hguardClosed := termRowsConjunction_left_closed guardFormula rowsFormula
    hselectedClosed
  have hrowsClosed := termRowsConjunction_right_closed guardFormula rowsFormula
    hselectedClosed
  have hguardCode :=
    (termRowsConjunction_left_code_le guardFormula rowsFormula).trans
      hselectedCode
  have hrowsCode :=
    (termRowsConjunction_right_code_le guardFormula rowsFormula).trans
      hselectedCode
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
  let modeCertificate := shortNumeralLiteralEqCertificate mode 5
    (‘5’ : ValuationTerm)
    (termValue_arithmeticFive modeFiveCapturedValuation) hmode
  let guardCertificate := capturedGuardCertificate consumedCount tag argument
    witnessCount hguard
  let capturedTerm := nativeAddTerm (shortBinaryNumeralTerm binderArity)
    (shortBinaryNumeralTerm argument)
  let rowsCertificate :=
    FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 0 (binderArity + argument) (‘0’ : ValuationTerm)
      capturedTerm (termValue_arithmeticZero modeFiveCapturedValuation)
      (by
        simp [capturedTerm, nativeAddTerm, termValue_arithmeticAdd,
          termValue_shortBinaryNumeralTerm]) hrows
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction guardCertificate
      rowsCertificate
  let internalCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := middleFormula) selectedCertificate
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
      (termValue_arithmeticFive modeFiveCapturedValuation) hmode
      branchBitBound hmodeSize
      (termRowsLiteral_closed (‘5’ : ValuationTerm)
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      (termRowsLiteralCode_le (‘5’ : ValuationTerm) branchBitBound
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have hguardResource :
      hybridFormulaStructuralPayloadBound guardCertificate <= guardResource :=
    capturedGuardCertificate_structuralPayloadBound_le_fixed consumedCount tag
      argument witnessCount branchBitBound hguard hconsumedSize htagSize
      hargumentSize hwitnessCountSize
  have hrowsResource :
      hybridFormulaStructuralPayloadBound rowsCertificate <= rowsResource := by
    exact termRowsAppendTwoCapturedCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount numericBound bitBound
      hrows henvironmentSize hwidthBound htokenCountBound
      hnextOutputCountBound hnumericSize
  have hselectedResource :
      hybridFormulaStructuralPayloadBound selectedCertificate <=
        selectedResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral guardCertificate
      rowsCertificate guardResource rowsResource syntaxResource hguardResource
      hrowsResource facts.syntaxPositive hguardClosed hrowsClosed hguardCode
      hrowsCode hselectedCode
  have hinternalResource :
      hybridFormulaStructuralPayloadBound internalCertificate <=
        internalResource :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral
      selectedCertificate selectedResource syntaxResource hselectedResource
      facts.syntaxPositive hselectedClosed hmiddleClosed hselectedCode
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
  simpa only [termRowsModeFiveCapturedFixedPayloadPolynomial, branchBitBound,
    syntaxResource, guardResource, rowsResource, atomicResource,
    selectedResource, internalResource, modeResource, modesResource] using
      houter

#print axioms
  compactFormulaTransformTermOutputRowsModeFiveCapturedBranch_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFiveCapturedFullyFixedBounds
