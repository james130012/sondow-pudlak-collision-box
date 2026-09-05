import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPositiveOuterFixedCore
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsZeroOneGuardFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAppendOneValueFullyFixedBounds
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds

/-! # Fully fixed append-one branch under term-output mode four -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 250000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFourOneFullyFixedBounds

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
open FoundationCompactNumericListedDirectNatListAppendOneValue
open FoundationCompactNumericListedDirectNatListAppendOneValueExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendOneValueFullyFixedBounds

private abbrev modeFourOneValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsModeFourOneFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource := termRowsOuterSyntaxPolynomial bitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource (termRowsTwoGuardFixedPayloadPolynomial bitBound)
    (appendOneFullyFixedPayloadPolynomial numericBound bitBound)
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    selectedResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termRowsPositiveAtomicFixedPayloadPolynomial bitBound) internalResource
  let modesResource := sixRightDisjunctionPathThreePayloadEnvelope
    syntaxResource modeResource
  termRowsPositiveOuterFixedPayloadPolynomial modesResource bitBound

theorem
    compactFormulaTransformTermOutputRowsModeFourOneBranch_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 4)
    (hguard : consumedCount = 2 ∧ tag = 1)
    (hrows : CompactFormulaTransformOutputOneValueRows tokenTable width
      tokenCount current next argument)
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
          (.modeFourOne hcount hconsumed hmode hguard hrows)) <=
      termRowsModeFourOneFixedPayloadPolynomial numericBound bitBound := by
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
  let guardFormula := termRowsGuardOneTagFormula consumedCount tag
  let rowsFormula := termRowsOneValueFormula tokenTable width tokenCount current
    next argument
  let selectedFormula := guardFormula ⋏ rowsFormula
  let rawFormula := doubleFailureFormula
      (shortBinaryNumeralTerm consumedCount) (shortBinaryNumeralTerm tag) ⋏
    termRowsSameFormula tokenTable width tokenCount current next
  let internalFormula := selectedFormula ⋎ rawFormula
  let guardResource := termRowsTwoGuardFixedPayloadPolynomial bitBound
  let rowsResource := appendOneFullyFixedPayloadPolynomial numericBound bitBound
  let atomicResource := termRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource guardResource rowsResource
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    selectedResource
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
      selectedFormula, guardFormula, rowsFormula, rawFormula]
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
  have htableSize : Nat.size tokenTable <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (0 : Fin 33)
  have hwidthSize : Nat.size width <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (1 : Fin 33)
  have htokenCountSize : Nat.size tokenCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (2 : Fin 33)
  have hcurrentFinishSize : Nat.size current.finish <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (4 : Fin 33)
  have hcurrentParserFinishSize : Nat.size current.parserFinish <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (5 : Fin 33)
  have hcurrentOutputCountSize : Nat.size current.outputCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (13 : Fin 33)
  have hnextFinishSize : Nat.size next.finish <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (15 : Fin 33)
  have hnextParserFinishSize : Nat.size next.parserFinish <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (16 : Fin 33)
  have hnextOutputBoundarySize : Nat.size next.outputBoundary <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (23 : Fin 33)
  have hnextOutputCountSize : Nat.size next.outputCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (24 : Fin 33)
  have hmodeSize : Nat.size mode <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (25 : Fin 33)
  have htagSize : Nat.size tag <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (27 : Fin 33)
  have hargumentSize : Nat.size argument <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (28 : Fin 33)
  have hconsumedSize : Nat.size consumedCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (29 : Fin 33)
  let modeCertificate := shortNumeralLiteralEqCertificate mode 4
    (‘4’ : ValuationTerm) (termValue_arithmeticFour modeFourOneValuation) hmode
  let guardCertificate := oneTagGuardCertificate consumedCount tag hguard
  let rowsCertificate :=
    compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount argument hrows
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction guardCertificate
      rowsCertificate
  let internalCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := rawFormula) selectedCertificate
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
      (‘4’ : ValuationTerm) (termValue_arithmeticFour modeFourOneValuation)
      hmode bitBound hmodeSize
      (termRowsLiteral_closed (‘4’ : ValuationTerm)
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (termRowsLiteralCode_le (‘4’ : ValuationTerm) bitBound
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hguardResource :
      hybridFormulaStructuralPayloadBound guardCertificate <= guardResource :=
    oneTagGuardCertificate_structuralPayloadBound_le_fixed consumedCount tag
      bitBound hguard hconsumedSize htagSize
  have hrowsResource :
      hybridFormulaStructuralPayloadBound rowsCertificate <= rowsResource :=
    compactAdditiveNatListAppendOneValueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount argument numericBound bitBound hrows htableSize
      hwidthSize htokenCountSize hcurrentParserFinishSize hcurrentFinishSize
      hcurrentOutputCountSize hnextParserFinishSize hnextFinishSize
      hnextOutputBoundarySize hnextOutputCountSize hargumentSize hwidthBound
      htokenCountBound hnextOutputCountBound hnumericSize
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
      facts.syntaxPositive hselectedClosed hrawClosed hselectedCode hrawCode
      hinternalCode
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
  simpa only [termRowsModeFourOneFixedPayloadPolynomial, syntaxResource,
    guardResource, rowsResource, atomicResource, selectedResource,
    internalResource, modeResource, modesResource] using houter

#print axioms
  compactFormulaTransformTermOutputRowsModeFourOneBranch_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFourOneFullyFixedBounds
