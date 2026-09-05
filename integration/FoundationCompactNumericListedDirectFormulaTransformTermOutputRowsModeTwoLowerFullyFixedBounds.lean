import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPositiveOuterFixedCore
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsZeroOneGuardFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedCertificate
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds

/-! # Fully fixed witness-slices branch under term-output mode two -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 220000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeTwoLowerFullyFixedBounds

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
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedPolynomial
open FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedCertificate

private abbrev modeTwoLowerValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsModeTwoLowerFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource := termRowsOuterSyntaxPolynomial bitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource (termRowsThreeGuardFixedPayloadPolynomial bitBound)
    (appendSlicesFullyFixedPayloadPolynomial numericBound bitBound)
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope
    syntaxResource selectedResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termRowsPositiveAtomicFixedPayloadPolynomial bitBound) internalResource
  let modesResource := sixRightDisjunctionPathTwoPayloadEnvelope syntaxResource
    modeResource
  termRowsPositiveOuterFixedPayloadPolynomial modesResource bitBound

theorem
    compactFormulaTransformTermOutputRowsModeTwoLowerBranch_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 2)
    (hguard : consumedCount = 2 ∧ tag = 0 ∧
      argument + 1 = binderArity)
    (hrows : CompactFormulaTransformOutputWitnessRows tokenTable width
      tokenCount current next witnessStart witnessFinish witnessCount)
    (henvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hwitnessCountBound : witnessCount <= numericBound)
    (hnextOutputCountBound : next.outputCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.modeTwoLower hcount hconsumed hmode hguard hrows)) <=
      termRowsModeTwoLowerFixedPayloadPolynomial numericBound bitBound := by
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
  let guardFormula := termRowsGuardZeroTagFormula consumedCount tag argument
    binderArity
  let rowsFormula := termRowsWitnessFormula tokenTable width tokenCount current
    next witnessStart witnessFinish witnessCount
  let selectedFormula := guardFormula ⋏ rowsFormula
  let rawFormula := tripleFailureFormula
      (shortBinaryNumeralTerm consumedCount) (shortBinaryNumeralTerm tag)
      (shortBinaryNumeralTerm argument) (shortBinaryNumeralTerm binderArity) ⋏
    termRowsRawPrefixFormula tokenTable width tokenCount current next
      consumedCount
  let internalFormula := selectedFormula ⋎ rawFormula
  let guardResource := termRowsThreeGuardFixedPayloadPolynomial bitBound
  let rowsResource := appendSlicesFullyFixedPayloadPolynomial numericBound
    bitBound
  let atomicResource := termRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource guardResource rowsResource
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope
    syntaxResource selectedResource
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
      selectedFormula, guardFormula, rowsFormula, rawFormula]
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
    (‘2’ : ValuationTerm) (termValue_arithmeticTwo modeTwoLowerValuation) hmode
  let guardCertificate := zeroTagGuardCertificate consumedCount tag argument
    binderArity hguard
  let rowsCertificate :=
    compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount witnessStart witnessFinish witnessCount
      next.parserFinish next.finish next.outputCount hrows
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction guardCertificate
      rowsCertificate
  let internalCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := rawFormula) selectedCertificate
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
      (‘2’ : ValuationTerm) (termValue_arithmeticTwo modeTwoLowerValuation)
      hmode bitBound hmodeSize
      (termRowsLiteral_closed (‘2’ : ValuationTerm)
        (Or.inr (Or.inr (Or.inl rfl))))
      (termRowsLiteralCode_le (‘2’ : ValuationTerm) bitBound
        (Or.inr (Or.inr (Or.inl rfl))))
  have hguardResource :
      hybridFormulaStructuralPayloadBound guardCertificate <= guardResource :=
    zeroTagGuardCertificate_structuralPayloadBound_le_fixed consumedCount tag
      argument binderArity bitBound hguard hconsumedSize htagSize
      hargumentSize hbinderAritySize
  have hrowsResource :
      hybridFormulaStructuralPayloadBound rowsCertificate <= rowsResource :=
    compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fixed
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount witnessStart witnessFinish witnessCount
      next.parserFinish next.finish next.outputCount numericBound bitBound hrows
      htableSize hwidthBound htokenCountBound hwitnessCountBound
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
      facts.syntaxPositive hselectedClosed hrawClosed hselectedCode hrawCode
      hinternalCode
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
  simpa only [termRowsModeTwoLowerFixedPayloadPolynomial, syntaxResource,
    guardResource, rowsResource, atomicResource, selectedResource,
    internalResource, modeResource, modesResource] using houter

#print axioms
  compactFormulaTransformTermOutputRowsModeTwoLowerBranch_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeTwoLowerFullyFixedBounds
