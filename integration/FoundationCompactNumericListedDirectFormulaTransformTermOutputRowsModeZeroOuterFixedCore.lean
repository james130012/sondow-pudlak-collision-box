import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterSyntaxFacts
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedCore
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsNativeLeFixedBounds
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds

/-! # Common fixed outer assembly for every selected mode-zero branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 160000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterFixedCore

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
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOuterSyntaxFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterSyntaxFacts

def termRowsModeZeroOuterFixedPayloadPolynomial
    (modeResource bitBound : Nat) : Nat :=
  let syntaxResource := termRowsOuterSyntaxPolynomial bitBound
  let modesResource :=
    sixRightDisjunctionPathZeroPayloadEnvelope syntaxResource modeResource
  let positiveResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (termRowsNativeLeFixedPayloadPolynomial bitBound) modesResource
  let casesResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource positiveResource
  hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termRowsPositiveAtomicFixedPayloadPolynomial bitBound) casesResource

noncomputable def termRowsModeZeroOuterCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (modeZeroCertificate : HybridCertificate
      (termRowsModeZeroFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount)) :
    HybridCertificate
      (compactFormulaTransformTermOutputRowsExplicitFormula tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount) :=
  .conjunction
    (consumedCountEqualityCertificate current next consumedCount hcount)
    (.disjunctionRight
      (.conjunction (consumedCountPositiveCertificate consumedCount hconsumed)
        (.disjunctionLeft modeZeroCertificate)))

theorem termRowsModeZeroOuterCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount modeResource bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (modeZeroCertificate : HybridCertificate
      (termRowsModeZeroFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount))
    (hmodeResource :
      hybridFormulaStructuralPayloadBound modeZeroCertificate <= modeResource)
    (henvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (termRowsModeZeroOuterCertificate tokenTable width tokenCount current
          next mode binderArity tag argument consumedCount witnessStart
          witnessFinish witnessCount hcount hconsumed modeZeroCertificate) <=
      termRowsModeZeroOuterFixedPayloadPolynomial modeResource bitBound := by
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
  let countFormula := termRowsCountFormula current next consumedCount
  let zeroCaseFormula := termRowsZeroCaseFormula tokenTable width tokenCount
    current next consumedCount
  let positiveFormula := termRowsPositiveCaseFormula tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount
  let casesFormula := termRowsCasesFormula tokenTable width tokenCount current
    next mode binderArity tag argument consumedCount witnessStart witnessFinish
    witnessCount
  let positiveGuardFormula := nativeLeFormula (‘1’ : ValuationTerm)
    (shortBinaryNumeralTerm consumedCount)
  let modesFormula := termRowsModesFormula tokenTable width tokenCount current
    next mode binderArity tag argument consumedCount witnessStart witnessFinish
    witnessCount
  let syntaxResource := termRowsOuterSyntaxPolynomial bitBound
  let countResource := termRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let positiveLeafResource := termRowsNativeLeFixedPayloadPolynomial bitBound
  let modesResource := sixRightDisjunctionPathZeroPayloadEnvelope
    syntaxResource modeResource
  let positiveResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource positiveLeafResource modesResource
  let casesResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    positiveResource
  have facts := termRowsModeZeroOuterSyntaxFacts tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount bitBound
    witnessStart witnessFinish witnessCount henvironmentSize
  have hcurrentParserTokensCountSize :
      Nat.size current.parserTokensCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (9 : Fin 33)
  have hnextParserTokensCountSize :
      Nat.size next.parserTokensCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (20 : Fin 33)
  have hconsumedSize : Nat.size consumedCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (29 : Fin 33)
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := modeOneFormula ⋎ (modeTwoFormula ⋎
        (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))))
      modeZeroCertificate
  let positiveCertificateFull :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      positiveCertificate modesCertificate
  let casesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := zeroCaseFormula) positiveCertificateFull
  let fullCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction countCertificate
      casesCertificate
  have hcountResource :
      hybridFormulaStructuralPayloadBound countCertificate <= countResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_fixed current
      next consumedCount bitBound hcount hcurrentParserTokensCountSize
      hconsumedSize hnextParserTokensCountSize
  have hpositiveLeafResource :
      hybridFormulaStructuralPayloadBound positiveCertificate <=
        positiveLeafResource :=
    consumedCountPositiveCertificate_structuralPayloadBound_le_fixed
      consumedCount bitBound hconsumed hconsumedSize
  have hmodesResource :
      hybridFormulaStructuralPayloadBound modesCertificate <= modesResource := by
    exact sixRightDisjunctionPathZeroPayloadBound_le_closedGeneral
      modeZeroFormula modeOneFormula modeTwoFormula modeFourFormula
      modeFiveFormula otherFormula modeZeroCertificate modeResource
      syntaxResource hmodeResource facts.syntaxPositive
      facts.modesDecomposedClosed facts.modesDecomposedCode
  have hpositiveResource :
      hybridFormulaStructuralPayloadBound positiveCertificateFull <=
        positiveResource := by
    exact checkedHybridConjunctionPayloadBound_le_closedGeneral
      positiveCertificate modesCertificate positiveLeafResource modesResource
      syntaxResource hpositiveLeafResource hmodesResource facts.syntaxPositive
      facts.positiveGuardClosed facts.modesClosed facts.positiveGuardCode
      facts.modesCode (by
        simpa only [positiveFormula, positiveGuardFormula, modesFormula,
          modeZeroFormula, modeOneFormula, modeTwoFormula, modeFourFormula,
          modeFiveFormula, otherFormula, termRowsPositiveCaseFormula,
          termRowsModesFormula] using facts.positiveCode)
  have hcasesResource :
      hybridFormulaStructuralPayloadBound casesCertificate <= casesResource := by
    exact checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      positiveCertificateFull positiveResource syntaxResource
      hpositiveResource facts.syntaxPositive facts.zeroCaseClosed
      facts.positiveClosed facts.zeroCaseCode facts.positiveCode facts.casesCode
  have hfixed :
      hybridFormulaStructuralPayloadBound fullCertificate <=
        hybridConjunctionGeneralPayloadEnvelope syntaxResource countResource
          casesResource := by
    exact checkedHybridConjunctionPayloadBound_le_closedGeneral countCertificate
      casesCertificate countResource casesResource syntaxResource
      hcountResource hcasesResource facts.syntaxPositive facts.countClosed
      facts.casesClosed facts.countCode facts.casesCode facts.fullCode
  change hybridFormulaStructuralPayloadBound fullCertificate <= _
  simpa only [termRowsModeZeroOuterFixedPayloadPolynomial, syntaxResource,
    countResource, positiveLeafResource, modesResource, positiveResource,
    casesResource] using hfixed

#print axioms termRowsModeZeroOuterCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterFixedCore
