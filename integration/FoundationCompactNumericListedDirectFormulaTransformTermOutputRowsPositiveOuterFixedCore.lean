import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterSyntaxFacts
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedCore
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsNativeLeFixedBounds
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds

/-! # Common fixed outer assembly after the six-way mode choice -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 140000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPositiveOuterFixedCore

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOuterSyntaxFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterSyntaxFacts

def termRowsPositiveOuterFixedPayloadPolynomial
    (modesResource bitBound : Nat) : Nat :=
  let syntaxResource := termRowsOuterSyntaxPolynomial bitBound
  let positiveResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource (termRowsNativeLeFixedPayloadPolynomial bitBound)
    modesResource
  let casesResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    positiveResource
  hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termRowsPositiveAtomicFixedPayloadPolynomial bitBound) casesResource

noncomputable def termRowsPositiveOuterCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (modesCertificate : HybridCertificate
      (termRowsModesFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount)) :
    HybridCertificate
      (compactFormulaTransformTermOutputRowsExplicitFormula tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount) :=
  .conjunction
    (consumedCountEqualityCertificate current next consumedCount hcount)
    (.disjunctionRight
      (.conjunction (consumedCountPositiveCertificate consumedCount hconsumed)
        modesCertificate))

theorem termRowsPositiveOuterCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount modesResource bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (modesCertificate : HybridCertificate
      (termRowsModesFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount))
    (hmodesResource :
      hybridFormulaStructuralPayloadBound modesCertificate <= modesResource)
    (henvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (termRowsPositiveOuterCertificate tokenTable width tokenCount current
          next mode binderArity tag argument consumedCount witnessStart
          witnessFinish witnessCount hcount hconsumed modesCertificate) <=
      termRowsPositiveOuterFixedPayloadPolynomial modesResource bitBound := by
  let syntaxResource := termRowsOuterSyntaxPolynomial bitBound
  let countResource := termRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let positiveLeafResource := termRowsNativeLeFixedPayloadPolynomial bitBound
  let positiveResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource positiveLeafResource modesResource
  let casesResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    positiveResource
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let positiveCertificateFull :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      positiveCertificate modesCertificate
  let casesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := termRowsZeroCaseFormula tokenTable width tokenCount current next
        consumedCount) positiveCertificateFull
  let fullCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction countCertificate
      casesCertificate
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
  have hpositiveResource :
      hybridFormulaStructuralPayloadBound positiveCertificateFull <=
        positiveResource := by
    exact checkedHybridConjunctionPayloadBound_le_closedGeneral
      positiveCertificate modesCertificate positiveLeafResource modesResource
      syntaxResource hpositiveLeafResource hmodesResource facts.syntaxPositive
      facts.positiveGuardClosed facts.modesClosed facts.positiveGuardCode
      facts.modesCode (by
        simpa only [termRowsPositiveCaseFormula] using facts.positiveCode)
  have hcasesResource :
      hybridFormulaStructuralPayloadBound casesCertificate <= casesResource :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      positiveCertificateFull positiveResource syntaxResource
      hpositiveResource facts.syntaxPositive facts.zeroCaseClosed
      facts.positiveClosed facts.zeroCaseCode facts.positiveCode facts.casesCode
  have hfixed :
      hybridFormulaStructuralPayloadBound fullCertificate <=
        hybridConjunctionGeneralPayloadEnvelope syntaxResource countResource
          casesResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral countCertificate
      casesCertificate countResource casesResource syntaxResource
      hcountResource hcasesResource facts.syntaxPositive facts.countClosed
      facts.casesClosed facts.countCode facts.casesCode facts.fullCode
  change hybridFormulaStructuralPayloadBound fullCertificate <= _
  simpa only [termRowsPositiveOuterFixedPayloadPolynomial, syntaxResource,
    countResource, positiveLeafResource, positiveResource, casesResource]
    using hfixed

#print axioms termRowsPositiveOuterCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPositiveOuterFixedCore
