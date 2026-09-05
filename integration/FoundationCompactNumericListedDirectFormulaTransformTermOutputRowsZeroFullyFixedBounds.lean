import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterSyntaxFacts
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedCore
import integration.FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds

/-! # Fully fixed zero-consumption branch of term-output rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsZeroFullyFixedBounds

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
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOuterSyntaxFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterSyntaxFacts
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds

private abbrev zeroBranchValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsZeroFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource := termRowsOuterSyntaxPolynomial bitBound
  let zeroCaseResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termRowsPositiveAtomicFixedPayloadPolynomial bitBound)
    (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
  let casesResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    zeroCaseResource
  hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termRowsPositiveAtomicFixedPayloadPolynomial bitBound) casesResource

theorem
    compactFormulaTransformTermOutputRowsZeroBranch_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : consumedCount = 0)
    (hsame : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
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
          (.zero hcount hconsumed hsame)) <=
      termRowsZeroFixedPayloadPolynomial numericBound bitBound := by
  let syntaxResource := termRowsOuterSyntaxPolynomial bitBound
  let countFormula := termRowsCountFormula current next consumedCount
  let zeroFormula := nativeEqFormula (shortBinaryNumeralTerm consumedCount)
    (‘0’ : ValuationTerm)
  let sameFormula := termRowsSameFormula tokenTable width tokenCount current next
  let zeroCaseFormula := zeroFormula ⋏ sameFormula
  let positiveFormula := termRowsPositiveCaseFormula tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount
  let casesFormula := zeroCaseFormula ⋎ positiveFormula
  let countResource := termRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let zeroResource := termRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let sameResource := sameRowsCompleteFullyFixedPayloadPolynomial numericBound
    bitBound
  let zeroCaseResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    zeroResource sameResource
  let casesResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    zeroCaseResource
  have facts := termRowsModeZeroOuterSyntaxFacts tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount bitBound
    witnessStart witnessFinish witnessCount henvironmentSize
  have hzeroCaseAlignment :
      termRowsZeroCaseFormula tokenTable width tokenCount current next
        consumedCount = zeroCaseFormula := by
    rfl
  have hzeroCaseClosed : zeroCaseFormula.freeVariables = ∅ := by
    simpa only [hzeroCaseAlignment] using facts.zeroCaseClosed
  have hzeroCaseCode :
      (binaryFormulaCode zeroCaseFormula).length <= syntaxResource := by
    simpa only [hzeroCaseAlignment] using facts.zeroCaseCode
  have hzeroClosed := termRowsConjunction_left_closed zeroFormula sameFormula
    hzeroCaseClosed
  have hsameClosed := termRowsConjunction_right_closed zeroFormula sameFormula
    hzeroCaseClosed
  have hzeroCode :=
    (termRowsConjunction_left_code_le zeroFormula sameFormula).trans
      hzeroCaseCode
  have hsameCode :=
    (termRowsConjunction_right_code_le zeroFormula sameFormula).trans
      hzeroCaseCode
  have hcurrentParserTokensCountSize :
      Nat.size current.parserTokensCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (9 : Fin 33)
  have hcurrentOutputBoundarySize :
      Nat.size current.outputBoundary <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (12 : Fin 33)
  have hnextParserTokensCountSize :
      Nat.size next.parserTokensCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (20 : Fin 33)
  have hnextOutputBoundarySize : Nat.size next.outputBoundary <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (23 : Fin 33)
  have hconsumedSize : Nat.size consumedCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (29 : Fin 33)
  have htokenTableSize : Nat.size tokenTable <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (0 : Fin 33)
  let countCertificate := consumedCountEqualityCertificate current next
    consumedCount hcount
  let zeroCertificate := consumedCountZeroCertificate consumedCount hconsumed
  let sameCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hsame
  let zeroCaseCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction zeroCertificate
      sameCertificate
  let casesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := positiveFormula) zeroCaseCertificate
  let fullCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction countCertificate
      casesCertificate
  have hcountResource :
      hybridFormulaStructuralPayloadBound countCertificate <= countResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_fixed current
      next consumedCount bitBound hcount hcurrentParserTokensCountSize
      hconsumedSize hnextParserTokensCountSize
  have hzeroResource :
      hybridFormulaStructuralPayloadBound zeroCertificate <= zeroResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_fixed
      consumedCount 0 (‘0’ : ValuationTerm)
      (termValue_arithmeticZero zeroBranchValuation) hconsumed bitBound
      hconsumedSize
      (termRowsLiteral_closed (‘0’ : ValuationTerm) (Or.inl rfl))
      (termRowsLiteralCode_le (‘0’ : ValuationTerm) bitBound (Or.inl rfl))
  have hsameTransparent :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hsame
  have hsameFixed :=
    compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_fullyFixed tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount numericBound bitBound hsame
      hwidthBound htokenCountBound hcurrentOutputCountBound htokenTableSize
      hcurrentOutputBoundarySize hnextOutputBoundarySize hnumericSize
  have hsameResource :
      hybridFormulaStructuralPayloadBound sameCertificate <= sameResource :=
    hsameTransparent.trans hsameFixed
  have hzeroCaseResource :
      hybridFormulaStructuralPayloadBound zeroCaseCertificate <=
        zeroCaseResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral zeroCertificate
      sameCertificate zeroResource sameResource syntaxResource hzeroResource
      hsameResource facts.syntaxPositive hzeroClosed hsameClosed hzeroCode
      hsameCode hzeroCaseCode
  have hcasesResource :
      hybridFormulaStructuralPayloadBound casesCertificate <= casesResource :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral
      zeroCaseCertificate zeroCaseResource syntaxResource hzeroCaseResource
      facts.syntaxPositive hzeroCaseClosed facts.positiveClosed hzeroCaseCode
      facts.positiveCode facts.casesCode
  have hfullResource :
      hybridFormulaStructuralPayloadBound fullCertificate <=
        hybridConjunctionGeneralPayloadEnvelope syntaxResource countResource
          casesResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral countCertificate
      casesCertificate countResource casesResource syntaxResource
      hcountResource hcasesResource facts.syntaxPositive facts.countClosed
      facts.casesClosed facts.countCode facts.casesCode facts.fullCode
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound fullCertificate <= _
  simpa only [termRowsZeroFixedPayloadPolynomial, syntaxResource,
    countResource, zeroResource, sameResource, zeroCaseResource,
    casesResource] using hfullResource

#print axioms
  compactFormulaTransformTermOutputRowsZeroBranch_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsZeroFullyFixedBounds
