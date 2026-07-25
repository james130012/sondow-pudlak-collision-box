import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsPublicBounds
import integration.FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixFullyFixedBounds
import integration.FoundationCompactNumericListedDirectNegationFormulaTagFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsFormulaFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAtomicFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsOtherModeFixedBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactPAHybridDisjunctionGeneralContextBounds

/-!
# Mapped output-row branch with fully fixed row and tag resources

Both the negation-tag certificate and the mapped source-prefix rows, including
their indexed head lookup, are charged by fully fixed checked-certificate
theorems rather than legacy graph envelopes.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsMappedRowsFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRows
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsFormulaFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAtomicFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsOtherModeFixedBounds
open FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate
open FoundationCompactNumericListedDirectNegationFormulaTagPublicBounds
open FoundationCompactNumericListedDirectNegationFormulaTagBranchAssemblyFixedBounds
open FoundationCompactNumericListedDirectNegationFormulaTagFullyFixedBounds
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefix
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixFullyFixedBounds

def outputRowsMappedOuterSyntaxPolynomial (bitBound : Nat) : Nat :=
  compactFormulaTransformFormulaOutputRowsFullFormulaCodePolynomial bitBound + 1

def outputRowsMappedTailFixedPayloadPolynomial
    (currentOutputCount numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (outputRowsMappedOuterSyntaxPolynomial bitBound)
    (negationFormulaTagFullyFixedPayloadPolynomial bitBound)
    (appendMappedSourcePrefixFullyFixedPayloadPolynomial currentOutputCount
      numericBound bitBound)

def outputRowsMappedCaseFixedPayloadPolynomial
    (currentOutputCount numericBound bitBound : Nat) : Nat :=
  outputRowsOtherModeFixedPayloadPolynomial
    (outputRowsMappedOuterSyntaxPolynomial bitBound) bitBound
    (outputRowsMappedTailFixedPayloadPolynomial currentOutputCount numericBound
      bitBound)

def outputRowsMappedSelectedFixedPayloadPolynomial
    (currentOutputCount numericBound bitBound : Nat) : Nat :=
  let syntaxResource := outputRowsMappedOuterSyntaxPolynomial bitBound
  let mappedResource := outputRowsMappedCaseFixedPayloadPolynomial
    currentOutputCount numericBound bitBound
  let sameMappedResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource mappedResource
  let positiveBodyResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource sameMappedResource
  let positiveResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (outputRowsNativeLeFixedPayloadPolynomial bitBound)
      positiveBodyResource
  let casesResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource positiveResource
  hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound) casesResource

theorem binaryFormulaCode_and_left_le_outputRows
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

theorem binaryFormulaCode_and_right_le_outputRows
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

theorem binaryFormulaCode_or_left_le_outputRows
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp [binaryFormulaCode]
  omega

theorem binaryFormulaCode_or_right_le_outputRows
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp [binaryFormulaCode]
  omega

theorem conjunction_left_closed_outputRows
    (left right : ValuationFormula)
    (hclosed : (left ⋏ right).freeVariables = ∅) :
    left.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).1

theorem conjunction_right_closed_outputRows
    (left right : ValuationFormula)
    (hclosed : (left ⋏ right).freeVariables = ∅) :
    right.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).2

theorem disjunction_left_closed_outputRows
    (left right : ValuationFormula)
    (hclosed : (left ⋎ right).freeVariables = ∅) :
    left.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_or] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).1

theorem disjunction_right_closed_outputRows
    (left right : ValuationFormula)
    (hclosed : (left ⋎ right).freeVariables = ∅) :
    right.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_or] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).2

theorem transparentHybridDisjunctionLeftPayloadEnvelope_le_closedGeneral_outputRows
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (leftResource syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryFormulaCode left).length <= syntaxResource)
    (hrightCode : (binaryFormulaCode right).length <= syntaxResource)
    (hdisjunctionCode :
      (binaryFormulaCode (left ⋎ right)).length <= syntaxResource) :
    transparentHybridDisjunctionLeftPayloadEnvelope valuation left right
        leftResource <=
      hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        leftResource := by
  have hclosed : (left ⋎ right).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_or, hleftClosed, hrightClosed]
    simp
  have hcontext : formulaCodeSum
      (valuationContext (left ⋎ right).freeVariables valuation) <=
        syntaxResource := by
    rw [hclosed]
    simp [valuationContext, formulaCodeSum]
  exact transparentHybridDisjunctionLeftPayloadEnvelope_le_general valuation
    left right leftResource syntaxResource hpositive hcontext hleftCode
    hrightCode hdisjunctionCode

theorem transparentHybridDisjunctionRightPayloadEnvelope_le_closedGeneral_outputRows
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (rightResource syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryFormulaCode left).length <= syntaxResource)
    (hrightCode : (binaryFormulaCode right).length <= syntaxResource)
    (hdisjunctionCode :
      (binaryFormulaCode (left ⋎ right)).length <= syntaxResource) :
    transparentHybridDisjunctionRightPayloadEnvelope valuation left right
        rightResource <=
      hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        rightResource := by
  have hclosed : (left ⋎ right).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_or, hleftClosed, hrightClosed]
    simp
  have hcontext : formulaCodeSum
      (valuationContext (left ⋎ right).freeVariables valuation) <=
        syntaxResource := by
    rw [hclosed]
    simp [valuationContext, formulaCodeSum]
  exact transparentHybridDisjunctionRightPayloadEnvelope_le_general valuation
    left right rightResource syntaxResource hpositive hcontext hleftCode
    hrightCode hdisjunctionCode

theorem
    compactFormulaTransformFormulaOutputRowsMappedBranchCertificate_structuralPayloadBound_le_rowsFullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmodeZero : mode ≠ 0)
    (hmodeOne : mode ≠ 1)
    (hmodeTwo : mode ≠ 2)
    (hmodeFour : mode ≠ 4)
    (hmodeFive : mode ≠ 5)
    (htag : CompactNegationFormulaTagGraph tag mappedHead)
    (hrows : CompactFormulaTransformOutputMappedPrefixRows tokenTable width
      tokenCount current next consumedCount mappedHead)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentParserFinishSize : Nat.size current.parserFinish <= bitBound)
    (hcurrentFinishSize : Nat.size current.finish <= bitBound)
    (hcurrentOutputCountSize : Nat.size current.outputCount <= bitBound)
    (hcurrentStartSize : Nat.size current.start <= bitBound)
    (hcurrentParserTokensFinishSize :
      Nat.size current.parserTokensFinish <= bitBound)
    (hcurrentParserTokensCountSize :
      Nat.size current.parserTokensCount <= bitBound)
    (hconsumedCountSize : Nat.size consumedCount <= bitBound)
    (hnextParserFinishSize : Nat.size next.parserFinish <= bitBound)
    (hnextFinishSize : Nat.size next.finish <= bitBound)
    (hnextOutputBoundarySize : Nat.size next.outputBoundary <= bitBound)
    (hnextOutputCountSize : Nat.size next.outputCount <= bitBound)
    (htagSize : Nat.size tag <= bitBound)
    (hmappedHeadSize : Nat.size mappedHead <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead
          (.mapped hcount hconsumed hmodeZero hmodeOne hmodeTwo hmodeFour
            hmodeFive htag hrows)) <=
      outputRowsMappedSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode tag consumedCount mappedHead
        (negationFormulaTagFullyFixedPayloadPolynomial bitBound)
        (appendMappedSourcePrefixFullyFixedPayloadPolynomial
          current.outputCount numericBound bitBound) := by
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let tagCertificate :=
    compactNegationFormulaTagExplicitHybridCertificateOfGraph
      tag mappedHead htag
  let rowsCertificate :=
    compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputBoundary next.outputCount mappedHead hrows
  let mappedTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tagCertificate rowsCertificate
  let mappedCertificate := otherModeWithTailCertificate mode hmodeZero
    hmodeOne hmodeTwo hmodeFour hmodeFive
    (compactNegationFormulaTagClosedFormula tag mappedHead ⋏
      compactAdditiveNatListAppendMappedSourcePrefixClosedFormula tokenTable
        width tokenCount current.parserFinish current.finish
        current.outputCount current.start current.parserTokensFinish
        current.parserTokensCount consumedCount next.parserFinish next.finish
        next.outputBoundary next.outputCount mappedHead) mappedTail
  let rowsResource :=
    appendMappedSourcePrefixFullyFixedPayloadPolynomial current.outputCount
      numericBound bitBound
  let tagResource :=
    negationFormulaTagFullyFixedPayloadPolynomial bitBound
  have hcountResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
      current next consumedCount hcount
  have hpositiveResource :=
    consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
      consumedCount hconsumed
  have htagResource :=
    compactNegationFormulaTagExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tag mappedHead bitBound htag htagSize hmappedHeadSize
  have hrowsResource :
      hybridFormulaStructuralPayloadBound rowsCertificate <= rowsResource := by
    simpa only [rowsCertificate, rowsResource] using
      compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current.parserFinish current.finish
        current.outputCount current.start current.parserTokensFinish
        current.parserTokensCount consumedCount next.parserFinish next.finish
        next.outputBoundary next.outputCount mappedHead numericBound bitBound
        hrows htableSize hwidthSize htokenCountSize hcurrentParserFinishSize
        hcurrentFinishSize hcurrentOutputCountSize hcurrentStartSize
        hcurrentParserTokensFinishSize hcurrentParserTokensCountSize
        hconsumedCountSize hnextParserFinishSize hnextFinishSize
        hnextOutputBoundarySize hnextOutputCountSize hmappedHeadSize hwidthBound
        htokenCountBound hnumericSize
  have hmappedTail := transparentHybridConjunctionPayloadBound_le
    tagCertificate rowsCertificate tagResource rowsResource htagResource
    hrowsResource
  have hmappedResource :=
    otherModeWithTailCertificate_structuralPayloadBound_le_transparent
      mode hmodeZero hmodeOne hmodeTwo hmodeFour hmodeFive
      (compactNegationFormulaTagClosedFormula tag mappedHead ⋏
        compactAdditiveNatListAppendMappedSourcePrefixClosedFormula tokenTable
          width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputBoundary next.outputCount mappedHead) mappedTail
      (transparentHybridConjunctionPayloadEnvelope
        FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
        (compactNegationFormulaTagClosedFormula tag mappedHead)
        (compactAdditiveNatListAppendMappedSourcePrefixClosedFormula tokenTable
          width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputBoundary next.outputCount mappedHead)
        tagResource rowsResource)
      hmappedTail
  have hselected :=
    outputRowsMappedSelectedCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode tag consumedCount
      mappedHead countCertificate positiveCertificate mappedCertificate
      tagResource rowsResource hcountResource hpositiveResource
      hmappedResource
  change
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          countCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := outputRowsZeroCaseFormula tokenTable width tokenCount
              current next consumedCount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              positiveCertificate
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left := outputRowsRawCaseFormula tokenTable width tokenCount
                  current next mode consumedCount)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                  (left := outputRowsSameFourCaseFormula tokenTable width
                    tokenCount current next mode) mappedCertificate))))) <=
      outputRowsMappedSelectedPayloadEnvelope tokenTable width tokenCount
        current next mode tag consumedCount mappedHead tagResource rowsResource
  exact hselected

theorem
    compactFormulaTransformFormulaOutputRowsMappedBranchCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmodeZero : mode ≠ 0)
    (hmodeOne : mode ≠ 1)
    (hmodeTwo : mode ≠ 2)
    (hmodeFour : mode ≠ 4)
    (hmodeFive : mode ≠ 5)
    (htag : CompactNegationFormulaTagGraph tag mappedHead)
    (hrows : CompactFormulaTransformOutputMappedPrefixRows tokenTable width
      tokenCount current next consumedCount mappedHead)
    (henvironmentSize : ∀ coordinate,
      Nat.size
        (compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
          tokenCount current next mode tag consumedCount mappedHead
          coordinate) <= bitBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentParserFinishSize : Nat.size current.parserFinish <= bitBound)
    (hcurrentFinishSize : Nat.size current.finish <= bitBound)
    (hcurrentOutputCountSize : Nat.size current.outputCount <= bitBound)
    (hcurrentStartSize : Nat.size current.start <= bitBound)
    (hcurrentParserTokensFinishSize :
      Nat.size current.parserTokensFinish <= bitBound)
    (hcurrentParserTokensCountSize :
      Nat.size current.parserTokensCount <= bitBound)
    (hconsumedCountSize : Nat.size consumedCount <= bitBound)
    (hnextParserFinishSize : Nat.size next.parserFinish <= bitBound)
    (hnextFinishSize : Nat.size next.finish <= bitBound)
    (hnextOutputBoundarySize : Nat.size next.outputBoundary <= bitBound)
    (hnextOutputCountSize : Nat.size next.outputCount <= bitBound)
    (htagSize : Nat.size tag <= bitBound)
    (hmappedHeadSize : Nat.size mappedHead <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead
          (.mapped hcount hconsumed hmodeZero hmodeOne hmodeTwo hmodeFour
            hmodeFive htag hrows)) <=
      outputRowsMappedSelectedFixedPayloadPolynomial current.outputCount
        numericBound bitBound := by
  let countFormula :=
    outputRowsCountFormula current next consumedCount
  let zeroFormula :=
    outputRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount
  let positiveGuard :=
    nativeLeFormula (‘1’ : ValuationTerm)
      (shortBinaryNumeralTerm consumedCount)
  let rawFormula :=
    outputRowsRawCaseFormula tokenTable width tokenCount current next mode
      consumedCount
  let sameFormula :=
    outputRowsSameFourCaseFormula tokenTable width tokenCount current next mode
  let tagFormula := compactNegationFormulaTagClosedFormula tag mappedHead
  let rowsFormula :=
    compactAdditiveNatListAppendMappedSourcePrefixClosedFormula tokenTable width
      tokenCount current.parserFinish current.finish current.outputCount
      current.start current.parserTokensFinish current.parserTokensCount
      consumedCount next.parserFinish next.finish next.outputBoundary
      next.outputCount mappedHead
  let tailFormula := tagFormula ⋏ rowsFormula
  let mappedFormula :=
    outputRowsMappedCaseFormula tokenTable width tokenCount current next mode
      tag consumedCount mappedHead
  let sameMappedFormula := sameFormula ⋎ mappedFormula
  let positiveBodyFormula := rawFormula ⋎ sameMappedFormula
  let positiveFormula := positiveGuard ⋏ positiveBodyFormula
  let casesFormula := zeroFormula ⋎ positiveFormula
  let fullFormula := countFormula ⋏ casesFormula
  let syntaxResource := outputRowsMappedOuterSyntaxPolynomial bitBound
  let countResource :=
    outputRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let positiveGuardResource :=
    outputRowsNativeLeFixedPayloadPolynomial bitBound
  let tagResource := negationFormulaTagFullyFixedPayloadPolynomial bitBound
  let rowsResource :=
    appendMappedSourcePrefixFullyFixedPayloadPolynomial current.outputCount
      numericBound bitBound
  let tailResource :=
    outputRowsMappedTailFixedPayloadPolynomial current.outputCount numericBound
      bitBound
  let mappedResource :=
    outputRowsMappedCaseFixedPayloadPolynomial current.outputCount numericBound
      bitBound
  let sameMappedResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource mappedResource
  let positiveBodyResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource sameMappedResource
  let positiveResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      positiveGuardResource positiveBodyResource
  let casesResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource positiveResource
  have hfullAlignment :
      fullFormula =
        compactFormulaTransformFormulaOutputRowsExplicitFormula tokenTable width
          tokenCount current next mode tag consumedCount mappedHead := by
    dsimp only [fullFormula, casesFormula, positiveFormula,
      positiveBodyFormula, sameMappedFormula, mappedFormula, tailFormula,
      rowsFormula, tagFormula, sameFormula, rawFormula, positiveGuard,
      zeroFormula, countFormula]
    unfold outputRowsCountFormula outputRowsZeroCaseFormula
      outputRowsRawCaseFormula outputRowsSameFourCaseFormula
      outputRowsMappedCaseFormula outputRowsMappedTailFormula
      compactFormulaTransformFormulaOutputRowsExplicitFormula
    rfl
  have hfullClosed : fullFormula.freeVariables = ∅ := by
    rw [hfullAlignment,
      ← compactFormulaTransformFormulaOutputRowsClosedFormula_alignment]
    exact compactFormulaTransformFormulaOutputRowsClosedFormula_closed
      tokenTable width tokenCount current next mode tag consumedCount mappedHead
  have hfullCode :
      (binaryFormulaCode fullFormula).length <= syntaxResource := by
    have hraw :=
      compactFormulaTransformFormulaOutputRowsClosedFormula_code_length_le_fixed
        tokenTable width tokenCount current next mode tag consumedCount
        mappedHead bitBound henvironmentSize
    rw [hfullAlignment,
      ← compactFormulaTransformFormulaOutputRowsClosedFormula_alignment]
    dsimp only [syntaxResource]
    unfold outputRowsMappedOuterSyntaxPolynomial
    omega
  have hsyntaxPositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold outputRowsMappedOuterSyntaxPolynomial
    omega
  have hcountClosed :=
    conjunction_left_closed_outputRows countFormula casesFormula hfullClosed
  have hcasesClosed :=
    conjunction_right_closed_outputRows countFormula casesFormula hfullClosed
  have hzeroClosed :=
    disjunction_left_closed_outputRows zeroFormula positiveFormula hcasesClosed
  have hpositiveClosed :=
    disjunction_right_closed_outputRows zeroFormula positiveFormula hcasesClosed
  have hguardClosed :=
    conjunction_left_closed_outputRows positiveGuard positiveBodyFormula
      hpositiveClosed
  have hpositiveBodyClosed :=
    conjunction_right_closed_outputRows positiveGuard positiveBodyFormula
      hpositiveClosed
  have hrawClosed :=
    disjunction_left_closed_outputRows rawFormula sameMappedFormula
      hpositiveBodyClosed
  have hsameMappedClosed :=
    disjunction_right_closed_outputRows rawFormula sameMappedFormula
      hpositiveBodyClosed
  have hsameClosed :=
    disjunction_left_closed_outputRows sameFormula mappedFormula
      hsameMappedClosed
  have hmappedClosed :=
    disjunction_right_closed_outputRows sameFormula mappedFormula
      hsameMappedClosed
  have hmappedAlignment :
      mappedFormula =
        otherModeWithTailFormula (shortBinaryNumeralTerm mode) tailFormula := by
    rfl
  have htailClosed : tailFormula.freeVariables = ∅ := by
    rw [hmappedAlignment] at hmappedClosed
    unfold otherModeWithTailFormula at hmappedClosed
    exact conjunction_right_closed_outputRows _ tailFormula
      (conjunction_right_closed_outputRows _ _
        (conjunction_right_closed_outputRows _ _
          (conjunction_right_closed_outputRows _ _
            (conjunction_right_closed_outputRows _ _ hmappedClosed))))
  have htagClosed :=
    conjunction_left_closed_outputRows tagFormula rowsFormula htailClosed
  have hrowsClosed :=
    conjunction_right_closed_outputRows tagFormula rowsFormula htailClosed
  have hcountCode :=
    (binaryFormulaCode_and_left_le_outputRows countFormula casesFormula).trans
      hfullCode
  have hcasesCode :=
    (binaryFormulaCode_and_right_le_outputRows countFormula casesFormula).trans
      hfullCode
  have hzeroCode :=
    (binaryFormulaCode_or_left_le_outputRows zeroFormula positiveFormula).trans
      hcasesCode
  have hpositiveCode :=
    (binaryFormulaCode_or_right_le_outputRows zeroFormula positiveFormula).trans
      hcasesCode
  have hguardCode :=
    (binaryFormulaCode_and_left_le_outputRows positiveGuard
      positiveBodyFormula).trans hpositiveCode
  have hpositiveBodyCode :=
    (binaryFormulaCode_and_right_le_outputRows positiveGuard
      positiveBodyFormula).trans hpositiveCode
  have hrawCode :=
    (binaryFormulaCode_or_left_le_outputRows rawFormula
      sameMappedFormula).trans hpositiveBodyCode
  have hsameMappedCode :=
    (binaryFormulaCode_or_right_le_outputRows rawFormula
      sameMappedFormula).trans hpositiveBodyCode
  have hsameCode :=
    (binaryFormulaCode_or_left_le_outputRows sameFormula mappedFormula).trans
      hsameMappedCode
  have hmappedCode :=
    (binaryFormulaCode_or_right_le_outputRows sameFormula mappedFormula).trans
      hsameMappedCode
  have htailCode : (binaryFormulaCode tailFormula).length <= syntaxResource := by
    rw [hmappedAlignment] at hmappedCode
    unfold otherModeWithTailFormula at hmappedCode
    exact (binaryFormulaCode_and_right_le_outputRows _ tailFormula).trans
      ((binaryFormulaCode_and_right_le_outputRows _ _).trans
        ((binaryFormulaCode_and_right_le_outputRows _ _).trans
          ((binaryFormulaCode_and_right_le_outputRows _ _).trans
            ((binaryFormulaCode_and_right_le_outputRows _ _).trans
              hmappedCode))))
  have htagCode :=
    (binaryFormulaCode_and_left_le_outputRows tagFormula rowsFormula).trans
      htailCode
  have hrowsCode :=
    (binaryFormulaCode_and_right_le_outputRows tagFormula rowsFormula).trans
      htailCode
  have hmodeSize : Nat.size mode <= bitBound := by
    have hraw := henvironmentSize (25 : Fin 29)
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using hraw
  have hnextParserTokensCountSize :
      Nat.size next.parserTokensCount <= bitBound := by
    have hraw := henvironmentSize (20 : Fin 29)
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using hraw
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let tagCertificate :=
    compactNegationFormulaTagExplicitHybridCertificateOfGraph tag mappedHead
      htag
  let rowsCertificate :=
    compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputBoundary next.outputCount mappedHead hrows
  let tailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction tagCertificate
      rowsCertificate
  let mappedCertificate := otherModeWithTailCertificate mode hmodeZero hmodeOne
    hmodeTwo hmodeFour hmodeFive tailFormula tailCertificate
  have hcountResource :
      hybridFormulaStructuralPayloadBound countCertificate <= countResource := by
    exact consumedCountEqualityCertificate_structuralPayloadBound_le_fixed
      current next consumedCount bitBound hcount
      hcurrentParserTokensCountSize hconsumedCountSize
      hnextParserTokensCountSize
  have hpositiveGuardResource :
      hybridFormulaStructuralPayloadBound positiveCertificate <=
        positiveGuardResource := by
    exact consumedCountPositiveCertificate_structuralPayloadBound_le_fixed
      consumedCount bitBound hconsumed hconsumedCountSize
  have htagResource :
      hybridFormulaStructuralPayloadBound tagCertificate <= tagResource := by
    exact
      compactNegationFormulaTagExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tag mappedHead bitBound htag htagSize hmappedHeadSize
  have hrowsResource :
      hybridFormulaStructuralPayloadBound rowsCertificate <= rowsResource := by
    simpa only [rowsCertificate, rowsResource] using
      compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current.parserFinish current.finish
        current.outputCount current.start current.parserTokensFinish
        current.parserTokensCount consumedCount next.parserFinish next.finish
        next.outputBoundary next.outputCount mappedHead numericBound bitBound
        hrows htableSize hwidthSize htokenCountSize hcurrentParserFinishSize
        hcurrentFinishSize hcurrentOutputCountSize hcurrentStartSize
        hcurrentParserTokensFinishSize hcurrentParserTokensCountSize
        hconsumedCountSize hnextParserFinishSize hnextFinishSize
        hnextOutputBoundarySize hnextOutputCountSize hmappedHeadSize hwidthBound
        htokenCountBound hnumericSize
  have htailRaw := transparentHybridConjunctionPayloadBound_le tagCertificate
    rowsCertificate tagResource rowsResource htagResource hrowsResource
  have htailAssembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
      tagFormula rowsFormula tagResource rowsResource syntaxResource
      hsyntaxPositive htagClosed hrowsClosed htagCode hrowsCode htailCode
  have htailResource :
      hybridFormulaStructuralPayloadBound tailCertificate <= tailResource := by
    exact htailRaw.trans (by
      dsimp only [tailResource]
      unfold outputRowsMappedTailFixedPayloadPolynomial
      exact htailAssembly)
  have hmappedResource :
      hybridFormulaStructuralPayloadBound mappedCertificate <=
        mappedResource := by
    dsimp only [mappedResource]
    unfold outputRowsMappedCaseFixedPayloadPolynomial
    exact otherModeWithTailCertificate_structuralPayloadBound_le_fixed mode
      bitBound syntaxResource hmodeZero hmodeOne hmodeTwo hmodeFour hmodeFive
      tailFormula tailCertificate tailResource htailResource hmodeSize
      hsyntaxPositive htailClosed (by
        rw [← hmappedAlignment]
        exact hmappedCode)
  let sameMappedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := sameFormula) mappedCertificate
  have hsameMappedRaw :=
    transparentHybridDisjunctionRightPayloadBound_le
      (left := sameFormula) mappedCertificate mappedResource hmappedResource
  have hsameMappedAssembly :=
    transparentHybridDisjunctionRightPayloadEnvelope_le_closedGeneral_outputRows
      FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate.zeroValuation
      sameFormula mappedFormula mappedResource
      syntaxResource hsyntaxPositive hsameClosed hmappedClosed hsameCode
      hmappedCode hsameMappedCode
  have hsameMappedResource :
      hybridFormulaStructuralPayloadBound sameMappedCertificate <=
        sameMappedResource :=
    hsameMappedRaw.trans (by
      dsimp only [sameMappedResource]
      exact hsameMappedAssembly)
  let positiveBodyCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := rawFormula) sameMappedCertificate
  have hpositiveBodyRaw :=
    transparentHybridDisjunctionRightPayloadBound_le
      (left := rawFormula) sameMappedCertificate sameMappedResource
      hsameMappedResource
  have hpositiveBodyAssembly :=
    transparentHybridDisjunctionRightPayloadEnvelope_le_closedGeneral_outputRows
      FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate.zeroValuation
      rawFormula sameMappedFormula sameMappedResource
      syntaxResource hsyntaxPositive hrawClosed hsameMappedClosed hrawCode
      hsameMappedCode hpositiveBodyCode
  have hpositiveBodyResource :
      hybridFormulaStructuralPayloadBound positiveBodyCertificate <=
        positiveBodyResource :=
    hpositiveBodyRaw.trans (by
      dsimp only [positiveBodyResource]
      exact hpositiveBodyAssembly)
  let positiveSelectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      positiveCertificate positiveBodyCertificate
  have hpositiveRaw := transparentHybridConjunctionPayloadBound_le
    positiveCertificate positiveBodyCertificate positiveGuardResource
    positiveBodyResource hpositiveGuardResource hpositiveBodyResource
  have hpositiveAssembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate.zeroValuation
      positiveGuard positiveBodyFormula
      positiveGuardResource positiveBodyResource syntaxResource
      hsyntaxPositive hguardClosed hpositiveBodyClosed hguardCode
      hpositiveBodyCode hpositiveCode
  have hpositiveResource :
      hybridFormulaStructuralPayloadBound positiveSelectedCertificate <=
        positiveResource :=
    hpositiveRaw.trans (by
      dsimp only [positiveResource]
      exact hpositiveAssembly)
  let casesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := zeroFormula) positiveSelectedCertificate
  have hcasesRaw := transparentHybridDisjunctionRightPayloadBound_le
    (left := zeroFormula) positiveSelectedCertificate positiveResource
    hpositiveResource
  have hcasesAssembly :=
    transparentHybridDisjunctionRightPayloadEnvelope_le_closedGeneral_outputRows
      FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate.zeroValuation
      zeroFormula positiveFormula positiveResource
      syntaxResource hsyntaxPositive hzeroClosed hpositiveClosed hzeroCode
      hpositiveCode hcasesCode
  have hcasesResource :
      hybridFormulaStructuralPayloadBound casesCertificate <= casesResource :=
    hcasesRaw.trans (by
      dsimp only [casesResource]
      exact hcasesAssembly)
  have houterRaw := transparentHybridConjunctionPayloadBound_le
    countCertificate casesCertificate countResource casesResource
    hcountResource hcasesResource
  have houterAssembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate.zeroValuation
      countFormula casesFormula countResource
      casesResource syntaxResource hsyntaxPositive hcountClosed hcasesClosed
      hcountCode hcasesCode hfullCode
  have hfixed := houterRaw.trans houterAssembly
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        countCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := zeroFormula)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            positiveCertificate
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := rawFormula)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left := sameFormula) mappedCertificate))))) <= _
  unfold outputRowsMappedSelectedFixedPayloadPolynomial
  simpa only [syntaxResource, countResource, positiveGuardResource,
    mappedResource, sameMappedResource, positiveBodyResource,
    positiveResource, casesResource, sameMappedCertificate,
    positiveBodyCertificate, positiveSelectedCertificate, casesCertificate]
    using hfixed

#print axioms
  compactFormulaTransformFormulaOutputRowsMappedBranchCertificate_structuralPayloadBound_le_rowsFullyFixed
#print axioms
  compactFormulaTransformFormulaOutputRowsMappedBranchCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsMappedRowsFullyFixedBounds
