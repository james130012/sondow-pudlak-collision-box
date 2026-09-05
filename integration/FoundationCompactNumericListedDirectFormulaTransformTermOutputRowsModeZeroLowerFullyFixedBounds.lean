import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOuterSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedCore
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsNativeLeFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsZeroOneGuardFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAppendTwoValuesFullyFixedBounds
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds

/-!
# Fully fixed mode-zero lower branch for term-output rows

The original checked branch certificate is assembled from five fixed leaves.
One complete closed-formula syntax budget pays every connective on the selected
path. No graph-dependent resource remains in the result.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 240000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroLowerFullyFixedBounds

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
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGuardFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFormulaFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOuterSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListAppendTwoValuesFormulaFixedBounds
open FoundationCompactNumericListedDirectNatListAppendTwoValuesFullyFixedBounds

private abbrev modeZeroLowerValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsModeZeroLowerFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource := termRowsOuterSyntaxPolynomial bitBound
  let guardRowsResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (termRowsThreeGuardFixedPayloadPolynomial bitBound)
      (appendTwoFullyFixedPayloadPolynomial numericBound bitBound)
  let internalResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource guardRowsResource
  let modeResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (termRowsPositiveAtomicFixedPayloadPolynomial bitBound) internalResource
  let modesResource :=
    sixRightDisjunctionPathZeroPayloadEnvelope syntaxResource modeResource
  let positiveResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (termRowsNativeLeFixedPayloadPolynomial bitBound) modesResource
  let casesResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource positiveResource
  hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termRowsPositiveAtomicFixedPayloadPolynomial bitBound) casesResource

theorem
    compactFormulaTransformTermOutputRowsModeZeroLowerBranch_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 0)
    (hguard : consumedCount = 2 ∧ tag = 0 ∧
      argument + 1 = binderArity)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 1 0)
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
          (.modeZeroLower hcount hconsumed hmode hguard hrows)) <=
      termRowsModeZeroLowerFixedPayloadPolynomial numericBound bitBound := by
  let countFormula := termRowsCountFormula current next consumedCount
  let zeroCaseFormula := termRowsZeroCaseFormula tokenTable width tokenCount
    current next consumedCount
  let positiveFormula := termRowsPositiveCaseFormula tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount
  let casesFormula := zeroCaseFormula ⋎ positiveFormula
  let modesFormula := termRowsModesFormula tokenTable width tokenCount current
    next mode binderArity tag argument consumedCount witnessStart witnessFinish
    witnessCount
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
  let positiveGuardFormula := nativeLeFormula (‘1’ : ValuationTerm)
    (shortBinaryNumeralTerm consumedCount)
  let modeEqFormula := nativeEqFormula (shortBinaryNumeralTerm mode)
    (‘0’ : ValuationTerm)
  let guardFormula := termRowsGuardZeroTagFormula consumedCount tag argument
    binderArity
  let rowsFormula := termRowsAppendTwoOneZeroFormula tokenTable width tokenCount
    current next
  let guardRowsFormula := guardFormula ⋏ rowsFormula
  let tripleFailure := tripleFailureFormula
    (shortBinaryNumeralTerm consumedCount) (shortBinaryNumeralTerm tag)
    (shortBinaryNumeralTerm argument) (shortBinaryNumeralTerm binderArity)
  let shiftedPairFormula := tripleFailure ⋏
    (termRowsGuardOneTagFormula consumedCount tag ⋏
      termRowsAppendTwoShiftedFormula tokenTable width tokenCount current next
        argument)
  let rawPairFormula := tripleFailure ⋏
    (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) ⋏
      termRowsRawPrefixFormula tokenTable width tokenCount current next
        consumedCount)
  let internalFormula := guardRowsFormula ⋎
    (shiftedPairFormula ⋎ rawPairFormula)
  let fullFormula := countFormula ⋏ casesFormula
  let syntaxResource := termRowsOuterSyntaxPolynomial bitBound
  let atomicResource := termRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let positiveLeafResource := termRowsNativeLeFixedPayloadPolynomial bitBound
  let guardResource := termRowsThreeGuardFixedPayloadPolynomial bitBound
  let rowsResource := appendTwoFullyFixedPayloadPolynomial numericBound bitBound
  let guardRowsResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource guardResource rowsResource
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope
    syntaxResource guardRowsResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource internalResource
  let modesResource := sixRightDisjunctionPathZeroPayloadEnvelope
    syntaxResource modeResource
  let positiveResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource positiveLeafResource modesResource
  let casesResource := hybridDisjunctionGeneralPayloadEnvelope
    syntaxResource positiveResource
  have hfullAlignment :
      fullFormula =
        compactFormulaTransformTermOutputRowsExplicitFormula tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount := by
    dsimp only [fullFormula, countFormula, casesFormula, zeroCaseFormula,
      positiveFormula]
    rw [compactFormulaTransformTermOutputRowsExplicitFormula_eq_named]
    rfl
  have hfullClosed : fullFormula.freeVariables = ∅ := by
    rw [hfullAlignment]
    exact compactFormulaTransformTermOutputRowsExplicitFormula_closed tokenTable
      width tokenCount current next mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount
  have hfullCode :
      (binaryFormulaCode fullFormula).length <= syntaxResource := by
    rw [hfullAlignment]
    exact compactFormulaTransformTermOutputRowsExplicitFormula_code_le_fixed
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount bitBound witnessStart witnessFinish witnessCount
      henvironmentSize
  have hsyntaxPositive : 1 <= syntaxResource := by
    exact termRowsOuterSyntaxPolynomial_positive bitBound
  have hcountClosed := termRowsConjunction_left_closed countFormula casesFormula
    hfullClosed
  have hcasesClosed := termRowsConjunction_right_closed countFormula casesFormula
    hfullClosed
  have hcountCode :=
    (termRowsConjunction_left_code_le countFormula casesFormula).trans hfullCode
  have hcasesCode :=
    (termRowsConjunction_right_code_le countFormula casesFormula).trans hfullCode
  have hzeroCaseClosed := termRowsDisjunction_left_closed zeroCaseFormula
    positiveFormula hcasesClosed
  have hpositiveClosed := termRowsDisjunction_right_closed zeroCaseFormula
    positiveFormula hcasesClosed
  have hzeroCaseCode :=
    (termRowsDisjunction_left_code_le zeroCaseFormula positiveFormula).trans
      hcasesCode
  have hpositiveCode :=
    (termRowsDisjunction_right_code_le zeroCaseFormula positiveFormula).trans
      hcasesCode
  have hpositiveDecomposition :
      positiveFormula = positiveGuardFormula ⋏ modesFormula := by
    rfl
  have hpositiveDecomposedClosed :
      (positiveGuardFormula ⋏ modesFormula).freeVariables = ∅ := by
    simpa only [hpositiveDecomposition] using hpositiveClosed
  have hpositiveDecomposedCode :
      (binaryFormulaCode (positiveGuardFormula ⋏ modesFormula)).length <=
        syntaxResource := by
    simpa only [hpositiveDecomposition] using hpositiveCode
  have hpositiveGuardClosed := termRowsConjunction_left_closed
    positiveGuardFormula modesFormula hpositiveDecomposedClosed
  have hmodesClosed := termRowsConjunction_right_closed positiveGuardFormula
    modesFormula hpositiveDecomposedClosed
  have hpositiveGuardCode :=
    (termRowsConjunction_left_code_le positiveGuardFormula modesFormula).trans
      hpositiveDecomposedCode
  have hmodesCode :=
    (termRowsConjunction_right_code_le positiveGuardFormula modesFormula).trans
      hpositiveDecomposedCode
  have hmodesDecomposition :
      modesFormula = modeZeroFormula ⋎
        (modeOneFormula ⋎ (modeTwoFormula ⋎
          (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula)))) := by
    rfl
  have hmodesDecomposedClosed :
      (modeZeroFormula ⋎
        (modeOneFormula ⋎ (modeTwoFormula ⋎
          (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))))).freeVariables =
        ∅ := by
    simpa only [hmodesDecomposition] using hmodesClosed
  have hmodesDecomposedCode :
      (binaryFormulaCode
        (modeZeroFormula ⋎
          (modeOneFormula ⋎ (modeTwoFormula ⋎
            (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula)))))).length <=
        syntaxResource := by
    simpa only [hmodesDecomposition] using hmodesCode
  have hmodeZeroClosed := termRowsDisjunction_left_closed modeZeroFormula
    (modeOneFormula ⋎ (modeTwoFormula ⋎
      (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))))
    hmodesDecomposedClosed
  have hmodeZeroCode :=
    (termRowsDisjunction_left_code_le modeZeroFormula
      (modeOneFormula ⋎ (modeTwoFormula ⋎
        (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))))).trans
      hmodesDecomposedCode
  have hmodeZeroDecomposition :
      modeZeroFormula = modeEqFormula ⋏ internalFormula := by
    dsimp only [modeZeroFormula, modeEqFormula, internalFormula,
      guardRowsFormula, guardFormula, rowsFormula, shiftedPairFormula,
      rawPairFormula, tripleFailure]
    unfold termRowsModeZeroFormula
    rfl
  have hmodeZeroDecomposedClosed :
      (modeEqFormula ⋏ internalFormula).freeVariables = ∅ := by
    simpa only [hmodeZeroDecomposition] using hmodeZeroClosed
  have hmodeZeroDecomposedCode :
      (binaryFormulaCode (modeEqFormula ⋏ internalFormula)).length <=
        syntaxResource := by
    simpa only [hmodeZeroDecomposition] using hmodeZeroCode
  have hmodeEqClosed := termRowsConjunction_left_closed modeEqFormula
    internalFormula hmodeZeroDecomposedClosed
  have hinternalClosed := termRowsConjunction_right_closed modeEqFormula
    internalFormula hmodeZeroDecomposedClosed
  have hmodeEqCode :=
    (termRowsConjunction_left_code_le modeEqFormula internalFormula).trans
      hmodeZeroDecomposedCode
  have hinternalCode :=
    (termRowsConjunction_right_code_le modeEqFormula internalFormula).trans
      hmodeZeroDecomposedCode
  have hguardRowsClosed := termRowsDisjunction_left_closed guardRowsFormula
    (shiftedPairFormula ⋎ rawPairFormula) hinternalClosed
  have hremainingClosed := termRowsDisjunction_right_closed guardRowsFormula
    (shiftedPairFormula ⋎ rawPairFormula) hinternalClosed
  have hguardRowsCode :=
    (termRowsDisjunction_left_code_le guardRowsFormula
      (shiftedPairFormula ⋎ rawPairFormula)).trans hinternalCode
  have hremainingCode :=
    (termRowsDisjunction_right_code_le guardRowsFormula
      (shiftedPairFormula ⋎ rawPairFormula)).trans hinternalCode
  have hguardClosed := termRowsConjunction_left_closed guardFormula rowsFormula
    hguardRowsClosed
  have hrowsClosed := termRowsConjunction_right_closed guardFormula rowsFormula
    hguardRowsClosed
  have hguardCode :=
    (termRowsConjunction_left_code_le guardFormula rowsFormula).trans
      hguardRowsCode
  have hrowsCode :=
    (termRowsConjunction_right_code_le guardFormula rowsFormula).trans
      hguardRowsCode
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
  have hnextParserTokensCountSize :
      Nat.size next.parserTokensCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (20 : Fin 33)
  have hnextOutputBoundarySize : Nat.size next.outputBoundary <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (23 : Fin 33)
  have hnextOutputCountSize : Nat.size next.outputCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (24 : Fin 33)
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
  have hbitBoundPositive : 1 <= bitBound := by
    have htwoSize := hconsumedSize
    rw [hguard.1] at htwoSize
    have htwoSizePositive : 0 < Nat.size 2 :=
      Nat.size_pos.mpr (by omega)
    omega
  have honeSize : Nat.size 1 <= bitBound := by
    norm_num [Nat.size]
    exact hbitBoundPositive
  have hzeroSize : Nat.size 0 <= bitBound := by simp
  let countCertificate :=
    consumedCountEqualityCertificate current next consumedCount hcount
  let positiveCertificate :=
    consumedCountPositiveCertificate consumedCount hconsumed
  let modeCertificate := shortNumeralLiteralEqCertificate mode 0
    (‘0’ : ValuationTerm) (termValue_arithmeticZero modeZeroLowerValuation)
    hmode
  let guardCertificate := zeroTagGuardCertificate consumedCount tag argument
    binderArity hguard
  let rowsCertificate :=
    FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 1 0 (‘1’ : ValuationTerm) (‘0’ : ValuationTerm)
      (termValue_arithmeticOne modeZeroLowerValuation)
      (termValue_arithmeticZero modeZeroLowerValuation) hrows
  let guardRowsCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      guardCertificate rowsCertificate
  let internalCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := shiftedPairFormula ⋎ rawPairFormula) guardRowsCertificate
  let modeFullCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction modeCertificate
      internalCertificate
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := modeOneFormula ⋎ (modeTwoFormula ⋎
        (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))))
      modeFullCertificate
  let positiveCaseCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      positiveCertificate modesCertificate
  let casesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := zeroCaseFormula) positiveCaseCertificate
  let fullCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction countCertificate
      casesCertificate
  have hcountResource :
      hybridFormulaStructuralPayloadBound countCertificate <= atomicResource :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_fixed current
      next consumedCount bitBound hcount hcurrentParserTokensCountSize
      hconsumedSize hnextParserTokensCountSize
  have hpositiveLeafResource :
      hybridFormulaStructuralPayloadBound positiveCertificate <=
        positiveLeafResource :=
    consumedCountPositiveCertificate_structuralPayloadBound_le_fixed
      consumedCount bitBound hconsumed hconsumedSize
  have hmodeResource :
      hybridFormulaStructuralPayloadBound modeCertificate <= atomicResource := by
    exact shortNumeralLiteralEqCertificate_structuralPayloadBound_le_fixed mode
      0 (‘0’ : ValuationTerm)
      (termValue_arithmeticZero modeZeroLowerValuation) hmode bitBound hmodeSize
      (termRowsLiteral_closed (‘0’ : ValuationTerm) (Or.inl rfl))
      (termRowsLiteralCode_le (‘0’ : ValuationTerm) bitBound (Or.inl rfl))
  have hguardResource :
      hybridFormulaStructuralPayloadBound guardCertificate <= guardResource :=
    zeroTagGuardCertificate_structuralPayloadBound_le_fixed consumedCount tag
      argument binderArity bitBound hguard hconsumedSize htagSize hargumentSize
      hbinderAritySize
  have honeClosed : (‘1’ : ValuationTerm).freeVariables = ∅ :=
    termRowsLiteral_closed (‘1’ : ValuationTerm) (Or.inr (Or.inl rfl))
  have hzeroClosed : (‘0’ : ValuationTerm).freeVariables = ∅ :=
    termRowsLiteral_closed (‘0’ : ValuationTerm) (Or.inl rfl)
  have honeCode : (binaryTermCode (‘1’ : ValuationTerm)).length <=
      appendTwoExactTermCodePolynomial bitBound := by
    unfold appendTwoExactTermCodePolynomial
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds.appendSourcePrefixCompositeTermCodePolynomial
    omega
  have hzeroCode : (binaryTermCode (‘0’ : ValuationTerm)).length <=
      appendTwoExactTermCodePolynomial bitBound := by
    have hbase : (binaryTermCode (‘0’ : ValuationTerm)).length <=
        FoundationCompactPABinaryNumeralAdditionBounds.binaryNumeralTermCodeEnvelope 0 := by
      decide
    have henvelope := hbase.trans
      (FoundationCompactPAExponentialShortNumeralCompilerBounds.binaryNumeralTermCodeEnvelope_mono_short
        (Nat.zero_le bitBound))
    unfold appendTwoExactTermCodePolynomial
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds.appendSourcePrefixCompositeTermCodePolynomial
    omega
  have hrowsResource :
      hybridFormulaStructuralPayloadBound rowsCertificate <= rowsResource := by
    exact
      compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current.parserFinish current.finish
        current.outputCount next.parserFinish next.finish next.outputBoundary
        next.outputCount 1 0 numericBound bitBound (‘1’ : ValuationTerm)
        (‘0’ : ValuationTerm)
        (termValue_arithmeticOne modeZeroLowerValuation)
        (termValue_arithmeticZero modeZeroLowerValuation) honeClosed hzeroClosed
        hrows htableSize hwidthSize htokenCountSize hcurrentParserFinishSize
        hcurrentFinishSize hcurrentOutputCountSize hnextParserFinishSize
        hnextFinishSize hnextOutputBoundarySize hnextOutputCountSize honeSize
        hzeroSize honeCode hzeroCode hwidthBound htokenCountBound
        hnextOutputCountBound hnumericSize
  have hguardRowsResource :
      hybridFormulaStructuralPayloadBound guardRowsCertificate <=
        guardRowsResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral guardCertificate
      rowsCertificate guardResource rowsResource syntaxResource hguardResource
      hrowsResource hsyntaxPositive hguardClosed hrowsClosed hguardCode
      hrowsCode hguardRowsCode
  have hinternalResource :
      hybridFormulaStructuralPayloadBound internalCertificate <=
        internalResource :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral
      guardRowsCertificate guardRowsResource syntaxResource
      hguardRowsResource hsyntaxPositive hguardRowsClosed hremainingClosed
      hguardRowsCode hremainingCode hinternalCode
  have hmodeFullResource :
      hybridFormulaStructuralPayloadBound modeFullCertificate <= modeResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral modeCertificate
      internalCertificate atomicResource internalResource syntaxResource
      hmodeResource hinternalResource hsyntaxPositive hmodeEqClosed
      hinternalClosed hmodeEqCode hinternalCode hmodeZeroDecomposedCode
  have hmodesResource :
      hybridFormulaStructuralPayloadBound modesCertificate <= modesResource :=
    sixRightDisjunctionPathZeroPayloadBound_le_closedGeneral modeZeroFormula
      modeOneFormula modeTwoFormula modeFourFormula modeFiveFormula otherFormula
      modeFullCertificate modeResource syntaxResource hmodeFullResource
      hsyntaxPositive hmodesDecomposedClosed hmodesDecomposedCode
  have hpositiveResource :
      hybridFormulaStructuralPayloadBound positiveCaseCertificate <=
        positiveResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral positiveCertificate
      modesCertificate positiveLeafResource modesResource syntaxResource
      hpositiveLeafResource hmodesResource hsyntaxPositive
      hpositiveGuardClosed hmodesClosed hpositiveGuardCode hmodesCode
      hpositiveDecomposedCode
  have hcasesResource :
      hybridFormulaStructuralPayloadBound casesCertificate <= casesResource :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      positiveCaseCertificate positiveResource syntaxResource
      hpositiveResource hsyntaxPositive hzeroCaseClosed hpositiveClosed
      hzeroCaseCode hpositiveCode hcasesCode
  have hfixed :
      hybridFormulaStructuralPayloadBound fullCertificate <=
        hybridConjunctionGeneralPayloadEnvelope syntaxResource atomicResource
          casesResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral countCertificate
      casesCertificate atomicResource casesResource syntaxResource
      hcountResource hcasesResource hsyntaxPositive hcountClosed hcasesClosed
      hcountCode hcasesCode hfullCode
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound fullCertificate <= _
  simpa only [termRowsModeZeroLowerFixedPayloadPolynomial, syntaxResource,
    atomicResource, positiveLeafResource, guardResource, rowsResource,
    guardRowsResource, internalResource, modeResource, modesResource,
    positiveResource, casesResource] using hfixed

#print axioms
  compactFormulaTransformTermOutputRowsModeZeroLowerBranch_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroLowerFullyFixedBounds
