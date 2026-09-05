import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterFixedCore
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureTripleFixedBound
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsZeroOneGuardFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAppendTwoValuesFullyFixedBounds
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds

/-! # Fully fixed shifted branch under term-output mode zero -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 220000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroShiftedFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGuardFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureTripleFixedBound
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOuterSyntaxFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterSyntaxFacts
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterFixedCore
open FoundationCompactNumericListedDirectNatListAppendTwoValuesFormulaFixedBounds
open FoundationCompactNumericListedDirectNatListAppendTwoValuesFullyFixedBounds

private abbrev modeZeroShiftedValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

private theorem shiftedValue_size_le (value : Nat) :
    Nat.size (value + 1) <= Nat.size value + 1 := by
  rw [Nat.size_le]
  have hvalue : value + 1 <= 2 ^ Nat.size value :=
    Nat.succ_le_iff.mpr (Nat.lt_size_self value)
  exact hvalue.trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat))
      (Nat.lt_succ_self (Nat.size value)))

def termRowsModeZeroShiftedFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let branchBitBound := bitBound + 1
  let syntaxResource := termRowsOuterSyntaxPolynomial branchBitBound
  let guardRowsResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource (termRowsTwoGuardFixedPayloadPolynomial branchBitBound)
    (appendTwoFullyFixedPayloadPolynomial numericBound branchBitBound)
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource (termOutputTripleFailureFixedPayloadPolynomial branchBitBound)
    guardRowsResource
  let middleResource := hybridDisjunctionGeneralPayloadEnvelope
    syntaxResource selectedResource
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope
    syntaxResource middleResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termRowsPositiveAtomicFixedPayloadPolynomial branchBitBound)
    internalResource
  termRowsModeZeroOuterFixedPayloadPolynomial modeResource branchBitBound

theorem
    compactFormulaTransformTermOutputRowsModeZeroShiftedBranch_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 0)
    (failure : TripleFailureCheckedData consumedCount tag argument binderArity)
    (hguard : consumedCount = 2 ∧ tag = 1)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 1 (argument + 1))
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
          (.modeZeroShifted hcount hconsumed hmode failure hguard hrows)) <=
      termRowsModeZeroShiftedFixedPayloadPolynomial numericBound bitBound := by
  let branchBitBound := bitBound + 1
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
    (‘0’ : ValuationTerm)
  let lowerPairFormula :=
    termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
      termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current next
  let failureFormula := tripleFailureFormula
    (shortBinaryNumeralTerm consumedCount) (shortBinaryNumeralTerm tag)
    (shortBinaryNumeralTerm argument) (shortBinaryNumeralTerm binderArity)
  let guardFormula := termRowsGuardOneTagFormula consumedCount tag
  let shiftedTerm := nativeAddTerm (shortBinaryNumeralTerm argument)
    (‘1’ : ValuationTerm)
  let rowsFormula := termRowsAppendTwoShiftedFormula tokenTable width tokenCount
    current next argument
  let guardRowsFormula := guardFormula ⋏ rowsFormula
  let shiftedPairFormula := failureFormula ⋏ guardRowsFormula
  let rawPairFormula := failureFormula ⋏
    (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) ⋏
      termRowsRawPrefixFormula tokenTable width tokenCount current next
        consumedCount)
  let tailFormula := shiftedPairFormula ⋎ rawPairFormula
  let internalFormula := lowerPairFormula ⋎ tailFormula
  let guardResource := termRowsTwoGuardFixedPayloadPolynomial branchBitBound
  let rowsResource := appendTwoFullyFixedPayloadPolynomial numericBound
    branchBitBound
  let failureResource := termOutputTripleFailureFixedPayloadPolynomial
    branchBitBound
  let atomicResource := termRowsPositiveAtomicFixedPayloadPolynomial
    branchBitBound
  let guardRowsResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource guardResource rowsResource
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource failureResource guardRowsResource
  let middleResource := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    selectedResource
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope
    syntaxResource middleResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource internalResource
  have henvironmentLarge : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <=
        branchBitBound := by
    intro coordinate
    exact (henvironmentSize coordinate).trans (by
      dsimp only [branchBitBound]
      omega)
  have facts := termRowsModeZeroOuterSyntaxFacts tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount branchBitBound
    witnessStart witnessFinish witnessCount henvironmentLarge
  have hmodeZeroClosed := termRowsDisjunction_left_closed modeZeroFormula
    (modeOneFormula ⋎ (modeTwoFormula ⋎
      (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))))
    facts.modesDecomposedClosed
  have hmodeZeroCode :=
    (termRowsDisjunction_left_code_le modeZeroFormula
      (modeOneFormula ⋎ (modeTwoFormula ⋎
        (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))))).trans
      facts.modesDecomposedCode
  have hmodeZeroDecomposition :
      modeZeroFormula = modeEqFormula ⋏ internalFormula := by
    dsimp only [modeZeroFormula, modeEqFormula, internalFormula,
      lowerPairFormula, tailFormula, shiftedPairFormula, rawPairFormula,
      failureFormula, guardRowsFormula, guardFormula, rowsFormula]
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
  have hlowerPairClosed := termRowsDisjunction_left_closed lowerPairFormula
    tailFormula hinternalClosed
  have htailClosed := termRowsDisjunction_right_closed lowerPairFormula
    tailFormula hinternalClosed
  have hlowerPairCode :=
    (termRowsDisjunction_left_code_le lowerPairFormula tailFormula).trans
      hinternalCode
  have htailCode :=
    (termRowsDisjunction_right_code_le lowerPairFormula tailFormula).trans
      hinternalCode
  have hshiftedPairClosed := termRowsDisjunction_left_closed shiftedPairFormula
    rawPairFormula htailClosed
  have hrawPairClosed := termRowsDisjunction_right_closed shiftedPairFormula
    rawPairFormula htailClosed
  have hshiftedPairCode :=
    (termRowsDisjunction_left_code_le shiftedPairFormula rawPairFormula).trans
      htailCode
  have hrawPairCode :=
    (termRowsDisjunction_right_code_le shiftedPairFormula rawPairFormula).trans
      htailCode
  have hfailureClosed := termRowsConjunction_left_closed failureFormula
    guardRowsFormula hshiftedPairClosed
  have hguardRowsClosed := termRowsConjunction_right_closed failureFormula
    guardRowsFormula hshiftedPairClosed
  have hfailureCode :=
    (termRowsConjunction_left_code_le failureFormula guardRowsFormula).trans
      hshiftedPairCode
  have hguardRowsCode :=
    (termRowsConjunction_right_code_le failureFormula guardRowsFormula).trans
      hshiftedPairCode
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
  have hbinderAritySize : Nat.size binderArity <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (26 : Fin 33)
  have htagSize : Nat.size tag <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (27 : Fin 33)
  have hargumentSize : Nat.size argument <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (28 : Fin 33)
  have hconsumedSize : Nat.size consumedCount <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (29 : Fin 33)
  have honeSize : Nat.size 1 <= branchBitBound := by
    dsimp only [branchBitBound]
    simp
  have hshiftedSize : Nat.size (argument + 1) <= branchBitBound :=
    (shiftedValue_size_le argument).trans (by
      have hraw := henvironmentSize (28 : Fin 33)
      simpa [compactFormulaTransformTermOutputRowsEnvironment,
        branchBitBound] using Nat.add_le_add_right hraw 1)
  have hnumericSizeLarge : Nat.size numericBound <= branchBitBound :=
    hnumericSize.trans (by
      dsimp only [branchBitBound]
      omega)
  have honeClosed : (‘1’ : ValuationTerm).freeVariables = ∅ :=
    termRowsLiteral_closed (‘1’ : ValuationTerm) (Or.inr (Or.inl rfl))
  have hshiftedClosed : shiftedTerm.freeVariables = ∅ := by
    simpa only [shiftedTerm] using failureAddArgumentOne_closed argument
  have honeCode : (binaryTermCode (‘1’ : ValuationTerm)).length <=
      appendTwoExactTermCodePolynomial branchBitBound := by
    unfold appendTwoExactTermCodePolynomial
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds.appendSourcePrefixCompositeTermCodePolynomial
    omega
  have hshiftedCode : (binaryTermCode shiftedTerm).length <=
      appendTwoExactTermCodePolynomial branchBitBound := by
    have hargumentCode := binaryNumeralTerm_code_length_le_envelope argument
      branchBitBound hargumentSize
    have hadd := paAddTerm_code_length_le
      (shortBinaryNumeralTerm argument) (‘1’ : ValuationTerm)
    change (binaryTermCode
      (paAddTerm (shortBinaryNumeralTerm argument)
        (‘1’ : ValuationTerm))).length <= _
    unfold appendTwoExactTermCodePolynomial
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds.appendSourcePrefixCompositeTermCodePolynomial
    omega
  let modeCertificate := shortNumeralLiteralEqCertificate mode 0
    (‘0’ : ValuationTerm) (termValue_arithmeticZero modeZeroShiftedValuation)
    hmode
  let failureCertificate := tripleFailureCertificateFromData consumedCount tag
    argument binderArity failure
  let guardCertificate := oneTagGuardCertificate consumedCount tag hguard
  let rowsCertificate :=
    FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 1 (argument + 1) (‘1’ : ValuationTerm) shiftedTerm
      (termValue_arithmeticOne modeZeroShiftedValuation)
      (by
        simp [shiftedTerm, nativeAddTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne, termValue_shortBinaryNumeralTerm]) hrows
  let guardRowsCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      guardCertificate rowsCertificate
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      failureCertificate guardRowsCertificate
  let middleCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := rawPairFormula) selectedCertificate
  let internalCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := lowerPairFormula) middleCertificate
  let modeFullCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction modeCertificate
      internalCertificate
  have hmodeResource :
      hybridFormulaStructuralPayloadBound modeCertificate <= atomicResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_fixed mode 0
      (‘0’ : ValuationTerm) (termValue_arithmeticZero modeZeroShiftedValuation)
      hmode branchBitBound hmodeSize
      (termRowsLiteral_closed (‘0’ : ValuationTerm) (Or.inl rfl))
      (termRowsLiteralCode_le (‘0’ : ValuationTerm) branchBitBound (Or.inl rfl))
  have hfailureResource :
      hybridFormulaStructuralPayloadBound failureCertificate <=
        failureResource :=
    (tripleFailureCertificateFromData_structuralPayloadBound_le_transparent
      consumedCount tag argument binderArity failure).trans
      ((tripleFailurePayloadEnvelopeFromData_le_publicFinite consumedCount tag
        argument binderArity failure).trans
        (tripleFailurePublicFinitePayloadEnvelope_le_fullyFixed consumedCount
          tag argument binderArity branchBitBound hconsumedSize htagSize
          hargumentSize hbinderAritySize))
  have hguardResource :
      hybridFormulaStructuralPayloadBound guardCertificate <= guardResource :=
    oneTagGuardCertificate_structuralPayloadBound_le_fixed consumedCount tag
      branchBitBound hguard hconsumedSize htagSize
  have hrowsResource :
      hybridFormulaStructuralPayloadBound rowsCertificate <= rowsResource := by
    exact
      compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current.parserFinish current.finish
        current.outputCount next.parserFinish next.finish next.outputBoundary
        next.outputCount 1 (argument + 1) numericBound branchBitBound
        (‘1’ : ValuationTerm) shiftedTerm
        (termValue_arithmeticOne modeZeroShiftedValuation)
        (by
          simp [shiftedTerm, nativeAddTerm, termValue_arithmeticAdd,
            termValue_arithmeticOne, termValue_shortBinaryNumeralTerm])
        honeClosed hshiftedClosed hrows htableSize hwidthSize htokenCountSize
        hcurrentParserFinishSize hcurrentFinishSize hcurrentOutputCountSize
        hnextParserFinishSize hnextFinishSize hnextOutputBoundarySize
        hnextOutputCountSize honeSize hshiftedSize honeCode hshiftedCode
        hwidthBound htokenCountBound hnextOutputCountBound hnumericSizeLarge
  have hguardRowsResource :
      hybridFormulaStructuralPayloadBound guardRowsCertificate <=
        guardRowsResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral guardCertificate
      rowsCertificate guardResource rowsResource syntaxResource hguardResource
      hrowsResource facts.syntaxPositive hguardClosed hrowsClosed hguardCode
      hrowsCode hguardRowsCode
  have hselectedResource :
      hybridFormulaStructuralPayloadBound selectedCertificate <=
        selectedResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral failureCertificate
      guardRowsCertificate failureResource guardRowsResource syntaxResource
      hfailureResource hguardRowsResource facts.syntaxPositive hfailureClosed
      hguardRowsClosed hfailureCode hguardRowsCode hshiftedPairCode
  have hmiddleResource :
      hybridFormulaStructuralPayloadBound middleCertificate <= middleResource :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral
      selectedCertificate selectedResource syntaxResource hselectedResource
      facts.syntaxPositive hshiftedPairClosed hrawPairClosed hshiftedPairCode
      hrawPairCode htailCode
  have hinternalResource :
      hybridFormulaStructuralPayloadBound internalCertificate <=
        internalResource :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral middleCertificate
      middleResource syntaxResource hmiddleResource facts.syntaxPositive
      hlowerPairClosed htailClosed hlowerPairCode htailCode hinternalCode
  have hmodeFullResource :
      hybridFormulaStructuralPayloadBound modeFullCertificate <= modeResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral modeCertificate
      internalCertificate atomicResource internalResource syntaxResource
      hmodeResource hinternalResource facts.syntaxPositive hmodeEqClosed
      hinternalClosed hmodeEqCode hinternalCode hmodeZeroDecomposedCode
  have houter :=
    termRowsModeZeroOuterCertificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount modeResource
      branchBitBound hcount hconsumed modeFullCertificate hmodeFullResource
      henvironmentLarge
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (termRowsModeZeroOuterCertificate tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount hcount hconsumed modeFullCertificate) <= _
  simpa only [termRowsModeZeroShiftedFixedPayloadPolynomial, branchBitBound,
    syntaxResource, guardResource, rowsResource, failureResource,
    atomicResource, guardRowsResource, selectedResource, middleResource,
    internalResource, modeResource] using houter

#print axioms
  compactFormulaTransformTermOutputRowsModeZeroShiftedBranch_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroShiftedFullyFixedBounds
