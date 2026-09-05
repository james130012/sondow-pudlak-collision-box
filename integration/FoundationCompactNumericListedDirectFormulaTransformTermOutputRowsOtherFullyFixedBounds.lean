import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPositiveOuterFixedCore
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixFullyFixedBounds
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds

/-! # Fully fixed fallback branch for all other term-output modes -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 240000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOtherFullyFixedBounds

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
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOuterSyntaxFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterSyntaxFacts
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPositiveOuterFixedCore
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixFullyFixedBounds

private abbrev otherBranchValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsOtherFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource := termRowsOuterSyntaxPolynomial bitBound
  let atomResource := termRowsNegativeAtomicFixedPayloadPolynomial bitBound
  let rowsResource := appendSourcePrefixFullyFixedPayloadPolynomial numericBound
    bitBound
  let fiveResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomResource rowsResource
  let fourResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomResource fiveResource
  let twoResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomResource fourResource
  let oneResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomResource twoResource
  let otherResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomResource oneResource
  let modesResource := sixRightDisjunctionPathFivePayloadEnvelope syntaxResource
    otherResource
  termRowsPositiveOuterFixedPayloadPolynomial modesResource bitBound

theorem
    compactFormulaTransformTermOutputRowsOtherBranch_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hzero : mode ≠ 0) (hone : mode ≠ 1) (htwo : mode ≠ 2)
    (hfour : mode ≠ 4) (hfive : mode ≠ 5)
    (hrows : CompactFormulaTransformOutputRawPrefixRows tokenTable width
      tokenCount current next consumedCount)
    (henvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount
          (.other hcount hconsumed hzero hone htwo hfour hfive hrows)) <=
      termRowsOtherFixedPayloadPolynomial numericBound bitBound := by
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
  let rowsFormula := termRowsRawPrefixFormula tokenTable width tokenCount
    current next consumedCount
  let otherFormula := termRowsOtherFormula tokenTable width tokenCount current
    next mode consumedCount
  let modeTerm := shortBinaryNumeralTerm mode
  let zeroFormula := nativeNeFormula modeTerm (‘0’ : ValuationTerm)
  let oneFormula := nativeNeFormula modeTerm (‘1’ : ValuationTerm)
  let twoFormula := nativeNeFormula modeTerm (‘2’ : ValuationTerm)
  let fourFormula := nativeNeFormula modeTerm (‘4’ : ValuationTerm)
  let fiveFormula := nativeNeFormula modeTerm (‘5’ : ValuationTerm)
  let fiveTailFormula := fiveFormula ⋏ rowsFormula
  let fourTailFormula := fourFormula ⋏ fiveTailFormula
  let twoTailFormula := twoFormula ⋏ fourTailFormula
  let oneTailFormula := oneFormula ⋏ twoTailFormula
  let atomResource := termRowsNegativeAtomicFixedPayloadPolynomial bitBound
  let rowsResource := appendSourcePrefixFullyFixedPayloadPolynomial numericBound
    bitBound
  let fiveResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomResource rowsResource
  let fourResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomResource fiveResource
  let twoResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomResource fourResource
  let oneResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomResource twoResource
  let otherResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomResource oneResource
  let modesResource := sixRightDisjunctionPathFivePayloadEnvelope syntaxResource
    otherResource
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
  have htailFourClosed := termRowsDisjunction_right_closed modeFourFormula
    (modeFiveFormula ⋎ otherFormula) htailThreeClosed
  have htailFourCode :=
    (termRowsDisjunction_right_code_le modeFourFormula
      (modeFiveFormula ⋎ otherFormula)).trans htailThreeCode
  have hotherClosed := termRowsDisjunction_right_closed modeFiveFormula
    otherFormula htailFourClosed
  have hotherCode :=
    (termRowsDisjunction_right_code_le modeFiveFormula otherFormula).trans
      htailFourCode
  have hotherAlignment :
      otherFormula = zeroFormula ⋏ oneTailFormula := by
    dsimp only [otherFormula, zeroFormula, oneTailFormula, oneFormula,
      twoTailFormula, twoFormula, fourTailFormula, fourFormula,
      fiveTailFormula, fiveFormula, rowsFormula, modeTerm]
    unfold termRowsOtherFormula otherModesWithTailFormula
    rfl
  have hotherDecomposedClosed :
      (zeroFormula ⋏ oneTailFormula).freeVariables = ∅ := by
    simpa only [hotherAlignment] using hotherClosed
  have hotherDecomposedCode :
      (binaryFormulaCode (zeroFormula ⋏ oneTailFormula)).length <=
        syntaxResource := by
    simpa only [hotherAlignment] using hotherCode
  have hzeroClosed := termRowsConjunction_left_closed zeroFormula oneTailFormula
    hotherDecomposedClosed
  have honeTailClosed := termRowsConjunction_right_closed zeroFormula
    oneTailFormula hotherDecomposedClosed
  have hzeroCode :=
    (termRowsConjunction_left_code_le zeroFormula oneTailFormula).trans
      hotherDecomposedCode
  have honeTailCode :=
    (termRowsConjunction_right_code_le zeroFormula oneTailFormula).trans
      hotherDecomposedCode
  have honeClosed := termRowsConjunction_left_closed oneFormula twoTailFormula
    honeTailClosed
  have htwoTailClosed := termRowsConjunction_right_closed oneFormula
    twoTailFormula honeTailClosed
  have honeCode :=
    (termRowsConjunction_left_code_le oneFormula twoTailFormula).trans
      honeTailCode
  have htwoTailCode :=
    (termRowsConjunction_right_code_le oneFormula twoTailFormula).trans
      honeTailCode
  have htwoClosed := termRowsConjunction_left_closed twoFormula fourTailFormula
    htwoTailClosed
  have hfourTailClosed := termRowsConjunction_right_closed twoFormula
    fourTailFormula htwoTailClosed
  have htwoCode :=
    (termRowsConjunction_left_code_le twoFormula fourTailFormula).trans
      htwoTailCode
  have hfourTailCode :=
    (termRowsConjunction_right_code_le twoFormula fourTailFormula).trans
      htwoTailCode
  have hfourClosed := termRowsConjunction_left_closed fourFormula
    fiveTailFormula hfourTailClosed
  have hfiveTailClosed := termRowsConjunction_right_closed fourFormula
    fiveTailFormula hfourTailClosed
  have hfourCode :=
    (termRowsConjunction_left_code_le fourFormula fiveTailFormula).trans
      hfourTailCode
  have hfiveTailCode :=
    (termRowsConjunction_right_code_le fourFormula fiveTailFormula).trans
      hfourTailCode
  have hfiveClosed := termRowsConjunction_left_closed fiveFormula rowsFormula
    hfiveTailClosed
  have hrowsClosed := termRowsConjunction_right_closed fiveFormula rowsFormula
    hfiveTailClosed
  have hfiveCode :=
    (termRowsConjunction_left_code_le fiveFormula rowsFormula).trans
      hfiveTailCode
  have hrowsCode :=
    (termRowsConjunction_right_code_le fiveFormula rowsFormula).trans
      hfiveTailCode
  have htableSize : Nat.size tokenTable <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (0 : Fin 33)
  have hwidthSize : Nat.size width <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (1 : Fin 33)
  have htokenCountSize : Nat.size tokenCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (2 : Fin 33)
  have hcurrentStartSize : Nat.size current.start <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (3 : Fin 33)
  have hcurrentFinishSize : Nat.size current.finish <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (4 : Fin 33)
  have hcurrentParserFinishSize : Nat.size current.parserFinish <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (5 : Fin 33)
  have hcurrentParserTokensFinishSize : Nat.size current.parserTokensFinish <=
      bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (6 : Fin 33)
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
  have hnextOutputCountSize : Nat.size next.outputCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (24 : Fin 33)
  have hmodeSize : Nat.size mode <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (25 : Fin 33)
  have hconsumedSize : Nat.size consumedCount <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (29 : Fin 33)
  let zeroCertificate := shortNumeralLiteralNeCertificate mode 0
    (‘0’ : ValuationTerm) (termValue_arithmeticZero otherBranchValuation) hzero
  let oneCertificate := shortNumeralLiteralNeCertificate mode 1
    (‘1’ : ValuationTerm) (termValue_arithmeticOne otherBranchValuation) hone
  let twoCertificate := shortNumeralLiteralNeCertificate mode 2
    (‘2’ : ValuationTerm) (termValue_arithmeticTwo otherBranchValuation) htwo
  let fourCertificate := shortNumeralLiteralNeCertificate mode 4
    (‘4’ : ValuationTerm) (termValue_arithmeticFour otherBranchValuation) hfour
  let fiveCertificate := shortNumeralLiteralNeCertificate mode 5
    (‘5’ : ValuationTerm) (termValue_arithmeticFive otherBranchValuation) hfive
  let rowsCertificate :=
    compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hrows
  let fiveTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction fiveCertificate
      rowsCertificate
  let fourTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction fourCertificate
      fiveTailCertificate
  let twoTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction twoCertificate
      fourTailCertificate
  let oneTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction oneCertificate
      twoTailCertificate
  let otherCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction zeroCertificate
      oneTailCertificate
  let tailFourCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := modeFiveFormula) otherCertificate
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
  have hzeroResource :
      hybridFormulaStructuralPayloadBound zeroCertificate <= atomResource :=
    shortNumeralLiteralNeCertificate_structuralPayloadBound_le_fixed mode 0
      (‘0’ : ValuationTerm) (termValue_arithmeticZero otherBranchValuation)
      hzero bitBound hmodeSize
      (termRowsLiteral_closed (‘0’ : ValuationTerm) (Or.inl rfl))
      (termRowsLiteralCode_le (‘0’ : ValuationTerm) bitBound (Or.inl rfl))
  have honeResource :
      hybridFormulaStructuralPayloadBound oneCertificate <= atomResource :=
    shortNumeralLiteralNeCertificate_structuralPayloadBound_le_fixed mode 1
      (‘1’ : ValuationTerm) (termValue_arithmeticOne otherBranchValuation)
      hone bitBound hmodeSize
      (termRowsLiteral_closed (‘1’ : ValuationTerm) (Or.inr (Or.inl rfl)))
      (termRowsLiteralCode_le (‘1’ : ValuationTerm) bitBound
        (Or.inr (Or.inl rfl)))
  have htwoResource :
      hybridFormulaStructuralPayloadBound twoCertificate <= atomResource :=
    shortNumeralLiteralNeCertificate_structuralPayloadBound_le_fixed mode 2
      (‘2’ : ValuationTerm) (termValue_arithmeticTwo otherBranchValuation)
      htwo bitBound hmodeSize
      (termRowsLiteral_closed (‘2’ : ValuationTerm)
        (Or.inr (Or.inr (Or.inl rfl))))
      (termRowsLiteralCode_le (‘2’ : ValuationTerm) bitBound
        (Or.inr (Or.inr (Or.inl rfl))))
  have hfourResource :
      hybridFormulaStructuralPayloadBound fourCertificate <= atomResource :=
    shortNumeralLiteralNeCertificate_structuralPayloadBound_le_fixed mode 4
      (‘4’ : ValuationTerm) (termValue_arithmeticFour otherBranchValuation)
      hfour bitBound hmodeSize
      (termRowsLiteral_closed (‘4’ : ValuationTerm)
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (termRowsLiteralCode_le (‘4’ : ValuationTerm) bitBound
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hfiveResource :
      hybridFormulaStructuralPayloadBound fiveCertificate <= atomResource :=
    shortNumeralLiteralNeCertificate_structuralPayloadBound_le_fixed mode 5
      (‘5’ : ValuationTerm) (termValue_arithmeticFive otherBranchValuation)
      hfive bitBound hmodeSize
      (termRowsLiteral_closed (‘5’ : ValuationTerm)
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      (termRowsLiteralCode_le (‘5’ : ValuationTerm) bitBound
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have hrowsTransparent :=
    compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount hrows
  have hrowsFixed :=
    compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount numericBound bitBound hrows htableSize hwidthSize
      htokenCountSize hcurrentParserFinishSize hcurrentFinishSize
      hcurrentOutputCountSize hcurrentStartSize hcurrentParserTokensFinishSize
      hcurrentParserTokensCountSize hconsumedSize hnextParserFinishSize
      hnextFinishSize hnextOutputCountSize hwidthBound htokenCountBound
      hnumericSize
  have hrowsResource :
      hybridFormulaStructuralPayloadBound rowsCertificate <= rowsResource :=
    hrowsTransparent.trans hrowsFixed
  have hfiveTailResource :
      hybridFormulaStructuralPayloadBound fiveTailCertificate <= fiveResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral fiveCertificate
      rowsCertificate atomResource rowsResource syntaxResource hfiveResource
      hrowsResource facts.syntaxPositive hfiveClosed hrowsClosed hfiveCode
      hrowsCode hfiveTailCode
  have hfourTailResource :
      hybridFormulaStructuralPayloadBound fourTailCertificate <= fourResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral fourCertificate
      fiveTailCertificate atomResource fiveResource syntaxResource
      hfourResource hfiveTailResource facts.syntaxPositive hfourClosed
      hfiveTailClosed hfourCode hfiveTailCode hfourTailCode
  have htwoTailResource :
      hybridFormulaStructuralPayloadBound twoTailCertificate <= twoResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral twoCertificate
      fourTailCertificate atomResource fourResource syntaxResource
      htwoResource hfourTailResource facts.syntaxPositive htwoClosed
      hfourTailClosed htwoCode hfourTailCode htwoTailCode
  have honeTailResource :
      hybridFormulaStructuralPayloadBound oneTailCertificate <= oneResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral oneCertificate
      twoTailCertificate atomResource twoResource syntaxResource honeResource
      htwoTailResource facts.syntaxPositive honeClosed htwoTailClosed honeCode
      htwoTailCode honeTailCode
  have hotherResource :
      hybridFormulaStructuralPayloadBound otherCertificate <= otherResource :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral zeroCertificate
      oneTailCertificate atomResource oneResource syntaxResource hzeroResource
      honeTailResource facts.syntaxPositive hzeroClosed honeTailClosed hzeroCode
      honeTailCode hotherDecomposedCode
  have hmodesResource :
      hybridFormulaStructuralPayloadBound modesCertificate <= modesResource :=
    sixRightDisjunctionPathFivePayloadBound_le_closedGeneral modeZeroFormula
      modeOneFormula modeTwoFormula modeFourFormula modeFiveFormula otherFormula
      otherCertificate otherResource syntaxResource hotherResource
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
  simpa only [termRowsOtherFixedPayloadPolynomial, syntaxResource, atomResource,
    rowsResource, fiveResource, fourResource, twoResource, oneResource,
    otherResource, modesResource] using houter

#print axioms
  compactFormulaTransformTermOutputRowsOtherBranch_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOtherFullyFixedBounds
