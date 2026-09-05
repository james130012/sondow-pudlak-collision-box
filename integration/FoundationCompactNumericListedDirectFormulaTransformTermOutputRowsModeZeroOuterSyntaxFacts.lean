import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOuterSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds

/-! # Reusable closed-syntax facts for the selected mode-zero outer path -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 140000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterSyntaxFacts

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOuterSyntaxFixedBounds

structure TermRowsModeZeroOuterSyntaxFacts
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount bitBound : Nat) : Prop where
  syntaxPositive : 1 <= termRowsOuterSyntaxPolynomial bitBound
  countClosed :
    (termRowsCountFormula current next consumedCount).freeVariables = ∅
  casesClosed :
    (termRowsCasesFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount).freeVariables = ∅
  countCode :
    (binaryFormulaCode (termRowsCountFormula current next consumedCount)).length <=
      termRowsOuterSyntaxPolynomial bitBound
  casesCode :
    (binaryFormulaCode
      (termRowsCasesFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount)).length <= termRowsOuterSyntaxPolynomial bitBound
  zeroCaseClosed :
    (termRowsZeroCaseFormula tokenTable width tokenCount current next
      consumedCount).freeVariables = ∅
  positiveClosed :
    (termRowsPositiveCaseFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount).freeVariables = ∅
  zeroCaseCode :
    (binaryFormulaCode
      (termRowsZeroCaseFormula tokenTable width tokenCount current next
        consumedCount)).length <= termRowsOuterSyntaxPolynomial bitBound
  positiveCode :
    (binaryFormulaCode
      (termRowsPositiveCaseFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount)).length <= termRowsOuterSyntaxPolynomial bitBound
  positiveGuardClosed :
    (nativeLeFormula (‘1’ : ValuationTerm)
      (shortBinaryNumeralTerm consumedCount)).freeVariables = ∅
  modesClosed :
    (termRowsModesFormula tokenTable width tokenCount current next mode
      binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount).freeVariables = ∅
  positiveGuardCode :
    (binaryFormulaCode
      (nativeLeFormula (‘1’ : ValuationTerm)
        (shortBinaryNumeralTerm consumedCount))).length <=
      termRowsOuterSyntaxPolynomial bitBound
  modesCode :
    (binaryFormulaCode
      (termRowsModesFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount)).length <= termRowsOuterSyntaxPolynomial bitBound
  modesDecomposedClosed :
    (termRowsModeZeroFormula tokenTable width tokenCount current next mode
        binderArity tag argument consumedCount ⋎
      (termRowsModeOneFormula tokenTable width tokenCount current next mode tag
          argument consumedCount ⋎
        (termRowsModeTwoFormula tokenTable width tokenCount current next mode
            binderArity tag argument consumedCount witnessStart witnessFinish
            witnessCount ⋎
          (termRowsModeFourFormula tokenTable width tokenCount current next mode
              tag argument consumedCount ⋎
            (termRowsModeFiveFormula tokenTable width tokenCount current next
                mode binderArity tag argument consumedCount witnessCount ⋎
              termRowsOtherFormula tokenTable width tokenCount current next mode
                consumedCount))))).freeVariables = ∅
  modesDecomposedCode :
    (binaryFormulaCode
      (termRowsModeZeroFormula tokenTable width tokenCount current next mode
          binderArity tag argument consumedCount ⋎
        (termRowsModeOneFormula tokenTable width tokenCount current next mode tag
            argument consumedCount ⋎
          (termRowsModeTwoFormula tokenTable width tokenCount current next mode
              binderArity tag argument consumedCount witnessStart witnessFinish
              witnessCount ⋎
            (termRowsModeFourFormula tokenTable width tokenCount current next mode
                tag argument consumedCount ⋎
              (termRowsModeFiveFormula tokenTable width tokenCount current next
                  mode binderArity tag argument consumedCount witnessCount ⋎
                termRowsOtherFormula tokenTable width tokenCount current next
                  mode consumedCount)))))).length <=
      termRowsOuterSyntaxPolynomial bitBound
  fullCode :
    (binaryFormulaCode
      (termRowsCountFormula current next consumedCount ⋏
        termRowsCasesFormula tokenTable width tokenCount current next mode
          binderArity tag argument consumedCount witnessStart witnessFinish
          witnessCount)).length <= termRowsOuterSyntaxPolynomial bitBound

theorem termRowsModeZeroOuterSyntaxFacts
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount bitBound : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (henvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <= bitBound) :
    TermRowsModeZeroOuterSyntaxFacts tokenTable width tokenCount current next
      mode binderArity tag argument consumedCount witnessStart witnessFinish
      witnessCount bitBound := by
  let countFormula := termRowsCountFormula current next consumedCount
  let casesFormula := termRowsCasesFormula tokenTable width tokenCount current
    next mode binderArity tag argument consumedCount witnessStart witnessFinish
    witnessCount
  let zeroCaseFormula := termRowsZeroCaseFormula tokenTable width tokenCount
    current next consumedCount
  let positiveFormula := termRowsPositiveCaseFormula tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount
  let positiveGuardFormula := nativeLeFormula (‘1’ : ValuationTerm)
    (shortBinaryNumeralTerm consumedCount)
  let modesFormula := termRowsModesFormula tokenTable width tokenCount current
    next mode binderArity tag argument consumedCount witnessStart witnessFinish
    witnessCount
  let fullFormula := countFormula ⋏ casesFormula
  have hfullAlignment :
      fullFormula =
        compactFormulaTransformTermOutputRowsExplicitFormula tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount := by
    dsimp only [fullFormula, countFormula, casesFormula]
    rw [compactFormulaTransformTermOutputRowsExplicitFormula_eq_named]
  have hfullClosed : fullFormula.freeVariables = ∅ := by
    rw [hfullAlignment]
    exact compactFormulaTransformTermOutputRowsExplicitFormula_closed tokenTable
      width tokenCount current next mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount
  have hfullCode :
      (binaryFormulaCode fullFormula).length <=
        termRowsOuterSyntaxPolynomial bitBound := by
    rw [hfullAlignment]
    exact compactFormulaTransformTermOutputRowsExplicitFormula_code_le_fixed
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount bitBound witnessStart witnessFinish witnessCount
      henvironmentSize
  have hcountClosed := termRowsConjunction_left_closed countFormula casesFormula
    hfullClosed
  have hcasesClosed := termRowsConjunction_right_closed countFormula casesFormula
    hfullClosed
  have hcountCode :=
    (termRowsConjunction_left_code_le countFormula casesFormula).trans hfullCode
  have hcasesCode :=
    (termRowsConjunction_right_code_le countFormula casesFormula).trans hfullCode
  have hcasesDecomposition : casesFormula = zeroCaseFormula ⋎ positiveFormula :=
    by rfl
  have hcasesDecomposedClosed :
      (zeroCaseFormula ⋎ positiveFormula).freeVariables = ∅ := by
    simpa only [hcasesDecomposition] using hcasesClosed
  have hcasesDecomposedCode :
      (binaryFormulaCode (zeroCaseFormula ⋎ positiveFormula)).length <=
        termRowsOuterSyntaxPolynomial bitBound := by
    simpa only [hcasesDecomposition] using hcasesCode
  have hzeroCaseClosed := termRowsDisjunction_left_closed zeroCaseFormula
    positiveFormula hcasesDecomposedClosed
  have hpositiveClosed := termRowsDisjunction_right_closed zeroCaseFormula
    positiveFormula hcasesDecomposedClosed
  have hzeroCaseCode :=
    (termRowsDisjunction_left_code_le zeroCaseFormula positiveFormula).trans
      hcasesDecomposedCode
  have hpositiveCode :=
    (termRowsDisjunction_right_code_le zeroCaseFormula positiveFormula).trans
      hcasesDecomposedCode
  have hpositiveDecomposition :
      positiveFormula = positiveGuardFormula ⋏ modesFormula := by rfl
  have hpositiveDecomposedClosed :
      (positiveGuardFormula ⋏ modesFormula).freeVariables = ∅ := by
    simpa only [hpositiveDecomposition] using hpositiveClosed
  have hpositiveDecomposedCode :
      (binaryFormulaCode (positiveGuardFormula ⋏ modesFormula)).length <=
        termRowsOuterSyntaxPolynomial bitBound := by
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
      modesFormula =
        termRowsModeZeroFormula tokenTable width tokenCount current next mode
            binderArity tag argument consumedCount ⋎
          (termRowsModeOneFormula tokenTable width tokenCount current next mode
              tag argument consumedCount ⋎
            (termRowsModeTwoFormula tokenTable width tokenCount current next mode
                binderArity tag argument consumedCount witnessStart
                witnessFinish witnessCount ⋎
              (termRowsModeFourFormula tokenTable width tokenCount current next
                  mode tag argument consumedCount ⋎
                (termRowsModeFiveFormula tokenTable width tokenCount current next
                    mode binderArity tag argument consumedCount witnessCount ⋎
                  termRowsOtherFormula tokenTable width tokenCount current next
                    mode consumedCount)))) := by rfl
  have hmodesDecomposedClosed := by
    rw [hmodesDecomposition] at hmodesClosed
    exact hmodesClosed
  have hmodesDecomposedCode := by
    rw [hmodesDecomposition] at hmodesCode
    exact hmodesCode
  exact {
    syntaxPositive := termRowsOuterSyntaxPolynomial_positive bitBound
    countClosed := by simpa only [countFormula] using hcountClosed
    casesClosed := by simpa only [casesFormula] using hcasesClosed
    countCode := by simpa only [countFormula] using hcountCode
    casesCode := by simpa only [casesFormula] using hcasesCode
    zeroCaseClosed := by simpa only [zeroCaseFormula] using hzeroCaseClosed
    positiveClosed := by simpa only [positiveFormula] using hpositiveClosed
    zeroCaseCode := by simpa only [zeroCaseFormula] using hzeroCaseCode
    positiveCode := by simpa only [positiveFormula] using hpositiveCode
    positiveGuardClosed := by
      simpa only [positiveGuardFormula] using hpositiveGuardClosed
    modesClosed := by simpa only [modesFormula] using hmodesClosed
    positiveGuardCode := by
      simpa only [positiveGuardFormula] using hpositiveGuardCode
    modesCode := by simpa only [modesFormula] using hmodesCode
    modesDecomposedClosed := hmodesDecomposedClosed
    modesDecomposedCode := hmodesDecomposedCode
    fullCode := by simpa only [fullFormula, countFormula, casesFormula] using
      hfullCode
  }

#print axioms termRowsModeZeroOuterSyntaxFacts

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroOuterSyntaxFacts
