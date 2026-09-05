import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPositiveOuterFixedCore
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAppendShiftedFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsZeroOneGuardFixedBounds
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds

/-! # Fully fixed shifted branch under term-output mode one -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeOneShiftedFullyFixedBounds

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
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAppendShiftedFullyFixedBounds
open FoundationCompactNumericListedDirectNatListAppendTwoValuesFormulaFixedBounds
open FoundationCompactNumericListedDirectNatListAppendTwoValuesFullyFixedBounds

private abbrev modeOneShiftedValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsModeOneShiftedFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let branchBitBound := termRowsShiftedBitBound bitBound
  let syntaxResource := termRowsOuterSyntaxPolynomial branchBitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termRowsTwoGuardFixedPayloadPolynomial branchBitBound)
    (appendTwoFullyFixedPayloadPolynomial numericBound branchBitBound)
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope
    syntaxResource selectedResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (termRowsPositiveAtomicFixedPayloadPolynomial branchBitBound)
    internalResource
  let modesResource := sixRightDisjunctionPathOnePayloadEnvelope syntaxResource
    modeResource
  termRowsPositiveOuterFixedPayloadPolynomial modesResource branchBitBound

theorem
    compactFormulaTransformTermOutputRowsModeOneShiftedBranch_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 1)
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
          (.modeOneShifted hcount hconsumed hmode hguard hrows)) <=
      termRowsModeOneShiftedFixedPayloadPolynomial numericBound bitBound := by
  let branchBitBound := termRowsShiftedBitBound bitBound
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
    (‘1’ : ValuationTerm)
  let guardFormula := termRowsGuardOneTagFormula consumedCount tag
  let shiftedTerm := nativeAddTerm (shortBinaryNumeralTerm argument)
    (‘1’ : ValuationTerm)
  let rowsFormula := termRowsAppendTwoShiftedFormula tokenTable width tokenCount
    current next argument
  let selectedFormula := guardFormula ⋏ rowsFormula
  let rawFormula :=
    doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) ⋏
      termRowsRawPrefixFormula tokenTable width tokenCount current next
        consumedCount
  let internalFormula := selectedFormula ⋎ rawFormula
  let guardResource := termRowsTwoGuardFixedPayloadPolynomial branchBitBound
  let rowsResource := appendTwoFullyFixedPayloadPolynomial numericBound
    branchBitBound
  let atomicResource := termRowsPositiveAtomicFixedPayloadPolynomial
    branchBitBound
  let selectedResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource guardResource rowsResource
  let internalResource := hybridDisjunctionGeneralPayloadEnvelope
    syntaxResource selectedResource
  let modeResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource internalResource
  let modesResource := sixRightDisjunctionPathOnePayloadEnvelope syntaxResource
    modeResource
  have henvironmentLarge : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <=
        branchBitBound := by
    intro coordinate
    exact (henvironmentSize coordinate).trans (by
      unfold branchBitBound termRowsShiftedBitBound
      omega)
  have facts := termRowsModeZeroOuterSyntaxFacts tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount branchBitBound
    witnessStart witnessFinish witnessCount henvironmentLarge
  have htailClosed := termRowsDisjunction_right_closed modeZeroFormula
    (modeOneFormula ⋎ (modeTwoFormula ⋎
      (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))))
    facts.modesDecomposedClosed
  have htailCode :=
    (termRowsDisjunction_right_code_le modeZeroFormula
      (modeOneFormula ⋎ (modeTwoFormula ⋎
        (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula))))).trans
      facts.modesDecomposedCode
  have hmodeOneClosed := termRowsDisjunction_left_closed modeOneFormula
    (modeTwoFormula ⋎ (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula)))
    htailClosed
  have hrestClosed := termRowsDisjunction_right_closed modeOneFormula
    (modeTwoFormula ⋎ (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula)))
    htailClosed
  have hmodeOneCode :=
    (termRowsDisjunction_left_code_le modeOneFormula
      (modeTwoFormula ⋎ (modeFourFormula ⋎
        (modeFiveFormula ⋎ otherFormula)))).trans htailCode
  have hrestCode :=
    (termRowsDisjunction_right_code_le modeOneFormula
      (modeTwoFormula ⋎ (modeFourFormula ⋎
        (modeFiveFormula ⋎ otherFormula)))).trans htailCode
  have hmodeOneDecomposition :
      modeOneFormula = modeEqFormula ⋏ internalFormula := by
    dsimp only [modeOneFormula, modeEqFormula, internalFormula,
      selectedFormula, guardFormula, rowsFormula, rawFormula]
    unfold termRowsModeOneFormula
    rfl
  have hmodeOneDecomposedClosed :
      (modeEqFormula ⋏ internalFormula).freeVariables = ∅ := by
    simpa only [hmodeOneDecomposition] using hmodeOneClosed
  have hmodeOneDecomposedCode :
      (binaryFormulaCode (modeEqFormula ⋏ internalFormula)).length <=
        syntaxResource := by
    simpa only [hmodeOneDecomposition] using hmodeOneCode
  have hmodeEqClosed := termRowsConjunction_left_closed modeEqFormula
    internalFormula hmodeOneDecomposedClosed
  have hinternalClosed := termRowsConjunction_right_closed modeEqFormula
    internalFormula hmodeOneDecomposedClosed
  have hmodeEqCode :=
    (termRowsConjunction_left_code_le modeEqFormula internalFormula).trans
      hmodeOneDecomposedCode
  have hinternalCode :=
    (termRowsConjunction_right_code_le modeEqFormula internalFormula).trans
      hmodeOneDecomposedCode
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
  have hmodeSize : Nat.size mode <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (25 : Fin 33)
  have htagSize : Nat.size tag <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (27 : Fin 33)
  have hconsumedSize : Nat.size consumedCount <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (29 : Fin 33)
  let modeCertificate := shortNumeralLiteralEqCertificate mode 1
    (‘1’ : ValuationTerm) (termValue_arithmeticOne modeOneShiftedValuation)
    hmode
  let guardCertificate := oneTagGuardCertificate consumedCount tag hguard
  let rowsCertificate :=
    FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 1 (argument + 1) (‘1’ : ValuationTerm) shiftedTerm
      (termValue_arithmeticOne modeOneShiftedValuation)
      (by
        simp [shiftedTerm, nativeAddTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne, termValue_shortBinaryNumeralTerm]) hrows
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      guardCertificate rowsCertificate
  let internalCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := rawFormula) selectedCertificate
  let modeFullCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction modeCertificate
      internalCertificate
  let selectedPathCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := modeTwoFormula ⋎
        (modeFourFormula ⋎ (modeFiveFormula ⋎ otherFormula)))
      modeFullCertificate
  let modesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := modeZeroFormula) selectedPathCertificate
  have hmodeResource :
      hybridFormulaStructuralPayloadBound modeCertificate <= atomicResource :=
    shortNumeralLiteralEqCertificate_structuralPayloadBound_le_fixed mode 1
      (‘1’ : ValuationTerm) (termValue_arithmeticOne modeOneShiftedValuation)
      hmode branchBitBound hmodeSize
      (termRowsLiteral_closed (‘1’ : ValuationTerm) (Or.inr (Or.inl rfl)))
      (termRowsLiteralCode_le (‘1’ : ValuationTerm) branchBitBound
        (Or.inr (Or.inl rfl)))
  have hguardResource :
      hybridFormulaStructuralPayloadBound guardCertificate <= guardResource :=
    oneTagGuardCertificate_structuralPayloadBound_le_fixed consumedCount tag
      branchBitBound hguard hconsumedSize htagSize
  have hrowsResource :
      hybridFormulaStructuralPayloadBound rowsCertificate <= rowsResource := by
    exact termRowsAppendTwoShiftedCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount numericBound bitBound
      hrows henvironmentSize hwidthBound htokenCountBound hnextOutputCountBound
      hnumericSize
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
      hinternalClosed hmodeEqCode hinternalCode hmodeOneDecomposedCode
  have hmodesResource :
      hybridFormulaStructuralPayloadBound modesCertificate <= modesResource :=
    sixRightDisjunctionPathOnePayloadBound_le_closedGeneral modeZeroFormula
      modeOneFormula modeTwoFormula modeFourFormula modeFiveFormula otherFormula
      modeFullCertificate modeResource syntaxResource hmodeFullResource
      facts.syntaxPositive facts.modesDecomposedClosed facts.modesDecomposedCode
  have houter := termRowsPositiveOuterCertificate_structuralPayloadBound_le_fixed
    tokenTable width tokenCount current next mode binderArity tag argument
    consumedCount witnessStart witnessFinish witnessCount modesResource
    branchBitBound hcount hconsumed modesCertificate hmodesResource
    henvironmentLarge
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (termRowsPositiveOuterCertificate tokenTable width tokenCount current next
        mode binderArity tag argument consumedCount witnessStart witnessFinish
        witnessCount hcount hconsumed modesCertificate) <= _
  simpa only [termRowsModeOneShiftedFixedPayloadPolynomial, branchBitBound,
    syntaxResource, guardResource, rowsResource, atomicResource,
    selectedResource, internalResource, modeResource, modesResource] using houter

#print axioms
  compactFormulaTransformTermOutputRowsModeOneShiftedBranch_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeOneShiftedFullyFixedBounds
