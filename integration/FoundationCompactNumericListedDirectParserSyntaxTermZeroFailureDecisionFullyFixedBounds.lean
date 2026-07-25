import integration.FoundationCompactNumericListedDirectParserSyntaxTermContinueTwoFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermTwoDecisionPathFixedBounds

/-! # Fully fixed Term zero-failure decision endpoint -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxTermZeroFailureDecisionFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionDecisionFixedBoundsCore
open FoundationCompactNumericListedDirectParserSyntaxTermAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermContinueTwoFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermTwoSelectedFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFormulaFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

private abbrev TermHybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate termZeroValuation formula

private theorem binaryFormulaCode_right_length_le_or
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

def syntaxTermZeroFailureSelectedFullyFixedPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
    (hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (parserFormulaTermLeFixedPayloadPolynomial bitBound)
      (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound))

def syntaxTermZeroFailureDecisionFullyFixedPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
      (syntaxTermZeroFailureSelectedFullyFixedPayloadEnvelope numericBound
        bitBound))

theorem
    compactSyntaxTermZeroFailureDecisionCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 0)
    (hargument : binderArity <= witness.argument)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htailCount : witness.tailCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hargumentSize : Nat.size witness.argument <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTermZeroFailureDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hargument
          hfailure) <=
      syntaxTermZeroFailureDecisionFullyFixedPayloadEnvelope numericBound
        bitBound := by
  let equalityFormula := nativeEqFormula witness.tag 0
  let leFormula := shortLeFormula binderArity witness.argument
  let failureFormula :=
    compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
  let selectedFormula := equalityFormula ⋏ (leFormula ⋏ failureFormula)
  let zeroSuccessFormula :=
    syntaxTermZeroSuccessDecisionFormula tokenTable width tokenCount current
      next binderArity witness
  let zeroPairFormula := zeroSuccessFormula ⋎ selectedFormula
  let rightTailFormula :=
    syntaxTermDecisionRightTailFormula tokenTable width tokenCount current next
      binderArity witness
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  let equalityCertificate := nativeEqCertificate witness.tag 0 htag
  let leCertificate :=
    shortLeCertificate binderArity witness.argument hargument
  let failureCertificate :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  let leFailureCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      leCertificate failureCertificate
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      equalityCertificate leFailureCertificate
  let zeroPairCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := zeroSuccessFormula) selectedCertificate
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hequalityResource :=
    syntaxTermNativeEqCertificate_structuralPayloadBound_le_fixed witness.tag 0
      bitBound htag htagSize (by omega)
  have hleResource :=
    syntaxTermShortLeCertificate_structuralPayloadBound_le_fixed
      binderArity witness.argument bitBound hargument hbinderSize hargumentSize
  have hfailureResource :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount numericBound bitBound hfailure hwidth htokenCount
      htailCount hcurrentValue hnextValue htokenTableSize hwidthSize
      htokenCountSize hcurrentSize hnextSize htailBoundarySize hnumericSize
      hbitPositive
  have hcode (formula : ValuationFormula)
      (hsub :
        (binaryFormulaCode formula).length <=
          (binaryFormulaCode
            (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable
              width tokenCount current next binderArity witness)).length) :
      (binaryFormulaCode formula).length <= syntaxResource := by
    dsimp only [syntaxResource]
    exact syntaxTermDecisionComponent_code_length_le_fixed tokenTable width
      tokenCount current next binderArity witness bitBound formula hsub hsize
  have hequalityCode :
      (binaryFormulaCode equalityFormula).length <= syntaxResource :=
    hcode equalityFormula (by
      dsimp only [equalityFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hleCode :
      (binaryFormulaCode leFormula).length <= syntaxResource :=
    hcode leFormula (by
      dsimp only [leFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hfailureCode :
      (binaryFormulaCode failureFormula).length <= syntaxResource :=
    hcode failureFormula (by
      dsimp only [failureFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hleFailureCode :
      (binaryFormulaCode (leFormula ⋏ failureFormula)).length <=
        syntaxResource :=
    hcode (leFormula ⋏ failureFormula) (by
      dsimp only [leFormula, failureFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hselectedCode :
      (binaryFormulaCode selectedFormula).length <= syntaxResource :=
    hcode selectedFormula (by
      dsimp only [selectedFormula, equalityFormula, leFormula,
        failureFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hzeroSuccessCode :
      (binaryFormulaCode zeroSuccessFormula).length <= syntaxResource :=
    hcode zeroSuccessFormula (by
      dsimp only [zeroSuccessFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
        syntaxTermZeroSuccessDecisionFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hzeroPairCode :
      (binaryFormulaCode zeroPairFormula).length <= syntaxResource :=
    hcode zeroPairFormula (by
      dsimp only [zeroPairFormula, selectedFormula, equalityFormula,
        leFormula, failureFormula, zeroSuccessFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
        syntaxTermZeroSuccessDecisionFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hfullCode :
      (binaryFormulaCode (zeroPairFormula ⋎ rightTailFormula)).length <=
        syntaxResource := by
    have hraw := hcode
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) le_rfl
    dsimp only [zeroPairFormula, selectedFormula, equalityFormula,
      leFormula, failureFormula, zeroSuccessFormula, rightTailFormula]
    simpa only [syntaxTermDecisionExplicitFormula_component_alignment,
      syntaxTermZeroPairDecisionFormula, syntaxTermZeroSuccessDecisionFormula,
      syntaxTermZeroFailureDecisionFormula]
      using hraw
  have hrightTailCode :
      (binaryFormulaCode rightTailFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_or zeroPairFormula
      rightTailFormula).trans hfullCode
  have hequalityClosed : equalityFormula.freeVariables = ∅ :=
    syntaxTermNativeEqFormula_freeVariables_eq_empty witness.tag 0
  have hleClosed : leFormula.freeVariables = ∅ :=
    syntaxTermShortLeFormula_freeVariables_eq_empty binderArity
      witness.argument
  have hfailureClosed : failureFormula.freeVariables = ∅ := by
    dsimp only [failureFormula]
    exact
      syntaxTermFailureClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount
  have hcontinueClosed :
      (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount 2).freeVariables = ∅ :=
    compactUnifiedParserSyntaxTermContinueTwoClosedFormula_freeVariables_eq_empty_fullyFixed
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount
  have hzeroSuccessClosed : zeroSuccessFormula.freeVariables = ∅ := by
    dsimp only [zeroSuccessFormula]
    unfold syntaxTermZeroSuccessDecisionFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeEqFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermShortLtFormula_freeVariables_eq_empty, hcontinueClosed]
    simp
  have honeClosed :
      (syntaxTermOneDecisionFormula tokenTable width tokenCount current next
        witness).freeVariables = ∅ := by
    unfold syntaxTermOneDecisionFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeEqFormula_freeVariables_eq_empty, hcontinueClosed]
    simp
  have htwoClosed :
      (syntaxTermTwoDecisionFormula tokenTable width tokenCount current next
        binderArity witness).freeVariables = ∅ :=
    syntaxTermTwoDecisionFormula_freeVariables_eq_empty_fullyFixed tokenTable
      width tokenCount current next binderArity witness
  have hinvalidClosed :
      (syntaxTermInvalidTagDecisionFormula tokenTable width tokenCount current
        next witness).freeVariables = ∅ := by
    unfold syntaxTermInvalidTagDecisionFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeNeFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeNeFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeNeFormula_freeVariables_eq_empty,
      syntaxTermFailureClosedFormula_freeVariables_eq_empty]
    simp
  have hrightTailClosed : rightTailFormula.freeVariables = ∅ := by
    dsimp only [rightTailFormula]
    unfold syntaxTermDecisionRightTailFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_or, honeClosed,
      LO.FirstOrder.Semiformula.freeVariables_or, htwoClosed, hinvalidClosed]
    simp
  have hleFailure :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral leCertificate
      failureCertificate
      (parserFormulaTermLeFixedPayloadPolynomial bitBound)
      (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound)
      syntaxResource hleResource hfailureResource
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hleClosed hfailureClosed hleCode hfailureCode
      hleFailureCode
  have hselected :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral equalityCertificate
      leFailureCertificate
      (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource
        (parserFormulaTermLeFixedPayloadPolynomial bitBound)
        (syntaxTermFailureFullyFixedPayloadPolynomial numericBound
          bitBound))
      syntaxResource hequalityResource hleFailure
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hequalityClosed (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hleClosed,
          hfailureClosed]
        simp)
      hequalityCode hleFailureCode hselectedCode
  have hzeroPair :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (left := zeroSuccessFormula) selectedCertificate
      (syntaxTermZeroFailureSelectedFullyFixedPayloadEnvelope numericBound
        bitBound)
      syntaxResource (by
        simpa only [syntaxTermZeroFailureSelectedFullyFixedPayloadEnvelope,
          syntaxResource] using hselected)
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hzeroSuccessClosed (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hequalityClosed,
          LO.FirstOrder.Semiformula.freeVariables_and, hleClosed,
          hfailureClosed]
        simp)
      hzeroSuccessCode hselectedCode hzeroPairCode
  have hzeroPairClosed : zeroPairFormula.freeVariables = ∅ := by
    rw [show zeroPairFormula = zeroSuccessFormula ⋎ selectedFormula from rfl,
      LO.FirstOrder.Semiformula.freeVariables_or, hzeroSuccessClosed]
    rw [show selectedFormula = equalityFormula ⋏
      (leFormula ⋏ failureFormula) from rfl,
      LO.FirstOrder.Semiformula.freeVariables_and, hequalityClosed,
      LO.FirstOrder.Semiformula.freeVariables_and, hleClosed, hfailureClosed]
    simp
  have hfull :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral
      (right := rightTailFormula) zeroPairCertificate
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        (syntaxTermZeroFailureSelectedFullyFixedPayloadEnvelope numericBound
          bitBound))
      syntaxResource hzeroPair
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hzeroPairClosed
      hrightTailClosed hzeroPairCode hrightTailCode hfullCode
  unfold compactSyntaxTermZeroFailureDecisionCertificate
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := rightTailFormula) zeroPairCertificate) <= _
  simpa only [syntaxTermZeroFailureDecisionFullyFixedPayloadEnvelope,
    syntaxResource] using hfull

#print axioms
  compactSyntaxTermZeroFailureDecisionCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxTermZeroFailureDecisionFullyFixedBounds
