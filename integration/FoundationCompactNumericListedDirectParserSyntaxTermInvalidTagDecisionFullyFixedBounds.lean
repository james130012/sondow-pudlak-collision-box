import integration.FoundationCompactNumericListedDirectParserSyntaxTermContinueTwoFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermTwoDecisionPathFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds

/-! # Fully fixed invalid-tag endpoint for the Term decision -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 650000

namespace FoundationCompactNumericListedDirectParserSyntaxTermInvalidTagDecisionFullyFixedBounds

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
open FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermContinueTwoFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermTwoSelectedFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFormulaFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

private abbrev TermHybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate termZeroValuation formula

def syntaxTermInvalidTagSelectedFullyFixedPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  let ne2Failure :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound)
      (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound)
  let ne1Tail :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound) ne2Failure
  hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound) ne1Tail

def syntaxTermInvalidTagDecisionFullyFixedPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        (syntaxTermInvalidTagSelectedFullyFixedPayloadEnvelope numericBound
          bitBound)))

private theorem binaryFormulaCode_left_length_le_or
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_length_le_or
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_left_length_le_and
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_length_le_and
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

noncomputable def syntaxTermInvalidTagFullyFixedDecisionCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hne0 : witness.tag ≠ 0)
    (hne1 : witness.tag ≠ 1)
    (hne2 : witness.tag ≠ 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    TermHybridCertificate
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  rw [syntaxTermDecisionExplicitFormula_component_alignment]
  unfold syntaxTermDecisionRightTailFormula
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeNeCertificate witness.tag 0 hne0)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeNeCertificate witness.tag 1 hne1)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeNeCertificate witness.tag 2 hne2)
          (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount hfailure)))
  exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        selectedCertificate))

theorem
    syntaxTermInvalidTagFullyFixedDecisionCertificate_structuralPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hne0 : witness.tag ≠ 0)
    (hne1 : witness.tag ≠ 1)
    (hne2 : witness.tag ≠ 2)
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
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermInvalidTagFullyFixedDecisionCertificate tokenTable width
          tokenCount current next binderArity witness hne0 hne1 hne2
          hfailure) <=
      syntaxTermInvalidTagDecisionFullyFixedPayloadEnvelope numericBound
        bitBound := by
  let ne0Formula := nativeNeFormula witness.tag 0
  let ne1Formula := nativeNeFormula witness.tag 1
  let ne2Formula := nativeNeFormula witness.tag 2
  let failureFormula :=
    compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
  let ne2FailureFormula := ne2Formula ⋏ failureFormula
  let ne1TailFormula := ne1Formula ⋏ ne2FailureFormula
  let selectedFormula := ne0Formula ⋏ ne1TailFormula
  let twoFormula :=
    syntaxTermTwoDecisionFormula tokenTable width tokenCount current next
      binderArity witness
  let twoTailFormula := twoFormula ⋎ selectedFormula
  let oneFormula :=
    syntaxTermOneDecisionFormula tokenTable width tokenCount current next
      witness
  let rightTailFormula := oneFormula ⋎ twoTailFormula
  let zeroPairFormula :=
    syntaxTermZeroPairDecisionFormula tokenTable width tokenCount current next
      binderArity witness
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  let ne0Certificate := nativeNeCertificate witness.tag 0 hne0
  let ne1Certificate := nativeNeCertificate witness.tag 1 hne1
  let ne2Certificate := nativeNeCertificate witness.tag 2 hne2
  let failureCertificate :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  let ne2FailureCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction ne2Certificate
      failureCertificate
  let ne1TailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction ne1Certificate
      ne2FailureCertificate
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction ne0Certificate
      ne1TailCertificate
  let twoTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := twoFormula) selectedCertificate
  let rightTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := oneFormula) twoTailCertificate
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hne0Resource :=
    syntaxTermNativeNeCertificate_structuralPayloadBound_le_fixed witness.tag 0
      bitBound hne0 htagSize (by omega)
  have hne1Resource :=
    syntaxTermNativeNeCertificate_structuralPayloadBound_le_fixed witness.tag 1
      bitBound hne1 htagSize (by omega)
  have hne2Resource :=
    syntaxTermNativeNeCertificate_structuralPayloadBound_le_fixed witness.tag 2
      bitBound hne2 htagSize (by omega)
  have hfailureResource :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount numericBound bitBound hfailure hwidth htokenCount
      htailCount hcurrentValue hnextValue htokenTableSize hwidthSize
      htokenCountSize hcurrentSize hnextSize htailBoundarySize hnumericSize
      hbitPositive
  have hfullRaw :=
    syntaxTermDecisionComponent_code_length_le_fixed tokenTable width
      tokenCount current next binderArity witness bitBound
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) le_rfl hsize
  have hfullCode :
      (binaryFormulaCode (zeroPairFormula ⋎ rightTailFormula)).length <=
        syntaxResource := by
    dsimp only [zeroPairFormula, rightTailFormula, oneFormula, twoTailFormula,
      twoFormula, selectedFormula, ne0Formula, ne1TailFormula, ne1Formula,
      ne2FailureFormula, ne2Formula, failureFormula, syntaxResource]
    simpa only [syntaxTermDecisionExplicitFormula_component_alignment,
      syntaxTermDecisionRightTailFormula, syntaxTermInvalidTagDecisionFormula]
      using hfullRaw
  have hzeroPairCode :
      (binaryFormulaCode zeroPairFormula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_or zeroPairFormula
      rightTailFormula).trans hfullCode
  have hrightTailCode :
      (binaryFormulaCode rightTailFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_or zeroPairFormula
      rightTailFormula).trans hfullCode
  have honeCode : (binaryFormulaCode oneFormula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_or oneFormula
      twoTailFormula).trans hrightTailCode
  have htwoTailCode :
      (binaryFormulaCode twoTailFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_or oneFormula
      twoTailFormula).trans hrightTailCode
  have htwoCode : (binaryFormulaCode twoFormula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_or twoFormula
      selectedFormula).trans htwoTailCode
  have hselectedCode :
      (binaryFormulaCode selectedFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_or twoFormula
      selectedFormula).trans htwoTailCode
  have hne0Code : (binaryFormulaCode ne0Formula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_and ne0Formula
      ne1TailFormula).trans hselectedCode
  have hne1TailCode :
      (binaryFormulaCode ne1TailFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_and ne0Formula
      ne1TailFormula).trans hselectedCode
  have hne1Code : (binaryFormulaCode ne1Formula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_and ne1Formula
      ne2FailureFormula).trans hne1TailCode
  have hne2FailureCode :
      (binaryFormulaCode ne2FailureFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_and ne1Formula
      ne2FailureFormula).trans hne1TailCode
  have hne2Code : (binaryFormulaCode ne2Formula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_and ne2Formula
      failureFormula).trans hne2FailureCode
  have hfailureCode :
      (binaryFormulaCode failureFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_and ne2Formula
      failureFormula).trans hne2FailureCode
  have hne0Closed : ne0Formula.freeVariables = ∅ :=
    syntaxTermNativeNeFormula_freeVariables_eq_empty witness.tag 0
  have hne1Closed : ne1Formula.freeVariables = ∅ :=
    syntaxTermNativeNeFormula_freeVariables_eq_empty witness.tag 1
  have hne2Closed : ne2Formula.freeVariables = ∅ :=
    syntaxTermNativeNeFormula_freeVariables_eq_empty witness.tag 2
  have hfailureClosed : failureFormula.freeVariables = ∅ := by
    dsimp only [failureFormula]
    exact syntaxTermFailureClosedFormula_freeVariables_eq_empty tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
  have hselectedClosed : selectedFormula.freeVariables = ∅ := by
    rw [show selectedFormula = ne0Formula ⋏
      (ne1Formula ⋏ (ne2Formula ⋏ failureFormula)) from rfl,
      LO.FirstOrder.Semiformula.freeVariables_and, hne0Closed,
      LO.FirstOrder.Semiformula.freeVariables_and, hne1Closed,
      LO.FirstOrder.Semiformula.freeVariables_and, hne2Closed, hfailureClosed]
    simp
  have hcontinueClosed :
      (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount 2).freeVariables = ∅ :=
    compactUnifiedParserSyntaxTermContinueTwoClosedFormula_freeVariables_eq_empty_fullyFixed
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount
  have hzeroSuccessClosed :
      (syntaxTermZeroSuccessDecisionFormula tokenTable width tokenCount current
        next binderArity witness).freeVariables = ∅ := by
    unfold syntaxTermZeroSuccessDecisionFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeEqFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermShortLtFormula_freeVariables_eq_empty, hcontinueClosed]
    simp
  have hzeroFailureClosed :
      (syntaxTermZeroFailureDecisionFormula tokenTable width tokenCount current
        next binderArity witness).freeVariables = ∅ := by
    unfold syntaxTermZeroFailureDecisionFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeEqFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermShortLeFormula_freeVariables_eq_empty,
      syntaxTermFailureClosedFormula_freeVariables_eq_empty]
    simp
  have hzeroPairClosed : zeroPairFormula.freeVariables = ∅ := by
    dsimp only [zeroPairFormula]
    unfold syntaxTermZeroPairDecisionFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_or, hzeroSuccessClosed,
      hzeroFailureClosed]
    simp
  have honeClosed : oneFormula.freeVariables = ∅ := by
    dsimp only [oneFormula]
    unfold syntaxTermOneDecisionFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeEqFormula_freeVariables_eq_empty, hcontinueClosed]
    simp
  have htwoClosed : twoFormula.freeVariables = ∅ := by
    dsimp only [twoFormula]
    exact syntaxTermTwoDecisionFormula_freeVariables_eq_empty_fullyFixed
      tokenTable width tokenCount current next binderArity witness
  have hne2Failure :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral ne2Certificate
      failureCertificate
      (parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound)
      (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound)
      syntaxResource hne2Resource hfailureResource
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hne2Closed hfailureClosed hne2Code hfailureCode hne2FailureCode
  have hne1Tail :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral ne1Certificate
      ne2FailureCertificate
      (parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound)
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource
        (parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound)
        (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound))
      syntaxResource hne1Resource hne2Failure
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hne1Closed (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hne2Closed,
          hfailureClosed]
        simp)
      hne1Code hne2FailureCode hne1TailCode
  have hselected :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral ne0Certificate
      ne1TailCertificate
      (parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound)
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource
        (parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound)
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource
          (parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound)
          (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound)))
      syntaxResource hne0Resource hne1Tail
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hne0Closed (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hne1Closed,
          LO.FirstOrder.Semiformula.freeVariables_and, hne2Closed,
          hfailureClosed]
        simp)
      hne0Code hne1TailCode hselectedCode
  have htwoTail :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (left := twoFormula) selectedCertificate
      (syntaxTermInvalidTagSelectedFullyFixedPayloadEnvelope numericBound
        bitBound)
      syntaxResource (by
        dsimp only [selectedCertificate]
        simpa only [syntaxTermInvalidTagSelectedFullyFixedPayloadEnvelope,
          syntaxResource] using hselected)
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      htwoClosed hselectedClosed htwoCode hselectedCode htwoTailCode
  have htwoTailClosed : twoTailFormula.freeVariables = ∅ := by
    rw [show twoTailFormula = twoFormula ⋎ selectedFormula from rfl,
      LO.FirstOrder.Semiformula.freeVariables_or, htwoClosed, hselectedClosed]
    simp
  have hrightTail :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (left := oneFormula) twoTailCertificate
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        (syntaxTermInvalidTagSelectedFullyFixedPayloadEnvelope numericBound
          bitBound))
      syntaxResource htwoTail
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      honeClosed htwoTailClosed honeCode htwoTailCode hrightTailCode
  have hrightTailClosed : rightTailFormula.freeVariables = ∅ := by
    rw [show rightTailFormula = oneFormula ⋎ twoTailFormula from rfl,
      LO.FirstOrder.Semiformula.freeVariables_or, honeClosed, htwoTailClosed]
    simp
  have hfull :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (left := zeroPairFormula) rightTailCertificate
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
          (syntaxTermInvalidTagSelectedFullyFixedPayloadEnvelope numericBound
            bitBound)))
      syntaxResource hrightTail
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hzeroPairClosed hrightTailClosed hzeroPairCode hrightTailCode hfullCode
  unfold syntaxTermInvalidTagFullyFixedDecisionCertificate
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := zeroPairFormula) rightTailCertificate) <= _
  simpa only [syntaxTermInvalidTagDecisionFullyFixedPayloadEnvelope,
    syntaxResource] using hfull

#print axioms
  syntaxTermInvalidTagFullyFixedDecisionCertificate_structuralPayloadBound_le

end FoundationCompactNumericListedDirectParserSyntaxTermInvalidTagDecisionFullyFixedBounds
