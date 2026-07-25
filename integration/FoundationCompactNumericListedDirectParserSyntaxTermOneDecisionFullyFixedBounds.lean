import integration.FoundationCompactNumericListedDirectParserSyntaxTermContinueTwoFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermTwoDecisionPathFixedBounds

/-! # Fully fixed Term tag-one decision endpoint -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserSyntaxTermOneDecisionFullyFixedBounds

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
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFormulaFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds

def syntaxTermOneSelectedFullyFixedPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound)
    (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
    (syntaxTermContinueTwoFullyFixedPayloadPolynomial numericBound bitBound)

def syntaxTermOneDecisionFullyFixedPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
      (syntaxTermOneSelectedFullyFixedPayloadEnvelope numericBound bitBound))

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

theorem
    compactSyntaxTermOneDecisionCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 1)
    (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 2)
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
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTermOneDecisionCertificate tokenTable width tokenCount
          current next binderArity witness htag hcontinue) <=
      syntaxTermOneDecisionFullyFixedPayloadEnvelope numericBound bitBound := by
  let selectedFormula :=
    syntaxTermOneDecisionFormula tokenTable width tokenCount current next
      witness
  let twoFormula :=
    syntaxTermTwoDecisionFormula tokenTable width tokenCount current next
      binderArity witness
  let invalidFormula :=
    syntaxTermInvalidTagDecisionFormula tokenTable width tokenCount current next
      witness
  let twoTailFormula := twoFormula ⋎ invalidFormula
  let rightTailFormula := selectedFormula ⋎ twoTailFormula
  let zeroPairFormula :=
    syntaxTermZeroPairDecisionFormula tokenTable width tokenCount current next
      binderArity witness
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  let equalityCertificate := nativeEqCertificate witness.tag 1 htag
  let continueCertificate :=
    compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount 2 hcontinue
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      equalityCertificate continueCertificate
  let rightTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := twoTailFormula) selectedCertificate
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hequalityResource :=
    syntaxTermNativeEqCertificate_structuralPayloadBound_le_fixed witness.tag 1
      bitBound htag htagSize (by omega)
  have hcontinueResource :=
    compactUnifiedParserSyntaxTermContinueTwoExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount numericBound bitBound hcontinue hwidth htokenCount
      htailCount hcurrentValue hnextValue htokenTableSize hwidthSize
      htokenCountSize hcurrentSize hnextSize htailBoundarySize hnumericSize
  have hfullRaw :=
    syntaxTermDecisionComponent_code_length_le_fixed tokenTable width
      tokenCount current next binderArity witness bitBound
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) le_rfl hsize
  have hfullCode :
      (binaryFormulaCode (zeroPairFormula ⋎ rightTailFormula)).length <=
        syntaxResource := by
    dsimp only [zeroPairFormula, rightTailFormula, selectedFormula,
      twoTailFormula, twoFormula, invalidFormula, syntaxResource]
    simpa only [syntaxTermDecisionExplicitFormula_component_alignment,
      syntaxTermDecisionRightTailFormula] using hfullRaw
  have hzeroPairCode :
      (binaryFormulaCode zeroPairFormula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_or zeroPairFormula
      rightTailFormula).trans hfullCode
  have hrightTailCode :
      (binaryFormulaCode rightTailFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_or zeroPairFormula
      rightTailFormula).trans hfullCode
  have hselectedCode :
      (binaryFormulaCode selectedFormula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_or selectedFormula
      twoTailFormula).trans hrightTailCode
  have htwoTailCode :
      (binaryFormulaCode twoTailFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_or selectedFormula
      twoTailFormula).trans hrightTailCode
  have hequalityCode :
      (binaryFormulaCode (nativeEqFormula witness.tag 1)).length <=
        syntaxResource := by
    have hraw :
        (binaryFormulaCode (nativeEqFormula witness.tag 1)).length <=
          (binaryFormulaCode selectedFormula).length := by
      dsimp only [selectedFormula]
      unfold syntaxTermOneDecisionFormula
      simp only [binaryFormulaCode, List.length_append]
      omega
    exact hraw.trans hselectedCode
  have hcontinueCode :
      (binaryFormulaCode
        (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount 2)).length <= syntaxResource := by
    have hraw :
        (binaryFormulaCode
          (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount 2)).length <=
          (binaryFormulaCode selectedFormula).length := by
      dsimp only [selectedFormula]
      unfold syntaxTermOneDecisionFormula
      simp only [binaryFormulaCode, List.length_append]
      omega
    exact hraw.trans hselectedCode
  have hcontinueClosed :
      (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount 2).freeVariables = ∅ :=
    compactUnifiedParserSyntaxTermContinueTwoClosedFormula_freeVariables_eq_empty_fullyFixed
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount
  have hselectedClosed : selectedFormula.freeVariables = ∅ := by
    dsimp only [selectedFormula]
    unfold syntaxTermOneDecisionFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeEqFormula_freeVariables_eq_empty, hcontinueClosed]
    simp
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
  have htwoClosed : twoFormula.freeVariables = ∅ := by
    dsimp only [twoFormula]
    exact syntaxTermTwoDecisionFormula_freeVariables_eq_empty_fullyFixed
      tokenTable width tokenCount current next binderArity witness
  have hinvalidClosed : invalidFormula.freeVariables = ∅ := by
    dsimp only [invalidFormula]
    unfold syntaxTermInvalidTagDecisionFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeNeFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeNeFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeNeFormula_freeVariables_eq_empty,
      syntaxTermFailureClosedFormula_freeVariables_eq_empty]
    simp
  have htwoTailClosed : twoTailFormula.freeVariables = ∅ := by
    dsimp only [twoTailFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_or, htwoClosed,
      hinvalidClosed]
    simp
  have hrightTailClosed : rightTailFormula.freeVariables = ∅ := by
    rw [show rightTailFormula = selectedFormula ⋎ twoTailFormula from rfl,
      LO.FirstOrder.Semiformula.freeVariables_or, hselectedClosed,
      htwoTailClosed]
    simp
  have hselected :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral equalityCertificate
      continueCertificate
      (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
      (syntaxTermContinueTwoFullyFixedPayloadPolynomial numericBound bitBound)
      syntaxResource hequalityResource hcontinueResource
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      (syntaxTermNativeEqFormula_freeVariables_eq_empty witness.tag 1)
      hcontinueClosed hequalityCode hcontinueCode hselectedCode
  have hrightTail :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral
      (right := twoTailFormula) selectedCertificate
      (syntaxTermOneSelectedFullyFixedPayloadEnvelope numericBound bitBound)
      syntaxResource (by
        simpa only [syntaxTermOneSelectedFullyFixedPayloadEnvelope,
          syntaxResource] using hselected)
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hselectedClosed htwoTailClosed hselectedCode htwoTailCode hrightTailCode
  have hfull :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (left := zeroPairFormula) rightTailCertificate
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        (syntaxTermOneSelectedFullyFixedPayloadEnvelope numericBound bitBound))
      syntaxResource hrightTail
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hzeroPairClosed hrightTailClosed
      hzeroPairCode hrightTailCode hfullCode
  unfold compactSyntaxTermOneDecisionCertificate
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := zeroPairFormula) rightTailCertificate) <= _
  simpa only [syntaxTermOneDecisionFullyFixedPayloadEnvelope,
    syntaxResource] using hfull

#print axioms
  compactSyntaxTermOneDecisionCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxTermOneDecisionFullyFixedBounds
