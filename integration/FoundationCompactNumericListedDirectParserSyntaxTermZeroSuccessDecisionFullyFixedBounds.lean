import integration.FoundationCompactNumericListedDirectParserSyntaxTermContinueTwoFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermTwoDecisionPathFixedBounds

/-! # Fully fixed Term zero-success decision endpoint -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxTermZeroSuccessDecisionFullyFixedBounds

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

def syntaxTermZeroSuccessSelectedFullyFixedPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
    (hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
      (syntaxTermContinueTwoFullyFixedPayloadPolynomial numericBound bitBound))

def syntaxTermZeroSuccessDecisionFullyFixedPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
      (syntaxTermZeroSuccessSelectedFullyFixedPayloadEnvelope numericBound
        bitBound))

theorem
    compactSyntaxTermZeroSuccessDecisionCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 0)
    (hargument : witness.argument < binderArity)
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
    (hargumentSize : Nat.size witness.argument <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTermZeroSuccessDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hargument
          hcontinue) <=
      syntaxTermZeroSuccessDecisionFullyFixedPayloadEnvelope numericBound
        bitBound := by
  let equalityFormula := nativeEqFormula witness.tag 0
  let strictFormula := shortLtFormula witness.argument binderArity
  let continueFormula :=
    compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount 2
  let selectedFormula := equalityFormula ⋏ (strictFormula ⋏ continueFormula)
  let zeroFailureFormula :=
    syntaxTermZeroFailureDecisionFormula tokenTable width tokenCount current
      next binderArity witness
  let zeroPairFormula := selectedFormula ⋎ zeroFailureFormula
  let rightTailFormula :=
    syntaxTermDecisionRightTailFormula tokenTable width tokenCount current next
      binderArity witness
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  let equalityCertificate := nativeEqCertificate witness.tag 0 htag
  let strictCertificate :=
    shortLtCertificate witness.argument binderArity hargument
  let continueCertificate :=
    compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount 2 hcontinue
  let strictContinueCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      strictCertificate continueCertificate
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      equalityCertificate strictContinueCertificate
  let zeroPairCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := zeroFailureFormula) selectedCertificate
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hequalityResource :=
    syntaxTermNativeEqCertificate_structuralPayloadBound_le_fixed witness.tag 0
      bitBound htag htagSize (by omega)
  have hstrictResource :=
    syntaxTermShortLtCertificate_structuralPayloadBound_le_fixed
      witness.argument binderArity bitBound hargument hargumentSize hbinderSize
  have hcontinueResource :=
    compactUnifiedParserSyntaxTermContinueTwoExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount numericBound bitBound hcontinue hwidth htokenCount
      htailCount hcurrentValue hnextValue htokenTableSize hwidthSize
      htokenCountSize hcurrentSize hnextSize htailBoundarySize hnumericSize
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
  have hstrictCode :
      (binaryFormulaCode strictFormula).length <= syntaxResource :=
    hcode strictFormula (by
      dsimp only [strictFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hcontinueCode :
      (binaryFormulaCode continueFormula).length <= syntaxResource :=
    hcode continueFormula (by
      dsimp only [continueFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hstrictContinueCode :
      (binaryFormulaCode (strictFormula ⋏ continueFormula)).length <=
        syntaxResource :=
    hcode (strictFormula ⋏ continueFormula) (by
      dsimp only [strictFormula, continueFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hselectedCode :
      (binaryFormulaCode selectedFormula).length <= syntaxResource :=
    hcode selectedFormula (by
      dsimp only [selectedFormula, equalityFormula, strictFormula,
        continueFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hzeroFailureCode :
      (binaryFormulaCode zeroFailureFormula).length <= syntaxResource :=
    hcode zeroFailureFormula (by
      dsimp only [zeroFailureFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
        syntaxTermZeroFailureDecisionFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hzeroPairCode :
      (binaryFormulaCode zeroPairFormula).length <= syntaxResource :=
    hcode zeroPairFormula (by
      dsimp only [zeroPairFormula, selectedFormula, equalityFormula,
        strictFormula, continueFormula, zeroFailureFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
        syntaxTermZeroFailureDecisionFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hfullCode :
      (binaryFormulaCode (zeroPairFormula ⋎ rightTailFormula)).length <=
        syntaxResource := by
    have hraw := hcode
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) le_rfl
    dsimp only [zeroPairFormula, selectedFormula, equalityFormula,
      strictFormula, continueFormula, zeroFailureFormula, rightTailFormula]
    simpa only [syntaxTermDecisionExplicitFormula_component_alignment,
      syntaxTermZeroPairDecisionFormula, syntaxTermZeroSuccessDecisionFormula]
      using hraw
  have hrightTailCode :
      (binaryFormulaCode rightTailFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_or zeroPairFormula
      rightTailFormula).trans hfullCode
  have hequalityClosed : equalityFormula.freeVariables = ∅ :=
    syntaxTermNativeEqFormula_freeVariables_eq_empty witness.tag 0
  have hstrictClosed : strictFormula.freeVariables = ∅ :=
    syntaxTermShortLtFormula_freeVariables_eq_empty witness.argument
      binderArity
  have hcontinueClosed : continueFormula.freeVariables = ∅ := by
    dsimp only [continueFormula]
    exact
      compactUnifiedParserSyntaxTermContinueTwoClosedFormula_freeVariables_eq_empty_fullyFixed
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount
  have hzeroFailureClosed : zeroFailureFormula.freeVariables = ∅ := by
    dsimp only [zeroFailureFormula]
    unfold syntaxTermZeroFailureDecisionFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeEqFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermShortLeFormula_freeVariables_eq_empty,
      syntaxTermFailureClosedFormula_freeVariables_eq_empty]
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
  have hstrictContinue :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral strictCertificate
      continueCertificate
      (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
      (syntaxTermContinueTwoFullyFixedPayloadPolynomial numericBound bitBound)
      syntaxResource hstrictResource hcontinueResource
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hstrictClosed hcontinueClosed hstrictCode hcontinueCode
      hstrictContinueCode
  have hselected :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral equalityCertificate
      strictContinueCertificate
      (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource
        (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
        (syntaxTermContinueTwoFullyFixedPayloadPolynomial numericBound
          bitBound))
      syntaxResource hequalityResource hstrictContinue
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hequalityClosed (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hstrictClosed,
          hcontinueClosed]
        simp)
      hequalityCode hstrictContinueCode hselectedCode
  have hzeroPair :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral
      (right := zeroFailureFormula) selectedCertificate
      (syntaxTermZeroSuccessSelectedFullyFixedPayloadEnvelope numericBound
        bitBound)
      syntaxResource (by
        simpa only [syntaxTermZeroSuccessSelectedFullyFixedPayloadEnvelope,
          syntaxResource] using hselected)
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hequalityClosed,
          LO.FirstOrder.Semiformula.freeVariables_and, hstrictClosed,
          hcontinueClosed]
        simp)
      hzeroFailureClosed hselectedCode hzeroFailureCode hzeroPairCode
  have hfull :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral
      (right := rightTailFormula) zeroPairCertificate
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        (syntaxTermZeroSuccessSelectedFullyFixedPayloadEnvelope numericBound
          bitBound))
      syntaxResource hzeroPair
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      (by
        rw [LO.FirstOrder.Semiformula.freeVariables_or,
          LO.FirstOrder.Semiformula.freeVariables_and, hequalityClosed,
          LO.FirstOrder.Semiformula.freeVariables_and, hstrictClosed,
          hcontinueClosed, hzeroFailureClosed]
        simp)
      hrightTailClosed hzeroPairCode hrightTailCode hfullCode
  unfold compactSyntaxTermZeroSuccessDecisionCertificate
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := rightTailFormula) zeroPairCertificate) <= _
  simpa only [syntaxTermZeroSuccessDecisionFullyFixedPayloadEnvelope,
    syntaxResource] using hfull

#print axioms
  compactSyntaxTermZeroSuccessDecisionCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxTermZeroSuccessDecisionFullyFixedBounds
