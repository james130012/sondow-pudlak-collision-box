import integration.FoundationCompactNumericListedDirectParserSyntaxTermTwoSelectedFixedBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Fully fixed outer decision path for the selected Term tag-two branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserSyntaxTermTwoDecisionPathFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionDecisionFixedBoundsCore
open FoundationCompactNumericListedDirectParserSyntaxTermAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermTwoSelectedFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFormulaFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

private abbrev TermHybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate termZeroValuation formula

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

private theorem
    compactUnifiedParserSyntaxTermContinueTwoFormula_freeVariables_eq_empty
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat) :
    (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable
      width tokenCount current next tailBoundary tailCount 2).freeVariables =
        ∅ := by
  unfold compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    first
    | exact shortBinaryNumeralTerm_freeVariables_eq_empty _
    | exact parserFormulaFixedNumeral_freeVariables_eq_empty 2

noncomputable def syntaxTermTwoFixedDecisionPathCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (selected : TermHybridCertificate
      (syntaxTermTwoDecisionFormula tokenTable width tokenCount current next
        binderArity witness)) :
    TermHybridCertificate
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  rw [syntaxTermDecisionExplicitFormula_component_alignment]
  unfold syntaxTermDecisionRightTailFormula
  exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        selected))

theorem
    syntaxTermTwoFixedDecisionPathCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (selected : TermHybridCertificate
      (syntaxTermTwoDecisionFormula tokenTable width tokenCount current next
        binderArity witness))
    (selectedResource : Nat)
    (hselected :
      hybridFormulaStructuralPayloadBound selected <= selectedResource)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermTwoFixedDecisionPathCertificate tokenTable width tokenCount
          current next binderArity witness selected) <=
      syntaxTermTwoDecisionPathFixedPayloadEnvelope selectedResource
        bitBound := by
  let zeroPairFormula :=
    syntaxTermZeroPairDecisionFormula tokenTable width tokenCount current next
      binderArity witness
  let oneFormula :=
    syntaxTermOneDecisionFormula tokenTable width tokenCount current next
      witness
  let twoFormula :=
    syntaxTermTwoDecisionFormula tokenTable width tokenCount current next
      binderArity witness
  let invalidFormula :=
    syntaxTermInvalidTagDecisionFormula tokenTable width tokenCount current
      next witness
  let twoTailFormula := twoFormula ⋎ invalidFormula
  let rightTailFormula := oneFormula ⋎ twoTailFormula
  let fullFormula := zeroPairFormula ⋎ rightTailFormula
  let syntaxResource := syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  let twoTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := invalidFormula) selected
  let rightTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := oneFormula) twoTailCertificate
  have hpositive :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound
  have hfullCodeRaw :=
    syntaxTermDecisionComponent_code_length_le_fixed tokenTable width tokenCount
      current next binderArity witness bitBound
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) (by omega) hsize
  have hfullCode :
      (binaryFormulaCode fullFormula).length <= syntaxResource := by
    dsimp only [fullFormula, rightTailFormula, twoTailFormula, zeroPairFormula,
      oneFormula, twoFormula, invalidFormula, syntaxResource]
    simpa only [syntaxTermDecisionExplicitFormula_component_alignment,
      syntaxTermDecisionRightTailFormula] using hfullCodeRaw
  have hzeroPairCode :
      (binaryFormulaCode zeroPairFormula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_or zeroPairFormula rightTailFormula).trans
      hfullCode
  have hrightTailCode :
      (binaryFormulaCode rightTailFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_or zeroPairFormula rightTailFormula).trans
      hfullCode
  have honeCode :
      (binaryFormulaCode oneFormula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_or oneFormula twoTailFormula).trans
      hrightTailCode
  have htwoTailCode :
      (binaryFormulaCode twoTailFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_or oneFormula twoTailFormula).trans
      hrightTailCode
  have htwoCode :
      (binaryFormulaCode twoFormula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_or twoFormula invalidFormula).trans
      htwoTailCode
  have hinvalidCode :
      (binaryFormulaCode invalidFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_or twoFormula invalidFormula).trans
      htwoTailCode
  have hcontinueClosed :
      (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount 2).freeVariables = ∅ :=
    compactUnifiedParserSyntaxTermContinueTwoFormula_freeVariables_eq_empty
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
    dsimp only [rightTailFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_or, honeClosed,
      htwoTailClosed]
    simp
  have htwoTail :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral selected
      selectedResource syntaxResource hselected hpositive htwoClosed
      hinvalidClosed htwoCode hinvalidCode htwoTailCode
  have hrightTail :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      twoTailCertificate
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource selectedResource)
      syntaxResource htwoTail hpositive honeClosed htwoTailClosed honeCode
      htwoTailCode hrightTailCode
  have hfull :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      rightTailCertificate
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
          selectedResource))
      syntaxResource hrightTail hpositive hzeroPairClosed hrightTailClosed
      hzeroPairCode hrightTailCode hfullCode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := zeroPairFormula) rightTailCertificate) <= _
  simpa only [syntaxTermTwoDecisionPathFixedPayloadEnvelope, syntaxResource]
    using hfull

#print axioms
  syntaxTermTwoFixedDecisionPathCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxTermTwoDecisionPathFixedBounds
