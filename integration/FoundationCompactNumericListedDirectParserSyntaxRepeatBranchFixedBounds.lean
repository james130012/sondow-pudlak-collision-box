import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatZeroBranchFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatPositiveBranchFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatFormulaSyntaxFixedBounds
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds

/-! # Fully fixed selected branch certificates for Repeat -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatBranchFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatZeroBranchFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatPositiveBranchCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatPositiveBranchFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows

private abbrev repeatZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate.zeroValuation

def repeatSelectedBranchPayloadEnvelope
    (bitBound childResource : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (compactUnifiedParserSyntaxRepeatFormulaSyntaxFixedPolynomial bitBound +
      childResource + 1)
    childResource

def repeatZeroBranchFormula
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) : ValuationFormula :=
  nativeEqFormula repeatCount 0 ⋏
    compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable width
      tokenCount witness.tailBoundary witness.tailCount next.tasksBoundary
      next.tasksCount

def repeatPositiveBranchFormula
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) : ValuationFormula :=
  nativeSuccessorEqFormula repeatCount witness.decrementedCount ⋏
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable
        width tokenCount next.tasksBoundary next.tasksCount witness.tailBoundary
        witness.tailCount 2 ⋏
      (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
          tokenCount next.tasksBoundary next.tasksCount (fixedNumeralTerm 0)
          (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
          (fixedNumeralTerm 0) ⋏
        compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
          tokenCount next.tasksBoundary next.tasksCount (fixedNumeralTerm 1)
          (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm witness.decrementedCount)))

theorem repeatBranchExplicitFormula_alignment
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) :
    compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width
        tokenCount next binderArity repeatCount witness =
      repeatZeroBranchFormula tokenTable width tokenCount next repeatCount
          witness ⋎
        repeatPositiveBranchFormula tokenTable width tokenCount next binderArity
          repeatCount witness := rfl

private theorem binaryFormulaCode_fiveConjunction_last_le
    (first second third fourth fifth : ValuationFormula) :
    (binaryFormulaCode fifth).length <=
      (binaryFormulaCode
        (first ⋏ (second ⋏ (third ⋏ (fourth ⋏ fifth))))).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_or_left_le
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_or_right_le
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem repeatBranchFormula_code_length_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (bitBound : Nat)
    (hsize : forall coordinate : Fin 25,
      Nat.size
        (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable width
          tokenCount current next binderArity repeatCount witness coordinate) <=
        bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width
        tokenCount next binderArity repeatCount witness)).length <=
      compactUnifiedParserSyntaxRepeatFormulaSyntaxFixedPolynomial bitBound := by
  have hfull :=
    compactUnifiedParserSyntaxRepeatExplicitFormula_code_length_le_fixed
      tokenTable width tokenCount current next binderArity repeatCount witness
      bitBound hsize
  have hbranchSub :
      (binaryFormulaCode
        (compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width
          tokenCount next binderArity repeatCount witness)).length <=
        (binaryFormulaCode
          (compactUnifiedParserSyntaxRepeatExplicitFormula tokenTable width
            tokenCount current next binderArity repeatCount witness)).length := by
    change
      (binaryFormulaCode
        (compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width
          tokenCount next binderArity repeatCount witness)).length <=
      (binaryFormulaCode
        (_ ⋏ (_ ⋏ (_ ⋏ (_ ⋏
          compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable
            width tokenCount next binderArity repeatCount witness))))).length
    exact binaryFormulaCode_fiveConjunction_last_le _ _ _ _ _
  exact hbranchSub.trans hfull

theorem repeatZeroSelectedBranchCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hrepeatZero : repeatCount = 0)
    (hsame : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      witness.tailBoundary witness.tailCount next.tasksBoundary
      next.tasksCount)
    (hsize : forall coordinate : Fin 25,
      Nat.size
        (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable width
          tokenCount current next binderArity repeatCount witness coordinate) <=
        bitBound)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htailCountValue : witness.tailCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (htasksBoundarySize : Nat.size next.tasksBoundary <= bitBound)
    (hrepeatSize : Nat.size repeatCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := repeatPositiveBranchFormula tokenTable width tokenCount next
            binderArity repeatCount witness)
          (repeatZeroBranchCertificate tokenTable width tokenCount next
            repeatCount witness hrepeatZero hsame)) <=
      repeatSelectedBranchPayloadEnvelope bitBound
        (repeatZeroBranchPayloadEnvelope numericBound bitBound) := by
  let child :=
    repeatZeroBranchCertificate tokenTable width tokenCount next repeatCount
      witness hrepeatZero hsame
  have hchild :=
    repeatZeroBranchCertificate_structuralPayloadBound_le_fixed tokenTable
      width tokenCount next repeatCount witness numericBound bitBound
      hrepeatZero hsame hwidthValue htokenCountValue htailCountValue htableSize
      htailBoundarySize htasksBoundarySize hrepeatSize hnumericSize
  let syntaxResource :=
    compactUnifiedParserSyntaxRepeatFormulaSyntaxFixedPolynomial bitBound +
      repeatZeroBranchPayloadEnvelope numericBound bitBound + 1
  have hbranchCode :=
    repeatBranchFormula_code_length_le_fixed tokenTable width tokenCount
      current next binderArity repeatCount witness bitBound hsize
  have hleftCode :
      (binaryFormulaCode (repeatZeroBranchFormula tokenTable width tokenCount
        next repeatCount witness)).length <= syntaxResource :=
    (FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      child |>.trans hchild).trans (by
        unfold syntaxResource
        omega)
  have hrightSub :
      (binaryFormulaCode (repeatPositiveBranchFormula tokenTable width tokenCount
        next binderArity repeatCount witness)).length <=
        (binaryFormulaCode
          (compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width
            tokenCount next binderArity repeatCount witness)).length := by
    rw [repeatBranchExplicitFormula_alignment]
    exact binaryFormulaCode_or_right_le _ _
  have hrightCode :
      (binaryFormulaCode (repeatPositiveBranchFormula tokenTable width tokenCount
        next binderArity repeatCount witness)).length <= syntaxResource :=
    hrightSub.trans (hbranchCode.trans (by
      unfold syntaxResource
      omega))
  have hfullCode :
      (binaryFormulaCode
        (compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width
          tokenCount next binderArity repeatCount witness)).length <=
        syntaxResource :=
    hbranchCode.trans (by
      unfold syntaxResource
      omega)
  have hselected :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral child
      (repeatZeroBranchPayloadEnvelope numericBound bitBound)
      syntaxResource
      hchild (by
        unfold syntaxResource
        omega)
      (repeatZeroBranchFormula_freeVariables_eq_empty tokenTable width tokenCount
        next repeatCount witness)
      (repeatPositiveBranchFormula_freeVariables_eq_empty tokenTable width
        tokenCount next binderArity repeatCount witness)
      hleftCode hrightCode hfullCode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft child) <=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource
      (repeatZeroBranchPayloadEnvelope numericBound bitBound)
  exact hselected

theorem repeatPositiveSelectedBranchCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hrepeatSuccessor : repeatCount = witness.decrementedCount + 1)
    (hdrop : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount witness.tailBoundary witness.tailCount 2)
    (htaskZero : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 0 0 binderArity 0)
    (htaskOne : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 1 2 binderArity
        witness.decrementedCount)
    (hsize : forall coordinate : Fin 25,
      Nat.size
        (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable width
          tokenCount current next binderArity repeatCount witness coordinate) <=
        bitBound)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htasksCountValue : next.tasksCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (htasksBoundarySize : Nat.size next.tasksBoundary <= bitBound)
    (htasksCountSize : Nat.size next.tasksCount <= bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hrepeatSize : Nat.size repeatCount <= bitBound)
    (hdecrementedSize : Nat.size witness.decrementedCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := repeatZeroBranchFormula tokenTable width tokenCount next
            repeatCount witness)
          (repeatPositiveBranchCertificate tokenTable width tokenCount next
            binderArity repeatCount witness hrepeatSuccessor hdrop htaskZero
            htaskOne)) <=
      repeatSelectedBranchPayloadEnvelope bitBound
        (repeatPositiveBranchPayloadEnvelope numericBound bitBound) := by
  let child :=
    repeatPositiveBranchCertificate tokenTable width tokenCount next binderArity
      repeatCount witness hrepeatSuccessor hdrop htaskZero htaskOne
  have hchild :=
    repeatPositiveBranchCertificate_structuralPayloadBound_le_fixed tokenTable
      width tokenCount next binderArity repeatCount witness numericBound bitBound
      hrepeatSuccessor hdrop htaskZero htaskOne hwidthValue htokenCountValue
      htasksCountValue htableSize hwidthSize htokenCountSize htasksBoundarySize
      htasksCountSize htailBoundarySize hbinderSize hrepeatSize hdecrementedSize
      hnumericSize
  let syntaxResource :=
    compactUnifiedParserSyntaxRepeatFormulaSyntaxFixedPolynomial bitBound +
      repeatPositiveBranchPayloadEnvelope numericBound bitBound + 1
  have hbranchCode :=
    repeatBranchFormula_code_length_le_fixed tokenTable width tokenCount
      current next binderArity repeatCount witness bitBound hsize
  have hrightCode :
      (binaryFormulaCode (repeatPositiveBranchFormula tokenTable width tokenCount
        next binderArity repeatCount witness)).length <= syntaxResource :=
    (FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      child |>.trans hchild).trans (by
        unfold syntaxResource
        omega)
  have hleftSub :
      (binaryFormulaCode (repeatZeroBranchFormula tokenTable width tokenCount
        next repeatCount witness)).length <=
        (binaryFormulaCode
          (compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width
            tokenCount next binderArity repeatCount witness)).length := by
    rw [repeatBranchExplicitFormula_alignment]
    exact binaryFormulaCode_or_left_le _ _
  have hleftCode :
      (binaryFormulaCode (repeatZeroBranchFormula tokenTable width tokenCount
        next repeatCount witness)).length <= syntaxResource :=
    hleftSub.trans (hbranchCode.trans (by
      unfold syntaxResource
      omega))
  have hfullCode :
      (binaryFormulaCode
        (compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width
          tokenCount next binderArity repeatCount witness)).length <=
        syntaxResource :=
    hbranchCode.trans (by
      unfold syntaxResource
      omega)
  have hselected :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral child
      (repeatPositiveBranchPayloadEnvelope numericBound bitBound)
      syntaxResource
      hchild (by
        unfold syntaxResource
        omega)
      (repeatZeroBranchFormula_freeVariables_eq_empty tokenTable width tokenCount
        next repeatCount witness)
      (repeatPositiveBranchFormula_freeVariables_eq_empty tokenTable width
        tokenCount next binderArity repeatCount witness)
      hleftCode hrightCode hfullCode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight child) <=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource
      (repeatPositiveBranchPayloadEnvelope numericBound bitBound)
  exact hselected

#print axioms
  repeatZeroSelectedBranchCertificate_structuralPayloadBound_le_fixed
#print axioms
  repeatPositiveSelectedBranchCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxRepeatBranchFixedBounds
