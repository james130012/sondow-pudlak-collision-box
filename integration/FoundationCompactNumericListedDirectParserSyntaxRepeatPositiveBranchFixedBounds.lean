import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatPositiveBranchCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatClosedPairFixedBounds

/-! # Fully fixed exact positive branch certificate for Repeat -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatPositiveBranchFixedBounds

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsBodyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsFullCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsFullFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatPositiveBranchCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatClosedPairFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsFullyFixedBounds

private abbrev repeatZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate.zeroValuation

def repeatPositiveTaskPairPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (repeatClosedPairSyntaxResource
      (repeatTaskZeroFullPayloadEnvelope numericBound bitBound)
      (repeatTaskOneFullPayloadEnvelope numericBound bitBound))
    (repeatTaskZeroFullPayloadEnvelope numericBound bitBound)
    (repeatTaskOneFullPayloadEnvelope numericBound bitBound)

def repeatPositiveDropTailPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (repeatClosedPairSyntaxResource
      (taskDropTwoCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (repeatPositiveTaskPairPayloadEnvelope numericBound bitBound))
    (taskDropTwoCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    (repeatPositiveTaskPairPayloadEnvelope numericBound bitBound)

def repeatPositiveBranchPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (repeatClosedPairSyntaxResource
      (repeatNativeEqFixedPayloadPolynomial bitBound)
      (repeatPositiveDropTailPayloadEnvelope numericBound bitBound))
    (repeatNativeEqFixedPayloadPolynomial bitBound)
    (repeatPositiveDropTailPayloadEnvelope numericBound bitBound)

private theorem nativeSuccessorEqFormula_freeVariables_eq_empty
    (value predecessor : Nat) :
    (nativeSuccessorEqFormula value predecessor).freeVariables = ∅ := by
  have hright :
      (‘!!(shortBinaryNumeralTerm predecessor) +
        !!(fixedNumeralTerm 1)’ : ValuationTerm).freeVariables = ∅ := by
    rw [FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds.arithmeticAddTerm_freeVariables_eq_union,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp [fixedNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]
  unfold nativeSuccessorEqFormula
  change
    (LO.FirstOrder.Semiformula.rel Language.Eq.eq
      ![shortBinaryNumeralTerm value,
        ‘!!(shortBinaryNumeralTerm predecessor) +
          !!(fixedNumeralTerm 1)’]).freeVariables = ∅
  rw [LO.FirstOrder.Semiformula.freeVariables_rel]
  ext candidate
  simp [shortBinaryNumeralTerm_freeVariables_eq_empty, hright]

theorem repeatPositiveBranchFormula_freeVariables_eq_empty
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) :
    (nativeSuccessorEqFormula repeatCount witness.decrementedCount ⋏
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
          tokenTable width tokenCount next.tasksBoundary next.tasksCount
          witness.tailBoundary witness.tailCount 2 ⋏
        (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
            width tokenCount next.tasksBoundary next.tasksCount
            (fixedNumeralTerm 0) (fixedNumeralTerm 0)
            (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0) ⋏
          compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
            width tokenCount next.tasksBoundary next.tasksCount
            (fixedNumeralTerm 1) (fixedNumeralTerm 2)
            (shortBinaryNumeralTerm binderArity)
            (shortBinaryNumeralTerm witness.decrementedCount)))).freeVariables =
      ∅ := by
  have hzero :=
    repeatAtRowsFullFormula_freeVariables_eq_empty tokenTable width tokenCount
      next.tasksBoundary next.tasksCount
      (fixedNumeralTerm 0) (fixedNumeralTerm 0)
      (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
      (by simp) (by simp) (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (by simp)
  have hone :=
    repeatAtRowsFullFormula_freeVariables_eq_empty tokenTable width tokenCount
      next.tasksBoundary next.tasksCount
      (fixedNumeralTerm 1) (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm witness.decrementedCount)
      (by simp) (by simp) (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  rw [LO.FirstOrder.Semiformula.freeVariables_and,
    nativeSuccessorEqFormula_freeVariables_eq_empty,
    LO.FirstOrder.Semiformula.freeVariables_and,
    compactAdditiveSyntaxTaskListDropTwoRowsClosedFormula_freeVariables_eq_empty,
    LO.FirstOrder.Semiformula.freeVariables_and, hzero, hone]
  simp

theorem repeatPositiveBranchCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
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
        (repeatPositiveBranchCertificate tokenTable width tokenCount next
          binderArity repeatCount witness hrepeatSuccessor hdrop htaskZero
          htaskOne) <=
      repeatPositiveBranchPayloadEnvelope numericBound bitBound := by
  let successorCertificate :=
    nativeSuccessorEqCertificate repeatCount witness.decrementedCount
      hrepeatSuccessor
  let dropCertificate :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksBoundary next.tasksCount
      witness.tailBoundary witness.tailCount 2 hdrop
  let taskZeroCertificate :=
    repeatAtRowsFullCertificateOfGraph tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 0 0 binderArity 0
      (fixedNumeralTerm 0) (fixedNumeralTerm 0)
      (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
      (by simp) (fun valuation => by simp)
      (fun valuation => termValue_shortBinaryNumeralTerm valuation binderArity)
      (fun valuation => by simp) htaskZero
  let taskOneCertificate :=
    repeatAtRowsFullCertificateOfGraph tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 1 2 binderArity
      witness.decrementedCount (fixedNumeralTerm 1) (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm witness.decrementedCount) (by simp)
      (fun valuation => by simp)
      (fun valuation => termValue_shortBinaryNumeralTerm valuation binderArity)
      (fun valuation =>
        termValue_shortBinaryNumeralTerm valuation witness.decrementedCount)
      htaskOne
  have hsuccessor :
      hybridFormulaStructuralPayloadBound successorCertificate <=
        repeatNativeEqFixedPayloadPolynomial bitBound :=
    nativeSuccessorEqCertificate_structuralPayloadBound_le_fixed
      repeatCount witness.decrementedCount bitBound hrepeatSuccessor
      hrepeatSize hdecrementedSize
  have hdropTransparent :
      hybridFormulaStructuralPayloadBound dropCertificate <=
        compactAdditiveSyntaxTaskListDropFixedNumeralRowsGraphPayloadEnvelope
          tokenTable width tokenCount next.tasksBoundary next.tasksCount
          witness.tailBoundary witness.tailCount 2 hdrop :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount next.tasksBoundary next.tasksCount
      witness.tailBoundary witness.tailCount 2 hdrop
  have hdropFixed :
      compactAdditiveSyntaxTaskListDropFixedNumeralRowsGraphPayloadEnvelope
          tokenTable width tokenCount next.tasksBoundary next.tasksCount
          witness.tailBoundary witness.tailCount 2 hdrop <=
        taskDropTwoCompleteFullyFixedPayloadPolynomial numericBound bitBound :=
    compactAdditiveSyntaxTaskListDropTwoRowsGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount next.tasksBoundary next.tasksCount
      witness.tailBoundary witness.tailCount numericBound bitBound hdrop
      hwidthValue htokenCountValue htasksCountValue htableSize
      htasksBoundarySize htailBoundarySize hnumericSize
  have hdropResource :
      hybridFormulaStructuralPayloadBound dropCertificate <=
        taskDropTwoCompleteFullyFixedPayloadPolynomial numericBound bitBound :=
    hdropTransparent.trans hdropFixed
  have htaskZero :
      hybridFormulaStructuralPayloadBound taskZeroCertificate <=
        repeatTaskZeroFullPayloadEnvelope numericBound bitBound :=
    repeatTaskZeroFullCertificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount next.tasksBoundary next.tasksCount
      binderArity numericBound bitBound htaskZero hwidthValue
      htokenCountValue htasksCountValue htableSize hwidthSize
      htokenCountSize htasksBoundarySize htasksCountSize hbinderSize
  have htaskOne :
      hybridFormulaStructuralPayloadBound taskOneCertificate <=
        repeatTaskOneFullPayloadEnvelope numericBound bitBound :=
    repeatTaskOneFullCertificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount next.tasksBoundary next.tasksCount
      binderArity witness.decrementedCount numericBound bitBound htaskOne
      hwidthValue htokenCountValue htasksCountValue htableSize hwidthSize
      htokenCountSize htasksBoundarySize htasksCountSize hbinderSize
      hdecrementedSize
  have htaskZeroClosed :
      (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
        width tokenCount next.tasksBoundary next.tasksCount
        (fixedNumeralTerm 0) (fixedNumeralTerm 0)
        (shortBinaryNumeralTerm binderArity)
        (fixedNumeralTerm 0)).freeVariables = ∅ :=
    repeatAtRowsFullFormula_freeVariables_eq_empty tokenTable width tokenCount
      next.tasksBoundary next.tasksCount
      (fixedNumeralTerm 0) (fixedNumeralTerm 0)
      (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
      (by simp) (by simp) (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (by simp)
  have htaskOneClosed :
      (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
        width tokenCount next.tasksBoundary next.tasksCount
        (fixedNumeralTerm 1) (fixedNumeralTerm 2)
        (shortBinaryNumeralTerm binderArity)
        (shortBinaryNumeralTerm witness.decrementedCount)).freeVariables = ∅ :=
    repeatAtRowsFullFormula_freeVariables_eq_empty tokenTable width tokenCount
      next.tasksBoundary next.tasksCount
      (fixedNumeralTerm 1) (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm witness.decrementedCount)
      (by simp) (by simp) (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have htaskPair :=
    closedPairCertificate_structuralPayloadBound_le_fixed repeatZeroValuation
      _ _ taskZeroCertificate taskOneCertificate
      (repeatTaskZeroFullPayloadEnvelope numericBound bitBound)
      (repeatTaskOneFullPayloadEnvelope numericBound bitBound)
      htaskZeroClosed htaskOneClosed
      htaskZero htaskOne
  have hdropTail :=
    closedPairCertificate_structuralPayloadBound_le_fixed repeatZeroValuation
      _ _ dropCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        taskZeroCertificate taskOneCertificate)
      (taskDropTwoCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (repeatPositiveTaskPairPayloadEnvelope numericBound bitBound)
      (compactAdditiveSyntaxTaskListDropTwoRowsClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount next.tasksBoundary next.tasksCount
        witness.tailBoundary witness.tailCount)
      (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, htaskZeroClosed,
          htaskOneClosed]
        simp)
      hdropResource htaskPair
  have hbranch :=
    closedPairCertificate_structuralPayloadBound_le_fixed repeatZeroValuation
      _ _ successorCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        dropCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          taskZeroCertificate taskOneCertificate))
      (repeatNativeEqFixedPayloadPolynomial bitBound)
      (repeatPositiveDropTailPayloadEnvelope numericBound bitBound)
      (nativeSuccessorEqFormula_freeVariables_eq_empty repeatCount
        witness.decrementedCount)
      (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and,
          compactAdditiveSyntaxTaskListDropTwoRowsClosedFormula_freeVariables_eq_empty,
          LO.FirstOrder.Semiformula.freeVariables_and, htaskZeroClosed,
          htaskOneClosed]
        simp)
      hsuccessor hdropTail
  unfold repeatPositiveBranchPayloadEnvelope
  simpa only [repeatPositiveBranchCertificate, successorCertificate,
    dropCertificate, taskZeroCertificate, taskOneCertificate] using hbranch

#print axioms repeatPositiveBranchCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxRepeatPositiveBranchFixedBounds
