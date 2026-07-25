import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatAtomicFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatClosedPairFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsFullyFixedBounds

/-! # Fully fixed exact zero branch certificate for Repeat -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatZeroBranchFixedBounds

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
open FoundationCompactNumericListedDirectParserSyntaxRepeatClosedPairFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate

private abbrev repeatZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate.zeroValuation

noncomputable def repeatZeroBranchCertificate
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hrepeatZero : repeatCount = 0)
    (hsame : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      witness.tailBoundary witness.tailCount next.tasksBoundary
      next.tasksCount) :
    CheckedHybridValuationBoundedFormulaCertificate repeatZeroValuation
      (nativeEqFormula repeatCount 0 ⋏
        compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable width
          tokenCount witness.tailBoundary witness.tailCount next.tasksBoundary
          next.tasksCount) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (nativeEqCertificate repeatCount 0 hrepeatZero)
    (compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount witness.tailBoundary witness.tailCount
      next.tasksBoundary next.tasksCount hsame)

def repeatZeroBranchPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (repeatClosedPairSyntaxResource
      (repeatNativeEqFixedPayloadPolynomial bitBound)
      (taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound))
    (repeatNativeEqFixedPayloadPolynomial bitBound)
    (taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)

private theorem nativeEqFormula_zero_freeVariables_eq_empty
    (value : Nat) :
    (nativeEqFormula value 0).freeVariables = ∅ := by
  unfold nativeEqFormula
  change
    (LO.FirstOrder.Semiformula.rel Language.Eq.eq
      ![shortBinaryNumeralTerm value, fixedNumeralTerm 0]).freeVariables = ∅
  rw [LO.FirstOrder.Semiformula.freeVariables_rel]
  ext candidate
  simp [shortBinaryNumeralTerm_freeVariables_eq_empty, fixedNumeralTerm,
    LO.FirstOrder.Semiterm.Operator.operator]

theorem repeatZeroBranchFormula_freeVariables_eq_empty
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) :
    (nativeEqFormula repeatCount 0 ⋏
      compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable width
        tokenCount witness.tailBoundary witness.tailCount next.tasksBoundary
        next.tasksCount).freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and,
    nativeEqFormula_zero_freeVariables_eq_empty,
    compactAdditiveSyntaxTaskListSameRowsClosedFormula_freeVariables_eq_empty_fullyFixed]
  simp

theorem repeatZeroBranchCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hrepeatZero : repeatCount = 0)
    (hsame : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      witness.tailBoundary witness.tailCount next.tasksBoundary
      next.tasksCount)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htailCountValue : witness.tailCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (htasksBoundarySize : Nat.size next.tasksBoundary <= bitBound)
    (hrepeatSize : Nat.size repeatCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (repeatZeroBranchCertificate tokenTable width tokenCount next
          repeatCount witness hrepeatZero hsame) <=
      repeatZeroBranchPayloadEnvelope numericBound bitBound := by
  let zeroCertificate := nativeEqCertificate repeatCount 0 hrepeatZero
  let sameCertificate :=
    compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount witness.tailBoundary witness.tailCount
      next.tasksBoundary next.tasksCount hsame
  have hzero :
      hybridFormulaStructuralPayloadBound zeroCertificate <=
        repeatNativeEqFixedPayloadPolynomial bitBound :=
    nativeEqCertificate_structuralPayloadBound_le_fixed repeatCount bitBound
      hrepeatZero hrepeatSize
  have hsameTransparent :
      hybridFormulaStructuralPayloadBound sameCertificate <=
        compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope tokenTable
          width tokenCount witness.tailBoundary witness.tailCount
          next.tasksBoundary next.tasksCount hsame :=
    compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount witness.tailBoundary witness.tailCount
      next.tasksBoundary next.tasksCount hsame
  have hsameFixed :
      compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope tokenTable
          width tokenCount witness.tailBoundary witness.tailCount
          next.tasksBoundary next.tasksCount hsame <=
        taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound :=
    compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount witness.tailBoundary witness.tailCount
      next.tasksBoundary next.tasksCount numericBound bitBound hsame
      hwidthValue htokenCountValue htailCountValue htableSize
      htailBoundarySize htasksBoundarySize hnumericSize
  have hsameResource :
      hybridFormulaStructuralPayloadBound sameCertificate <=
        taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound :=
    hsameTransparent.trans hsameFixed
  have hpair :=
    closedPairCertificate_structuralPayloadBound_le_fixed repeatZeroValuation
      _ _ zeroCertificate sameCertificate
      (repeatNativeEqFixedPayloadPolynomial bitBound)
      (taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (nativeEqFormula_zero_freeVariables_eq_empty repeatCount)
      (compactAdditiveSyntaxTaskListSameRowsClosedFormula_freeVariables_eq_empty_fullyFixed
        tokenTable width tokenCount witness.tailBoundary witness.tailCount
        next.tasksBoundary next.tasksCount)
      hzero hsameResource
  unfold repeatZeroBranchPayloadEnvelope
  simpa only [repeatZeroBranchCertificate, zeroCertificate, sameCertificate]
    using hpair

#print axioms repeatZeroBranchCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxRepeatZeroBranchFixedBounds
