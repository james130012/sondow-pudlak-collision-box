import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsFullFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatAtomicFixedBounds

/-! # Exact positive branch certificate for Repeat -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatPositiveBranchCertificate

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsFullCertificate

private abbrev repeatZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate.zeroValuation

noncomputable def repeatPositiveBranchCertificate
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hrepeatSuccessor : repeatCount = witness.decrementedCount + 1)
    (hdrop : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount witness.tailBoundary witness.tailCount 2)
    (htaskZero : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 0 0 binderArity 0)
    (htaskOne : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 1 2 binderArity
        witness.decrementedCount) :
    CheckedHybridValuationBoundedFormulaCertificate repeatZeroValuation
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
              (shortBinaryNumeralTerm witness.decrementedCount)))) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (nativeSuccessorEqCertificate repeatCount witness.decrementedCount
      hrepeatSuccessor)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount next.tasksBoundary next.tasksCount
        witness.tailBoundary witness.tailCount 2 hdrop)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (repeatAtRowsFullCertificateOfGraph tokenTable width tokenCount
          next.tasksBoundary next.tasksCount 0 0 binderArity 0
          (fixedNumeralTerm 0) (fixedNumeralTerm 0)
          (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
          (by simp) (fun valuation => by simp)
          (fun valuation =>
            termValue_shortBinaryNumeralTerm valuation binderArity)
          (fun valuation => by simp) htaskZero)
        (repeatAtRowsFullCertificateOfGraph tokenTable width tokenCount
          next.tasksBoundary next.tasksCount 1 2 binderArity
          witness.decrementedCount (fixedNumeralTerm 1) (fixedNumeralTerm 2)
          (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm witness.decrementedCount) (by simp)
          (fun valuation => by simp)
          (fun valuation =>
            termValue_shortBinaryNumeralTerm valuation binderArity)
          (fun valuation =>
            termValue_shortBinaryNumeralTerm valuation
              witness.decrementedCount)
          htaskOne)))

end FoundationCompactNumericListedDirectParserSyntaxRepeatPositiveBranchCertificate
