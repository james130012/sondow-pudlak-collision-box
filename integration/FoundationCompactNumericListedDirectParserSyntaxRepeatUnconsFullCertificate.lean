import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail23456FixedBounds

/-! # Full six-leaf function-task uncons certificate for Repeat -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsFullCertificate

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail23456Certificate

def parserSyntaxRepeatUnconsFullFormula
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity repeatCount : Nat) :
    ValuationFormula :=
  (“0 < !!(shortBinaryNumeralTerm sourceCount)” : ValuationFormula) ⋏
    parserSyntaxRepeatUnconsTail23456Formula tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      binderArity repeatCount

noncomputable def parserSyntaxRepeatUnconsFullCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity repeatCount : Nat)
    (hpositive : 0 < sourceCount)
    (hdrop : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount 1)
    (htriple : CompactAdditiveTripleBoundaryRows tokenCount tailCount
      tailBoundary)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount 2 binderArity
      repeatCount)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount) :
    CheckedHybridValuationBoundedFormulaCertificate
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      (parserSyntaxRepeatUnconsFullFormula tokenTable width tokenCount
        sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
        binderArity repeatCount) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedPositiveCertificate sourceCount hpositive)
    (parserSyntaxRepeatUnconsTail23456Certificate tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      binderArity repeatCount hdrop htriple hcons hsize harea)

theorem parserSyntaxRepeatUnconsFullFormula_alignment
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity repeatCount : Nat) :
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount tailBoundarySize binderArity repeatCount
        (FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
          2) =
      parserSyntaxRepeatUnconsFullFormula tokenTable width tokenCount
        sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
        binderArity repeatCount := by
  rw [
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula,
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula_alignment]
  rfl

end FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsFullCertificate
