import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail456FixedBounds
import integration.FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate

/-! # Exact TripleBoundary and Tail456 certificate for Repeat uncons -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail3456Certificate

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail456Certificate

def parserSyntaxRepeatUnconsTail3456Formula
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize binderArity repeatCount : Nat) :
    ValuationFormula :=
  compactAdditiveTripleBoundaryRowsClosedFormula tokenCount tailCount
      tailBoundary ⋏
    (parserSyntaxRepeatUnconsTail456ConsFormula tokenTable width tokenCount
        tailBoundary tailCount sourceBoundary sourceCount binderArity
        repeatCount ⋏
      parserSyntaxRepeatUnconsTail56Formula tailBoundarySize tailBoundary
        tailCount tokenCount)

noncomputable def parserSyntaxRepeatUnconsTail3456Certificate
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize binderArity repeatCount : Nat)
    (htriple : CompactAdditiveTripleBoundaryRows tokenCount tailCount
      tailBoundary)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount 2 binderArity
      repeatCount)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount) :
    CheckedHybridValuationBoundedFormulaCertificate
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      (parserSyntaxRepeatUnconsTail3456Formula tokenTable width tokenCount
        tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
        binderArity repeatCount) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph
      tokenCount tailCount tailBoundary htriple)
    (parserSyntaxRepeatUnconsTail456Certificate tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
      binderArity repeatCount hcons hsize harea)

end FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail3456Certificate
