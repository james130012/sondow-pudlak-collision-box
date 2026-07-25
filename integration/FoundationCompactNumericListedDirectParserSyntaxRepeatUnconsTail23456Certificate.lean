import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail3456FixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsExplicitHybridCertificate

/-! # Exact DropOne and Tail3456 certificate for Repeat uncons -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail23456Certificate

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail3456Certificate

def parserSyntaxRepeatUnconsTail23456Formula
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity repeatCount : Nat) :
    ValuationFormula :=
  compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable
      width tokenCount sourceBoundary sourceCount tailBoundary tailCount 1 ⋏
    parserSyntaxRepeatUnconsTail3456Formula tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
      binderArity repeatCount

noncomputable def parserSyntaxRepeatUnconsTail23456Certificate
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity repeatCount : Nat)
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
      (parserSyntaxRepeatUnconsTail23456Formula tokenTable width tokenCount
        sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
        binderArity repeatCount) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount 1 hdrop)
    (parserSyntaxRepeatUnconsTail3456Certificate tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
      binderArity repeatCount htriple hcons hsize harea)

end FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail23456Certificate
