import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail3456FixedBounds

/-! # Exact parser `DropOne ∧ Tail3456` certificate -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail23456Certificate

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail3456Certificate

def parserSyntaxFormulaUnconsTail23456Formula
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity : Nat) : ValuationFormula :=
  compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable
      width tokenCount sourceBoundary sourceCount tailBoundary tailCount 1 ⋏
    parserSyntaxFormulaUnconsTail3456Formula tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
      binderArity

noncomputable def parserSyntaxFormulaUnconsTail23456Certificate
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity : Nat)
    (hdrop : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount 1)
    (htriple : CompactAdditiveTripleBoundaryRows tokenCount tailCount
      tailBoundary)
    (hcons :
      FoundationCompactNumericListedDirectSyntaxTaskListConsRows.CompactAdditiveSyntaxTaskListConsRows
        tokenTable width tokenCount tailBoundary tailCount sourceBoundary
        sourceCount 1 binderArity 0)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount) :
    CheckedHybridValuationBoundedFormulaCertificate
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      (parserSyntaxFormulaUnconsTail23456Formula tokenTable width tokenCount
        sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
        binderArity) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount 1 hdrop)
    (parserSyntaxFormulaUnconsTail3456Certificate tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
      binderArity htriple hcons hsize harea)

end FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail23456Certificate
