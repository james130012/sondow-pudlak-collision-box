import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456FixedBounds

/-! # Exact parser `TripleBoundary ∧ Tail456` certificate -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail3456Certificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456Certificate

def parserSyntaxFormulaUnconsTail3456Formula
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize binderArity : Nat) : ValuationFormula :=
  compactAdditiveTripleBoundaryRowsClosedFormula tokenCount tailCount
      tailBoundary ⋏
    (parserSyntaxFormulaUnconsTail456ConsFormula tokenTable width tokenCount
        tailBoundary tailCount sourceBoundary sourceCount binderArity ⋏
      parserSyntaxFormulaUnconsTail56Formula tailBoundarySize tailBoundary
        tailCount tokenCount)

noncomputable def parserSyntaxFormulaUnconsTail3456Certificate
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize binderArity : Nat)
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
      (parserSyntaxFormulaUnconsTail3456Formula tokenTable width tokenCount
        tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
        binderArity) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph
      tokenCount tailCount tailBoundary htriple)
    (parserSyntaxFormulaUnconsTail456Certificate tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
      binderArity hcons hsize harea)

end FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail3456Certificate
