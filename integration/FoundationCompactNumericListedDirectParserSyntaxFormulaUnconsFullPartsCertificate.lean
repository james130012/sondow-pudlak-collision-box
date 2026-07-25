import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail23456FixedBounds

/-! # Full six-leaf certificate for the exact parser Uncons formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullPartsCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail23456Certificate

def parserSyntaxFormulaUnconsFullFormula
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity : Nat) : ValuationFormula :=
  (“0 < !!(shortBinaryNumeralTerm sourceCount)” : ValuationFormula) ⋏
    parserSyntaxFormulaUnconsTail23456Formula tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      binderArity

noncomputable def parserSyntaxFormulaUnconsFullPartsCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity : Nat)
    (hpositive : 0 < sourceCount)
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
      (parserSyntaxFormulaUnconsFullFormula tokenTable width tokenCount
        sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
        binderArity) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedPositiveCertificate sourceCount hpositive)
    (parserSyntaxFormulaUnconsTail23456Certificate tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      binderArity hdrop htriple hcons hsize harea)

end FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullPartsCertificate
