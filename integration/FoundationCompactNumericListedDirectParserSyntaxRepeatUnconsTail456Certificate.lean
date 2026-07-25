import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56Certificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionGraphCertificate

/-! # Exact function ConsRows and size-area tail for Repeat uncons -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail456Certificate

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56Certificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionGraphCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate

def parserSyntaxRepeatUnconsTail456ConsFormula
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount binderArity repeatCount : Nat) : ValuationFormula :=
  compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula
    tokenTable width tokenCount tailBoundary tailCount sourceBoundary
    sourceCount (fixedNumeralTerm 2)
    (shortBinaryNumeralTerm binderArity)
    (shortBinaryNumeralTerm repeatCount)

def parserSyntaxRepeatUnconsTail56Formula
    (tailBoundarySize tailBoundary tailCount tokenCount : Nat) :
    ValuationFormula :=
  compactNatSizeClosedFormula tailBoundarySize tailBoundary ⋏
    (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
      (!!(shortBinaryNumeralTerm tailCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula)

noncomputable def parserSyntaxRepeatConsCertificate
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount binderArity repeatCount : Nat)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount 2 binderArity
      repeatCount) :
    CheckedHybridValuationBoundedFormulaCertificate
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      (parserSyntaxRepeatUnconsTail456ConsFormula tokenTable width tokenCount
        tailBoundary tailCount sourceBoundary sourceCount binderArity
        repeatCount) :=
  functionConsCertificateOfGraph tokenTable width tokenCount tailBoundary
    tailCount sourceBoundary sourceCount binderArity repeatCount hcons

noncomputable def parserSyntaxRepeatUnconsTail456Certificate
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize binderArity repeatCount : Nat)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount 2 binderArity
      repeatCount)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount) :
    CheckedHybridValuationBoundedFormulaCertificate
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      (parserSyntaxRepeatUnconsTail456ConsFormula tokenTable width tokenCount
          tailBoundary tailCount sourceBoundary sourceCount binderArity
          repeatCount ⋏
        parserSyntaxRepeatUnconsTail56Formula tailBoundarySize tailBoundary
          tailCount tokenCount) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (parserSyntaxRepeatConsCertificate tokenTable width tokenCount tailBoundary
      tailCount sourceBoundary sourceCount binderArity repeatCount hcons)
    (unconsRowsWithSizeTail56Certificate tailBoundarySize tailBoundary
      tailCount tokenCount hsize harea)

end FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail456Certificate
