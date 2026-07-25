import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail3456FixedBounds

/-!
# `DropOne ∧ Tail3456` checked certificate
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail23456Certificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail3456Certificate

noncomputable def unconsRowsWithSizeTail23456Certificate
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount :
      Nat)
    (hdrop : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount 1)
    (htriple : CompactAdditiveTripleBoundaryRows tokenCount tailCount
      tailBoundary)
    (hcons : FoundationCompactNumericListedDirectSyntaxTaskListConsRows.CompactAdditiveSyntaxTaskListConsRows
      tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount headKind headBinderArity headRepeatCount)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount) :
    CheckedHybridValuationBoundedFormulaCertificate
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
          tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
          tailCount 1 ⋏
        (compactAdditiveTripleBoundaryRowsClosedFormula tokenCount tailCount
            tailBoundary ⋏
          (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula
              tokenTable width tokenCount tailBoundary tailCount sourceBoundary
              sourceCount (shortBinaryNumeralTerm headKind)
              (shortBinaryNumeralTerm headBinderArity)
              (shortBinaryNumeralTerm headRepeatCount) ⋏
            (compactNatSizeClosedFormula tailBoundarySize tailBoundary ⋏
              (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
                (!!(shortBinaryNumeralTerm tailCount) + 1) *
                  !!(shortBinaryNumeralTerm tokenCount)” :
                ValuationFormula))))) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount 1 hdrop)
    (unconsRowsWithSizeTail3456Certificate tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
      headKind headBinderArity headRepeatCount htriple hcons hsize harea)

end FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail23456Certificate
