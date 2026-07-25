import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail23456FixedBounds

/-!
# Full six-leaf parts certificate for syntax-task-list uncons
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullPartsCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail23456Certificate

noncomputable def unconsRowsWithSizeFullPartsCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize headKind headBinderArity headRepeatCount :
      Nat)
    (hpositive : 0 < sourceCount)
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
      ((“0 < !!(shortBinaryNumeralTerm sourceCount)” : ValuationFormula) ⋏
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
            tokenTable width tokenCount sourceBoundary sourceCount
            tailBoundary tailCount 1 ⋏
          (compactAdditiveTripleBoundaryRowsClosedFormula tokenCount tailCount
              tailBoundary ⋏
            (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula
                tokenTable width tokenCount tailBoundary tailCount
                sourceBoundary sourceCount (shortBinaryNumeralTerm headKind)
                (shortBinaryNumeralTerm headBinderArity)
                (shortBinaryNumeralTerm headRepeatCount) ⋏
              (compactNatSizeClosedFormula tailBoundarySize tailBoundary ⋏
                (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
                  (!!(shortBinaryNumeralTerm tailCount) + 1) *
                    !!(shortBinaryNumeralTerm tokenCount)” :
                  ValuationFormula)))))) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedPositiveCertificate sourceCount hpositive)
    (unconsRowsWithSizeTail23456Certificate tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      headKind headBinderArity headRepeatCount hdrop htriple hcons hsize
      harea)

end FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullPartsCertificate
