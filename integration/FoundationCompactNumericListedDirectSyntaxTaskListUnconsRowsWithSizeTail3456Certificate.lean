import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail456FixedBounds

/-!
# `TripleBoundary ∧ Tail456` checked certificate
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail3456Certificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail456Certificate

noncomputable def unconsRowsWithSizeTail3456Certificate
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize headKind headBinderArity headRepeatCount :
      Nat)
    (htriple : CompactAdditiveTripleBoundaryRows tokenCount tailCount
      tailBoundary)
    (hcons : FoundationCompactNumericListedDirectSyntaxTaskListConsRows.CompactAdditiveSyntaxTaskListConsRows
      tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount headKind headBinderArity headRepeatCount)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount) :
    CheckedHybridValuationBoundedFormulaCertificate
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
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
              ValuationFormula)))) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph
      tokenCount tailCount tailBoundary htriple)
    (unconsRowsWithSizeTail456Certificate tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
      headKind headBinderArity headRepeatCount hcons hsize harea)

end FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail3456Certificate
