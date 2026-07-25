import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56FixedBounds

/-!
# `ConsRows ∧ (NatSize ∧ area)` checked certificate
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail456Certificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56Certificate

noncomputable def unconsRowsWithSizeTail456Certificate
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize headKind headBinderArity headRepeatCount :
      Nat)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount headKind
      headBinderArity headRepeatCount)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount) :
    CheckedHybridValuationBoundedFormulaCertificate
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula
          tokenTable width tokenCount tailBoundary tailCount sourceBoundary
          sourceCount (shortBinaryNumeralTerm headKind)
          (shortBinaryNumeralTerm headBinderArity)
          (shortBinaryNumeralTerm headRepeatCount) ⋏
        (compactNatSizeClosedFormula tailBoundarySize tailBoundary ⋏
          (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
            (!!(shortBinaryNumeralTerm tailCount) + 1) *
              !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula))) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount headKind headBinderArity headRepeatCount
      (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)
      (termValue_shortBinaryNumeralTerm · headKind)
      (termValue_shortBinaryNumeralTerm · headBinderArity)
      (termValue_shortBinaryNumeralTerm · headRepeatCount) hcons)
    (unconsRowsWithSizeTail56Certificate tailBoundarySize tailBoundary
      tailCount tokenCount hsize harea)

end FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail456Certificate
