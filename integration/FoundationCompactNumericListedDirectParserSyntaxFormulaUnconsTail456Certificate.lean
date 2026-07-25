import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56Certificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserGraphFullyFixedBounds

/-! # Exact parser `ConsRows ∧ (NatSize ∧ area)` certificate -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456Certificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56Certificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate

private abbrev parserFixedNumeralTerm (value : Nat) : ValuationTerm :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
    value

private theorem termValue_parserFixedNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (parserFixedNumeralTerm value) = value := by
  simp [parserFixedNumeralTerm,
    FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm,
    termValue]

def parserSyntaxFormulaUnconsTail456ConsFormula
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount binderArity : Nat) : ValuationFormula :=
  compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula
    tokenTable width tokenCount tailBoundary tailCount sourceBoundary
    sourceCount (parserFixedNumeralTerm 1)
    (shortBinaryNumeralTerm binderArity) (parserFixedNumeralTerm 0)

def parserSyntaxFormulaUnconsTail56Formula
    (tailBoundarySize tailBoundary tailCount tokenCount : Nat) :
    ValuationFormula :=
  compactNatSizeClosedFormula tailBoundarySize tailBoundary ⋏
    (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
      (!!(shortBinaryNumeralTerm tailCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula)

noncomputable def parserSyntaxFormulaConsCertificate
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount binderArity : Nat)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount 1 binderArity 0) :
    CheckedHybridValuationBoundedFormulaCertificate
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      (parserSyntaxFormulaUnconsTail456ConsFormula tokenTable width tokenCount
        tailBoundary tailCount sourceBoundary sourceCount binderArity) :=
  compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
    tokenTable width tokenCount tailBoundary tailCount sourceBoundary
    sourceCount 1 binderArity 0 (parserFixedNumeralTerm 1)
    (shortBinaryNumeralTerm binderArity) (parserFixedNumeralTerm 0)
    (termValue_parserFixedNumeralTerm · 1)
    (termValue_shortBinaryNumeralTerm · binderArity)
    (termValue_parserFixedNumeralTerm · 0) hcons

noncomputable def parserSyntaxFormulaUnconsTail456Certificate
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize binderArity : Nat)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount 1 binderArity 0)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount) :
    CheckedHybridValuationBoundedFormulaCertificate
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      (parserSyntaxFormulaUnconsTail456ConsFormula tokenTable width tokenCount
          tailBoundary tailCount sourceBoundary sourceCount binderArity ⋏
        parserSyntaxFormulaUnconsTail56Formula tailBoundarySize tailBoundary
          tailCount tokenCount) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (parserSyntaxFormulaConsCertificate tokenTable width tokenCount tailBoundary
      tailCount sourceBoundary sourceCount binderArity hcons)
    (unconsRowsWithSizeTail56Certificate tailBoundarySize tailBoundary
      tailCount tokenCount hsize harea)

end FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456Certificate
