import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionFullyFixedBounds

/-! # Opaque graph data for the function ConsRows certificate -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionGraphCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate

theorem termValue_functionFixedNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (fixedNumeralTerm value) = value := by
  simp [fixedNumeralTerm, termValue]

noncomputable def functionConsHeadDataOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount binderArity functionArity : Nat)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 2 binderArity
      functionArity) :
    CompactAdditiveSyntaxTaskListConsHeadData tokenTable width tokenCount
      targetBoundary 2 binderArity functionArity :=
  compactAdditiveSyntaxTaskListConsRowsHeadDataOfGraph tokenTable width
    tokenCount sourceBoundary sourceCount targetBoundary targetCount 2
    binderArity functionArity hcons

noncomputable def functionConsTailRowsOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount binderArity functionArity : Nat)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 2 binderArity
      functionArity)
    (index : Fin sourceCount) :
    CompactAdditiveSyntaxTaskListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index :=
  compactAdditiveSyntaxTaskListConsRowsTailRowDataOfGraph tokenTable width
    tokenCount sourceBoundary sourceCount targetBoundary targetCount 2
    binderArity functionArity hcons index

noncomputable def functionConsCertificateOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount binderArity functionArity : Nat)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 2 binderArity
      functionArity) :
    CheckedHybridValuationBoundedFormulaCertificate
      FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation
      (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount (fixedNumeralTerm 2)
        (shortBinaryNumeralTerm binderArity)
        (shortBinaryNumeralTerm functionArity)) :=
  compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataExplicitHybridCertificate
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
    targetCount 2 binderArity functionArity (fixedNumeralTerm 2)
    (shortBinaryNumeralTerm binderArity)
    (shortBinaryNumeralTerm functionArity)
    (termValue_functionFixedNumeralTerm · 2)
    (termValue_shortBinaryNumeralTerm · binderArity)
    (termValue_shortBinaryNumeralTerm · functionArity) hcons.1
    (functionConsHeadDataOfGraph tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount binderArity functionArity hcons)
    (functionConsTailRowsOfGraph tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount binderArity functionArity hcons)

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionGraphCertificate
