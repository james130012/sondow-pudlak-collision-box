import integration.FoundationCompactNumericListedDirectNatListConsRowsCountCertificateFixedBound
import integration.FoundationCompactNumericListedDirectNatListConsRowsHeadCertificate
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCertificate

/-! # Public exact certificate for the closed natural-list cons-rows formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsClosedCertificate

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectNatListConsRowsCountCertificateFixedBound
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsHeadCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCertificate

noncomputable def compactAdditiveNatListConsRowsClosedCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount head : Nat)
    (hcount : targetCount = sourceCount + 1)
    (headData : CompactAdditiveNatListConsHeadData tokenTable width tokenCount
      targetBoundary head)
    (tailRows : (index : Fin sourceCount) ->
      CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    CheckedHybridValuationBoundedFormulaCertificate
      natListConsRowsTailUniversalZeroValuation
      (compactAdditiveNatListConsRowsClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount head) := by
  let countCertificate := natListConsRowsCountEqualityCertificate sourceCount
    targetCount hcount
  let headCertificate := compactAdditiveNatListConsRowsHeadCertificate
    tokenTable width tokenCount targetBoundary head headData
  let tailCertificate := compactAdditiveNatListConsRowsTailUniversalCertificate
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
    tailRows
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    countCertificate
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      headCertificate tailCertificate)
  exact CheckedHybridValuationBoundedFormulaCertificate.cast
    (compactAdditiveNatListConsRowsClosedFormula_alignment tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary targetCount
      head).symm parts

#print axioms compactAdditiveNatListConsRowsClosedCertificate

end FoundationCompactNumericListedDirectNatListConsRowsClosedCertificate
