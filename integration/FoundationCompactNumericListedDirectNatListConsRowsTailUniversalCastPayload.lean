import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCertificate

/-! # Formula casts preserve the cons-tail universal structural payload -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCastPayload

open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCertificate

theorem compactAdditiveNatListConsRowsTailUniversalCertificate_payload_eq_raw
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListConsRowsTailUniversalCertificate tokenTable
          width tokenCount sourceBoundary sourceCount targetBoundary rows) =
      hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListConsRowsTailRawUniversalCertificate tokenTable
          width tokenCount sourceBoundary sourceCount targetBoundary rows) := by
  rfl

#print axioms
  compactAdditiveNatListConsRowsTailUniversalCertificate_payload_eq_raw

end FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCastPayload
