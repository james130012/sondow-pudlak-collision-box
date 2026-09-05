import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalTransparentResources

/-! # Exact transparent payload of the raw cons-tail universal certificate -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailUniversalRawTransparentBound

open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridBoundedUniversalTransparentPayload
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalTransparentResources

theorem
    compactAdditiveNatListConsRowsTailRawUniversalCertificate_payload_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListConsRowsTailRawUniversalCertificate tokenTable
          width tokenCount sourceBoundary sourceCount targetBoundary rows) <=
      natListConsRowsTailUniversalTransparentPayloadEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows := by
  unfold compactAdditiveNatListConsRowsTailRawUniversalCertificate
    natListConsRowsTailUniversalTransparentPayloadEnvelope
  exact Nat.le_of_eq
    (hybridBoundedUniversal_structuralPayload_eq_transparent _ _ _ _)

#print axioms
  compactAdditiveNatListConsRowsTailRawUniversalCertificate_payload_le_transparent

end FoundationCompactNumericListedDirectNatListConsRowsTailUniversalRawTransparentBound
