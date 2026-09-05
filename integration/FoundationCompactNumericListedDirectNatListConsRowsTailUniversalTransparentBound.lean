import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCastPayload
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalRawTransparentBound

/-! # Transparent payload bound of the cons-tail universal certificate -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 80000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailUniversalTransparentBound

open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCastPayload
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalRawTransparentBound
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalTransparentResources

theorem
    compactAdditiveNatListConsRowsTailUniversalCertificate_payload_le_transparent
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListConsRowsTailUniversalCertificate tokenTable
          width tokenCount sourceBoundary sourceCount targetBoundary rows) <=
      natListConsRowsTailUniversalTransparentPayloadEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows := by
  rw [compactAdditiveNatListConsRowsTailUniversalCertificate_payload_eq_raw]
  exact
    compactAdditiveNatListConsRowsTailRawUniversalCertificate_payload_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows

#print axioms
  compactAdditiveNatListConsRowsTailUniversalCertificate_payload_le_transparent

end FoundationCompactNumericListedDirectNatListConsRowsTailUniversalTransparentBound
