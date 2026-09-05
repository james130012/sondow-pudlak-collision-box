import integration.FoundationCompactNumericListedDirectNatListConsRowsTailTransparentBound
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailFixedEnvelope

/-! # Uniform payload bound for one natural-list cons tail branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 160000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailUniformBound

open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailTransparentBound
open FoundationCompactNumericListedDirectNatListConsRowsTailFixedEnvelope

theorem compactAdditiveNatListConsRowsTailBranchCertificate_payload_le_uniform
    (tokenTable width tokenCount sourceBoundary targetBoundary index
      numericBound bitBound : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsecondSuccessor : index + 2 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListConsRowsTailBranchCertificate tokenTable width
          tokenCount sourceBoundary targetBoundary index data) <=
      natListConsTailInstalledPayloadPolynomial numericBound bitBound := by
  exact
    (compactAdditiveNatListConsRowsTailBranchCertificate_payload_le_transparent
      tokenTable width tokenCount sourceBoundary targetBoundary index
      numericBound bitBound data hwidth htokenCount hsecondSuccessor
      htokenTableSize hsourceBoundarySize htargetBoundarySize
      hnumericSize).trans
      (natListConsTailTransparentEnvelope_le_fullyFixed tokenTable width
        tokenCount sourceBoundary targetBoundary index numericBound bitBound
        data hwidth htokenCount hsecondSuccessor htokenTableSize
        hsourceBoundarySize htargetBoundarySize hnumericSize)

#print axioms
  compactAdditiveNatListConsRowsTailBranchCertificate_payload_le_uniform

end FoundationCompactNumericListedDirectNatListConsRowsTailUniformBound
