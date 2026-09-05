import integration.FoundationCompactNumericListedDirectNatListConsRowsTailTerminalPartsPayloadBound

/-! # Public payload bound for one natural-list cons tail terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailTerminalPayloadBound

open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalLeafBounds
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalPartsPayloadBound
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalResources
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalSemanticBounds

theorem compactAdditiveNatListConsRowsTailTerminalCertificate_payload_le_fullyFixed
    {tokenTable width tokenCount sourceBoundary targetBoundary index : Nat}
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index)
    (numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsecondSuccessor : index + 2 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListConsRowsTailTerminalCertificate tokenTable width
          tokenCount sourceBoundary targetBoundary index data) <=
      natListConsRowsTailTerminalFullyFixedPayloadPolynomial numericBound
        bitBound := by
  have facts := buildNatListConsRowsTailFixedFacts data numericBound bitBound
    hwidth htokenCount hsecondSuccessor hnumericSize
  have leaves := buildNatListConsRowsTailLeafBounds data numericBound bitBound
    facts htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have hparts :=
    compactAdditiveNatListConsRowsTailPartsCertificate_payload_le_fullyFixed
      data numericBound bitBound facts leaves
  simpa only [compactAdditiveNatListConsRowsTailTerminalCertificate,
    hybridFormulaStructuralPayloadBound] using hparts

#print axioms
  compactAdditiveNatListConsRowsTailTerminalCertificate_payload_le_fullyFixed

end FoundationCompactNumericListedDirectNatListConsRowsTailTerminalPayloadBound
