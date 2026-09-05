import integration.FoundationCompactNumericListedDirectNatListConsRowsTailBranchCertificate
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailTerminalPayloadBound
import integration.FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds

/-! # Transparent payload bound for one installed cons-tail branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 260000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailTransparentBound

open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalPayloadBound
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalResources
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

theorem compactAdditiveNatListConsRowsTailBranchCertificate_payload_le_transparent
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
      explicitBoundedWitnessHybridStructuralPayloadEnvelope
        (consRowsTailValuation index) tokenCount
        (compactAdditiveNatListConsRowsTailBranchTerminal tokenTable width
          tokenCount sourceBoundary targetBoundary)
        (compactAdditiveNatListConsTailValues data)
        (natListConsRowsTailTerminalFullyFixedPayloadPolynomial numericBound
          bitBound) := by
  let body := compactAdditiveNatListConsRowsTailBranchTerminal tokenTable width
    tokenCount sourceBoundary targetBoundary
  let values := compactAdditiveNatListConsTailValues data
  let terminal :=
    compactAdditiveNatListConsRowsTailTerminalCertificate tokenTable width
      tokenCount sourceBoundary targetBoundary index data
  have hterminal :
      hybridFormulaStructuralPayloadBound terminal <=
        natListConsRowsTailTerminalFullyFixedPayloadPolynomial numericBound
          bitBound := by
    simpa only [terminal] using
      compactAdditiveNatListConsRowsTailTerminalCertificate_payload_le_fullyFixed
        data numericBound bitBound hwidth htokenCount hsecondSuccessor
        htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have htransparent :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount body values (compactAdditiveNatListConsTailValues_le data)
      terminal
      (natListConsRowsTailTerminalFullyFixedPayloadPolynomial numericBound
        bitBound) hterminal
  change hybridFormulaStructuralPayloadBound
      (compactAdditiveNatListConsRowsTailBranchCertificate tokenTable width
        tokenCount sourceBoundary targetBoundary index data) <= _
  simpa only [compactAdditiveNatListConsRowsTailBranchCertificate, body, values,
    terminal, hybridFormulaStructuralPayloadBound] using htransparent

#print axioms
  compactAdditiveNatListConsRowsTailBranchCertificate_payload_le_transparent

end FoundationCompactNumericListedDirectNatListConsRowsTailTransparentBound
