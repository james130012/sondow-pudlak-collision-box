import integration.FoundationCompactNumericListedDirectNatListConsRowsHeadCertificate
import integration.FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds

/-! # Transparent payload bound for the installed cons-head witnesses -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 260000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsHeadTransparentBound

open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsHeadCertificate
open FoundationCompactNumericListedDirectNatListConsRowsHeadTerminalUniformBound

private abbrev consHeadZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation

theorem compactAdditiveNatListConsRowsHeadCertificate_payloadLength_le_transparent
    (tokenTable width tokenCount targetBoundary head numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hheadSize : Nat.size head <= bitBound)
    (data : CompactAdditiveNatListConsHeadData tokenTable width tokenCount
      targetBoundary head) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListConsRowsHeadCertificate tokenTable width
          tokenCount targetBoundary head data) <=
      explicitBoundedWitnessHybridStructuralPayloadEnvelope
        consHeadZeroValuation tokenCount
        (compactAdditiveNatListConsRowsHeadTerminal tokenTable width tokenCount
          targetBoundary head)
        (compactAdditiveNatListConsHeadValues data)
        (natListConsHeadTerminalPayloadEnvelope numericBound bitBound) := by
  let body := compactAdditiveNatListConsRowsHeadTerminal tokenTable width
    tokenCount targetBoundary head
  let values := compactAdditiveNatListConsHeadValues data
  let terminal :=
    compactAdditiveNatListConsRowsHeadTerminalCertificate tokenTable width
      tokenCount targetBoundary head data
  have hterminal :
      hybridFormulaStructuralPayloadBound terminal <=
        natListConsHeadTerminalPayloadEnvelope numericBound bitBound := by
    simpa only [terminal] using
      compactAdditiveNatListConsRowsHeadTerminalCertificate_payloadLength_le_uniform
        tokenTable width tokenCount targetBoundary head numericBound bitBound
        hwidthValue htokenCountValue htableSize hwidthSize htokenCountSize
        htargetBoundarySize hheadSize data
  have htransparent :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount body values (compactAdditiveNatListConsHeadValues_le data)
      terminal (natListConsHeadTerminalPayloadEnvelope numericBound bitBound)
      hterminal
  change hybridFormulaStructuralPayloadBound
      (compactAdditiveNatListConsRowsHeadCertificate tokenTable width
        tokenCount targetBoundary head data) <= _
  simpa only [compactAdditiveNatListConsRowsHeadCertificate, body, values,
    terminal, hybridFormulaStructuralPayloadBound] using htransparent

#print axioms
  compactAdditiveNatListConsRowsHeadCertificate_payloadLength_le_transparent

end FoundationCompactNumericListedDirectNatListConsRowsHeadTransparentBound
