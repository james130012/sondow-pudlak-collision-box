import integration.FoundationCompactNumericListedDirectNatListConsRowsTailBranchCertificate
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailFixedInputs
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity04Bounds

/-! # Fixed public envelope for one natural-list cons tail branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 260000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailFixedEnvelope

open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity04Bounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailFixedInputs
open FoundationCompactNumericListedDirectNatListConsRowsTailSyntaxUniformBound
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalResources

def natListConsTailInstalledPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04
    (natListConsRowsTailTerminalContextCodePolynomial numericBound)
    numericBound (natListConsRowsTailBranchFormulaCodePolynomial bitBound)
    (natListConsRowsTailTerminalFullyFixedPayloadPolynomial numericBound
      bitBound)

theorem natListConsTailTransparentEnvelope_le_fullyFixed
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
    explicitBoundedWitnessHybridStructuralPayloadEnvelope
        (consRowsTailValuation index) tokenCount
        (compactAdditiveNatListConsRowsTailBranchTerminal tokenTable width
          tokenCount sourceBoundary targetBoundary)
        (compactAdditiveNatListConsTailValues data)
        (natListConsRowsTailTerminalFullyFixedPayloadPolynomial numericBound
          bitBound) <=
      natListConsTailInstalledPayloadPolynomial numericBound bitBound := by
  let body := compactAdditiveNatListConsRowsTailBranchTerminal tokenTable width
    tokenCount sourceBoundary targetBoundary
  let values := compactAdditiveNatListConsTailValues data
  have hindex : index <= numericBound := by omega
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbodyCode := natListConsTailBodyCode_le_public tokenTable width
    tokenCount sourceBoundary targetBoundary bitBound htokenTableSize
    hwidthSize htokenCountSize hsourceBoundarySize htargetBoundarySize
  have hcontextCode := natListConsTailBodyContextCode_le_public tokenTable width
    tokenCount sourceBoundary targetBoundary index numericBound hindex
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity04
      (consRowsTailValuation index)
      (natListConsRowsTailTerminalContextCodePolynomial numericBound)
      tokenCount numericBound
      (natListConsRowsTailBranchFormulaCodePolynomial bitBound) body values
      (compactAdditiveNatListConsTailValues_le data) htokenCount hbodyCode
      hcontextCode
      (le_refl
        (natListConsRowsTailTerminalFullyFixedPayloadPolynomial numericBound
          bitBound))
  simpa only [natListConsTailInstalledPayloadPolynomial, body, values] using
    hfixed

#print axioms natListConsTailTransparentEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectNatListConsRowsTailFixedEnvelope
