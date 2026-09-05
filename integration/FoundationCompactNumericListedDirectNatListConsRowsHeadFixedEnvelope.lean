import integration.FoundationCompactNumericListedDirectNatListConsRowsHeadFixedInputs
import integration.FoundationCompactNumericListedDirectNatListConsRowsHeadCertificate
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-! # Fixed public envelope for the natural-list cons head witnesses -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 260000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsHeadFixedEnvelope

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsHeadCertificate
open FoundationCompactNumericListedDirectNatListConsRowsHeadFixedInputs
open FoundationCompactNumericListedDirectNatListConsRowsHeadSyntaxUniformBound
open FoundationCompactNumericListedDirectNatListConsRowsHeadTerminalUniformBound

private abbrev consHeadZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation

def natListConsHeadInstalledPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02 0 numericBound
    (natListConsHeadTerminalBodyCodeEnvelope bitBound)
    (natListConsHeadTerminalPayloadEnvelope numericBound bitBound)

theorem natListConsHeadTransparentEnvelope_le_fullyFixed
    (tokenTable width tokenCount targetBoundary head numericBound bitBound : Nat)
    (htokenCountValue : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hheadSize : Nat.size head <= bitBound)
    (data : CompactAdditiveNatListConsHeadData tokenTable width tokenCount
      targetBoundary head) :
    explicitBoundedWitnessHybridStructuralPayloadEnvelope
        consHeadZeroValuation tokenCount
        (compactAdditiveNatListConsRowsHeadTerminal tokenTable width tokenCount
          targetBoundary head)
        (compactAdditiveNatListConsHeadValues data)
        (natListConsHeadTerminalPayloadEnvelope numericBound bitBound) <=
      natListConsHeadInstalledPayloadPolynomial numericBound bitBound := by
  let body := compactAdditiveNatListConsRowsHeadTerminal tokenTable width
    tokenCount targetBoundary head
  let values := compactAdditiveNatListConsHeadValues data
  have hbodyCode := natListConsHeadBodyCode_le_public tokenTable width tokenCount
    targetBoundary head bitBound htableSize hwidthSize htokenCountSize
    htargetBoundarySize hheadSize
  have hcontextCode := natListConsHeadBodyContextCode_le_zero tokenTable width
    tokenCount targetBoundary head
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02
      consHeadZeroValuation 0 tokenCount numericBound
      (natListConsHeadTerminalBodyCodeEnvelope bitBound) body values
      (compactAdditiveNatListConsHeadValues_le data) htokenCountValue hbodyCode
      hcontextCode (le_refl
        (natListConsHeadTerminalPayloadEnvelope numericBound bitBound))
  simpa only [natListConsHeadInstalledPayloadPolynomial, body, values] using
    hfixed

#print axioms natListConsHeadTransparentEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectNatListConsRowsHeadFixedEnvelope
