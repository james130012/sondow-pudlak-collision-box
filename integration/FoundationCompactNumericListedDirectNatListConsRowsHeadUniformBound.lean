import integration.FoundationCompactNumericListedDirectNatListConsRowsHeadTransparentBound
import integration.FoundationCompactNumericListedDirectNatListConsRowsHeadFixedEnvelope

/-! # Uniform installation of the natural-list cons head witnesses -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 320000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsHeadUniformBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsHeadCertificate
open FoundationCompactNumericListedDirectNatListConsRowsHeadTransparentBound
open FoundationCompactNumericListedDirectNatListConsRowsHeadFixedEnvelope

private abbrev consHeadZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation

theorem compactAdditiveNatListConsRowsHeadCertificate_payloadLength_le_uniform
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
      natListConsHeadInstalledPayloadPolynomial numericBound bitBound := by
  exact
    (compactAdditiveNatListConsRowsHeadCertificate_payloadLength_le_transparent
      tokenTable width tokenCount targetBoundary head numericBound bitBound
      hwidthValue htokenCountValue htableSize hwidthSize htokenCountSize
      htargetBoundarySize hheadSize data).trans
      (natListConsHeadTransparentEnvelope_le_fullyFixed tokenTable width
        tokenCount targetBoundary head numericBound bitBound htokenCountValue
        htableSize hwidthSize htokenCountSize htargetBoundarySize hheadSize
        data)

#print axioms
  compactAdditiveNatListConsRowsHeadCertificate_payloadLength_le_uniform

end FoundationCompactNumericListedDirectNatListConsRowsHeadUniformBound
