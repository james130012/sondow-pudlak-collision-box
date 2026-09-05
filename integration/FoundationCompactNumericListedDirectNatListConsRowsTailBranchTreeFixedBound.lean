import integration.FoundationCompactNumericListedDirectNatListConsRowsTailBranchTreeUniformBound
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodySyntaxUniformBound
import integration.FoundationCompactPABoundedUniversalEnvelopeMonotonicity
import integration.FoundationCompactPAUnaryAtomicTransportPolynomialBounds

/-! # Fully fixed polynomial bound for the cons-tail finite branch tree -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailBranchTreeFixedBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPABoundedUniversalEnvelopeMonotonicity
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchTreeUniformBound
open FoundationCompactNumericListedDirectNatListConsRowsTailFixedEnvelope
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyPolynomialResources
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodySyntaxUniformBound

def natListConsRowsTailUniversalSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound +
    natListConsRowsTailUniversalBodyFormulaCodePolynomial numericBound bitBound

def natListConsRowsTailUniversalFormulaFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  boundedUniversalClosedFormulaEnvelope
      (natListConsRowsTailUniversalSyntaxFixedPolynomial numericBound bitBound) +
    2 * natListConsRowsTailUniversalBodyFormulaCodePolynomial numericBound
      bitBound

def natListConsRowsTailUniversalLocalPayloadFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (natListConsRowsTailUniversalFormulaFixedPolynomial numericBound bitBound)

def natListConsRowsTailBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  (numericBound + 1) *
    (natListConsTailInstalledPayloadPolynomial numericBound bitBound +
      3 * natListConsRowsTailUniversalLocalPayloadFixedPolynomial numericBound
        bitBound)

theorem natListConsRowsTailBranchesStructuralPayloadPolynomial_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCountSuccessor : sourceCount + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidth : width <= numericBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    natListConsRowsTailBranchesStructuralPayloadPolynomial tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary numericBound
        bitBound <=
      natListConsRowsTailBranchesFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let body :=
    FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.compactAdditiveNatListConsRowsTailBody
      tokenTable width tokenCount sourceBoundary targetBoundary
  have hsourceCount : sourceCount <= numericBound := by omega
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody :
      (binaryFormulaCode body).length <=
        natListConsRowsTailUniversalBodyFormulaCodePolynomial numericBound
          bitBound := by
    dsimp only [body]
    exact compactAdditiveNatListConsRowsTailBody_code_length_le_uniform
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound htokenCount htokenTableSize hwidthSize htokenCountSize
      hsourceBoundarySize htargetBoundarySize
  have hsyntax :
      explicitHybridUniversalSyntaxResource sourceCount body <=
        natListConsRowsTailUniversalSyntaxFixedPolynomial numericBound
          bitBound := by
    unfold explicitHybridUniversalSyntaxResource
      natListConsRowsTailUniversalSyntaxFixedPolynomial
    omega
  have hclosed := boundedUniversalClosedFormulaEnvelope_mono hsyntax
  have hformula :
      explicitHybridUniversalFormulaEnvelope sourceCount body <=
        natListConsRowsTailUniversalFormulaFixedPolynomial numericBound
          bitBound := by
    unfold explicitHybridUniversalFormulaEnvelope
      natListConsRowsTailUniversalFormulaFixedPolynomial
    omega
  have hlocal :
      explicitHybridUniversalLocalPayloadEnvelope sourceCount body <=
        natListConsRowsTailUniversalLocalPayloadFixedPolynomial numericBound
          bitBound := by
    unfold explicitHybridUniversalLocalPayloadEnvelope
      natListConsRowsTailUniversalLocalPayloadFixedPolynomial
    exact smallContextAssemblyEnvelope_mono_local hformula
  unfold natListConsRowsTailBranchesStructuralPayloadPolynomial
    explicitHybridUniversalBranchesPayloadPolynomial
    natListConsRowsTailBranchesFullyFixedPayloadPolynomial
  exact Nat.mul_le_mul (by omega)
    (Nat.add_le_add le_rfl (Nat.mul_le_mul_left 3 hlocal))

theorem
    compactAdditiveNatListConsRowsTailUniformBranches_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat)
    (rows : (index : Fin sourceCount) ->
      FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.CompactAdditiveNatListConsTailRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCountSuccessor : sourceCount + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate.hybridBranchesStructuralPayloadEnvelope
        sourceCount (∅ : Finset Nat)
        (compactAdditiveNatListConsRowsTailUniformBranches tokenTable width
          tokenCount sourceBoundary sourceCount targetBoundary rows) <=
      natListConsRowsTailBranchesFullyFixedPayloadPolynomial numericBound
        bitBound := by
  exact
    (compactAdditiveNatListConsRowsTailUniformBranches_structuralPayloadBound_le
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound rows hwidth htokenCount hsourceCountSuccessor
      htokenTableSize hsourceBoundarySize htargetBoundarySize
      hnumericSize).trans
      (natListConsRowsTailBranchesStructuralPayloadPolynomial_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        numericBound bitBound htokenCount hsourceCountSuccessor htokenTableSize
        hwidth hsourceBoundarySize htargetBoundarySize hnumericSize)

#print axioms
  natListConsRowsTailBranchesStructuralPayloadPolynomial_le_fullyFixed
#print axioms
  compactAdditiveNatListConsRowsTailUniformBranches_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectNatListConsRowsTailBranchTreeFixedBound
