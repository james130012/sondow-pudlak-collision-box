import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniformBound
import integration.FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds

/-! # Uniform finite branch tree for natural-list cons tail rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 220000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailBranchTreeUniformBound

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailFixedEnvelope
open FoundationCompactNumericListedDirectNatListConsRowsTailUniformBound

private abbrev consRowsTailTreeZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation

noncomputable def compactAdditiveNatListConsRowsTailUniformBranches
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    CheckedHybridValuationUniversalBranches consRowsTailTreeZeroValuation
      (compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
        sourceBoundary targetBoundary) sourceCount :=
  buildExplicitHybridUniversalBranches sourceCount (fun index hindex =>
    compactAdditiveNatListConsRowsTailBranchCertificate tokenTable width
      tokenCount sourceBoundary targetBoundary index (rows ⟨index, hindex⟩))

theorem compactAdditiveNatListConsRowsTailUniformBranches_leafPayloadBound
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCountSuccessor : sourceCount + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    HybridBranchesLeafPayloadBound
      (natListConsTailInstalledPayloadPolynomial numericBound bitBound)
      (compactAdditiveNatListConsRowsTailUniformBranches tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows) := by
  unfold compactAdditiveNatListConsRowsTailUniformBranches
  apply buildExplicitHybridUniversalBranches_leafPayloadBound
  intro index hindex
  have hsecondSuccessor : index + 2 <= numericBound := by omega
  exact
    compactAdditiveNatListConsRowsTailBranchCertificate_payload_le_uniform
      tokenTable width tokenCount sourceBoundary targetBoundary index
      numericBound bitBound (rows ⟨index, hindex⟩) hwidth htokenCount
      hsecondSuccessor htokenTableSize hsourceBoundarySize
      htargetBoundarySize hnumericSize

def natListConsRowsTailBranchesStructuralPayloadPolynomial
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat) : Nat :=
  explicitHybridUniversalBranchesPayloadPolynomial sourceCount
    (compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
      sourceBoundary targetBoundary)
    (natListConsTailInstalledPayloadPolynomial numericBound bitBound)

theorem
    compactAdditiveNatListConsRowsTailUniformBranches_structuralPayloadBound_le
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCountSuccessor : sourceCount + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridBranchesStructuralPayloadEnvelope sourceCount (∅ : Finset Nat)
        (compactAdditiveNatListConsRowsTailUniformBranches tokenTable width
          tokenCount sourceBoundary sourceCount targetBoundary rows) <=
      natListConsRowsTailBranchesStructuralPayloadPolynomial tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary numericBound
        bitBound := by
  unfold natListConsRowsTailBranchesStructuralPayloadPolynomial
  exact hybridBranchesStructuralPayloadEnvelope_le_polynomial
    (natListConsTailInstalledPayloadPolynomial numericBound bitBound)
    (compactAdditiveNatListConsRowsTailUniformBranches tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary rows)
    (compactAdditiveNatListConsRowsTailUniformBranches_leafPayloadBound
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound rows hwidth htokenCount hsourceCountSuccessor
      htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize)

#print axioms compactAdditiveNatListConsRowsTailUniformBranches
#print axioms
  compactAdditiveNatListConsRowsTailUniformBranches_leafPayloadBound
#print axioms
  compactAdditiveNatListConsRowsTailUniformBranches_structuralPayloadBound_le

end FoundationCompactNumericListedDirectNatListConsRowsTailBranchTreeUniformBound
