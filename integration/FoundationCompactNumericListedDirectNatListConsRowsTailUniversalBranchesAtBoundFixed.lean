import integration.FoundationCompactNumericListedDirectNatListConsRowsTailContextualBranchesFixed
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCertificate
import integration.FoundationCompactPAHybridBranchesStructuralPayloadTransport

/-! # Fixed contextual bound after transporting branches to the numeral term -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBranchesAtBoundFixed

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridBranchesStructuralPayloadTransport
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchTreeUniformBound
open FoundationCompactNumericListedDirectNatListConsRowsTailContextualBranchesFixed
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCertificate

theorem natListConsRowsTailUniversalBranchesAtBoundResource_le_fullyFixed
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
    contextualBranchesUnderBoundPayloadEnvelope ∅ sourceCount
        (Rewriting.free
          (natListConsRowsTailUniversalBody tokenTable width tokenCount
            sourceBoundary targetBoundary))
        (hybridBranchesStructuralPayloadEnvelope sourceCount (∅ : Finset Nat)
          (compactAdditiveNatListConsRowsTailUniversalBranchesAtBoundTerm
            tokenTable width tokenCount sourceBoundary sourceCount
            targetBoundary rows)) <=
      natListConsRowsTailContextualBranchesFullyFixedPayloadPolynomial
        numericBound bitBound := by
  have htransport :
      hybridBranchesStructuralPayloadEnvelope sourceCount (∅ : Finset Nat)
          (compactAdditiveNatListConsRowsTailUniversalBranchesAtBoundTerm
            tokenTable width tokenCount sourceBoundary sourceCount
            targetBoundary rows) =
        hybridBranchesStructuralPayloadEnvelope sourceCount (∅ : Finset Nat)
          (compactAdditiveNatListConsRowsTailUniformBranches tokenTable width
            tokenCount sourceBoundary sourceCount targetBoundary rows) := by
    unfold compactAdditiveNatListConsRowsTailUniversalBranchesAtBoundTerm
    exact hybridBranchesStructuralPayloadEnvelope_transport sourceCount ∅
      natListConsRowsTailUniversalZeroValuation
      (natListConsRowsTailUniversalBody tokenTable width tokenCount
        sourceBoundary targetBoundary)
      sourceCount
      (termValue natListConsRowsTailUniversalZeroValuation
        (natListConsRowsTailUniversalBoundTerm sourceCount))
      (natListConsRowsTailUniversalBoundValue_eq sourceCount).symm
      (compactAdditiveNatListConsRowsTailUniformBranches tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows)
  rw [htransport]
  simpa only [natListConsRowsTailUniversalBody] using
    compactAdditiveNatListConsRowsTailContextualBranchesResource_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound rows hwidth htokenCount hsourceCountSuccessor
      htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize

#print axioms
  natListConsRowsTailUniversalBranchesAtBoundResource_le_fullyFixed

end FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBranchesAtBoundFixed
