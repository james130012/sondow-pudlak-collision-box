import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalTransparentBound
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalTransparentNormalized
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBranchesAtBoundFixed
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailShiftedBoundFixed
import integration.FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds

/-! # Fully fixed payload bound for the cons-tail bounded universal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 240000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailUniversalFixedBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchTreeFixedBound
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchTreeUniformBound
open FoundationCompactNumericListedDirectNatListConsRowsTailContextualBranchesFixed
open FoundationCompactNumericListedDirectNatListConsRowsTailShiftedBoundFixed
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBranchesAtBoundFixed
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyPolynomialResources
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodySyntaxUniformBound
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalTransparentBound
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalTransparentNormalized
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalTransparentResources

def natListConsRowsTailUniversalFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  closedShortUniversalShellFixedPayloadPolynomial numericBound bitBound
    (natListConsRowsTailUniversalSyntaxFixedPolynomial numericBound bitBound)
    (natListConsRowsTailUniversalBodyFormulaCodePolynomial numericBound bitBound)
    (natListConsRowsTailContextualBranchesFullyFixedPayloadPolynomial
      numericBound bitBound)
    (natListConsRowsTailShiftedBoundFixedPayloadPolynomial numericBound bitBound)

theorem natListConsRowsTailUniversalTransparentPayloadEnvelope_le_fullyFixed
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
    natListConsRowsTailUniversalTransparentPayloadEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows <=
      natListConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let body := natListConsRowsTailUniversalBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅
    sourceCount (Rewriting.free body)
    (hybridBranchesStructuralPayloadEnvelope sourceCount (∅ : Finset Nat)
      (compactAdditiveNatListConsRowsTailUniversalBranchesAtBoundTerm
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        rows))
  let boundResource := compileShiftedBoundEqualityPayloadResource
    natListConsRowsTailUniversalZeroValuation ∅
      (shortBinaryNumeralTerm sourceCount)
  have hsourceCount : sourceCount <= numericBound := by omega
  have hsourceCountSize : Nat.size sourceCount <= bitBound :=
    (Nat.size_le_size hsourceCount).trans hnumericSize
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody :
      (binaryFormulaCode body).length <=
        natListConsRowsTailUniversalBodyFormulaCodePolynomial numericBound
          bitBound := by
    dsimp only [body, natListConsRowsTailUniversalBody]
    exact compactAdditiveNatListConsRowsTailBody_code_length_le_uniform
      tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound htokenCount htokenTableSize hwidthSize htokenCountSize
      hsourceBoundarySize htargetBoundarySize
  have hboundResource :
      boundResource <=
        natListConsRowsTailShiftedBoundFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [boundResource]
    exact natListConsRowsTailShiftedBoundResource_le_fullyFixed sourceCount
      numericBound bitBound hsourceCount hsourceCountSize
  have hbranchResource :
      branchResource <=
        natListConsRowsTailContextualBranchesFullyFixedPayloadPolynomial
          numericBound bitBound := by
    dsimp only [branchResource]
    exact natListConsRowsTailUniversalBranchesAtBoundResource_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        numericBound bitBound rows hwidth htokenCount hsourceCountSuccessor
        htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have hshell :=
    compileContextualTermBoundedUniversalPayloadEnvelope_empty_short_le_fixed
      body sourceCount numericBound bitBound
      (natListConsRowsTailUniversalSyntaxFixedPolynomial numericBound bitBound)
      (natListConsRowsTailUniversalBodyFormulaCodePolynomial numericBound
        bitBound)
      boundResource branchResource
      (natListConsRowsTailShiftedBoundFixedPayloadPolynomial numericBound
        bitBound)
      (natListConsRowsTailContextualBranchesFullyFixedPayloadPolynomial
        numericBound bitBound)
      hsourceCount hsourceCountSize
      (by
        unfold natListConsRowsTailUniversalSyntaxFixedPolynomial
        omega)
      hbody hboundResource hbranchResource
  rw [natListConsRowsTailUniversalTransparentPayloadEnvelope_eq_normalized]
  unfold natListConsRowsTailUniversalFullyFixedPayloadPolynomial
  simpa only [body, branchResource, boundResource] using hshell

theorem compactAdditiveNatListConsRowsTailUniversalCertificate_payload_le_fullyFixed
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
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListConsRowsTailUniversalCertificate tokenTable
          width tokenCount sourceBoundary sourceCount targetBoundary rows) <=
      natListConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound
        bitBound := by
  exact
    (compactAdditiveNatListConsRowsTailUniversalCertificate_payload_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      rows).trans
    (natListConsRowsTailUniversalTransparentPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound rows hwidth htokenCount hsourceCountSuccessor
      htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize)

#print axioms
  natListConsRowsTailUniversalTransparentPayloadEnvelope_le_fullyFixed
#print axioms
  compactAdditiveNatListConsRowsTailUniversalCertificate_payload_le_fullyFixed

end FoundationCompactNumericListedDirectNatListConsRowsTailUniversalFixedBound
