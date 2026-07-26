import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectUniversal
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchTreeUniformResource

/-!
# Proof-independent resource bound for the bounded-row universal

This module reuses the compiled branch tree while replacing its selected-row
resource by the finite uniform ceiling.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectUniversalUniformResource

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchTree
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectUniversal
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchTreeUniformResource

def compactSequentFormulaStepRowsBoundedDirectUniversalUniformResource
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound : Nat) : Nat :=
  let body :=
    compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount valueBound
  compileContextualTermBoundedUniversalPayloadEnvelope ∅ rowCount
    (Rew.bShift (shortBinaryNumeralTerm rowCount)) body
    (closedShortBoundEqualityPayloadPolynomial rowCount)
    (contextualBranchesUnderBoundPayloadEnvelope ∅ rowCount
      (Rewriting.free body)
      (compactSequentFormulaStepRowsBoundedDirectBranchesUniformStructuralEnvelope
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound))

theorem
    compileCompactSequentFormulaStepRowsBoundedDirectUniversalContext_payloadLength_le_uniform
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactSequentFormulaStepRowBounded tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound) :
    (compileCompactSequentFormulaStepRowsBoundedDirectUniversalContext
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound hrows).payloadLength <=
      compactSequentFormulaStepRowsBoundedDirectUniversalUniformResource
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound := by
  let body :=
    compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount valueBound
  let branches :=
    compactSequentFormulaStepRowsBoundedFullyDirectBranches tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowCount
      valueBound hrows
  let boundEquality :=
    compactSequentFormulaStepRowsBoundedDirectBoundEquality rowCount
  let direct := compileContextualTermBoundedUniversal (Gamma := ∅) rowCount
    (Rew.bShift (shortBinaryNumeralTerm rowCount)) body boundEquality branches
  have hboundRaw :=
    compileClosedShortBoundEquality_payloadLength_le_publicPolynomial rowCount
  have hbound : boundEquality.payloadLength <=
      closedShortBoundEqualityPayloadPolynomial rowCount := by
    simpa only [boundEquality,
      compactSequentFormulaStepRowsBoundedDirectBoundEquality,
      CertifiedPAContextProof.castContext_payloadLength,
      CertifiedPAContextProof.cast_payloadLength] using hboundRaw
  have hbranchesCore : branches.structuralPayloadBound rowCount <=
      compactSequentFormulaStepRowsBoundedDirectBranchesUniformStructuralEnvelope
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound := by
    exact
      compactSequentFormulaStepRowsBoundedFullyDirectBranches_structuralPayloadBound_le_uniform
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound hrows
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ rowCount
    (Rewriting.free body)
    (compactSequentFormulaStepRowsBoundedDirectBranchesUniformStructuralEnvelope
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound)
  have hbranches :
      branches.compileUnderBoundAssumptionStructuralPayloadBound <=
        branchResource := by
    unfold branchResource contextualBranchesUnderBoundPayloadEnvelope
      CertifiedContextFiniteUniversalBranches.compileUnderBoundAssumptionStructuralPayloadBound
      CertifiedContextFiniteUniversalBranches.underExhaustionStructuralPayloadBound
    dsimp only [body] at hbranchesCore ⊢
    simp only [Finset.image_empty] at hbranchesCore ⊢
    omega
  have hstructural :=
    compileContextualTermBoundedUniversal_payloadLength_le_structural
      (Gamma := ∅) rowCount
      (Rew.bShift (shortBinaryNumeralTerm rowCount)) body
      boundEquality branches
  have henvelope :=
    compileContextualTermBoundedUniversalStructuralPayloadBound_le_envelope
      (Gamma := ∅) rowCount
      (Rew.bShift (shortBinaryNumeralTerm rowCount)) body
      boundEquality branches
      (closedShortBoundEqualityPayloadPolynomial rowCount)
      branchResource hbound hbranches
  unfold compileCompactSequentFormulaStepRowsBoundedDirectUniversalContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change direct.payloadLength <= _
  exact hstructural.trans (henvelope.trans (by rfl))

#print axioms
  compileCompactSequentFormulaStepRowsBoundedDirectUniversalContext_payloadLength_le_uniform

end FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectUniversalUniformResource
