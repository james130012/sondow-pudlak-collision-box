import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsBoundedExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedBranchPublicDirectCompiler

/-!
# Branch-sensitive direct bounds for all adjacent rows

Each row uses the checked branch-sensitive `14 + 14 + 9` witness compiler.
Rows are aggregated only over `Fin rowCount`; `valueBound` is not enumerated.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped BigOperators

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsBranchDirectBounds

open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedBranchPublicDirectCompiler
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsBoundedExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAExplicitDirectUniversalBranches
open FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectBranchProof
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount valueBound rowIndex : Nat)
    (hrow : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound) :
    CertifiedPAContextProof
      (valuationContext
        (Rewriting.free
          (compactFormulaTransformAdjacentRowsBoundedUniversalBody
            tokenTable width tokenCount stateBoundary stateCount mode
            witnessStart witnessFinish witnessCount valueBound)).freeVariables
        (extendValuation rowIndex zeroValuation))
      (Rewriting.free
        (compactFormulaTransformAdjacentRowsBoundedUniversalBody
          tokenTable width tokenCount stateBoundary stateCount mode witnessStart
          witnessFinish witnessCount valueBound)) := by
  have hcurrent : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue (adjacentRowsBranchValuation rowIndex) (&0 : ValuationTerm))
      mode witnessStart witnessFinish witnessCount valueBound := by
    simpa [adjacentRowsBranchValuation, zeroValuation] using hrow
  let raw :=
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexBranchPublicDirectOfGraph
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
      witnessFinish witnessCount valueBound hcurrent
  exact castValuationContextProof
    (compactFormulaTransformAdjacentRowsBoundedUniversalBody_free_alignment
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound).symm raw

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectBranchPayloadResource
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount valueBound rowIndex : Nat)
    (hrow : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound) : Nat :=
  compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexBranchPublicDirectPayloadEnvelopeOfGraph
    (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
    stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
    witnessFinish witnessCount valueBound (by
      simpa [adjacentRowsBranchValuation, zeroValuation] using hrow)

theorem
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectBranchProof_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount valueBound rowIndex : Nat)
    (hrow : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound) :
    (compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectBranchProof
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound rowIndex hrow).payloadLength <=
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectBranchPayloadResource
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound rowIndex hrow := by
  unfold
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectBranchProof
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectBranchPayloadResource
  rw [castValuationContextProof_payloadLength_eq]
  exact
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexBranchPublicDirectOfGraph_payloadLength_le
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
      witnessFinish witnessCount valueBound _

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectLeafPayloadResourceSum
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) : Nat :=
  ∑ rowIndex : Fin rowCount,
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectBranchPayloadResource
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound rowIndex
      (hrows rowIndex rowIndex.isLt)

theorem
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectBranchProof_le_leafSum
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound rowIndex : Nat)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound)
    (hrowIndex : rowIndex < rowCount) :
    (compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectBranchProof
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound rowIndex
      (hrows rowIndex hrowIndex)).payloadLength <=
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectLeafPayloadResourceSum
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows := by
  let finiteIndex : Fin rowCount := ⟨rowIndex, hrowIndex⟩
  have hleaf :=
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectBranchProof_payloadLength_le
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound rowIndex
      (hrows rowIndex hrowIndex)
  have hmember :
      compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectBranchPayloadResource
          tokenTable width tokenCount stateBoundary stateCount mode witnessStart
          witnessFinish witnessCount valueBound finiteIndex
          (hrows finiteIndex finiteIndex.isLt) <=
        compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectLeafPayloadResourceSum
          tokenTable width tokenCount stateBoundary stateCount rowCount mode
          witnessStart witnessFinish witnessCount valueBound hrows := by
    unfold
      compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectLeafPayloadResourceSum
    exact Finset.single_le_sum
      (fun (candidate : Fin rowCount) _ => Nat.zero_le
        (compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectBranchPayloadResource
          tokenTable width tokenCount stateBoundary stateCount mode witnessStart
          witnessFinish witnessCount valueBound candidate
          (hrows candidate candidate.isLt)))
      (Finset.mem_univ finiteIndex)
  dsimp only [finiteIndex] at hmember
  exact hleaf.trans hmember

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveFullyDirectBranches
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    CertifiedContextFiniteUniversalBranches
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (Rewriting.free
        (compactFormulaTransformAdjacentRowsBoundedUniversalBody
          tokenTable width tokenCount stateBoundary stateCount mode witnessStart
          witnessFinish witnessCount valueBound)) rowCount := by
  have hbodyVariables :
      (compactFormulaTransformAdjacentRowsBoundedUniversalBody
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound).freeVariables ⊆
          (∅ : Finset Nat) := by
    rw [
      compactFormulaTransformAdjacentRowsBoundedUniversalBody_freeVariables_eq_empty]
  exact buildExplicitDirectUniversalBranches ∅ hbodyVariables rowCount
    (fun rowIndex hrowIndex =>
      compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectBranchProof
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound rowIndex
        (hrows rowIndex hrowIndex))

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveFullyDirectBranchesStructuralEnvelope
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) : Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope zeroValuation rowCount
    (compactFormulaTransformAdjacentRowsBoundedUniversalBody
      tokenTable width tokenCount stateBoundary stateCount mode witnessStart
      witnessFinish witnessCount valueBound) ∅
    (fun _ =>
      compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectLeafPayloadResourceSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows) rowCount

theorem
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveFullyDirectBranches_structuralPayloadBound_le
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    (compactFormulaTransformAdjacentRowsBoundedBranchSensitiveFullyDirectBranches
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows).structuralPayloadBound
        rowCount <=
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveFullyDirectBranchesStructuralEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows := by
  have hbodyVariables :
      (compactFormulaTransformAdjacentRowsBoundedUniversalBody
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound).freeVariables ⊆
          (∅ : Finset Nat) := by
    rw [
      compactFormulaTransformAdjacentRowsBoundedUniversalBody_freeVariables_eq_empty]
  unfold
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveFullyDirectBranches
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveFullyDirectBranchesStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables rowCount
    (fun _ =>
      compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectLeafPayloadResourceSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows)
    rowCount
    (fun rowIndex hrowIndex =>
      compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectBranchProof
        tokenTable width tokenCount stateBoundary stateCount mode witnessStart
        witnessFinish witnessCount valueBound rowIndex
        (hrows rowIndex hrowIndex))
    (fun rowIndex hrowIndex =>
      compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectBranchProof_le_leafSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound rowIndex hrows
        hrowIndex)

theorem
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveFullyDirectBranchesStructuralEnvelope_le_polynomial
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : forall rowIndex, rowIndex < rowCount ->
      CompactFormulaTransformAdjacentCurrentBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount valueBound) :
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveFullyDirectBranchesStructuralEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows <=
      explicitDirectUniversalBranchesPayloadPolynomial rowCount
        (compactFormulaTransformAdjacentRowsBoundedUniversalBody
          tokenTable width tokenCount stateBoundary stateCount mode witnessStart
          witnessFinish witnessCount valueBound)
        (compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectLeafPayloadResourceSum
          tokenTable width tokenCount stateBoundary stateCount rowCount mode
          witnessStart witnessFinish witnessCount valueBound hrows) := by
  unfold
    compactFormulaTransformAdjacentRowsBoundedBranchSensitiveFullyDirectBranchesStructuralEnvelope
  exact directBranchesStructuralPayloadEnvelope_le_polynomial
    (compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectLeafPayloadResourceSum
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound hrows)
    (fun _ =>
      compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectLeafPayloadResourceSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows)
    (fun _ => Nat.le_refl _)

#print axioms
  compactFormulaTransformAdjacentRowsBoundedBranchSensitiveDirectBranchProof_payloadLength_le
#print axioms
  compactFormulaTransformAdjacentRowsBoundedBranchSensitiveFullyDirectBranches_structuralPayloadBound_le
#print axioms
  compactFormulaTransformAdjacentRowsBoundedBranchSensitiveFullyDirectBranchesStructuralEnvelope_le_polynomial

end FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsBranchDirectBounds
