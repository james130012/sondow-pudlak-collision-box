import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsBoundedExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectLeafPublicFiniteBounds

/-!
# Graph-independent finite envelope for all adjacent-row direct leaves

Each checked row selects one member of the finite 37-coordinate family. Summing
that pointwise bound removes the complete row-graph package from the numerical
leaf resource.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic
open scoped BigOperators

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsDirectLeafPublicFiniteBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectLeafPublicFiniteBounds

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedDirectLeafPublicFiniteCoordinateSum
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat) : Nat :=
  ∑ rowIndex : Fin rowCount,
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFiniteCoordinatePayloadEnvelopeSum
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
      witnessFinish witnessCount valueBound

theorem
    compactFormulaTransformAdjacentRowsBoundedDirectLeafPayloadResourceSum_le_publicFiniteCoordinateSum
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactFormulaTransformAdjacentCurrentBounded tokenTable width tokenCount
        stateBoundary stateCount rowIndex mode witnessStart witnessFinish
        witnessCount valueBound) :
    compactFormulaTransformAdjacentRowsBoundedDirectLeafPayloadResourceSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound hrows <=
      compactFormulaTransformAdjacentRowsBoundedDirectLeafPublicFiniteCoordinateSum
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound := by
  unfold
    compactFormulaTransformAdjacentRowsBoundedDirectLeafPayloadResourceSum
    compactFormulaTransformAdjacentRowsBoundedDirectLeafPublicFiniteCoordinateSum
  apply Finset.sum_le_sum
  intro rowIndex hrowIndex
  unfold compactFormulaTransformAdjacentRowsBoundedDirectBranchPayloadResource
  exact
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph_le_finiteCoordinateSum
      (adjacentRowsBranchValuation rowIndex) tokenTable width tokenCount
      stateBoundary stateCount (&0 : ValuationTerm) mode witnessStart
      witnessFinish witnessCount valueBound (by
        simpa [adjacentRowsBranchValuation, zeroValuation] using
          hrows rowIndex rowIndex.isLt)

#print axioms
  compactFormulaTransformAdjacentRowsBoundedDirectLeafPayloadResourceSum_le_publicFiniteCoordinateSum

end FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsDirectLeafPublicFiniteBounds
