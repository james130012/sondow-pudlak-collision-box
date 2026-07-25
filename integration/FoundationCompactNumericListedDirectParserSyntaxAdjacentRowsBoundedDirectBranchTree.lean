import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectBranches
import integration.FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds

/-!
# Finite direct branch tree for all bounded adjacent parser rows

The same fixed public row resource bounds every leaf.  The explicit finite
branch constructor then exposes the complete proof-tree assembly cost and its
polynomial envelope.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectBranchTree

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAExplicitDirectUniversalBranches
open FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectBranches

noncomputable def compactParserSyntaxAdjacentRowsBoundedFullyDirectBranches
    (tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
        stateBoundary stateCount rowIndex valueBound)
    (hrowCount : rowCount <= numericBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    CertifiedContextFiniteUniversalBranches
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (Rewriting.free
        (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
          tokenCount stateBoundary stateCount valueBound)) rowCount := by
  have hbodyVariables :
      (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
        tokenCount stateBoundary stateCount valueBound).freeVariables ⊆
          (∅ : Finset Nat) := by
    rw [
      compactParserSyntaxAdjacentRowsBoundedUniversalBody_freeVariables_eq_empty]
  exact buildExplicitDirectUniversalBranches ∅ hbodyVariables rowCount
    (fun rowIndex hrowIndex =>
      compactParserSyntaxAdjacentRowsBoundedDirectBranchProof tokenTable width
        tokenCount stateBoundary stateCount rowCount valueBound numericBound
        bitBound rowIndex hrowIndex hrowCount (hrows rowIndex hrowIndex)
        hvalueBound hwidth hwidthBit htokenCount hstateCount htokenTableSize
        hstateBoundarySize hareaNumeric hareaBit hnumericSize hbitPositive)

def compactParserSyntaxAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope
    (tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound : Nat) : Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope zeroValuation rowCount
    (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
      tokenCount stateBoundary stateCount valueBound) ∅
    (fun _ =>
      compactParserSyntaxAdjacentRowsBoundedDirectBranchResource tokenTable
        width tokenCount stateBoundary stateCount valueBound numericBound
          bitBound)
    rowCount

theorem
    compactParserSyntaxAdjacentRowsBoundedFullyDirectBranches_structuralPayloadBound_le
    (tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
        stateBoundary stateCount rowIndex valueBound)
    (hrowCount : rowCount <= numericBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compactParserSyntaxAdjacentRowsBoundedFullyDirectBranches tokenTable width
      tokenCount stateBoundary stateCount rowCount valueBound numericBound
      bitBound hrows hrowCount hvalueBound hwidth hwidthBit htokenCount
      hstateCount htokenTableSize hstateBoundarySize hareaNumeric hareaBit
      hnumericSize hbitPositive).structuralPayloadBound rowCount <=
    compactParserSyntaxAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
        numericBound bitBound := by
  have hbodyVariables :
      (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
        tokenCount stateBoundary stateCount valueBound).freeVariables ⊆
          (∅ : Finset Nat) := by
    rw [
      compactParserSyntaxAdjacentRowsBoundedUniversalBody_freeVariables_eq_empty]
  unfold compactParserSyntaxAdjacentRowsBoundedFullyDirectBranches
    compactParserSyntaxAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables rowCount
    (fun _ =>
      compactParserSyntaxAdjacentRowsBoundedDirectBranchResource tokenTable
        width tokenCount stateBoundary stateCount valueBound numericBound
          bitBound)
    rowCount
    (fun rowIndex hrowIndex =>
      compactParserSyntaxAdjacentRowsBoundedDirectBranchProof tokenTable width
        tokenCount stateBoundary stateCount rowCount valueBound numericBound
        bitBound rowIndex hrowIndex hrowCount (hrows rowIndex hrowIndex)
        hvalueBound hwidth hwidthBit htokenCount hstateCount htokenTableSize
        hstateBoundarySize hareaNumeric hareaBit hnumericSize hbitPositive)
    (fun rowIndex hrowIndex =>
      compactParserSyntaxAdjacentRowsBoundedDirectBranchProof_payloadLength_le
        tokenTable width tokenCount stateBoundary stateCount rowCount
        valueBound numericBound bitBound rowIndex hrowIndex hrowCount
        (hrows rowIndex hrowIndex) hvalueBound hwidth hwidthBit htokenCount
        hstateCount htokenTableSize hstateBoundarySize hareaNumeric hareaBit
        hnumericSize hbitPositive)

theorem
    compactParserSyntaxAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope_le_polynomial
    (tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound : Nat) :
    compactParserSyntaxAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
          numericBound bitBound <=
      explicitDirectUniversalBranchesPayloadPolynomial rowCount
        (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
          tokenCount stateBoundary stateCount valueBound)
        (compactParserSyntaxAdjacentRowsBoundedDirectBranchResource tokenTable
          width tokenCount stateBoundary stateCount valueBound numericBound
            bitBound) := by
  unfold
    compactParserSyntaxAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope
  exact directBranchesStructuralPayloadEnvelope_le_polynomial
    (compactParserSyntaxAdjacentRowsBoundedDirectBranchResource tokenTable
      width tokenCount stateBoundary stateCount valueBound numericBound
        bitBound)
    (fun _ =>
      compactParserSyntaxAdjacentRowsBoundedDirectBranchResource tokenTable
        width tokenCount stateBoundary stateCount valueBound numericBound
          bitBound)
    (fun _ => Nat.le_refl _)

#print axioms compactParserSyntaxAdjacentRowsBoundedFullyDirectBranches
#print axioms
  compactParserSyntaxAdjacentRowsBoundedFullyDirectBranches_structuralPayloadBound_le
#print axioms
  compactParserSyntaxAdjacentRowsBoundedFullyDirectBranchesStructuralEnvelope_le_polynomial

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectBranchTree
