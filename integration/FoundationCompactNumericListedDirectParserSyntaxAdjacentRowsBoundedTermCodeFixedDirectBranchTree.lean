import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranches
import integration.FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds

/-! # Fixed-resource branch tree for all adjacent parser rows -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchTree

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAExplicitDirectUniversalBranches
open FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectBranches
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranches

noncomputable def
    compactParserSyntaxAdjacentRowsBoundedTermCodeFixedFullyDirectBranches
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
      compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchProof
        tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
        numericBound bitBound rowIndex hrowIndex hrowCount
        (hrows rowIndex hrowIndex) hvalueBound hwidth hwidthBit htokenCount
        hstateCount htokenTableSize hstateBoundarySize hareaNumeric hareaBit
        hnumericSize hbitPositive)

def
    compactParserSyntaxAdjacentRowsBoundedTermCodeFixedBranchesStructuralEnvelope
    (tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound : Nat) : Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope zeroValuation rowCount
    (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
      tokenCount stateBoundary stateCount valueBound) ∅
    (fun _ =>
      compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchResource
        tokenCount valueBound numericBound bitBound)
    rowCount

theorem
    compactParserSyntaxAdjacentRowsBoundedTermCodeFixedFullyDirectBranches_structuralPayloadBound_le
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
    (compactParserSyntaxAdjacentRowsBoundedTermCodeFixedFullyDirectBranches
      tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound hrows hrowCount hvalueBound hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hnumericSize hbitPositive).structuralPayloadBound rowCount <=
    compactParserSyntaxAdjacentRowsBoundedTermCodeFixedBranchesStructuralEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound := by
  have hbodyVariables :
      (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
        tokenCount stateBoundary stateCount valueBound).freeVariables ⊆
          (∅ : Finset Nat) := by
    rw [
      compactParserSyntaxAdjacentRowsBoundedUniversalBody_freeVariables_eq_empty]
  unfold
    compactParserSyntaxAdjacentRowsBoundedTermCodeFixedFullyDirectBranches
    compactParserSyntaxAdjacentRowsBoundedTermCodeFixedBranchesStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables rowCount
    (fun _ =>
      compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchResource
        tokenCount valueBound numericBound bitBound)
    rowCount
    (fun rowIndex hrowIndex =>
      compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchProof
        tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
        numericBound bitBound rowIndex hrowIndex hrowCount
        (hrows rowIndex hrowIndex) hvalueBound hwidth hwidthBit htokenCount
        hstateCount htokenTableSize hstateBoundarySize hareaNumeric hareaBit
        hnumericSize hbitPositive)
    (fun rowIndex hrowIndex =>
      compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchProof_payloadLength_le
        tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
        numericBound bitBound rowIndex hrowIndex hrowCount
        (hrows rowIndex hrowIndex) hvalueBound hwidth hwidthBit htokenCount
        hstateCount htokenTableSize hstateBoundarySize hareaNumeric hareaBit
        hnumericSize hbitPositive)

theorem
    compactParserSyntaxAdjacentRowsBoundedTermCodeFixedBranchesStructuralEnvelope_le_polynomial
    (tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound : Nat) :
    compactParserSyntaxAdjacentRowsBoundedTermCodeFixedBranchesStructuralEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
          numericBound bitBound <=
      explicitDirectUniversalBranchesPayloadPolynomial rowCount
        (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
          tokenCount stateBoundary stateCount valueBound)
        (compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchResource
          tokenCount valueBound numericBound bitBound) := by
  unfold
    compactParserSyntaxAdjacentRowsBoundedTermCodeFixedBranchesStructuralEnvelope
  exact directBranchesStructuralPayloadEnvelope_le_polynomial
    (compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchResource
      tokenCount valueBound numericBound bitBound)
    (fun _ =>
      compactParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchResource
        tokenCount valueBound numericBound bitBound)
    (fun _ => Nat.le_refl _)

#print axioms
  compactParserSyntaxAdjacentRowsBoundedTermCodeFixedFullyDirectBranches
#print axioms
  compactParserSyntaxAdjacentRowsBoundedTermCodeFixedFullyDirectBranches_structuralPayloadBound_le
#print axioms
  compactParserSyntaxAdjacentRowsBoundedTermCodeFixedBranchesStructuralEnvelope_le_polynomial

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedTermCodeFixedDirectBranchTree
