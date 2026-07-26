import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedUniformResourceBranches
import integration.FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds

/-! # Uniform-resource branch tree for all adjacent parser rows -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedUniformResourceBranchTree

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAExplicitDirectUniversalBranches
open FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectBranches
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedUniformResourceBranches

noncomputable def
    compactParserSyntaxAdjacentRowsBoundedUniformFullyDirectBranches
    (tokenTable width tokenCount stateBoundary stateCount rowCount
      formulaValueBound uniformValueBound numericBound bitBound : Nat)
    (hformulaValue : formulaValueBound <= uniformValueBound)
    (hrows : ∀ rowIndex < rowCount,
      CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
        stateBoundary stateCount rowIndex formulaValueBound)
    (hrowCount : rowCount <= numericBound)
    (hvalueBound : formulaValueBound <= numericBound)
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
          tokenCount stateBoundary stateCount formulaValueBound)) rowCount := by
  have hbodyVariables :
      (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
        tokenCount stateBoundary stateCount formulaValueBound).freeVariables ⊆
          (∅ : Finset Nat) := by
    rw [
      compactParserSyntaxAdjacentRowsBoundedUniversalBody_freeVariables_eq_empty]
  exact buildExplicitDirectUniversalBranches ∅ hbodyVariables rowCount
    (fun rowIndex hrowIndex =>
      compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchProof tokenTable
        width tokenCount stateBoundary stateCount rowCount formulaValueBound
        uniformValueBound numericBound bitBound rowIndex hformulaValue hrowIndex
        hrowCount (hrows rowIndex hrowIndex) hvalueBound hwidth hwidthBit
        htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
        hareaBit hnumericSize hbitPositive)

def compactParserSyntaxAdjacentRowsBoundedUniformBranchesStructuralEnvelope
    (tokenTable width tokenCount stateBoundary stateCount rowCount
      formulaValueBound uniformValueBound numericBound bitBound : Nat) : Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope zeroValuation rowCount
    (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
      tokenCount stateBoundary stateCount formulaValueBound) ∅
    (fun _ =>
      compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchResource
        tokenCount uniformValueBound numericBound bitBound)
    rowCount

theorem
    compactParserSyntaxAdjacentRowsBoundedUniformFullyDirectBranches_structuralPayloadBound_le
    (tokenTable width tokenCount stateBoundary stateCount rowCount
      formulaValueBound uniformValueBound numericBound bitBound : Nat)
    (hformulaValue : formulaValueBound <= uniformValueBound)
    (hrows : ∀ rowIndex < rowCount,
      CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
        stateBoundary stateCount rowIndex formulaValueBound)
    (hrowCount : rowCount <= numericBound)
    (hvalueBound : formulaValueBound <= numericBound)
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
    (compactParserSyntaxAdjacentRowsBoundedUniformFullyDirectBranches tokenTable
      width tokenCount stateBoundary stateCount rowCount formulaValueBound
      uniformValueBound numericBound bitBound hformulaValue hrows hrowCount
      hvalueBound hwidth hwidthBit htokenCount hstateCount htokenTableSize
      hstateBoundarySize hareaNumeric hareaBit hnumericSize
      hbitPositive).structuralPayloadBound rowCount <=
    compactParserSyntaxAdjacentRowsBoundedUniformBranchesStructuralEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowCount
      formulaValueBound uniformValueBound numericBound bitBound := by
  have hbodyVariables :
      (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
        tokenCount stateBoundary stateCount formulaValueBound).freeVariables ⊆
          (∅ : Finset Nat) := by
    rw [
      compactParserSyntaxAdjacentRowsBoundedUniversalBody_freeVariables_eq_empty]
  unfold compactParserSyntaxAdjacentRowsBoundedUniformFullyDirectBranches
    compactParserSyntaxAdjacentRowsBoundedUniformBranchesStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables rowCount
    (fun _ =>
      compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchResource
        tokenCount uniformValueBound numericBound bitBound)
    rowCount
    (fun rowIndex hrowIndex =>
      compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchProof tokenTable
        width tokenCount stateBoundary stateCount rowCount formulaValueBound
        uniformValueBound numericBound bitBound rowIndex hformulaValue hrowIndex
        hrowCount (hrows rowIndex hrowIndex) hvalueBound hwidth hwidthBit
        htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
        hareaBit hnumericSize hbitPositive)
    (fun rowIndex hrowIndex =>
      compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchProof_payloadLength_le
        tokenTable width tokenCount stateBoundary stateCount rowCount
        formulaValueBound uniformValueBound numericBound bitBound rowIndex
        hformulaValue hrowIndex hrowCount (hrows rowIndex hrowIndex) hvalueBound
        hwidth hwidthBit htokenCount hstateCount htokenTableSize
        hstateBoundarySize hareaNumeric hareaBit hnumericSize hbitPositive)

theorem
    compactParserSyntaxAdjacentRowsBoundedUniformBranchesStructuralEnvelope_le_polynomial
    (tokenTable width tokenCount stateBoundary stateCount rowCount
      formulaValueBound uniformValueBound numericBound bitBound : Nat) :
    compactParserSyntaxAdjacentRowsBoundedUniformBranchesStructuralEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowCount
        formulaValueBound uniformValueBound numericBound bitBound <=
      explicitDirectUniversalBranchesPayloadPolynomial rowCount
        (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
          tokenCount stateBoundary stateCount formulaValueBound)
        (compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchResource
          tokenCount uniformValueBound numericBound bitBound) := by
  unfold compactParserSyntaxAdjacentRowsBoundedUniformBranchesStructuralEnvelope
  exact directBranchesStructuralPayloadEnvelope_le_polynomial
    (compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchResource tokenCount
      uniformValueBound numericBound bitBound)
    (fun _ =>
      compactParserSyntaxAdjacentRowsBoundedUniformDirectBranchResource
        tokenCount uniformValueBound numericBound bitBound)
    (fun _ => Nat.le_refl _)

#print axioms
  compactParserSyntaxAdjacentRowsBoundedUniformFullyDirectBranches_structuralPayloadBound_le
#print axioms
  compactParserSyntaxAdjacentRowsBoundedUniformBranchesStructuralEnvelope_le_polynomial

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedUniformResourceBranchTree
