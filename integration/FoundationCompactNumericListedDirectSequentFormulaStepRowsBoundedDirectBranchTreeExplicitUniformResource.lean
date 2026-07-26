import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchExplicitUniformResource
import integration.FoundationCompactPAExplicitDirectUniversalBranches

/-! # Finite branch tree with one explicit row-independent resource -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchTreeExplicitUniformResource

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAExplicitDirectUniversalBranches
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchExplicitUniformResource

noncomputable def
    compactSequentFormulaStepRowsBoundedFullyDirectExplicitUniformBranches
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactSequentFormulaStepRowBounded tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound) :
    CertifiedContextFiniteUniversalBranches
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (Rewriting.free
        (compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount
          valueBound))
      rowCount := by
  have hbodyVariables :
      (compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        valueBound).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [
      compactSequentFormulaStepRowsBoundedUniversalBody_freeVariables_eq_empty]
  exact buildExplicitDirectUniversalBranches ∅ hbodyVariables rowCount
    (fun rowIndex hrowIndex =>
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchProof
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount rowIndex valueBound (hrows rowIndex hrowIndex)
        hrowIndex)

def compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchesStructuralEnvelope
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound : Nat) : Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope zeroValuation rowCount
    (compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount valueBound)
    ∅
    (fun _ =>
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchResource
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound)
    rowCount

theorem
    compactSequentFormulaStepRowsBoundedFullyDirectExplicitUniformBranches_structuralPayloadBound_le
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactSequentFormulaStepRowBounded tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound) :
    (compactSequentFormulaStepRowsBoundedFullyDirectExplicitUniformBranches
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound hrows).structuralPayloadBound rowCount <=
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchesStructuralEnvelope
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound := by
  have hbodyVariables :
      (compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        valueBound).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [
      compactSequentFormulaStepRowsBoundedUniversalBody_freeVariables_eq_empty]
  unfold
    compactSequentFormulaStepRowsBoundedFullyDirectExplicitUniformBranches
    compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchesStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables rowCount
    (fun _ =>
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchResource
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound)
    rowCount
    (fun rowIndex hrowIndex =>
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchProof
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount rowIndex valueBound (hrows rowIndex hrowIndex)
        hrowIndex)
    (fun rowIndex hrowIndex =>
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformBranchProof_payloadLength_le
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount rowIndex valueBound (hrows rowIndex hrowIndex)
        hrowIndex)

#print axioms
  compactSequentFormulaStepRowsBoundedFullyDirectExplicitUniformBranches
#print axioms
  compactSequentFormulaStepRowsBoundedFullyDirectExplicitUniformBranches_structuralPayloadBound_le

end FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchTreeExplicitUniformResource
