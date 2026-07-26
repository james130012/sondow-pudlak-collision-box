import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranch
import integration.FoundationCompactPAExplicitDirectUniversalBranches

/-! # Finite direct branch tree for all bounded sequent rows -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchTree

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAExplicitDirectUniversalBranches
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranch

noncomputable def
    compactSequentFormulaStepRowsBoundedDirectBranchResourceSum
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactSequentFormulaStepRowBounded tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound) : Nat :=
  Finset.univ.sum (fun index : Fin rowCount =>
    compactSequentFormulaStepRowsBoundedDirectBranchResource tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount index.val
      valueBound (hrows index.val index.isLt))

theorem compactSequentFormulaStepRowsBoundedDirectBranchProof_le_resourceSum
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound rowIndex : Nat)
    (hrows : ∀ candidate < rowCount,
      CompactSequentFormulaStepRowBounded tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount candidate
        valueBound)
    (hrowIndex : rowIndex < rowCount) :
    (compactSequentFormulaStepRowsBoundedDirectBranchProof tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound (hrows rowIndex hrowIndex)).payloadLength <=
      compactSequentFormulaStepRowsBoundedDirectBranchResourceSum tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        rowCount valueBound hrows := by
  let finiteIndex : Fin rowCount := ⟨rowIndex, hrowIndex⟩
  have hleaf :=
    compactSequentFormulaStepRowsBoundedDirectBranchProof_payloadLength_le
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound (hrows rowIndex hrowIndex)
  have hmember :
      compactSequentFormulaStepRowsBoundedDirectBranchResource tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount
          finiteIndex.val valueBound
          (hrows finiteIndex.val finiteIndex.isLt) <=
        compactSequentFormulaStepRowsBoundedDirectBranchResourceSum tokenTable
          width tokenCount suffixBoundary suffixCount valueBoundary valueCount
          rowCount valueBound hrows := by
    unfold compactSequentFormulaStepRowsBoundedDirectBranchResourceSum
    exact Finset.single_le_sum
      (fun (candidate : Fin rowCount) _ => Nat.zero_le
        (compactSequentFormulaStepRowsBoundedDirectBranchResource tokenTable
          width tokenCount suffixBoundary suffixCount valueBoundary valueCount
          candidate.val valueBound
          (hrows candidate.val candidate.isLt)))
      (Finset.mem_univ finiteIndex)
  simpa only [finiteIndex] using hleaf.trans hmember

noncomputable def compactSequentFormulaStepRowsBoundedFullyDirectBranches
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
      compactSequentFormulaStepRowsBoundedDirectBranchProof tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound (hrows rowIndex hrowIndex))

def compactSequentFormulaStepRowsBoundedDirectBranchesStructuralEnvelope
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactSequentFormulaStepRowBounded tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound) : Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope zeroValuation rowCount
    (compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount valueBound)
    ∅
    (fun _ =>
      compactSequentFormulaStepRowsBoundedDirectBranchResourceSum tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        rowCount valueBound hrows)
    rowCount

theorem
    compactSequentFormulaStepRowsBoundedFullyDirectBranches_structuralPayloadBound_le
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactSequentFormulaStepRowBounded tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound) :
    (compactSequentFormulaStepRowsBoundedFullyDirectBranches tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowCount
      valueBound hrows).structuralPayloadBound rowCount <=
      compactSequentFormulaStepRowsBoundedDirectBranchesStructuralEnvelope
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound hrows := by
  have hbodyVariables :
      (compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        valueBound).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [
      compactSequentFormulaStepRowsBoundedUniversalBody_freeVariables_eq_empty]
  unfold compactSequentFormulaStepRowsBoundedFullyDirectBranches
    compactSequentFormulaStepRowsBoundedDirectBranchesStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables rowCount
    (fun _ =>
      compactSequentFormulaStepRowsBoundedDirectBranchResourceSum tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        rowCount valueBound hrows)
    rowCount
    (fun rowIndex hrowIndex =>
      compactSequentFormulaStepRowsBoundedDirectBranchProof tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound (hrows rowIndex hrowIndex))
    (fun rowIndex hrowIndex =>
      compactSequentFormulaStepRowsBoundedDirectBranchProof_le_resourceSum
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound rowIndex hrows hrowIndex)

#print axioms
  compactSequentFormulaStepRowsBoundedDirectBranchProof_le_resourceSum
#print axioms
  compactSequentFormulaStepRowsBoundedFullyDirectBranches
#print axioms
  compactSequentFormulaStepRowsBoundedFullyDirectBranches_structuralPayloadBound_le

end FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchTree
