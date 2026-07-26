import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchTree
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchUniformResource

/-!
# Proof-independent resource ceiling for the bounded-row branch tree

The row-index supremum turns the one-row ceiling into one resource shared by
every branch.  The existing finite-universal branch builder then accounts for
the complete tree without retaining the selected row proofs.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchTreeUniformResource

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAExplicitDirectUniversalBranches
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranch
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchTree
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchUniformResource

noncomputable def
    compactSequentFormulaStepRowsBoundedDirectBranchFamilyUniformResource
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound : Nat) : Nat :=
  (Finset.univ : Finset (Fin rowCount)).sup (fun index =>
    compactSequentFormulaStepRowsBoundedDirectBranchUniformResource tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      index.val valueBound)

theorem
    compactSequentFormulaStepRowsBoundedDirectBranchResource_le_familyUniform
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound rowIndex : Nat)
    (hrow : CompactSequentFormulaStepRowBounded tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex valueBound)
    (hrowIndex : rowIndex < rowCount) :
    compactSequentFormulaStepRowsBoundedDirectBranchResource tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound hrow <=
      compactSequentFormulaStepRowsBoundedDirectBranchFamilyUniformResource
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound := by
  let data :=
    compactSequentFormulaStepRowsBoundedDirectBranchData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound hrow
  have hrowUniform :=
    compactSequentFormulaStepRowsBoundedDirectBranchResource_le_uniform
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound data
  let index : Fin rowCount := ⟨rowIndex, hrowIndex⟩
  have hfamily :
      compactSequentFormulaStepRowsBoundedDirectBranchUniformResource tokenTable
          width tokenCount suffixBoundary suffixCount valueBoundary valueCount
          index.val valueBound <=
        compactSequentFormulaStepRowsBoundedDirectBranchFamilyUniformResource
          tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount rowCount valueBound := by
    unfold
      compactSequentFormulaStepRowsBoundedDirectBranchFamilyUniformResource
    exact Finset.le_sup
      (s := (Finset.univ : Finset (Fin rowCount)))
      (f := fun candidate : Fin rowCount =>
        compactSequentFormulaStepRowsBoundedDirectBranchUniformResource
          tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount candidate.val valueBound)
      (Finset.mem_univ index)
  simpa only [
    compactSequentFormulaStepRowsBoundedDirectBranchResource, data, index] using
      hrowUniform.trans hfamily

theorem compactSequentFormulaStepRowsBoundedDirectBranchProof_le_familyUniform
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound rowIndex : Nat)
    (hrow : CompactSequentFormulaStepRowBounded tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex valueBound)
    (hrowIndex : rowIndex < rowCount) :
    (compactSequentFormulaStepRowsBoundedDirectBranchProof tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound hrow).payloadLength <=
      compactSequentFormulaStepRowsBoundedDirectBranchFamilyUniformResource
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound := by
  exact
    (compactSequentFormulaStepRowsBoundedDirectBranchProof_payloadLength_le
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound hrow).trans
        (compactSequentFormulaStepRowsBoundedDirectBranchResource_le_familyUniform
          tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount rowCount valueBound rowIndex hrow hrowIndex)

def compactSequentFormulaStepRowsBoundedDirectBranchesUniformStructuralEnvelope
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound : Nat) : Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope zeroValuation rowCount
    (compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount valueBound)
    ∅
    (fun _ =>
      compactSequentFormulaStepRowsBoundedDirectBranchFamilyUniformResource
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound)
    rowCount

theorem
    compactSequentFormulaStepRowsBoundedFullyDirectBranches_structuralPayloadBound_le_uniform
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactSequentFormulaStepRowBounded tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound) :
    (compactSequentFormulaStepRowsBoundedFullyDirectBranches tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowCount
      valueBound hrows).structuralPayloadBound rowCount <=
      compactSequentFormulaStepRowsBoundedDirectBranchesUniformStructuralEnvelope
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound := by
  have hbodyVariables :
      (compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        valueBound).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [
      compactSequentFormulaStepRowsBoundedUniversalBody_freeVariables_eq_empty]
  unfold compactSequentFormulaStepRowsBoundedFullyDirectBranches
    compactSequentFormulaStepRowsBoundedDirectBranchesUniformStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables rowCount
    (fun _ =>
      compactSequentFormulaStepRowsBoundedDirectBranchFamilyUniformResource
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound)
    rowCount
    (fun rowIndex hrowIndex =>
      compactSequentFormulaStepRowsBoundedDirectBranchProof tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound (hrows rowIndex hrowIndex))
    (fun rowIndex hrowIndex =>
      compactSequentFormulaStepRowsBoundedDirectBranchProof_le_familyUniform
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound rowIndex (hrows rowIndex hrowIndex)
        hrowIndex)

#print axioms
  compactSequentFormulaStepRowsBoundedDirectBranchResource_le_familyUniform
#print axioms
  compactSequentFormulaStepRowsBoundedDirectBranchProof_le_familyUniform
#print axioms
  compactSequentFormulaStepRowsBoundedFullyDirectBranches_structuralPayloadBound_le_uniform

end FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchTreeUniformResource
