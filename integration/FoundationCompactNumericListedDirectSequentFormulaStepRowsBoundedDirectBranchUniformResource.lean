import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranch

/-!
# Proof-independent resource ceiling for one bounded sequent row

The eighteen witnesses range over one finite box.  Taking the supremum of the
actual compiler resource over that box removes the selected row and its graph
proof from the public branch bound without summing over all candidates.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchUniformResource

open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler

def compactSequentFormulaStepRowOfBoundedWitnessVector
    {valueBound : Nat} (values : Fin 18 -> Fin (valueBound + 1)) :
    CompactSequentFormulaStepCoordinates :=
  compactSequentFormulaStepRowOfValues
    (values 17).val (values 16).val (values 15).val (values 14).val
    (values 13).val (values 12).val (values 11).val (values 10).val
    (values 9).val (values 8).val (values 7).val (values 6).val
    (values 5).val (values 4).val (values 3).val (values 2).val
    (values 1).val (values 0).val

theorem compactSequentFormulaStepRowOfBoundedWitnessVector_witnessValue
    {valueBound : Nat} (values : Fin 18 -> Fin (valueBound + 1))
    (coordinate : Fin 18) :
    compactSequentFormulaStepRowBoundedDirectWitnessValues
        (compactSequentFormulaStepRowOfBoundedWitnessVector values) coordinate =
      (values coordinate).val := by
  fin_cases coordinate <;>
    rfl

def compactSequentFormulaStepBoundedWitnessVectorOfData
    {tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat}
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) :
    Fin 18 -> Fin (valueBound + 1) :=
  fun coordinate =>
    ⟨compactSequentFormulaStepRowBoundedDirectWitnessValues data.row coordinate,
      Nat.lt_succ_of_le (data.values_le coordinate)⟩

theorem compactSequentFormulaStepRowOfBoundedWitnessVector_data
    {tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat}
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) :
    compactSequentFormulaStepRowOfBoundedWitnessVector
        (compactSequentFormulaStepBoundedWitnessVectorOfData data) =
      data.row := by
  rfl

noncomputable def compactSequentFormulaStepBoundedWitnessVectorData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (values : Fin 18 -> Fin (valueBound + 1))
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex
      (compactSequentFormulaStepRowOfBoundedWitnessVector values)) :
    CompactSequentFormulaStepRowBoundedDirectData tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex valueBound :=
  { row := compactSequentFormulaStepRowOfBoundedWitnessVector values
    values_le := fun coordinate => by
      rw [
        compactSequentFormulaStepRowOfBoundedWitnessVector_witnessValue values
          coordinate]
      exact Nat.le_of_lt_succ (values coordinate).isLt
    graph := hgraph }

noncomputable def compactSequentFormulaStepRowsBoundedDirectBranchCandidateResource
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (values : Fin 18 -> Fin (valueBound + 1)) : Nat := by
  classical
  exact
    if hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount rowIndex
        (compactSequentFormulaStepRowOfBoundedWitnessVector values) then
      compactSequentFormulaStepRowBoundedAtValuationIndexWitnessPayloadEnvelope
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowIndex valueBound
        (compactSequentFormulaStepBoundedWitnessVectorData tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
          valueBound values hgraph)
    else
      0

noncomputable def compactSequentFormulaStepRowsBoundedDirectBranchUniformResource
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat) : Nat :=
  (Finset.univ : Finset (Fin 18 -> Fin (valueBound + 1))).sup
    (compactSequentFormulaStepRowsBoundedDirectBranchCandidateResource tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      rowIndex valueBound)

theorem compactSequentFormulaStepRowsBoundedDirectBranchResource_le_uniform
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) :
    compactSequentFormulaStepRowBoundedAtValuationIndexWitnessPayloadEnvelope
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowIndex valueBound data <=
      compactSequentFormulaStepRowsBoundedDirectBranchUniformResource tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        rowIndex valueBound := by
  let values :=
    compactSequentFormulaStepBoundedWitnessVectorOfData data
  have hrow :
      compactSequentFormulaStepRowOfBoundedWitnessVector values = data.row :=
    compactSequentFormulaStepRowOfBoundedWitnessVector_data data
  have hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex
      (compactSequentFormulaStepRowOfBoundedWitnessVector values) := by
    simpa only [hrow] using data.graph
  have hdata :
      compactSequentFormulaStepBoundedWitnessVectorData tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
          valueBound values hgraph =
        data := by
    cases data
    rfl
  have hcandidate :
      compactSequentFormulaStepRowsBoundedDirectBranchCandidateResource tokenTable
          width tokenCount suffixBoundary suffixCount valueBoundary valueCount
          rowIndex valueBound values =
        compactSequentFormulaStepRowBoundedAtValuationIndexWitnessPayloadEnvelope
          tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount rowIndex valueBound data := by
    unfold
      compactSequentFormulaStepRowsBoundedDirectBranchCandidateResource
    rw [dif_pos hgraph]
    rw [hdata]
  rw [← hcandidate]
  exact Finset.le_sup (Finset.mem_univ values)

#print axioms
  compactSequentFormulaStepRowsBoundedDirectBranchResource_le_uniform

end FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectBranchUniformResource
