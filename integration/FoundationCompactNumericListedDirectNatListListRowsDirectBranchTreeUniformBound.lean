import integration.FoundationCompactNumericListedDirectNatListListRowsDirectUniformBranchProof
import integration.FoundationCompactPAExplicitDirectUniversalBranches

/-! # Uniform finite branch tree for additive natural-list-list rows -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectNatListListRowsDirectBranchTreeUniformBound

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAExplicitDirectUniversalBranches
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsDirectBranchUniformResources
open FoundationCompactNumericListedDirectNatListListRowsDirectUniformBranchProof

private abbrev listRowsTreeZeroValuation : Nat -> Nat :=
  FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation

noncomputable def compactAdditiveNatListListRowsFullyDirectUniformBranches
    (tokenTable width tokenCount boundaryTable count numericBound bitBound : Nat)
    (hrows : CompactAdditiveNatListListRowsWellFormed tokenTable width
      tokenCount boundaryTable count)
    (hcount : count <= numericBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedContextFiniteUniversalBranches
      ((∅ : Finset ValuationFormula).image Rewriting.shift)
      (Rewriting.free
        (compactAdditiveNatListListRowsBody tokenTable width tokenCount
          boundaryTable))
      count := by
  have hbodyVariables :
      (compactAdditiveNatListListRowsBody tokenTable width tokenCount
        boundaryTable).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [compactAdditiveNatListListRowsBody_freeVariables_eq_empty]
  exact buildExplicitDirectUniversalBranches ∅ hbodyVariables count
    (fun rowIndex hrowIndex =>
      compactAdditiveNatListListRowsDirectUniformBranchProof tokenTable width
        tokenCount boundaryTable count rowIndex numericBound bitBound hrows
        hrowIndex hcount hwidth htokenCount htableSize hboundarySize
        hnumericSize)

def compactAdditiveNatListListRowsDirectUniformBranchesStructuralEnvelope
    (tokenTable width tokenCount boundaryTable count numericBound bitBound : Nat) :
    Nat :=
  explicitDirectUniversalBranchesStructuralEnvelope listRowsTreeZeroValuation
    count
    (compactAdditiveNatListListRowsBody tokenTable width tokenCount
      boundaryTable)
    ∅
    (fun _ => compactAdditiveNatListListRowsBranchPayloadResource tokenTable
      width tokenCount boundaryTable numericBound bitBound)
    count

theorem
    compactAdditiveNatListListRowsFullyDirectUniformBranches_structuralPayloadBound_le
    (tokenTable width tokenCount boundaryTable count numericBound bitBound : Nat)
    (hrows : CompactAdditiveNatListListRowsWellFormed tokenTable width
      tokenCount boundaryTable count)
    (hcount : count <= numericBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compactAdditiveNatListListRowsFullyDirectUniformBranches tokenTable width
      tokenCount boundaryTable count numericBound bitBound hrows hcount hwidth
      htokenCount htableSize hboundarySize hnumericSize).structuralPayloadBound
        count <=
      compactAdditiveNatListListRowsDirectUniformBranchesStructuralEnvelope
        tokenTable width tokenCount boundaryTable count numericBound
        bitBound := by
  have hbodyVariables :
      (compactAdditiveNatListListRowsBody tokenTable width tokenCount
        boundaryTable).freeVariables ⊆ (∅ : Finset Nat) := by
    rw [compactAdditiveNatListListRowsBody_freeVariables_eq_empty]
  unfold compactAdditiveNatListListRowsFullyDirectUniformBranches
    compactAdditiveNatListListRowsDirectUniformBranchesStructuralEnvelope
  exact buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    ∅ hbodyVariables count
    (fun _ => compactAdditiveNatListListRowsBranchPayloadResource tokenTable
      width tokenCount boundaryTable numericBound bitBound)
    count
    (fun rowIndex hrowIndex =>
      compactAdditiveNatListListRowsDirectUniformBranchProof tokenTable width
        tokenCount boundaryTable count rowIndex numericBound bitBound hrows
        hrowIndex hcount hwidth htokenCount htableSize hboundarySize
        hnumericSize)
    (fun rowIndex hrowIndex =>
      compactAdditiveNatListListRowsDirectUniformBranchProof_payloadLength_le
        tokenTable width tokenCount boundaryTable count rowIndex numericBound
        bitBound hrows hrowIndex hcount hwidth htokenCount htableSize
        hboundarySize hnumericSize)

#print axioms
  compactAdditiveNatListListRowsFullyDirectUniformBranches_structuralPayloadBound_le

end FoundationCompactNumericListedDirectNatListListRowsDirectBranchTreeUniformBound
