import integration.FoundationCompactNumericListedDirectNatListListRowsDirectBranchUniformBound

/-! # Semantic row selection for the uniform natural-list-list branch -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectNatListListRowsDirectUniformBranchProof

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsDirectBranchUniformResources
open FoundationCompactNumericListedDirectNatListListRowsDirectBranchUniformBound

private abbrev listRowsBranchZeroValuation : Nat -> Nat :=
  FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation

noncomputable def compactAdditiveNatListListRowsDirectUniformBranchProof
    (tokenTable width tokenCount boundaryTable count rowIndex numericBound
      bitBound : Nat)
    (hrows : CompactAdditiveNatListListRowsWellFormed tokenTable width
      tokenCount boundaryTable count)
    (hrowIndex : rowIndex < count)
    (hcount : count <= numericBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (Rewriting.free
          (compactAdditiveNatListListRowsBody tokenTable width tokenCount
            boundaryTable)).freeVariables
        (extendValuation rowIndex listRowsBranchZeroValuation))
      (Rewriting.free
        (compactAdditiveNatListListRowsBody tokenTable width tokenCount
          boundaryTable)) := by
  let data := compactAdditiveNatListListRowDataOfWellFormed tokenTable width
    tokenCount boundaryTable count hrows ⟨rowIndex, hrowIndex⟩
  exact (compactAdditiveNatListListRowsDirectUniformBranchBoundOfData tokenTable
    width tokenCount boundaryTable count rowIndex numericBound bitBound data
    hrowIndex hcount hwidth htokenCount htableSize hboundarySize
    hnumericSize).proof

theorem compactAdditiveNatListListRowsDirectUniformBranchProof_payloadLength_le
    (tokenTable width tokenCount boundaryTable count rowIndex numericBound
      bitBound : Nat)
    (hrows : CompactAdditiveNatListListRowsWellFormed tokenTable width
      tokenCount boundaryTable count)
    (hrowIndex : rowIndex < count)
    (hcount : count <= numericBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compactAdditiveNatListListRowsDirectUniformBranchProof tokenTable width
      tokenCount boundaryTable count rowIndex numericBound bitBound hrows
      hrowIndex hcount hwidth htokenCount htableSize hboundarySize
      hnumericSize).payloadLength <=
      compactAdditiveNatListListRowsBranchPayloadResource tokenTable width
        tokenCount boundaryTable numericBound bitBound := by
  let data := compactAdditiveNatListListRowDataOfWellFormed tokenTable width
    tokenCount boundaryTable count hrows ⟨rowIndex, hrowIndex⟩
  exact (compactAdditiveNatListListRowsDirectUniformBranchBoundOfData tokenTable
    width tokenCount boundaryTable count rowIndex numericBound bitBound data
    hrowIndex hcount hwidth htokenCount htableSize hboundarySize
    hnumericSize).payloadLength_le

#print axioms compactAdditiveNatListListRowsDirectUniformBranchProof
#print axioms
  compactAdditiveNatListListRowsDirectUniformBranchProof_payloadLength_le

end FoundationCompactNumericListedDirectNatListListRowsDirectUniformBranchProof
