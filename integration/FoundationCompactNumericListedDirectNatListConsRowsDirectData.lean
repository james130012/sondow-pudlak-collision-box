import integration.FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate

/-! # Explicit head and tail data extracted from natural-list cons rows -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectNatListConsRowsDirectData

open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate

noncomputable def compactAdditiveNatListConsHeadDataOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount head : Nat)
    (hgraph : CompactAdditiveNatListConsRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount head) :
    CompactAdditiveNatListConsHeadData tokenTable width tokenCount
      targetBoundary head := by
  let targetLeftExists := hgraph.2.1
  let targetLeft := Classical.choose targetLeftExists
  have htargetLeft := Classical.choose_spec targetLeftExists
  let targetRightExists := htargetLeft.2
  let targetRight := Classical.choose targetRightExists
  have htargetRight := Classical.choose_spec targetRightExists
  exact
    { targetLeft := targetLeft
      targetRight := targetRight
      targetLeft_le := htargetLeft.1
      targetRight_le := htargetRight.1
      targetLeft_entry := htargetRight.2.1
      targetRight_entry := htargetRight.2.2.1
      token_cell := htargetRight.2.2.2 }

noncomputable def compactAdditiveNatListConsTailRowDataOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount head rowIndex : Nat)
    (hgraph : CompactAdditiveNatListConsRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount head)
    (hrowIndex : rowIndex < sourceCount) :
    CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary rowIndex := by
  let sourceLeftExists := hgraph.2.2 rowIndex hrowIndex
  let sourceLeft := Classical.choose sourceLeftExists
  have hsourceLeft := Classical.choose_spec sourceLeftExists
  let sourceRightExists := hsourceLeft.2
  let sourceRight := Classical.choose sourceRightExists
  have hsourceRight := Classical.choose_spec sourceRightExists
  let targetLeftExists := hsourceRight.2
  let targetLeft := Classical.choose targetLeftExists
  have htargetLeft := Classical.choose_spec targetLeftExists
  let targetRightExists := htargetLeft.2
  let targetRight := Classical.choose targetRightExists
  have htargetRight := Classical.choose_spec targetRightExists
  exact
    { sourceLeft := sourceLeft
      sourceRight := sourceRight
      targetLeft := targetLeft
      targetRight := targetRight
      sourceLeft_le := hsourceLeft.1
      sourceRight_le := hsourceRight.1
      targetLeft_le := htargetLeft.1
      targetRight_le := htargetRight.1
      sourceLeft_entry := htargetRight.2.1
      sourceRight_entry := htargetRight.2.2.1
      targetLeft_entry := htargetRight.2.2.2.1
      targetRight_entry := htargetRight.2.2.2.2.1
      atomic_row_eq := htargetRight.2.2.2.2.2 }

#print axioms compactAdditiveNatListConsHeadDataOfGraph
#print axioms compactAdditiveNatListConsTailRowDataOfGraph

end FoundationCompactNumericListedDirectNatListConsRowsDirectData
