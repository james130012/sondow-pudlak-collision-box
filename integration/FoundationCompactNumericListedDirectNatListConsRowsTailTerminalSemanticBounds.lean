import integration.FoundationCompactNumericListedDirectNatListConsRowsTailTerminalResources

/-! # Semantic and size facts for one natural-list cons tail row -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 160000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailTerminalSemanticBounds

open FoundationCompactPAValuationContextRewriting
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailCertificate

structure NatListConsRowsTailFixedFacts
    {tokenTable width tokenCount sourceBoundary targetBoundary index : Nat}
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index)
    (numericBound bitBound : Nat) : Prop where
  width_le : width <= numericBound
  tokenCount_le : tokenCount <= numericBound
  index_le : index <= numericBound
  successor_le : index + 1 <= numericBound
  secondSuccessor_le : index + 2 <= numericBound
  valuation_zero_le : (consRowsTailValuation index) 0 <= numericBound
  tokenCount_size : Nat.size tokenCount <= bitBound
  index_size : Nat.size index <= bitBound
  successor_size : Nat.size (index + 1) <= bitBound
  secondSuccessor_size : Nat.size (index + 2) <= bitBound
  sourceLeft_le : data.sourceLeft <= numericBound
  sourceRight_le : data.sourceRight <= numericBound
  targetLeft_le : data.targetLeft <= numericBound
  targetRight_le : data.targetRight <= numericBound
  sourceLeft_size : Nat.size data.sourceLeft <= bitBound
  sourceRight_size : Nat.size data.sourceRight <= bitBound
  targetLeft_size : Nat.size data.targetLeft <= bitBound
  targetRight_size : Nat.size data.targetRight <= bitBound

theorem buildNatListConsRowsTailFixedFacts
    {tokenTable width tokenCount sourceBoundary targetBoundary index : Nat}
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index)
    (numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsecondSuccessor : index + 2 <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    NatListConsRowsTailFixedFacts data numericBound bitBound := by
  have hindex : index <= numericBound := by omega
  have hsuccessor : index + 1 <= numericBound := by omega
  have hsourceLeft : data.sourceLeft <= numericBound :=
    data.sourceLeft_le.trans htokenCount
  have hsourceRight : data.sourceRight <= numericBound :=
    data.sourceRight_le.trans htokenCount
  have htargetLeft : data.targetLeft <= numericBound :=
    data.targetLeft_le.trans htokenCount
  have htargetRight : data.targetRight <= numericBound :=
    data.targetRight_le.trans htokenCount
  refine {
    width_le := hwidth
    tokenCount_le := htokenCount
    index_le := hindex
    successor_le := hsuccessor
    secondSuccessor_le := hsecondSuccessor
    valuation_zero_le := ?_
    tokenCount_size := (Nat.size_le_size htokenCount).trans hnumericSize
    index_size := (Nat.size_le_size hindex).trans hnumericSize
    successor_size := (Nat.size_le_size hsuccessor).trans hnumericSize
    secondSuccessor_size :=
      (Nat.size_le_size hsecondSuccessor).trans hnumericSize
    sourceLeft_le := hsourceLeft
    sourceRight_le := hsourceRight
    targetLeft_le := htargetLeft
    targetRight_le := htargetRight
    sourceLeft_size := (Nat.size_le_size hsourceLeft).trans hnumericSize
    sourceRight_size := (Nat.size_le_size hsourceRight).trans hnumericSize
    targetLeft_size := (Nat.size_le_size htargetLeft).trans hnumericSize
    targetRight_size := (Nat.size_le_size htargetRight).trans hnumericSize }
  simpa [consRowsTailValuation,
    FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation,
    extendValuation] using hindex

#print axioms buildNatListConsRowsTailFixedFacts

end FoundationCompactNumericListedDirectNatListConsRowsTailTerminalSemanticBounds
