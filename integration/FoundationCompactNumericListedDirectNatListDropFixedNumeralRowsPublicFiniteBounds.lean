import integration.FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds

/-! Finite row envelopes for dropping fixed natural-list rows. -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds

open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate

private theorem dropRowData_ext
    {tokenTable width tokenCount sourceBoundary targetBoundary consumed index :
      Nat}
    (left right : CompactAdditiveNatListDropRowData tokenTable width tokenCount
      sourceBoundary targetBoundary consumed index)
    (hsourceLeft : left.sourceLeft = right.sourceLeft)
    (hsourceRight : left.sourceRight = right.sourceRight)
    (htargetLeft : left.targetLeft = right.targetLeft)
    (htargetRight : left.targetRight = right.targetRight) :
    left = right := by
  cases left
  cases right
  simp_all

noncomputable def
    compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelopeOfValues
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed index
      sourceLeft sourceRight targetLeft targetRight : Nat) : Nat := by
  classical
  exact if hdata : Exists fun data : CompactAdditiveNatListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index =>
      data.sourceLeft = sourceLeft ∧
      data.sourceRight = sourceRight ∧
      data.targetLeft = targetLeft ∧
      data.targetRight = targetRight then
    compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index
      (Classical.choose hdata)
  else 0

private theorem dropBranchEnvelope_le_valueEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed index :
      Nat)
    (data : CompactAdditiveNatListDropRowData tokenTable width tokenCount
      sourceBoundary targetBoundary consumed index) :
    compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary consumed index
        data <=
      compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelopeOfValues
        tokenTable width tokenCount sourceBoundary targetBoundary consumed index
        data.sourceLeft data.sourceRight data.targetLeft data.targetRight := by
  let hexists : Exists fun candidate : CompactAdditiveNatListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index =>
      candidate.sourceLeft = data.sourceLeft ∧
      candidate.sourceRight = data.sourceRight ∧
      candidate.targetLeft = data.targetLeft ∧
      candidate.targetRight = data.targetRight :=
    Exists.intro data (by simp)
  let selected := Classical.choose hexists
  have hselected := Classical.choose_spec hexists
  have heq : selected = data := dropRowData_ext selected data
    hselected.1 hselected.2.1 hselected.2.2.1 hselected.2.2.2
  unfold
    compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelopeOfValues
  rw [dif_pos hexists]
  simpa only [selected, heq] using
    (le_refl
      (compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary consumed index
        data))

private theorem dropValue_le_finiteSum
    (bound value : Nat) (resource : Nat -> Nat) (hvalue : value <= bound) :
    resource value <= (Finset.range (bound + 1)).sum resource := by
  exact Finset.single_le_sum
    (fun candidate _ => Nat.zero_le (resource candidate))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hvalue))

def compactAdditiveNatListDropFixedNumeralRowsPublicFiniteBranchEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed index :
      Nat) : Nat :=
  (Finset.range (tokenCount + 1)).sum fun sourceLeft =>
    (Finset.range (tokenCount + 1)).sum fun sourceRight =>
      (Finset.range (tokenCount + 1)).sum fun targetLeft =>
        (Finset.range (tokenCount + 1)).sum fun targetRight =>
          compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelopeOfValues
            tokenTable width tokenCount sourceBoundary targetBoundary consumed
            index sourceLeft sourceRight targetLeft targetRight

theorem
    compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed index :
      Nat)
    (data : CompactAdditiveNatListDropRowData tokenTable width tokenCount
      sourceBoundary targetBoundary consumed index) :
    compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary consumed index
        data <=
      compactAdditiveNatListDropFixedNumeralRowsPublicFiniteBranchEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary consumed
        index := by
  have hvalue := dropBranchEnvelope_le_valueEnvelope tokenTable width tokenCount
    sourceBoundary targetBoundary consumed index data
  let resource :=
    compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelopeOfValues
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index
  have htargetRight := dropValue_le_finiteSum tokenCount data.targetRight
    (fun targetRight => resource data.sourceLeft data.sourceRight
      data.targetLeft targetRight) data.targetRight_le
  have htargetLeft := dropValue_le_finiteSum tokenCount data.targetLeft
    (fun targetLeft =>
      (Finset.range (tokenCount + 1)).sum fun targetRight =>
        resource data.sourceLeft data.sourceRight targetLeft targetRight)
    data.targetLeft_le
  have hsourceRight := dropValue_le_finiteSum tokenCount data.sourceRight
    (fun sourceRight =>
      (Finset.range (tokenCount + 1)).sum fun targetLeft =>
        (Finset.range (tokenCount + 1)).sum fun targetRight =>
          resource data.sourceLeft sourceRight targetLeft targetRight)
    data.sourceRight_le
  have hsourceLeft := dropValue_le_finiteSum tokenCount data.sourceLeft
    (fun sourceLeft =>
      (Finset.range (tokenCount + 1)).sum fun sourceRight =>
        (Finset.range (tokenCount + 1)).sum fun targetLeft =>
          (Finset.range (tokenCount + 1)).sum fun targetRight =>
            resource sourceLeft sourceRight targetLeft targetRight)
    data.sourceLeft_le
  unfold compactAdditiveNatListDropFixedNumeralRowsPublicFiniteBranchEnvelope
  exact hvalue.trans
    (htargetRight.trans (htargetLeft.trans (hsourceRight.trans hsourceLeft)))

def compactAdditiveNatListDropFixedNumeralRowsPublicFiniteLeafPayloadResourceSum
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat) : Nat :=
  Finset.sum Finset.univ fun index : Fin targetCount =>
    compactAdditiveNatListDropFixedNumeralRowsPublicFiniteBranchEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index

theorem
    compactAdditiveNatListDropFixedNumeralRowsBranchPayloadResourceSum_le_publicFinite
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat)
    (rows : (index : Fin targetCount) -> CompactAdditiveNatListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index) :
    compactAdditiveNatListDropFixedNumeralRowsBranchPayloadResourceSum
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed rows <=
      compactAdditiveNatListDropFixedNumeralRowsPublicFiniteLeafPayloadResourceSum
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed := by
  unfold compactAdditiveNatListDropFixedNumeralRowsBranchPayloadResourceSum
    compactAdditiveNatListDropFixedNumeralRowsPublicFiniteLeafPayloadResourceSum
  exact Finset.sum_le_sum fun index _ =>
    compactAdditiveNatListDropFixedNumeralRowsBranchStructuralPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index
      (rows index)

end FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
