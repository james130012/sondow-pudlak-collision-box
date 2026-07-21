import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds

/-!
# Finite data envelopes for syntax-task cons rows

The head row has two bounded cursor values and every tail row has four.  The
finite envelopes select the unique admissible semantic data at each value tuple
and sum over all tuples.  No graph proof remains in the resulting resources.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate

private theorem consHeadData_ext
    {tokenTable width tokenCount targetBoundary headKind headBinderArity
      headRepeatCount : Nat}
    (left right : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width
      tokenCount targetBoundary headKind headBinderArity headRepeatCount)
    (htargetLeft : left.targetLeft = right.targetLeft)
    (htargetRight : left.targetRight = right.targetRight) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem consTailData_ext
    {tokenTable width tokenCount sourceBoundary targetBoundary index : Nat}
    (left right : CompactAdditiveSyntaxTaskListConsTailRowData tokenTable width
      tokenCount sourceBoundary targetBoundary index)
    (hsourceLeft : left.sourceLeft = right.sourceLeft)
    (hsourceRight : left.sourceRight = right.sourceRight)
    (htargetLeft : left.targetLeft = right.targetLeft)
    (htargetRight : left.targetRight = right.targetRight) :
    left = right := by
  cases left
  cases right
  simp_all

noncomputable def
    compactAdditiveSyntaxTaskListConsRowsHeadPayloadEnvelopeOfValues
    (tokenTable width tokenCount targetBoundary headKind headBinderArity
      headRepeatCount targetLeft targetRight : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm) :
    Nat := by
  classical
  exact if hdata : Exists fun data :
      CompactAdditiveSyntaxTaskListConsHeadData tokenTable width tokenCount
        targetBoundary headKind headBinderArity headRepeatCount =>
      data.targetLeft = targetLeft ∧ data.targetRight = targetRight then
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadPayloadEnvelope
      tokenTable width tokenCount targetBoundary headKind headBinderArity
      headRepeatCount headKindTerm headBinderArityTerm headRepeatCountTerm
      (Classical.choose hdata)
  else 0

private theorem consHeadEnvelope_le_valueEnvelope
    (tokenTable width tokenCount targetBoundary headKind headBinderArity
      headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (data : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width
      tokenCount targetBoundary headKind headBinderArity headRepeatCount) :
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadPayloadEnvelope
        tokenTable width tokenCount targetBoundary headKind headBinderArity
        headRepeatCount headKindTerm headBinderArityTerm headRepeatCountTerm
        data <=
      compactAdditiveSyntaxTaskListConsRowsHeadPayloadEnvelopeOfValues
        tokenTable width tokenCount targetBoundary headKind headBinderArity
        headRepeatCount data.targetLeft data.targetRight headKindTerm
        headBinderArityTerm headRepeatCountTerm := by
  let hexists : Exists fun candidate :
      CompactAdditiveSyntaxTaskListConsHeadData tokenTable width tokenCount
        targetBoundary headKind headBinderArity headRepeatCount =>
      candidate.targetLeft = data.targetLeft ∧
        candidate.targetRight = data.targetRight :=
    Exists.intro data (by simp)
  let selected := Classical.choose hexists
  have hselected := Classical.choose_spec hexists
  have heq : selected = data :=
    consHeadData_ext selected data hselected.1 hselected.2
  unfold compactAdditiveSyntaxTaskListConsRowsHeadPayloadEnvelopeOfValues
  rw [dif_pos hexists]
  simpa only [selected, heq] using
    (le_refl
      (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadPayloadEnvelope
        tokenTable width tokenCount targetBoundary headKind headBinderArity
        headRepeatCount headKindTerm headBinderArityTerm headRepeatCountTerm
        data))

private theorem consValue_le_finiteSum
    (bound value : Nat) (resource : Nat -> Nat) (hvalue : value <= bound) :
    resource value <= (Finset.range (bound + 1)).sum resource := by
  exact Finset.single_le_sum
    (fun candidate _ => Nat.zero_le (resource candidate))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hvalue))

def compactAdditiveSyntaxTaskListConsRowsHeadPublicFinitePayloadEnvelope
    (tokenTable width tokenCount targetBoundary headKind headBinderArity
      headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm) :
    Nat :=
  (Finset.range (tokenCount + 1)).sum fun targetLeft =>
    (Finset.range (tokenCount + 1)).sum fun targetRight =>
      compactAdditiveSyntaxTaskListConsRowsHeadPayloadEnvelopeOfValues
        tokenTable width tokenCount targetBoundary headKind headBinderArity
        headRepeatCount targetLeft targetRight headKindTerm
        headBinderArityTerm headRepeatCountTerm

theorem
    compactAdditiveSyntaxTaskListConsRowsHeadPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount targetBoundary headKind headBinderArity
      headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (data : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width
      tokenCount targetBoundary headKind headBinderArity headRepeatCount) :
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadPayloadEnvelope
        tokenTable width tokenCount targetBoundary headKind headBinderArity
        headRepeatCount headKindTerm headBinderArityTerm headRepeatCountTerm
        data <=
      compactAdditiveSyntaxTaskListConsRowsHeadPublicFinitePayloadEnvelope
        tokenTable width tokenCount targetBoundary headKind headBinderArity
        headRepeatCount headKindTerm headBinderArityTerm
        headRepeatCountTerm := by
  have hvalue := consHeadEnvelope_le_valueEnvelope tokenTable width tokenCount
    targetBoundary headKind headBinderArity headRepeatCount headKindTerm
    headBinderArityTerm headRepeatCountTerm data
  let resource := compactAdditiveSyntaxTaskListConsRowsHeadPayloadEnvelopeOfValues
    tokenTable width tokenCount targetBoundary headKind headBinderArity
    headRepeatCount
  have hright := consValue_le_finiteSum tokenCount data.targetRight
    (fun targetRight => resource data.targetLeft targetRight headKindTerm
      headBinderArityTerm headRepeatCountTerm) data.targetRight_le
  have hleft := consValue_le_finiteSum tokenCount data.targetLeft
    (fun targetLeft =>
      (Finset.range (tokenCount + 1)).sum fun targetRight =>
        resource targetLeft targetRight headKindTerm headBinderArityTerm
          headRepeatCountTerm)
    data.targetLeft_le
  unfold compactAdditiveSyntaxTaskListConsRowsHeadPublicFinitePayloadEnvelope
  exact hvalue.trans (hright.trans hleft)

noncomputable def
    compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadEnvelopeOfValues
    (tokenTable width tokenCount sourceBoundary targetBoundary index sourceLeft
      sourceRight targetLeft targetRight : Nat) : Nat := by
  classical
  exact if hdata : Exists fun data :
      CompactAdditiveSyntaxTaskListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index =>
      data.sourceLeft = sourceLeft ∧
      data.sourceRight = sourceRight ∧
      data.targetLeft = targetLeft ∧
      data.targetRight = targetRight then
    compactAdditiveSyntaxTaskListConsRowsTailBranchStructuralPayloadEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary index
      (Classical.choose hdata)
  else 0

private theorem consTailEnvelope_le_valueEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveSyntaxTaskListConsTailRowData tokenTable width
      tokenCount sourceBoundary targetBoundary index) :
    compactAdditiveSyntaxTaskListConsRowsTailBranchStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary index data <=
      compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadEnvelopeOfValues
        tokenTable width tokenCount sourceBoundary targetBoundary index
        data.sourceLeft data.sourceRight data.targetLeft data.targetRight := by
  let hexists : Exists fun candidate :
      CompactAdditiveSyntaxTaskListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index =>
      candidate.sourceLeft = data.sourceLeft ∧
      candidate.sourceRight = data.sourceRight ∧
      candidate.targetLeft = data.targetLeft ∧
      candidate.targetRight = data.targetRight :=
    Exists.intro data (by simp)
  let selected := Classical.choose hexists
  have hselected := Classical.choose_spec hexists
  have heq : selected = data := consTailData_ext selected data
    hselected.1 hselected.2.1 hselected.2.2.1 hselected.2.2.2
  unfold compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadEnvelopeOfValues
  rw [dif_pos hexists]
  simpa only [selected, heq] using
    (le_refl
      (compactAdditiveSyntaxTaskListConsRowsTailBranchStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary index data))

def compactAdditiveSyntaxTaskListConsRowsTailPublicFiniteBranchEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat) :
    Nat :=
  (Finset.range (tokenCount + 1)).sum fun sourceLeft =>
    (Finset.range (tokenCount + 1)).sum fun sourceRight =>
      (Finset.range (tokenCount + 1)).sum fun targetLeft =>
        (Finset.range (tokenCount + 1)).sum fun targetRight =>
          compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadEnvelopeOfValues
            tokenTable width tokenCount sourceBoundary targetBoundary index
            sourceLeft sourceRight targetLeft targetRight

theorem
    compactAdditiveSyntaxTaskListConsRowsTailBranchStructuralPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveSyntaxTaskListConsTailRowData tokenTable width
      tokenCount sourceBoundary targetBoundary index) :
    compactAdditiveSyntaxTaskListConsRowsTailBranchStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary index data <=
      compactAdditiveSyntaxTaskListConsRowsTailPublicFiniteBranchEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary index := by
  have hvalue := consTailEnvelope_le_valueEnvelope tokenTable width tokenCount
    sourceBoundary targetBoundary index data
  let resource :=
    compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadEnvelopeOfValues
      tokenTable width tokenCount sourceBoundary targetBoundary index
  have htargetRight := consValue_le_finiteSum tokenCount data.targetRight
    (fun targetRight => resource data.sourceLeft data.sourceRight
      data.targetLeft targetRight) data.targetRight_le
  have htargetLeft := consValue_le_finiteSum tokenCount data.targetLeft
    (fun targetLeft =>
      (Finset.range (tokenCount + 1)).sum fun targetRight =>
        resource data.sourceLeft data.sourceRight targetLeft targetRight)
    data.targetLeft_le
  have hsourceRight := consValue_le_finiteSum tokenCount data.sourceRight
    (fun sourceRight =>
      (Finset.range (tokenCount + 1)).sum fun targetLeft =>
        (Finset.range (tokenCount + 1)).sum fun targetRight =>
          resource data.sourceLeft sourceRight targetLeft targetRight)
    data.sourceRight_le
  have hsourceLeft := consValue_le_finiteSum tokenCount data.sourceLeft
    (fun sourceLeft =>
      (Finset.range (tokenCount + 1)).sum fun sourceRight =>
        (Finset.range (tokenCount + 1)).sum fun targetLeft =>
          (Finset.range (tokenCount + 1)).sum fun targetRight =>
            resource sourceLeft sourceRight targetLeft targetRight)
    data.sourceLeft_le
  unfold compactAdditiveSyntaxTaskListConsRowsTailPublicFiniteBranchEnvelope
  exact hvalue.trans
    (htargetRight.trans (htargetLeft.trans (hsourceRight.trans hsourceLeft)))

def compactAdditiveSyntaxTaskListConsRowsTailPublicFiniteLeafPayloadResourceSum
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary :
      Nat) : Nat :=
  Finset.sum Finset.univ fun index : Fin sourceCount =>
    compactAdditiveSyntaxTaskListConsRowsTailPublicFiniteBranchEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary index

theorem
    compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadResourceSum_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary :
      Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadResourceSum tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows <=
      compactAdditiveSyntaxTaskListConsRowsTailPublicFiniteLeafPayloadResourceSum
        tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary := by
  unfold compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadResourceSum
    compactAdditiveSyntaxTaskListConsRowsTailPublicFiniteLeafPayloadResourceSum
  exact Finset.sum_le_sum fun index _ =>
    compactAdditiveSyntaxTaskListConsRowsTailBranchStructuralPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount sourceBoundary targetBoundary index
      (rows index)

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds
