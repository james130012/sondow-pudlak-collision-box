import integration.FoundationCompactNumericListedDirectVerifierPayloadEquality

/-!
# Equality of two direct natural-number-list slices

Two valid additive layouts of the same `List Nat` carry the same header and
the same value token in every position.  Hence their complete fixed-width
token slices agree bit for bit.  This is the completeness direction paired
with `CompactFixedWidthTokenSlicesEq.natListValues_eq`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListSliceEquality

open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierPayloadEquality

theorem CompactAdditiveNatListDirectLayout.slicesEq_of_eq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat}
    {sourceValues targetValues : List Nat}
    (hsource : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceValues)
    (htarget : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetValues)
    (hvalues : sourceValues = targetValues) :
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish := by
  subst targetValues
  have hsourceFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hsource
  have htargetFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq htarget
  have hsourceSlice :=
    CompactAdditiveNatListDirectLayout.toSlice hsource
  have htargetSlice :=
    CompactAdditiveNatListDirectLayout.toSlice htarget
  have hsourceBound : sourceFinish <= tokenCount := by
    rcases hsourceSlice with
      ⟨bodyStart, _hbodyStart, hheader, hfinish⟩
    rw [hfinish]
    exact hheader.2
  have htargetBound : targetFinish <= tokenCount := by
    rcases htargetSlice with
      ⟨bodyStart, _hbodyStart, hheader, hfinish⟩
    rw [hfinish]
    exact hheader.2
  refine ⟨sourceValues.length + 1, ?_, ?_, ?_,
    hsourceBound, htargetBound, ?_⟩
  · omega
  · omega
  · omega
  · intro offset hoffset bitIndex hbitIndex
    cases offset with
    | zero =>
        have hsourceHeader :=
          CompactAdditiveNatListDirectLayout.headerEntry hsource
        have htargetHeader :=
          CompactAdditiveNatListDirectLayout.headerEntry htarget
        exact (hsourceHeader.2 bitIndex hbitIndex).trans
          (htargetHeader.2 bitIndex hbitIndex).symm
    | succ index =>
        have hindex : index < sourceValues.length := by omega
        have hsourceValue :=
          CompactAdditiveNatListDirectLayout.valueEntry
            hsource index hindex
        have htargetValue :=
          CompactAdditiveNatListDirectLayout.valueEntry
            htarget index hindex
        simpa [Nat.succ_eq_add_one, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using
            (hsourceValue.2 bitIndex hbitIndex).trans
              (htargetValue.2 bitIndex hbitIndex).symm

#print axioms CompactAdditiveNatListDirectLayout.slicesEq_of_eq

end FoundationCompactNumericListedDirectNatListSliceEquality
