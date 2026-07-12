import integration.FoundationCompactNumericListedDirectBoolListPackedValue

/-!
# Direct equality of atomic additive rows

Boolean and natural-number list elements each occupy one token.  This module
gives a bounded arithmetic relation saying that two such rows have identical
fixed-width bits, then proves that relation equivalent to equality of the
typed values carried by valid rows.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectAtomicRowEquality

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts

/-- Two one-token rows have the same fixed-width bit block. -/
def CompactAdditiveAtomicRowEq
    (tokenTable width tokenCount
      left right otherLeft otherRight : Nat) : Prop :=
  left < tokenCount ∧
    right = left + 1 ∧
    otherLeft < tokenCount ∧
    otherRight = otherLeft + 1 ∧
    ∀ bitIndex < width,
      tokenTable.testBit (left * width + bitIndex) =
        tokenTable.testBit (otherLeft * width + bitIndex)

def compactAdditiveAtomicRowEqDef : 𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount left right otherLeft otherRight.
    left < tokenCount ∧
    right = left + 1 ∧
    otherLeft < tokenCount ∧
    otherRight = otherLeft + 1 ∧
    ∀ bitIndex < width,
      ((left * width + bitIndex) ∈ tokenTable ↔
        (otherLeft * width + bitIndex) ∈ tokenTable)”

@[simp] theorem compactAdditiveAtomicRowEqDef_spec
    (tokenTable width tokenCount
      left right otherLeft otherRight : Nat) :
    compactAdditiveAtomicRowEqDef.val.Evalb
        ![tokenTable, width, tokenCount,
          left, right, otherLeft, otherRight] ↔
      CompactAdditiveAtomicRowEq
        tokenTable width tokenCount
          left right otherLeft otherRight := by
  simp [compactAdditiveAtomicRowEqDef, CompactAdditiveAtomicRowEq,
    arithmeticMem_nat_iff_testBit]

theorem compactAdditiveAtomicRowEqDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveAtomicRowEqDef.val := by
  simp [compactAdditiveAtomicRowEqDef]

theorem CompactAdditiveTokenCell.atomicRowEq
    {tokenTable width tokenCount
      left right otherLeft otherRight value : Nat}
    (hleft : CompactAdditiveTokenCell
      tokenTable width tokenCount left value right)
    (hright : CompactAdditiveTokenCell
      tokenTable width tokenCount otherLeft value otherRight) :
    CompactAdditiveAtomicRowEq
      tokenTable width tokenCount
        left right otherLeft otherRight := by
  refine ⟨hleft.1, hleft.2.1, hright.1, hright.2.1, ?_⟩
  intro bitIndex hbit
  exact (hleft.2.2.2 bitIndex hbit).trans
    (hright.2.2.2 bitIndex hbit).symm

theorem CompactAdditiveAtomicRowEq.value_eq
    {tokenTable width tokenCount
      left right otherLeft otherRight leftValue rightValue : Nat}
    (heq : CompactAdditiveAtomicRowEq
      tokenTable width tokenCount
        left right otherLeft otherRight)
    (hleft : CompactAdditiveTokenCell
      tokenTable width tokenCount left leftValue right)
    (hright : CompactAdditiveTokenCell
      tokenTable width tokenCount otherLeft rightValue otherRight) :
    leftValue = rightValue := by
  apply Nat.eq_of_testBit_eq
  intro bitIndex
  by_cases hbit : bitIndex < width
  · exact (hleft.2.2.2 bitIndex hbit).symm.trans
      ((heq.2.2.2.2 bitIndex hbit).trans
        (hright.2.2.2 bitIndex hbit))
  · have hwidth : width ≤ bitIndex := Nat.le_of_not_gt hbit
    have hleftLt : leftValue < 2 ^ bitIndex :=
      Nat.size_le.mp (hleft.2.2.1.trans hwidth)
    have hrightLt : rightValue < 2 ^ bitIndex :=
      Nat.size_le.mp (hright.2.2.1.trans hwidth)
    rw [Nat.testBit_eq_false_of_lt hleftLt,
      Nat.testBit_eq_false_of_lt hrightLt]

theorem CompactAdditiveAtomicRowEq.boolValue_eq
    {tokenTable width tokenCount left right otherLeft otherRight : Nat}
    {leftValue rightValue : Bool}
    (heq : CompactAdditiveAtomicRowEq
      tokenTable width tokenCount
        left right otherLeft otherRight)
    (hleft : CompactAdditiveBoolValueDirectLayout
      tokenTable width tokenCount left right leftValue)
    (hright : CompactAdditiveBoolValueDirectLayout
      tokenTable width tokenCount otherLeft otherRight rightValue) :
    leftValue = rightValue := by
  have htag : compactAdditiveBoolTag leftValue =
      compactAdditiveBoolTag rightValue :=
    heq.value_eq hleft.1 hright.1
  cases leftValue <;> cases rightValue <;>
    simp [compactAdditiveBoolTag] at htag ⊢

theorem CompactAdditiveAtomicRowEq.natValue_eq
    {tokenTable width tokenCount left right otherLeft otherRight : Nat}
    {leftValue rightValue : Nat}
    (heq : CompactAdditiveAtomicRowEq
      tokenTable width tokenCount
        left right otherLeft otherRight)
    (hleft : CompactAdditiveNatValueDirectLayout
      tokenTable width tokenCount left right leftValue)
    (hright : CompactAdditiveNatValueDirectLayout
      tokenTable width tokenCount otherLeft otherRight rightValue) :
    leftValue = rightValue :=
  heq.value_eq hleft hright

#print axioms compactAdditiveAtomicRowEqDef_spec
#print axioms compactAdditiveAtomicRowEqDef_sigmaZero
#print axioms CompactAdditiveTokenCell.atomicRowEq
#print axioms CompactAdditiveAtomicRowEq.value_eq
#print axioms CompactAdditiveAtomicRowEq.boolValue_eq
#print axioms CompactAdditiveAtomicRowEq.natValue_eq

end FoundationCompactNumericListedDirectAtomicRowEquality
