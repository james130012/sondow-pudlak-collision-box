import integration.FoundationCompactListedCertifiedEncoder

/-!
# Bit-cost trace for the compact natural-number decoder

Constructing `Nat.bit b n` is charged by `Nat.size n + 1`; hence this is a
bit-cost model rather than a unit-cost model for unbounded naturals.
-/

namespace FoundationCompactNatDecoderCost

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCanonicalDecodeLength

def decodeBinaryNatTrace :
    List Bool -> Option (Nat × List Bool) × Nat
  | [] => (none, 1)
  | [_] => (none, 2)
  | false :: false :: rest => (some (0, rest), 2)
  | false :: true :: _ => (none, 2)
  | true :: bit :: rest =>
      let tail := decodeBinaryNatTrace rest
      match tail.1 with
      | none => (none, tail.2 + 2)
      | some (n, suffix) =>
          (some (Nat.bit bit n, suffix), tail.2 + Nat.size n + 3)

theorem decodeBinaryNatTrace_result :
    forall bits : List Bool,
      (decodeBinaryNatTrace bits).1 = decodeBinaryNat bits
  | [] => by rfl
  | [bit] => by cases bit <;> rfl
  | false :: false :: rest => by rfl
  | false :: true :: rest => by rfl
  | true :: bit :: rest => by
      simp only [decodeBinaryNatTrace, decodeBinaryNat]
      rw [decodeBinaryNatTrace_result rest]
      cases decodeBinaryNat rest <;> rfl

theorem decodeBinaryNatTrace_cost_pos
    (bits : List Bool) :
    1 <= (decodeBinaryNatTrace bits).2 := by
  induction bits using decodeBinaryNatTrace.induct <;>
    simp [decodeBinaryNatTrace, *] <;>
    split <;> omega

theorem natDecodeQuadratic_step (length extra : Nat)
    (hextra : extra <= length) :
    (length + 1) * (length + 1) + extra + 3 <=
      (length + 3) * (length + 3) := by
  simp only [Nat.add_mul, Nat.mul_add]
  omega

theorem natDecodeQuadratic_fail_step (length : Nat) :
    (length + 1) * (length + 1) + 2 <=
      (length + 3) * (length + 3) := by
  simp only [Nat.add_mul, Nat.mul_add]
  omega

theorem decodeBinaryNatTrace_cost_le :
    forall bits : List Bool,
      (decodeBinaryNatTrace bits).2 <=
        (bits.length + 1) * (bits.length + 1)
  | [] => by simp [decodeBinaryNatTrace]
  | [bit] => by cases bit <;> simp [decodeBinaryNatTrace]
  | false :: false :: rest => by
      have hstep := natDecodeQuadratic_fail_step rest.length
      change 2 <= (rest.length + 3) * (rest.length + 3)
      omega
  | false :: true :: rest => by
      have hstep := natDecodeQuadratic_fail_step rest.length
      change 2 <= (rest.length + 3) * (rest.length + 3)
      omega
  | true :: bit :: rest => by
      have ih := decodeBinaryNatTrace_cost_le rest
      simp only [decodeBinaryNatTrace]
      cases hresult : (decodeBinaryNatTrace rest).1 with
      | none =>
          have hstep := natDecodeQuadratic_fail_step rest.length
          change (decodeBinaryNatTrace rest).2 + 2 <=
            (rest.length + 3) * (rest.length + 3)
          omega
      | some result =>
          rcases result with ⟨n, suffix⟩
          have htailDecode :
              decodeBinaryNat rest = some (n, suffix) := by
            rw [← decodeBinaryNatTrace_result rest]
            exact hresult
          have hcanonical :=
            decodeBinaryNat_canonical_length_le htailDecode
          rw [binaryNatCode_length] at hcanonical
          have hsize : Nat.size n <= rest.length := by omega
          have hstep :=
            natDecodeQuadratic_step rest.length (Nat.size n) hsize
          change (decodeBinaryNatTrace rest).2 + Nat.size n + 3 <=
            (rest.length + 3) * (rest.length + 3)
          omega

theorem decodeBinaryNatTrace_success_cost_le
    {bits suffix : List Bool} {n : Nat}
    (_hdecode : (decodeBinaryNatTrace bits).1 = some (n, suffix)) :
    (decodeBinaryNatTrace bits).2 <=
      (bits.length + 1) * (bits.length + 1) :=
  decodeBinaryNatTrace_cost_le bits

#print axioms decodeBinaryNatTrace_result
#print axioms decodeBinaryNatTrace_cost_le

end FoundationCompactNatDecoderCost
