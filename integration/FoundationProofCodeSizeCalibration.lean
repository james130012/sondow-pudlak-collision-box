import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding
import Mathlib.Data.Nat.Size

/-!
# Foundation proof-code bit-size calibration

The raw Foundation derivation constructors use a fixed number of nested
pairing operations.  This file proves the bit-length estimates needed to turn
those constructors into quantitative proof compilers.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationProofCodeSizeCalibration

/-- Adding the constructor tag `1` costs at most one binary digit. -/
theorem size_add_one_le (n : Nat) :
    Nat.size (n + 1) ≤ Nat.size n + 1 := by
  rw [Nat.size_le]
  have hn : n + 1 ≤ 2 ^ Nat.size n :=
    Nat.succ_le_iff.mpr (Nat.lt_size_self n)
  exact hn.trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat))
      (Nat.lt_succ_self (Nat.size n)))

/-- Foundation's pairing operation has linear bit-length overhead. -/
theorem size_pair_le (a b : Nat) :
    Nat.size (LO.FirstOrder.Arithmetic.pair a b) ≤
      2 * (Nat.size a + Nat.size b + 2) := by
  rw [Nat.size_le]
  let k : Nat := Nat.size a + Nat.size b + 2
  have ha : a < 2 ^ (Nat.size a + Nat.size b) :=
    (Nat.lt_size_self a).trans_le
      (Nat.pow_le_pow_right (by decide)
        (Nat.le_add_right (Nat.size a) (Nat.size b)))
  have hb : b < 2 ^ (Nat.size a + Nat.size b) :=
    (Nat.lt_size_self b).trans_le
      (Nat.pow_le_pow_right (by decide)
        (Nat.le_add_left (Nat.size b) (Nat.size a)))
  have hp : 0 < 2 ^ (Nat.size a + Nat.size b) :=
    Nat.pow_pos (by decide)
  have hab : a + b + 1 < 2 ^ k := by
    have hsum :
        a + b + 1 <
          4 * 2 ^ (Nat.size a + Nat.size b) := by
      omega
    simpa [k, pow_add, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hsum
  have hsquare :
      (a + b + 1) ^ 2 < (2 ^ k) ^ 2 :=
    Nat.pow_lt_pow_left hab (by omega)
  have hpair_bound :
      LO.FirstOrder.Arithmetic.pair a b ≤ (a + b + 1) ^ 2 := by
    rw [LO.FirstOrder.Arithmetic.nat_pair_eq]
    simp only [Nat.pair]
    split_ifs with h
    · have hab_le : a ≤ b := Nat.le_of_lt h
      calc
        b * b + a ≤ b * b + b := Nat.add_le_add_left hab_le (b * b)
        _ ≤ (b + 1) * (b + 1) := by
          simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
          omega
        _ ≤ (a + b + 1) * (a + b + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        _ = (a + b + 1) ^ 2 := by simp [pow_two]
    · have hba_le : b ≤ a := Nat.le_of_not_gt h
      calc
        a * a + a + b ≤ a * a + a + a :=
          Nat.add_le_add_left hba_le (a * a + a)
        _ ≤ (a + 1) * (a + 1) := by
          simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
          omega
        _ ≤ (a + b + 1) * (a + b + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        _ = (a + b + 1) ^ 2 := by simp [pow_two]
  have hpair :
      LO.FirstOrder.Arithmetic.pair a b < 2 ^ (2 * k) := by
    calc
      LO.FirstOrder.Arithmetic.pair a b ≤ (a + b + 1) ^ 2 :=
        hpair_bound
      _ < (2 ^ k) ^ 2 := hsquare
      _ = 2 ^ (k * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * k) := by rw [Nat.mul_comm]
  simpa [k] using hpair

/-- A tagged Foundation constructor `pair a b + 1` also has linear
bit-length overhead. -/
theorem size_pair_add_one_le (a b : Nat) :
    Nat.size (LO.FirstOrder.Arithmetic.pair a b + 1) ≤
      2 * (Nat.size a + Nat.size b + 2) + 1 := by
  exact (size_add_one_le _).trans
    (Nat.add_le_add_right (size_pair_le a b) 1)

/-- Standard-`Nat` form, used to erase hidden arithmetic-instance parameters
from specialized Foundation constructors. -/
theorem size_natPair_le (a b : Nat) :
    Nat.size (Nat.pair a b) ≤
      2 * (Nat.size a + Nat.size b + 2) := by
  rw [← LO.FirstOrder.Arithmetic.nat_pair_eq b a]
  exact size_pair_le a b

theorem size_pair3_le (a b c : Nat) :
    Nat.size (Nat.pair a (Nat.pair b c)) ≤
      4 * (Nat.size a + Nat.size b + Nat.size c + 3) := by
  calc
    Nat.size (Nat.pair a (Nat.pair b c)) ≤
        2 * (Nat.size a + Nat.size (Nat.pair b c) + 2) :=
      size_natPair_le a (Nat.pair b c)
    _ ≤ 4 * (Nat.size a + Nat.size b + Nat.size c + 3) := by
      have hbc := size_natPair_le b c
      omega

theorem size_pair4_le (a b c d : Nat) :
    Nat.size (Nat.pair a (Nat.pair b (Nat.pair c d))) ≤
      8 * (Nat.size a + Nat.size b + Nat.size c + Nat.size d + 4) := by
  calc
    Nat.size (Nat.pair a (Nat.pair b (Nat.pair c d))) ≤
        2 * (Nat.size a + Nat.size (Nat.pair b (Nat.pair c d)) + 2) :=
      size_natPair_le a (Nat.pair b (Nat.pair c d))
    _ ≤ 8 *
        (Nat.size a + Nat.size b + Nat.size c + Nat.size d + 4) := by
      have hbcd := size_pair3_le b c d
      omega

theorem size_pair5_le (a b c d e : Nat) :
    Nat.size (Nat.pair a (Nat.pair b (Nat.pair c (Nat.pair d e)))) ≤
      16 *
        (Nat.size a + Nat.size b + Nat.size c + Nat.size d +
          Nat.size e + 5) := by
  calc
    Nat.size (Nat.pair a (Nat.pair b (Nat.pair c (Nat.pair d e)))) ≤
        2 *
          (Nat.size a + Nat.size (Nat.pair b (Nat.pair c (Nat.pair d e))) + 2) :=
      size_natPair_le a (Nat.pair b (Nat.pair c (Nat.pair d e)))
    _ ≤ 16 *
        (Nat.size a + Nat.size b + Nat.size c + Nat.size d +
          Nat.size e + 5) := by
      have hbcde := size_pair4_le b c d e
      omega

theorem size_pair6_le (a b c d e f : Nat) :
    Nat.size
        (Nat.pair a (Nat.pair b (Nat.pair c (Nat.pair d (Nat.pair e f))))) ≤
      32 *
        (Nat.size a + Nat.size b + Nat.size c + Nat.size d +
          Nat.size e + Nat.size f + 6) := by
  calc
    Nat.size
        (Nat.pair a (Nat.pair b (Nat.pair c (Nat.pair d (Nat.pair e f))))) ≤
        2 *
          (Nat.size a +
            Nat.size (Nat.pair b (Nat.pair c (Nat.pair d (Nat.pair e f)))) + 2) :=
      size_natPair_le a
        (Nat.pair b (Nat.pair c (Nat.pair d (Nat.pair e f))))
    _ ≤ 32 *
        (Nat.size a + Nat.size b + Nat.size c + Nat.size d +
          Nat.size e + Nat.size f + 6) := by
      have hbcdef := size_pair5_le b c d e f
      omega

/-- Bit-size bound for Foundation's logical initial-sequent constructor. -/
theorem size_axL_le (s p : Nat) :
    Nat.size (LO.FirstOrder.Arithmetic.Bootstrapping.axL s p) ≤
      4 * (Nat.size s + Nat.size p + 3) + 1 := by
  rw [LO.FirstOrder.Arithmetic.Bootstrapping.axL]
  simp only [LO.FirstOrder.Arithmetic.nat_pair_eq]
  refine (size_add_one_le _).trans ?_
  have h := size_pair3_le s 0 p
  simp only [Nat.size_zero] at h
  omega

/-- Bit-size bound for Foundation's weakening constructor. -/
theorem size_wkRule_le (s d : Nat) :
    Nat.size (LO.FirstOrder.Arithmetic.Bootstrapping.wkRule s d) ≤
      4 * (Nat.size s + Nat.size d + 6) + 1 := by
  rw [LO.FirstOrder.Arithmetic.Bootstrapping.wkRule]
  simp only [LO.FirstOrder.Arithmetic.nat_pair_eq]
  change Nat.size (Nat.pair s (Nat.pair 6 d) + 1) ≤
    4 * (Nat.size s + Nat.size d + 6) + 1
  refine (size_add_one_le _).trans ?_
  have h := size_pair3_le s 6 d
  have h6 : Nat.size 6 = 3 := by decide
  rw [h6] at h
  have h' :
      Nat.size (Nat.pair s (Nat.pair 6 d)) ≤
        4 * (Nat.size s + Nat.size d + 6) := by
    omega
  exact Nat.add_le_add_right h' 1

/-- Bit-size bound for Foundation's conjunction constructor. -/
theorem size_andIntro_le (s p q dp dq : Nat) :
    Nat.size
        (LO.FirstOrder.Arithmetic.Bootstrapping.andIntro s p q dp dq) ≤
      32 *
        (Nat.size s + Nat.size p + Nat.size q + Nat.size dp +
          Nat.size dq + 8) + 1 := by
  rw [LO.FirstOrder.Arithmetic.Bootstrapping.andIntro]
  simp only [LO.FirstOrder.Arithmetic.nat_pair_eq]
  change Nat.size
      (Nat.pair s (Nat.pair 2 (Nat.pair p (Nat.pair q (Nat.pair dp dq)))) + 1) ≤
    32 *
      (Nat.size s + Nat.size p + Nat.size q + Nat.size dp +
        Nat.size dq + 8) + 1
  refine (size_add_one_le _).trans ?_
  have h := size_pair6_le s 2 p q dp dq
  have h2 : Nat.size 2 = 2 := by decide
  rw [h2] at h
  have h' :
      Nat.size
          (Nat.pair s
            (Nat.pair 2 (Nat.pair p (Nat.pair q (Nat.pair dp dq))))) ≤
        32 *
          (Nat.size s + Nat.size p + Nat.size q + Nat.size dp +
            Nat.size dq + 8) := by
    omega
  exact Nat.add_le_add_right h' 1

/-- Bit-size bound for Foundation's cut constructor. -/
theorem size_cutRule_le (s p d₁ d₂ : Nat) :
    Nat.size
        (LO.FirstOrder.Arithmetic.Bootstrapping.cutRule s p d₁ d₂) ≤
      16 *
        (Nat.size s + Nat.size p + Nat.size d₁ + Nat.size d₂ + 9) + 1 := by
  rw [LO.FirstOrder.Arithmetic.Bootstrapping.cutRule]
  simp only [LO.FirstOrder.Arithmetic.nat_pair_eq]
  change Nat.size
      (Nat.pair s (Nat.pair 8 (Nat.pair p (Nat.pair d₁ d₂))) + 1) ≤
    16 *
      (Nat.size s + Nat.size p + Nat.size d₁ + Nat.size d₂ + 9) + 1
  refine (size_add_one_le _).trans ?_
  have h := size_pair5_le s 8 p d₁ d₂
  have h8 : Nat.size 8 = 4 := by decide
  rw [h8] at h
  have h' :
      Nat.size (Nat.pair s (Nat.pair 8 (Nat.pair p (Nat.pair d₁ d₂)))) ≤
        16 *
          (Nat.size s + Nat.size p + Nat.size d₁ + Nat.size d₂ + 9) := by
    omega
  exact Nat.add_le_add_right h' 1

#check size_add_one_le
#print axioms size_add_one_le

#check size_pair_le
#print axioms size_pair_le

#check size_pair_add_one_le
#print axioms size_pair_add_one_le

#check size_axL_le
#print axioms size_axL_le

#check size_wkRule_le
#print axioms size_wkRule_le

#check size_andIntro_le
#print axioms size_andIntro_le

#check size_cutRule_le
#print axioms size_cutRule_le

end FoundationProofCodeSizeCalibration
