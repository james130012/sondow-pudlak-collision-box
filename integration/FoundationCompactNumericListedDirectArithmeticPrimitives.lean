import integration.FoundationCompactNumericListedDirectTraceBounds
import Foundation.FirstOrder.Arithmetic.Exponential.Log

/-!
# Direct arithmetic primitives for the compact listed trace

This module starts the handwritten arithmetic graph from Foundation's bounded
binary-length formula.  It does not use the generic RE projection or `rfind`
representation route.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectArithmeticPrimitives

/-- Foundation's model-theoretic binary length agrees with the exact
`Nat.size` coordinate used by the public verifier and all trace bounds. -/
theorem binaryLength_nat_eq_size (n : Nat) :
    LO.FirstOrder.Arithmetic.binaryLength n = Nat.size n := by
  induction n using Nat.binaryRec' with
  | zero => simp [LO.FirstOrder.Arithmetic.binaryLength]
  | bit bit n hn ih =>
      have hnonzero : Nat.bit bit n ≠ 0 :=
        Nat.bit_ne_zero_iff.mpr hn
      rw [Nat.size_bit hnonzero]
      cases bit with
      | false =>
          have hnpos : 0 < n := by
            exact Nat.pos_of_ne_zero (by simpa [Nat.bit] using hnonzero)
          have hlength :=
            LO.FirstOrder.Arithmetic.length_two_mul_of_pos
              (V := Nat) hnpos
          change LO.FirstOrder.Arithmetic.binaryLength (2 * n) =
            LO.FirstOrder.Arithmetic.binaryLength n + 1 at hlength
          simpa [Nat.bit, ih] using hlength
      | true =>
          have hlength :=
            LO.FirstOrder.Arithmetic.length_two_mul_add_one
              (V := Nat) n
          change LO.FirstOrder.Arithmetic.binaryLength (2 * n + 1) =
            LO.FirstOrder.Arithmetic.binaryLength n + 1 at hlength
          simpa [Nat.bit, ih] using hlength

/-- Direct bounded arithmetic graph for the honest binary code length. -/
def compactNatSizeDef : 𝚺₀.Semisentence 2 :=
  LO.FirstOrder.Arithmetic.lengthDef

@[simp] theorem compactNatSizeDef_spec (size value : Nat) :
    compactNatSizeDef.val.Evalb ![size, value] ↔
      size = Nat.size value := by
  simp [compactNatSizeDef]
  change size = LO.FirstOrder.Arithmetic.binaryLength value ↔
    size = Nat.size value
  rw [binaryLength_nat_eq_size]

theorem compactNatSizeDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNatSizeDef.val := by
  simp [compactNatSizeDef]

#print axioms binaryLength_nat_eq_size
#print axioms compactNatSizeDef_spec
#print axioms compactNatSizeDef_sigmaZero

end FoundationCompactNumericListedDirectArithmeticPrimitives
