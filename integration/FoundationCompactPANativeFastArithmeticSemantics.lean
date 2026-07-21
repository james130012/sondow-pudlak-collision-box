import integration.FoundationCompactPAFastArithmeticLeafRecognizer
import integration.FoundationCompactPAValuationBoundedFormulaCompiler

/-!
# Native semantics for fast arithmetic leaves

The fast PA compilers use Lean's concrete `Nat` operations.  Foundation's
named predicates are interpreted through its abstract exponential, length,
and membership operations.  This file proves, rather than assumes, that the
two interpretations coincide in the standard natural-number model.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationCompactPANativeFastArithmeticSemantics

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAFastArithmeticLeafRecognizer

@[simp] theorem nativeExp_eq_pow (exponent : Nat) :
    LO.Exp.exp exponent = 2 ^ exponent := by
  induction exponent with
  | zero => simp
  | succ exponent ih => grind [LO.FirstOrder.Arithmetic.exp_succ]

@[simp] theorem nativeLength_eq_size (value : Nat) :
    LO.Length.length value = Nat.size value := by
  induction value using Nat.binaryRec' with
  | zero => simp
  | bit bit high hcanonical ih =>
      have hnonzero : Nat.bit bit high ≠ 0 :=
        Nat.bit_ne_zero_iff.mpr hcanonical
      have hsize : Nat.size (Nat.bit bit high) = Nat.size high + 1 :=
        Nat.size_bit hnonzero
      cases bit with
      | false =>
          have hhigh : high ≠ 0 := by
            intro hzero
            have himpossible := hcanonical hzero
            simp at himpossible
          have hpositive : 0 < high := Nat.pos_of_ne_zero hhigh
          calc
            LO.Length.length (Nat.bit false high) =
                LO.Length.length (2 * high) := by simp [Nat.bit]
            _ = LO.Length.length high + 1 :=
              LO.FirstOrder.Arithmetic.length_two_mul_of_pos hpositive
            _ = Nat.size high + 1 := by rw [ih]
            _ = Nat.size (Nat.bit false high) := hsize.symm
      | true =>
          calc
            LO.Length.length (Nat.bit true high) =
                LO.Length.length (2 * high + 1) := by simp [Nat.bit]
            _ = LO.Length.length high + 1 :=
              LO.FirstOrder.Arithmetic.length_two_mul_add_one high
            _ = Nat.size high + 1 := by rw [ih]
            _ = Nat.size (Nat.bit true high) := hsize.symm

@[simp] theorem nativeBit_iff_testBit (index value : Nat) :
    index ∈ value ↔ value.testBit index = true := by
  induction value using Nat.binaryRec' generalizing index with
  | zero =>
      simp [LO.FirstOrder.Arithmetic.mem_iff_bit,
        LO.FirstOrder.Arithmetic.Bit, LO.FirstOrder.Arithmetic.LenBit]
  | bit bit high _ ih =>
      cases bit with
      | false =>
          cases index with
          | zero =>
              rw [Nat.testBit_bit_zero]
              conv_lhs =>
                rw [show Nat.bit false high = 2 * high by simp [Nat.bit]]
              simp only [Bool.false_eq_true, iff_false]
              exact LO.FirstOrder.Arithmetic.zero_not_mem (V := Nat) high
          | succ index =>
              rw [Nat.testBit_bit_succ]
              change (index + 1 ∈ 2 * high) ↔
                high.testBit index = true
              exact
                (LO.FirstOrder.Arithmetic.succ_mem_two_mul_iff
                  (V := Nat) (i := index) (a := high)).trans (ih index)
      | true =>
          cases index with
          | zero =>
              rw [Nat.testBit_bit_zero]
              conv_lhs =>
                rw [show Nat.bit true high = 2 * high + 1 by simp [Nat.bit]]
              simp only [eq_self, iff_true]
              exact LO.FirstOrder.Arithmetic.zero_mem_double_add_one
                (V := Nat) high
          | succ index =>
              rw [Nat.testBit_bit_succ]
              change (index + 1 ∈ 2 * high + 1) ↔
                high.testBit index = true
              exact
                (LO.FirstOrder.Arithmetic.succ_mem_two_mul_succ_iff
                  (V := Nat) (i := index) (a := high)).trans (ih index)

theorem expInstance_value
    (valuation : Nat -> Nat) (value exponent : ArithmeticTerm)
    (htruth : formulaValue valuation (expInstance value exponent)) :
    termValue valuation value = 2 ^ termValue valuation exponent := by
  have hfoundation : termValue valuation value =
      LO.Exp.exp (termValue valuation exponent) := by
    simpa [formulaValue, expInstance, termValue] using htruth
  simpa using hfoundation

theorem lengthInstance_value
    (valuation : Nat -> Nat) (size value : ArithmeticTerm)
    (htruth : formulaValue valuation (lengthInstance size value)) :
    termValue valuation size = Nat.size (termValue valuation value) := by
  have hfoundation : termValue valuation size =
      LO.Length.length (termValue valuation value) := by
    simpa [formulaValue, lengthInstance, termValue] using htruth
  simpa using hfoundation

theorem bitInstance_value
    (valuation : Nat -> Nat) (index value : ArithmeticTerm)
    (htruth : formulaValue valuation (bitInstance index value)) :
    (termValue valuation value).testBit
      (termValue valuation index) = true := by
  have hfoundation : termValue valuation index ∈
      termValue valuation value := by
    simpa [formulaValue, bitInstance, termValue] using htruth
  exact (nativeBit_iff_testBit _ _).mp hfoundation

theorem notBitInstance_value
    (valuation : Nat -> Nat) (index value : ArithmeticTerm)
    (htruth : formulaValue valuation (∼bitInstance index value)) :
    (termValue valuation value).testBit
      (termValue valuation index) = false := by
  have hfoundation : termValue valuation index ∉
      termValue valuation value := by
    simpa [formulaValue, bitInstance, termValue] using htruth
  have hnot : ¬((termValue valuation value).testBit
      (termValue valuation index) = true) := by
    simpa [nativeBit_iff_testBit] using hfoundation
  exact Bool.eq_false_of_not_eq_true hnot

#print axioms nativeExp_eq_pow
#print axioms nativeLength_eq_size
#print axioms nativeBit_iff_testBit
#print axioms expInstance_value
#print axioms lengthInstance_value
#print axioms bitInstance_value
#print axioms notBitInstance_value

end FoundationCompactPANativeFastArithmeticSemantics
