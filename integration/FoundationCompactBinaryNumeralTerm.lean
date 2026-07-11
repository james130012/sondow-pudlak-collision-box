import integration.FoundationCompactSyntaxTransformationCodeBounds

/-!
# Short binary numeral terms for the concrete arithmetic syntax

Foundation's default numeral syntax is unary.  For quantitative diagonal
specialization we instead build `n` one binary digit at a time using
`2 * previous + bit`.  Each digit adds a fixed syntax fragment.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactBinaryNumeralTerm

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCanonicalDecodeLength

def arithmeticZeroTerm : LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  Semiterm.func Language.Zero.zero ![]

def arithmeticOneTerm : LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  Semiterm.func Language.One.one ![]

def arithmeticTwoTerm : LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  Semiterm.func Language.Add.add ![arithmeticOneTerm, arithmeticOneTerm]

def binaryNumeralDoubleTerm
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  Semiterm.func Language.Mul.mul ![arithmeticTwoTerm, term]

def binaryNumeralBitTerm
    (bit : Bool) (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  if bit then
    Semiterm.func Language.Add.add
      ![binaryNumeralDoubleTerm term, arithmeticOneTerm]
  else
    binaryNumeralDoubleTerm term

/-- A closed arithmetic term for `n` whose tree depth and binary code length
are linear in the bit length of `n`. -/
def binaryNumeralTerm : Nat -> LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  Nat.binaryRec' arithmeticZeroTerm
    (fun bit _ _ previous => binaryNumeralBitTerm bit previous)

@[simp] theorem binaryNumeralTerm_zero :
    binaryNumeralTerm 0 = arithmeticZeroTerm := by
  simp [binaryNumeralTerm]

theorem binaryNumeralTerm_bit
    (bit : Bool) (value : Nat) (hcanonical : value = 0 -> bit = true) :
    binaryNumeralTerm (Nat.bit bit value) =
      binaryNumeralBitTerm bit (binaryNumeralTerm value) := by
  simpa [binaryNumeralTerm] using
    (Nat.binaryRec'_eq (motive := fun _ =>
      LO.FirstOrder.ArithmeticSemiterm Nat 0) bit value hcanonical)

def binaryNumeralStepBudget : Nat :=
  (binaryTermCode
      (binaryNumeralBitTerm true arithmeticZeroTerm)).length +
    (binaryTermCode
      (binaryNumeralBitTerm false arithmeticZeroTerm)).length

/-- One binary digit adds at most the fixed, executable syntax budget above. -/
theorem binaryNumeralBitTerm_code_length_le
    (bit : Bool) (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryTermCode (binaryNumeralBitTerm bit term)).length <=
      (binaryTermCode term).length + binaryNumeralStepBudget := by
  cases bit <;>
    simp [binaryNumeralBitTerm, binaryNumeralDoubleTerm,
      binaryNumeralStepBudget, arithmeticTwoTerm, arithmeticOneTerm,
      arithmeticZeroTerm, binaryTermCode] <;> omega

/-- The custom numeral code is linear in the genuine binary length
`Nat.size n`, rather than in the numeric value `n`. -/
theorem binaryNumeralTerm_code_length_le_size (value : Nat) :
    (binaryTermCode (binaryNumeralTerm value)).length <=
      (binaryTermCode arithmeticZeroTerm).length +
        binaryNumeralStepBudget * Nat.size value := by
  induction value using Nat.binaryRec' with
  | zero => simp
  | bit bit value hcanonical ih =>
      rw [binaryNumeralTerm_bit bit value hcanonical]
      have hstep := binaryNumeralBitTerm_code_length_le bit
        (binaryNumeralTerm value)
      have hnonzero : Nat.bit bit value ≠ 0 :=
        Nat.bit_ne_zero_iff.mpr hcanonical
      rw [Nat.size_bit hnonzero]
      calc
        (binaryTermCode
            (binaryNumeralBitTerm bit (binaryNumeralTerm value))).length <=
            (binaryTermCode (binaryNumeralTerm value)).length +
              binaryNumeralStepBudget := hstep
        _ <= ((binaryTermCode arithmeticZeroTerm).length +
              binaryNumeralStepBudget * Nat.size value) +
                binaryNumeralStepBudget :=
          Nat.add_le_add_right ih binaryNumeralStepBudget
        _ = (binaryTermCode arithmeticZeroTerm).length +
              binaryNumeralStepBudget * (Nat.size value + 1) := by
          simp [Nat.mul_succ, Nat.add_assoc]

/-- One syntax digit has the intended arithmetic value in the standard model. -/
theorem binaryNumeralBitTerm_val
    (bit : Bool) (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (binaryNumeralBitTerm bit term).val (M := Nat) ![]
        (fun _ : Nat => 0) =
      Nat.bit bit (term.val (M := Nat) ![] (fun _ : Nat => 0)) := by
  cases bit <;>
    simp [binaryNumeralBitTerm, binaryNumeralDoubleTerm,
      arithmeticTwoTerm, arithmeticOneTerm,
      Semiterm.val_func, Nat.bit_val]

/-- The short term denotes exactly the natural number from which it was built. -/
theorem binaryNumeralTerm_val (value : Nat) :
    (binaryNumeralTerm value).val (M := Nat) ![]
      (fun _ : Nat => 0) = value := by
  induction value using Nat.binaryRec' with
  | zero => simp [binaryNumeralTerm_zero, arithmeticZeroTerm,
      Semiterm.val_func]
  | bit bit value hcanonical ih =>
      rw [binaryNumeralTerm_bit bit value hcanonical,
        binaryNumeralBitTerm_val, ih]

#print axioms binaryNumeralTerm_bit
#print axioms binaryNumeralBitTerm_code_length_le
#print axioms binaryNumeralTerm_code_length_le_size
#print axioms binaryNumeralBitTerm_val
#print axioms binaryNumeralTerm_val

end FoundationCompactBinaryNumeralTerm
