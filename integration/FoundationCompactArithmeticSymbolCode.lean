import integration.FoundationCompactBinaryNatStreamMachine
import Foundation.FirstOrder.Bootstrapping.Syntax.Language

/-!
# Arithmetic-language symbol codes for the numeric compact parser

The typed compact decoder uses `Encodable.decode₂` for function and relation
symbols.  Since the ordered-ring language is finite, its exact domain can be
checked by two explicit primitive-recursive predicates.  The equivalence
theorems below ensure that the numeric parser accepts exactly the same symbol
codes as the typed decoder.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

namespace FoundationCompactArithmeticSymbolCode

def ArithmeticFuncCodeValid (arity code : Nat) : Prop :=
  (arity = 0 ∧ code = 0) ∨
  (arity = 0 ∧ code = 1) ∨
  (arity = 2 ∧ code = 0) ∨
  (arity = 2 ∧ code = 1)

def ArithmeticRelCodeValid (arity code : Nat) : Prop :=
  (arity = 2 ∧ code = 0) ∨
  (arity = 2 ∧ code = 1)

instance arithmeticFuncCodeValidDecidable :
    DecidableRel ArithmeticFuncCodeValid := by
  intro arity code
  unfold ArithmeticFuncCodeValid
  infer_instance

instance arithmeticRelCodeValidDecidable :
    DecidableRel ArithmeticRelCodeValid := by
  intro arity code
  unfold ArithmeticRelCodeValid
  infer_instance

theorem arithmeticFuncCodeValid_primrec :
    PrimrecRel ArithmeticFuncCodeValid := by
  unfold ArithmeticFuncCodeValid
  refine (
    (((Primrec.eq.comp Primrec₂.left (Primrec₂.const 0)).and
      (Primrec.eq.comp Primrec₂.right (Primrec₂.const 0))).or
     ((Primrec.eq.comp Primrec₂.left (Primrec₂.const 0)).and
      (Primrec.eq.comp Primrec₂.right (Primrec₂.const 1)))).or
    (((Primrec.eq.comp Primrec₂.left (Primrec₂.const 2)).and
      (Primrec.eq.comp Primrec₂.right (Primrec₂.const 0))).or
     ((Primrec.eq.comp Primrec₂.left (Primrec₂.const 2)).and
      (Primrec.eq.comp Primrec₂.right (Primrec₂.const 1))))).of_eq ?_
  rintro ⟨arity, code⟩
  simp only [or_assoc]

theorem arithmeticRelCodeValid_primrec :
    PrimrecRel ArithmeticRelCodeValid := by
  unfold ArithmeticRelCodeValid
  exact
    ((Primrec.eq.comp Primrec₂.left (Primrec₂.const 2)).and
      (Primrec.eq.comp Primrec₂.right (Primrec₂.const 0))).or
    ((Primrec.eq.comp Primrec₂.left (Primrec₂.const 2)).and
      (Primrec.eq.comp Primrec₂.right (Primrec₂.const 1)))

def arithmeticFuncCodeValidBool (arity code : Nat) : Bool :=
  decide (ArithmeticFuncCodeValid arity code)

def arithmeticRelCodeValidBool (arity code : Nat) : Bool :=
  decide (ArithmeticRelCodeValid arity code)

theorem arithmeticFuncCodeValidBool_primrec :
    Primrec₂ arithmeticFuncCodeValidBool := by
  exact arithmeticFuncCodeValid_primrec.decide

theorem arithmeticRelCodeValidBool_primrec :
    Primrec₂ arithmeticRelCodeValidBool := by
  exact arithmeticRelCodeValid_primrec.decide

theorem arithmeticFuncCodeValid_iff_decode₂_ne_none
    (arity code : Nat) :
    ArithmeticFuncCodeValid arity code <->
      (Encodable.decode₂ _ code :
        Option ((ℒₒᵣ : LO.FirstOrder.Language).Func arity)) ≠ none := by
  rw [Encodable.decode₂_ne_none_iff]
  simpa [ArithmeticFuncCodeValid] using
    (LO.FirstOrder.Language.ORing.of_mem_range_encode_func
      (k := arity) (f := code)).symm

theorem arithmeticRelCodeValid_iff_decode₂_ne_none
    (arity code : Nat) :
    ArithmeticRelCodeValid arity code <->
      (Encodable.decode₂ _ code :
        Option ((ℒₒᵣ : LO.FirstOrder.Language).Rel arity)) ≠ none := by
  rw [Encodable.decode₂_ne_none_iff]
  simpa [ArithmeticRelCodeValid] using
    (LO.FirstOrder.Language.ORing.of_mem_range_encode_rel
      (k := arity) (r := code)).symm

theorem arithmeticFuncCodeValidBool_eq_true_iff
    (arity code : Nat) :
    arithmeticFuncCodeValidBool arity code = true <->
      (Encodable.decode₂ _ code :
        Option ((ℒₒᵣ : LO.FirstOrder.Language).Func arity)) ≠ none := by
  simpa [arithmeticFuncCodeValidBool] using
    arithmeticFuncCodeValid_iff_decode₂_ne_none arity code

theorem arithmeticRelCodeValidBool_eq_true_iff
    (arity code : Nat) :
    arithmeticRelCodeValidBool arity code = true <->
      (Encodable.decode₂ _ code :
        Option ((ℒₒᵣ : LO.FirstOrder.Language).Rel arity)) ≠ none := by
  simpa [arithmeticRelCodeValidBool] using
    arithmeticRelCodeValid_iff_decode₂_ne_none arity code

#print axioms arithmeticFuncCodeValid_primrec
#print axioms arithmeticRelCodeValid_primrec
#print axioms arithmeticFuncCodeValidBool_eq_true_iff
#print axioms arithmeticRelCodeValidBool_eq_true_iff

end FoundationCompactArithmeticSymbolCode
