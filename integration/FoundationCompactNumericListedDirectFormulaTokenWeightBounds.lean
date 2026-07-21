import integration.FoundationCompactNumericTokenBitLength
import integration.FoundationCompactAdditiveTokenCodec

/-!
# Additive weights of canonical arithmetic token lists

The numeric syntax token stream uses the same self-delimiting natural-number
code as the typed binary syntax code.  This file records the exact bit-length
identity and the resulting additive list-value bounds.  These lemmas let
typed formula code-length estimates control the concrete numeric values stored
by the direct verifier.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTokenWeightBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericTokenBitLength

theorem nat_size_le_self_formulaTokenWeight (value : Nat) :
    Nat.size value ≤ value := by
  rw [Nat.size_le]
  exact value.lt_two_pow_self

theorem list_length_le_compactAdditiveTokenWeight
    (tokens : List Nat) :
    tokens.length ≤ compactAdditiveTokenWeight tokens := by
  induction tokens with
  | nil => simp
  | cons token tokens ih =>
      simp only [List.length_cons, compactAdditiveTokenWeight_cons]
      omega

theorem compactAdditiveValueWeight_natList_le_two_mul_tokenWeight_add_one
    (tokens : List Nat) :
    compactAdditiveValueWeight tokens ≤
      2 * compactAdditiveTokenWeight tokens + 1 := by
  rw [compactAdditiveValueWeight_list]
  have hsize : Nat.size tokens.length ≤
      compactAdditiveTokenWeight tokens :=
    (nat_size_le_self_formulaTokenWeight tokens.length).trans
      (list_length_le_compactAdditiveTokenWeight tokens)
  change Nat.size tokens.length + 1 +
      (tokens.map (fun token => Nat.size token + 1)).sum ≤ _
  change Nat.size tokens.length + 1 +
      compactAdditiveTokenWeight tokens ≤ _
  omega

theorem compactAdditiveTokenWeight_le_valueWeight_natList
    (tokens : List Nat) :
    compactAdditiveTokenWeight tokens ≤
      compactAdditiveValueWeight tokens := by
  rw [compactAdditiveValueWeight_list]
  change compactAdditiveTokenWeight tokens ≤
    Nat.size tokens.length + 1 + compactAdditiveTokenWeight tokens
  omega

theorem compactAdditiveTokenBitLength_term_canonical
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) :
    compactAdditiveTokenBitLength (compactArithmeticTermTokens term) =
      (binaryTermCode term).length := by
  unfold compactAdditiveTokenBitLength
  simpa [compactBinaryNatCode] using
    congrArg List.length
      (compactArithmeticTermTokens_flatMap_binaryNatCode term)

theorem compactAdditiveTokenBitLength_formula_canonical
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) :
    compactAdditiveTokenBitLength (compactArithmeticFormulaTokens formula) =
      (binaryFormulaCode formula).length := by
  unfold compactAdditiveTokenBitLength
  simpa [compactBinaryNatCode] using
    congrArg List.length
      (compactArithmeticFormulaTokens_flatMap_binaryNatCode formula)

theorem compactArithmeticTermTokens_additiveValueWeight_le
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) :
    compactAdditiveValueWeight (compactArithmeticTermTokens term) ≤
      (binaryTermCode term).length + 1 := by
  have hvalue :=
    compactAdditiveValueWeight_natList_le_two_mul_tokenWeight_add_one
      (compactArithmeticTermTokens term)
  rw [← compactAdditiveTokenBitLength_eq_two_mul_weight,
    compactAdditiveTokenBitLength_term_canonical] at hvalue
  exact hvalue

theorem compactArithmeticFormulaTokens_additiveValueWeight_le
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) :
    compactAdditiveValueWeight (compactArithmeticFormulaTokens formula) ≤
      (binaryFormulaCode formula).length + 1 := by
  have hvalue :=
    compactAdditiveValueWeight_natList_le_two_mul_tokenWeight_add_one
      (compactArithmeticFormulaTokens formula)
  rw [← compactAdditiveTokenBitLength_eq_two_mul_weight,
    compactAdditiveTokenBitLength_formula_canonical] at hvalue
  exact hvalue

theorem compactArithmeticFormulaTokens_tokenWeight_le
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) :
    2 * compactAdditiveTokenWeight
        (compactArithmeticFormulaTokens formula) =
      (binaryFormulaCode formula).length := by
  rw [← compactAdditiveTokenBitLength_eq_two_mul_weight]
  exact compactAdditiveTokenBitLength_formula_canonical formula

#print axioms compactAdditiveTokenBitLength_formula_canonical
#print axioms compactArithmeticTermTokens_additiveValueWeight_le
#print axioms compactArithmeticFormulaTokens_additiveValueWeight_le
#print axioms compactArithmeticFormulaTokens_tokenWeight_le

end FoundationCompactNumericListedDirectFormulaTokenWeightBounds
