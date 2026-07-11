import integration.FoundationCompactNumericAllClosure
import integration.FoundationCompactListedVerifierArithmeticInput

/-!
# Pure numeric canonical token bit length

The candidate-length guard uses the real length of the original binary formula
serialization, not the number of decoded natural tokens. This module proves
that re-encoding every numeric token with the same `binaryNatCode` recovers the
exact term and formula bit lengths.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericTokenBitLength

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxTokenMachine
open FoundationCompactListedVerifierArithmeticInput

def compactBinaryNatCode (value : Nat) : List Bool :=
  binaryNatCode value

theorem compactBinaryNatCode_primrec :
    Primrec compactBinaryNatCode := by
  have hpairs : Primrec (fun value : Nat =>
      value.bits.flatMap fun bit => [true, bit]) := by
    have hpair : Primrec₂ (fun (_value : Nat) (bit : Bool) =>
        [true, bit]) :=
      Primrec.list_cons.comp₂ (Primrec₂.const true)
        (Primrec.list_cons.comp₂ Primrec₂.right (Primrec₂.const []))
    exact Primrec.list_flatMap natBits_primrec hpair
  exact
    (Primrec.list_append.comp hpairs
      (Primrec.const [false, false])).of_eq fun value => by
        rfl

def compactTokenBitLength (tokens : List Nat) : Nat :=
  (tokens.flatMap compactBinaryNatCode).length

theorem compactTokenBitLength_primrec :
    Primrec compactTokenBitLength := by
  have hencoded : Primrec (fun tokens : List Nat =>
      tokens.flatMap compactBinaryNatCode) :=
    Primrec.list_flatMap Primrec.id
      (compactBinaryNatCode_primrec.comp₂ Primrec₂.right)
  exact Primrec.list_length.comp hencoded

theorem compactArithmeticTermTokens_flatMap_binaryNatCode
    {binderArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat binderArity) :
    (compactArithmeticTermTokens term).flatMap compactBinaryNatCode =
      binaryTermCode term := by
  induction term with
  | bvar index =>
      simp [compactArithmeticTermTokens, compactBinaryNatCode,
        binaryTermCode]
  | fvar freeIndex =>
      simp [compactArithmeticTermTokens, compactBinaryNatCode,
        binaryTermCode]
  | @func functionArity functionSymbol arguments ih =>
      simp only [compactArithmeticTermTokens, binaryTermCode,
        List.flatMap_append]
      have hheader :
          List.flatMap compactBinaryNatCode
              [2, functionArity, Encodable.encode functionSymbol] =
            binaryNatCode 2 ++ binaryNatCode functionArity ++
              binaryNatCode (Encodable.encode functionSymbol) := by
        simp [compactBinaryNatCode, List.append_assoc]
      rw [hheader]
      rw [← flatten_map_flatMap_eq_flatMap_flatten]
      simp only [List.map_ofFn, Function.comp_def]
      congr 1
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext index
      exact ih index

theorem compactArithmeticFormulaTokens_flatMap_binaryNatCode
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) :
    (compactArithmeticFormulaTokens formula).flatMap compactBinaryNatCode =
      binaryFormulaCode formula := by
  induction formula with
  | @rel formulaArity relationArity relationSymbol arguments =>
      simp only [compactArithmeticFormulaTokens, binaryFormulaCode,
        List.flatMap_append]
      have hheader :
          List.flatMap compactBinaryNatCode
              [0, relationArity, Encodable.encode relationSymbol] =
            binaryNatCode 0 ++ binaryNatCode relationArity ++
              binaryNatCode (Encodable.encode relationSymbol) := by
        simp [compactBinaryNatCode, List.append_assoc]
      rw [hheader]
      rw [← flatten_map_flatMap_eq_flatMap_flatten]
      simp only [List.map_ofFn, Function.comp_def]
      congr 1
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext index
      exact compactArithmeticTermTokens_flatMap_binaryNatCode
        (arguments index)
  | @nrel formulaArity relationArity relationSymbol arguments =>
      simp only [compactArithmeticFormulaTokens, binaryFormulaCode,
        List.flatMap_append]
      have hheader :
          List.flatMap compactBinaryNatCode
              [1, relationArity, Encodable.encode relationSymbol] =
            binaryNatCode 1 ++ binaryNatCode relationArity ++
              binaryNatCode (Encodable.encode relationSymbol) := by
        simp [compactBinaryNatCode, List.append_assoc]
      rw [hheader]
      rw [← flatten_map_flatMap_eq_flatMap_flatten]
      simp only [List.map_ofFn, Function.comp_def]
      congr 1
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext index
      exact compactArithmeticTermTokens_flatMap_binaryNatCode
        (arguments index)
  | @verum formulaArity =>
      rfl
  | @falsum formulaArity =>
      rfl
  | @and formulaArity left right ihLeft ihRight =>
      simp [compactArithmeticFormulaTokens, binaryFormulaCode,
        compactBinaryNatCode, ihLeft, ihRight]
  | @or formulaArity left right ihLeft ihRight =>
      simp [compactArithmeticFormulaTokens, binaryFormulaCode,
        compactBinaryNatCode, ihLeft, ihRight]
  | @all formulaArity body ih =>
      simp [compactArithmeticFormulaTokens, binaryFormulaCode,
        compactBinaryNatCode, ih]
  | @exs formulaArity body ih =>
      simp [compactArithmeticFormulaTokens, binaryFormulaCode,
        compactBinaryNatCode, ih]

theorem compactTokenBitLength_formula_canonical
    {binderArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat binderArity) :
    compactTokenBitLength (compactArithmeticFormulaTokens formula) =
      (binaryFormulaCode formula).length := by
  simp [compactTokenBitLength,
    compactArithmeticFormulaTokens_flatMap_binaryNatCode]

#print axioms compactBinaryNatCode_primrec
#print axioms compactTokenBitLength_primrec
#print axioms compactArithmeticTermTokens_flatMap_binaryNatCode
#print axioms compactArithmeticFormulaTokens_flatMap_binaryNatCode
#print axioms compactTokenBitLength_formula_canonical

end FoundationCompactNumericTokenBitLength
