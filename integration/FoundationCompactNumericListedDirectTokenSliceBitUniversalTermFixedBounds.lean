import integration.FoundationCompactNumericListedDirectTokenSliceBitAtomFixedBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Fixed term-code bounds for the token-slice bit body

This module isolates the shifted start, width, table, offset, and bit-index
terms used under the inner bounded universal.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceBitUniversalTermFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationCodeBounds

private theorem binaryFunctionTerm_code_length_le_tokenSliceUniversalTerm
    {arity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermCode
      (LO.FirstOrder.Semiterm.func functionSymbol ![left, right])).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead functionSymbol := by
  simp [binaryTermCode, binaryFunctionTermCodeOverhead,
    Matrix.fun_eq_vec_two]
  omega

theorem arithmeticAddTerm_eq_func_tokenSliceUniversalTerm
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (‘!!left + !!right’ : LO.FirstOrder.ArithmeticSemiterm Nat arity) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

theorem arithmeticMulTerm_eq_func_tokenSliceUniversalTerm
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (‘!!left * !!right’ : LO.FirstOrder.ArithmeticSemiterm Nat arity) =
      LO.FirstOrder.Semiterm.func Language.Mul.mul ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Mul.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

def tokenSliceBitUniversalBodyTermCodePolynomial (bitBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let offsetCode :=
    (binaryTermCode
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)).length
  let boundCode :=
    (binaryTermCode
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length
  32 * numeralCode + 8 * offsetCode + 4 * boundCode +
    4 * binaryFunctionTermCodeOverhead Language.Add.add +
    2 * binaryFunctionTermCodeOverhead Language.Mul.mul + 1

theorem tokenSliceBitUniversalTerms_code_le_fixed
    (tokenTable width sourceStart targetStart bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound) :
    let tableTerm := shortBinaryNumeralTerm tokenTable
    let widthTerm := shortBinaryNumeralTerm width
    let sourceTerm := shortBinaryNumeralTerm sourceStart
    let targetTerm := shortBinaryNumeralTerm targetStart
    let offsetTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
      Rew.bShift (&0 : ValuationTerm)
    let bitTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1 := #0
    let sourceShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
      Rew.bShift (Rew.shift sourceTerm)
    let targetShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
      Rew.bShift (Rew.shift targetTerm)
    let widthShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
      Rew.bShift (Rew.shift widthTerm)
    let tableShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
      Rew.bShift (Rew.shift tableTerm)
    let sourceSum : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
      ‘!!sourceShift + !!offsetTerm’
    let targetSum : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
      ‘!!targetShift + !!offsetTerm’
    let sourceProduct : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
      ‘!!sourceSum * !!widthShift’
    let targetProduct : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
      ‘!!targetSum * !!widthShift’
    let sourceIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
      ‘!!sourceProduct + !!bitTerm’
    let targetIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
      ‘!!targetProduct + !!bitTerm’
    let termBound := tokenSliceBitUniversalBodyTermCodePolynomial bitBound
    (binaryTermCode sourceIndex).length <= termBound ∧
      (binaryTermCode targetIndex).length <= termBound ∧
      (binaryTermCode tableShift).length <= termBound := by
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let sourceTerm := shortBinaryNumeralTerm sourceStart
  let targetTerm := shortBinaryNumeralTerm targetStart
  let offsetTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (&0 : ValuationTerm)
  let bitTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1 := #0
  let sourceShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift sourceTerm)
  let targetShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift targetTerm)
  let widthShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift widthTerm)
  let tableShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift tableTerm)
  let sourceSum : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!sourceShift + !!offsetTerm’
  let targetSum : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!targetShift + !!offsetTerm’
  let sourceProduct : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!sourceSum * !!widthShift’
  let targetProduct : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!targetSum * !!widthShift’
  let sourceIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!sourceProduct + !!bitTerm’
  let targetIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!targetProduct + !!bitTerm’
  let termBound := tokenSliceBitUniversalBodyTermCodePolynomial bitBound
  have htableCode :=
    binaryNumeralTerm_code_length_le_envelope tokenTable bitBound htableSize
  have hwidthCode :=
    binaryNumeralTerm_code_length_le_envelope width bitBound hwidthSize
  have hsourceCode :=
    binaryNumeralTerm_code_length_le_envelope sourceStart bitBound
      hsourceStartSize
  have htargetCode :=
    binaryNumeralTerm_code_length_le_envelope targetStart bitBound
      htargetStartSize
  have htableFree := binaryTermCode_shift_length_le tableTerm
  have hwidthFree := binaryTermCode_shift_length_le widthTerm
  have hsourceFree := binaryTermCode_shift_length_le sourceTerm
  have htargetFree := binaryTermCode_shift_length_le targetTerm
  have htableSymbols :=
    termSymbolCount_le_binaryTermCode_length (Rew.shift tableTerm)
  have hwidthSymbols :=
    termSymbolCount_le_binaryTermCode_length (Rew.shift widthTerm)
  have hsourceSymbols :=
    termSymbolCount_le_binaryTermCode_length (Rew.shift sourceTerm)
  have htargetSymbols :=
    termSymbolCount_le_binaryTermCode_length (Rew.shift targetTerm)
  have htableBound := binaryTermCode_bShift_length_le_add_symbols
    (Rew.shift tableTerm)
  have hwidthBound := binaryTermCode_bShift_length_le_add_symbols
    (Rew.shift widthTerm)
  have hsourceBound := binaryTermCode_bShift_length_le_add_symbols
    (Rew.shift sourceTerm)
  have htargetBound := binaryTermCode_bShift_length_le_add_symbols
    (Rew.shift targetTerm)
  have hoffsetSymbols :=
    termSymbolCount_le_binaryTermCode_length
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
  have hoffsetBound := binaryTermCode_bShift_length_le_add_symbols
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
  have hsourceSum :
      (binaryTermCode sourceSum).length <=
        (binaryTermCode sourceShift).length +
          (binaryTermCode offsetTerm).length +
            binaryFunctionTermCodeOverhead Language.Add.add := by
    dsimp only [sourceSum]
    rw [arithmeticAddTerm_eq_func_tokenSliceUniversalTerm]
    exact binaryFunctionTerm_code_length_le_tokenSliceUniversalTerm
      Language.Add.add sourceShift offsetTerm
  have htargetSum :
      (binaryTermCode targetSum).length <=
        (binaryTermCode targetShift).length +
          (binaryTermCode offsetTerm).length +
            binaryFunctionTermCodeOverhead Language.Add.add := by
    dsimp only [targetSum]
    rw [arithmeticAddTerm_eq_func_tokenSliceUniversalTerm]
    exact binaryFunctionTerm_code_length_le_tokenSliceUniversalTerm
      Language.Add.add targetShift offsetTerm
  have hsourceProduct :
      (binaryTermCode sourceProduct).length <=
        (binaryTermCode sourceSum).length +
          (binaryTermCode widthShift).length +
            binaryFunctionTermCodeOverhead Language.Mul.mul := by
    dsimp only [sourceProduct]
    rw [arithmeticMulTerm_eq_func_tokenSliceUniversalTerm]
    exact binaryFunctionTerm_code_length_le_tokenSliceUniversalTerm
      Language.Mul.mul sourceSum widthShift
  have htargetProduct :
      (binaryTermCode targetProduct).length <=
        (binaryTermCode targetSum).length +
          (binaryTermCode widthShift).length +
            binaryFunctionTermCodeOverhead Language.Mul.mul := by
    dsimp only [targetProduct]
    rw [arithmeticMulTerm_eq_func_tokenSliceUniversalTerm]
    exact binaryFunctionTerm_code_length_le_tokenSliceUniversalTerm
      Language.Mul.mul targetSum widthShift
  have hsourceIndex :
      (binaryTermCode sourceIndex).length <=
        (binaryTermCode sourceProduct).length +
          (binaryTermCode bitTerm).length +
            binaryFunctionTermCodeOverhead Language.Add.add := by
    dsimp only [sourceIndex]
    rw [arithmeticAddTerm_eq_func_tokenSliceUniversalTerm]
    exact binaryFunctionTerm_code_length_le_tokenSliceUniversalTerm
      Language.Add.add sourceProduct bitTerm
  have htargetIndex :
      (binaryTermCode targetIndex).length <=
        (binaryTermCode targetProduct).length +
          (binaryTermCode bitTerm).length +
            binaryFunctionTermCodeOverhead Language.Add.add := by
    dsimp only [targetIndex]
    rw [arithmeticAddTerm_eq_func_tokenSliceUniversalTerm]
    exact binaryFunctionTerm_code_length_le_tokenSliceUniversalTerm
      Language.Add.add targetProduct bitTerm
  dsimp only [sourceIndex, targetIndex, sourceProduct, targetProduct,
    sourceSum, targetSum, sourceShift, targetShift, offsetTerm, widthShift,
    tableShift, bitTerm, tableTerm, widthTerm, sourceTerm, targetTerm, termBound,
    tokenSliceBitUniversalBodyTermCodePolynomial] at *
  omega

#print axioms tokenSliceBitUniversalTerms_code_le_fixed

end FoundationCompactNumericListedDirectTokenSliceBitUniversalTermFixedBounds
