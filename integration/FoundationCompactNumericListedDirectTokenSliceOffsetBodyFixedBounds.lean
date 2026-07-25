import integration.FoundationCompactNumericListedDirectTokenSliceBitUniversalFixedBounds
import integration.FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds

/-!
# Fixed code bounds for the token-slice offset body

The offset body has two live bound variables: offset and bit index.  Its code
is bounded directly, without a global assumption about `Rew.fix`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceOffsetBodyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABitAtomArityCodeBounds
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitMembershipValuationCompilerPublicBounds
open FoundationCompactPAFormulaIffCodeBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSliceBitUniversalTermFixedBounds

private theorem binaryFunctionTerm_code_length_le_offsetBody
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

def tokenSliceOffsetBitBodyTermCodePolynomial (bitBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let offsetCode :=
    (binaryTermCode
      (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2)).length
  let bitCode :=
    (binaryTermCode
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2)).length
  64 * numeralCode + 8 * offsetCode + 4 * bitCode +
    4 * binaryFunctionTermCodeOverhead Language.Add.add +
    2 * binaryFunctionTermCodeOverhead Language.Mul.mul + 1

def tokenSliceOffsetBitBodyCodePolynomial (bitBound : Nat) : Nat :=
  64 * (bitAtomArityCodePolynomial
    (tokenSliceOffsetBitBodyTermCodePolynomial bitBound) + 1)

def tokenSliceOffsetBodyBoundTermCodePolynomial (bitBound : Nat) : Nat :=
  16 * binaryNumeralTermCodeEnvelope bitBound + 1

def tokenSliceOffsetBodyCodePolynomial (bitBound : Nat) : Nat :=
  32 * (tokenSliceOffsetBitBodyCodePolynomial bitBound +
    tokenSliceOffsetBodyBoundTermCodePolynomial bitBound +
    finiteCaseLessThanFormulaCodeOverhead + 64) + 128

theorem tokenSliceAtValuationOffsetBitTerms_code_le_fixed
    (tokenTable width sourceStart targetStart bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound) :
    let tableTerm := shortBinaryNumeralTerm tokenTable
    let widthTerm := shortBinaryNumeralTerm width
    let sourceTerm := shortBinaryNumeralTerm sourceStart
    let targetTerm := shortBinaryNumeralTerm targetStart
    let offsetTerm : LO.FirstOrder.ArithmeticSemiterm Nat 2 := #1
    let bitTerm : LO.FirstOrder.ArithmeticSemiterm Nat 2 := #0
    let sourceShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
      Rew.bShift (Rew.bShift sourceTerm)
    let targetShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
      Rew.bShift (Rew.bShift targetTerm)
    let widthShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
      Rew.bShift (Rew.bShift widthTerm)
    let tableShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
      Rew.bShift (Rew.bShift tableTerm)
    let sourceSum := ‘!!sourceShift + !!offsetTerm’
    let targetSum := ‘!!targetShift + !!offsetTerm’
    let sourceProduct := ‘!!sourceSum * !!widthShift’
    let targetProduct := ‘!!targetSum * !!widthShift’
    let sourceIndex := ‘!!sourceProduct + !!bitTerm’
    let targetIndex := ‘!!targetProduct + !!bitTerm’
    let termBound := tokenSliceOffsetBitBodyTermCodePolynomial bitBound
    (binaryTermCode sourceIndex).length <= termBound ∧
      (binaryTermCode targetIndex).length <= termBound ∧
      (binaryTermCode tableShift).length <= termBound := by
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let sourceTerm := shortBinaryNumeralTerm sourceStart
  let targetTerm := shortBinaryNumeralTerm targetStart
  let offsetTerm : LO.FirstOrder.ArithmeticSemiterm Nat 2 := #1
  let bitTerm : LO.FirstOrder.ArithmeticSemiterm Nat 2 := #0
  let sourceShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift sourceTerm)
  let targetShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift targetTerm)
  let widthShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift widthTerm)
  let tableShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift tableTerm)
  let sourceSum := ‘!!sourceShift + !!offsetTerm’
  let targetSum := ‘!!targetShift + !!offsetTerm’
  let sourceProduct := ‘!!sourceSum * !!widthShift’
  let targetProduct := ‘!!targetSum * !!widthShift’
  let sourceIndex := ‘!!sourceProduct + !!bitTerm’
  let targetIndex := ‘!!targetProduct + !!bitTerm’
  let termBound := tokenSliceOffsetBitBodyTermCodePolynomial bitBound
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
  have htableSymbols0 :=
    termSymbolCount_le_binaryTermCode_length tableTerm
  have hwidthSymbols0 :=
    termSymbolCount_le_binaryTermCode_length widthTerm
  have hsourceSymbols0 :=
    termSymbolCount_le_binaryTermCode_length sourceTerm
  have htargetSymbols0 :=
    termSymbolCount_le_binaryTermCode_length targetTerm
  have htableShift1 := binaryTermCode_bShift_length_le_add_symbols tableTerm
  have hwidthShift1 := binaryTermCode_bShift_length_le_add_symbols widthTerm
  have hsourceShift1 := binaryTermCode_bShift_length_le_add_symbols sourceTerm
  have htargetShift1 := binaryTermCode_bShift_length_le_add_symbols targetTerm
  have htableSymbols1 := termSymbolCount_le_binaryTermCode_length
    (Rew.bShift tableTerm)
  have hwidthSymbols1 := termSymbolCount_le_binaryTermCode_length
    (Rew.bShift widthTerm)
  have hsourceSymbols1 := termSymbolCount_le_binaryTermCode_length
    (Rew.bShift sourceTerm)
  have htargetSymbols1 := termSymbolCount_le_binaryTermCode_length
    (Rew.bShift targetTerm)
  have htableShift2 := binaryTermCode_bShift_length_le_add_symbols
    (Rew.bShift tableTerm)
  have hwidthShift2 := binaryTermCode_bShift_length_le_add_symbols
    (Rew.bShift widthTerm)
  have hsourceShift2 := binaryTermCode_bShift_length_le_add_symbols
    (Rew.bShift sourceTerm)
  have htargetShift2 := binaryTermCode_bShift_length_le_add_symbols
    (Rew.bShift targetTerm)
  have hsourceSum :
      (binaryTermCode sourceSum).length <=
        (binaryTermCode sourceShift).length +
          (binaryTermCode offsetTerm).length +
            binaryFunctionTermCodeOverhead Language.Add.add := by
    dsimp only [sourceSum]
    rw [arithmeticAddTerm_eq_func_tokenSliceUniversalTerm]
    exact binaryFunctionTerm_code_length_le_offsetBody Language.Add.add
      sourceShift offsetTerm
  have htargetSum :
      (binaryTermCode targetSum).length <=
        (binaryTermCode targetShift).length +
          (binaryTermCode offsetTerm).length +
            binaryFunctionTermCodeOverhead Language.Add.add := by
    dsimp only [targetSum]
    rw [arithmeticAddTerm_eq_func_tokenSliceUniversalTerm]
    exact binaryFunctionTerm_code_length_le_offsetBody Language.Add.add
      targetShift offsetTerm
  have hsourceProduct :
      (binaryTermCode sourceProduct).length <=
        (binaryTermCode sourceSum).length +
          (binaryTermCode widthShift).length +
            binaryFunctionTermCodeOverhead Language.Mul.mul := by
    dsimp only [sourceProduct]
    rw [arithmeticMulTerm_eq_func_tokenSliceUniversalTerm]
    exact binaryFunctionTerm_code_length_le_offsetBody Language.Mul.mul
      sourceSum widthShift
  have htargetProduct :
      (binaryTermCode targetProduct).length <=
        (binaryTermCode targetSum).length +
          (binaryTermCode widthShift).length +
            binaryFunctionTermCodeOverhead Language.Mul.mul := by
    dsimp only [targetProduct]
    rw [arithmeticMulTerm_eq_func_tokenSliceUniversalTerm]
    exact binaryFunctionTerm_code_length_le_offsetBody Language.Mul.mul
      targetSum widthShift
  have hsourceIndex :
      (binaryTermCode sourceIndex).length <=
        (binaryTermCode sourceProduct).length +
          (binaryTermCode bitTerm).length +
            binaryFunctionTermCodeOverhead Language.Add.add := by
    dsimp only [sourceIndex]
    rw [arithmeticAddTerm_eq_func_tokenSliceUniversalTerm]
    exact binaryFunctionTerm_code_length_le_offsetBody Language.Add.add
      sourceProduct bitTerm
  have htargetIndex :
      (binaryTermCode targetIndex).length <=
        (binaryTermCode targetProduct).length +
          (binaryTermCode bitTerm).length +
            binaryFunctionTermCodeOverhead Language.Add.add := by
    dsimp only [targetIndex]
    rw [arithmeticAddTerm_eq_func_tokenSliceUniversalTerm]
    exact binaryFunctionTerm_code_length_le_offsetBody Language.Add.add
      targetProduct bitTerm
  dsimp only [sourceIndex, targetIndex, sourceProduct, targetProduct,
    sourceSum, targetSum, sourceShift, targetShift, offsetTerm, widthShift,
    tableShift, bitTerm, tableTerm, widthTerm, sourceTerm, targetTerm,
    termBound, tokenSliceOffsetBitBodyTermCodePolynomial] at *
  omega

theorem tokenSliceAtValuationOffsetBitBody_code_length_le_fixed
    (tokenTable width sourceStart targetStart bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound) :
    (binaryFormulaCode
      (tokenSliceAtValuationOffsetBitBody
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm sourceStart)
        (shortBinaryNumeralTerm targetStart))).length <=
      tokenSliceOffsetBitBodyCodePolynomial bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let sourceTerm := shortBinaryNumeralTerm sourceStart
  let targetTerm := shortBinaryNumeralTerm targetStart
  let offsetTerm : LO.FirstOrder.ArithmeticSemiterm Nat 2 := #1
  let bitTerm : LO.FirstOrder.ArithmeticSemiterm Nat 2 := #0
  let sourceShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift sourceTerm)
  let targetShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift targetTerm)
  let widthShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift widthTerm)
  let tableShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift tableTerm)
  let sourceIndex := ‘(!!sourceShift + !!offsetTerm) * !!widthShift +
    !!bitTerm’
  let targetIndex := ‘(!!targetShift + !!offsetTerm) * !!widthShift +
    !!bitTerm’
  let termBound := tokenSliceOffsetBitBodyTermCodePolynomial bitBound
  let sourceAtom := binaryBitAtomAtTerms sourceIndex tableShift
  let targetAtom := binaryBitAtomAtTerms targetIndex tableShift
  have hterms := tokenSliceAtValuationOffsetBitTerms_code_le_fixed tokenTable
    width sourceStart targetStart bitBound htableSize hwidthSize
    hsourceStartSize htargetStartSize
  have hsourceIndex : (binaryTermCode sourceIndex).length <= termBound := by
    simpa only [sourceIndex, sourceShift, offsetTerm, widthShift, bitTerm,
      tableTerm, widthTerm, sourceTerm, targetTerm, termBound] using hterms.1
  have htargetIndex : (binaryTermCode targetIndex).length <= termBound := by
    simpa only [targetIndex, targetShift, offsetTerm, widthShift, bitTerm,
      tableTerm, widthTerm, sourceTerm, targetTerm, termBound] using hterms.2.1
  have htableShift : (binaryTermCode tableShift).length <= termBound := by
    simpa only [tableShift, tableTerm, widthTerm, sourceTerm, targetTerm,
      termBound] using hterms.2.2
  have hsourceAtom :
      (binaryFormulaCode sourceAtom).length <=
        bitAtomArityCodePolynomial termBound :=
    binaryBitAtomAtTerms_code_length_le_arity sourceIndex tableShift
      termBound hsourceIndex htableShift
  have htargetAtom :
      (binaryFormulaCode targetAtom).length <=
        bitAtomArityCodePolynomial termBound :=
    binaryBitAtomAtTerms_code_length_le_arity targetIndex tableShift
      termBound htargetIndex htableShift
  have hiff := binaryFormulaCode_iff_length_le sourceAtom targetAtom
  have hformula :
      tokenSliceAtValuationOffsetBitBody tableTerm widthTerm sourceTerm
        targetTerm = sourceAtom 🡘 targetAtom := by
    rfl
  rw [hformula]
  unfold tokenSliceOffsetBitBodyCodePolynomial
  dsimp only [termBound] at hsourceAtom htargetAtom
  omega

theorem tokenSliceAtValuationOffsetBody_code_length_le_fixed
    (tokenTable width sourceStart targetStart bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound) :
    (binaryFormulaCode
      (tokenSliceAtValuationOffsetBody
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm sourceStart)
        (shortBinaryNumeralTerm targetStart))).length <=
      tokenSliceOffsetBodyCodePolynomial bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let sourceTerm := shortBinaryNumeralTerm sourceStart
  let targetTerm := shortBinaryNumeralTerm targetStart
  let innerBody := tokenSliceAtValuationOffsetBitBody tableTerm widthTerm
    sourceTerm targetTerm
  let boundTerm : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift widthTerm)
  let lowerBound :=
    finiteCaseLessThanFormula
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2) boundTerm
  let universalBody := lowerBound 🡒 innerBody
  let boundCode := tokenSliceOffsetBodyBoundTermCodePolynomial bitBound
  let innerCode := tokenSliceOffsetBitBodyCodePolynomial bitBound
  have hwidthCode :=
    binaryNumeralTerm_code_length_le_envelope width bitBound hwidthSize
  have hwidthSymbols0 :=
    termSymbolCount_le_binaryTermCode_length widthTerm
  have hwidthShift1 :=
    binaryTermCode_bShift_length_le_add_symbols widthTerm
  have hwidthSymbols1 :=
    termSymbolCount_le_binaryTermCode_length (Rew.bShift widthTerm)
  have hwidthShift2 :=
    binaryTermCode_bShift_length_le_add_symbols (Rew.bShift widthTerm)
  have hboundCode :
      (binaryTermCode boundTerm).length <= boundCode := by
    dsimp only [boundTerm, widthTerm, boundCode]
    unfold tokenSliceOffsetBodyBoundTermCodePolynomial
    dsimp only [widthTerm] at hwidthSymbols0 hwidthShift1 hwidthSymbols1 hwidthShift2
    omega
  have hinnerCode :
      (binaryFormulaCode innerBody).length <= innerCode := by
    dsimp only [innerBody, innerCode, tableTerm, widthTerm, sourceTerm,
      targetTerm]
    exact tokenSliceAtValuationOffsetBitBody_code_length_le_fixed tokenTable
      width sourceStart targetStart bitBound htableSize hwidthSize
      hsourceStartSize htargetStartSize
  have htermBoundRaw := finiteCaseLessThanFormula_code_length_le
    (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2) boundTerm
  have htermBound :
      (binaryFormulaCode lowerBound).length <=
        (binaryTermCode
          (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2)).length +
          boundCode + finiteCaseLessThanFormulaCodeOverhead := by
    simpa only [lowerBound] using
      htermBoundRaw.trans (Nat.add_le_add_right
        (Nat.add_le_add_left hboundCode
          (binaryTermCode
            (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2)).length)
        finiteCaseLessThanFormulaCodeOverhead)
  have himplication := binarySemiformulaCode_implication_length_le
    lowerBound innerBody
  have htagFive : (binaryNatCode 5).length <= 64 := by decide
  have hzeroCode :
      (binaryTermCode
        (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2)).length <= 64 := by
    decide
  have huniversalBody :
      (binaryFormulaCode universalBody).length <=
        2 * ((binaryTermCode
          (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2)).length +
            boundCode + finiteCaseLessThanFormulaCodeOverhead) +
          innerCode + 64 := by
    dsimp only [universalBody]
    omega
  have hall :
      (binaryFormulaCode (∀⁰ universalBody)).length <=
        (binaryFormulaCode universalBody).length + 8 := by
    have htag : (binaryNatCode 6).length <= 8 := by decide
    simp only [binaryFormulaCode, List.length_append]
    omega
  have halign :
      tokenSliceAtValuationOffsetBody tableTerm widthTerm sourceTerm
          targetTerm =
        ∀⁰ universalBody := by
    unfold tokenSliceAtValuationOffsetBody
    rw [LO.FirstOrder.Semiformula.ballLT,
      LO.FirstOrder.Semiformula.ball_eq]
    unfold universalBody lowerBound
    rw [finiteCaseLessThanFormula_eq_operator]
  rw [halign]
  unfold tokenSliceOffsetBodyCodePolynomial
  omega

#print axioms tokenSliceAtValuationOffsetBitTerms_code_le_fixed
#print axioms tokenSliceAtValuationOffsetBitBody_code_length_le_fixed
#print axioms tokenSliceAtValuationOffsetBody_code_length_le_fixed

end FoundationCompactNumericListedDirectTokenSliceOffsetBodyFixedBounds
