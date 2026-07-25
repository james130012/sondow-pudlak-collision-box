import integration.FoundationCompactNumericListedDirectTokenSliceBitClosedTermUniversalEndpointFixedBounds
import integration.FoundationCompactNumericListedDirectTokenSliceOffsetBodyFixedBounds

/-!
# Offset-body code bounds over arbitrary closed token-slice starts

The original composite start terms are preserved under both bound variables.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermBodyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABitAtomArityCodeBounds
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPAFormulaIffCodeBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSliceBitUniversalTermFixedBounds
open FoundationCompactNumericListedDirectTokenSliceOffsetBodyFixedBounds

private theorem binaryFunctionTerm_code_length_le_closedOffsetBody
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

private theorem arithmeticAddTerm_code_length_le_closedOffsetBody
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermCode
      (‘!!left + !!right’ :
        LO.FirstOrder.ArithmeticSemiterm Nat arity)).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead Language.Add.add := by
  rw [arithmeticAddTerm_eq_func_tokenSliceUniversalTerm]
  exact binaryFunctionTerm_code_length_le_closedOffsetBody Language.Add.add
    left right

private theorem arithmeticMulTerm_code_length_le_closedOffsetBody
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermCode
      (‘!!left * !!right’ :
        LO.FirstOrder.ArithmeticSemiterm Nat arity)).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead Language.Mul.mul := by
  rw [arithmeticMulTerm_eq_func_tokenSliceUniversalTerm]
  exact binaryFunctionTerm_code_length_le_closedOffsetBody Language.Mul.mul
    left right

def tokenSliceClosedTermOffsetBitBodyTermCodePolynomial
    (termCode : Nat) : Nat :=
  let offsetCode :=
    (binaryTermCode
      (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2)).length
  let bitCode :=
    (binaryTermCode
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2)).length
  64 * termCode + 8 * offsetCode + 4 * bitCode +
    4 * binaryFunctionTermCodeOverhead Language.Add.add +
    2 * binaryFunctionTermCodeOverhead Language.Mul.mul + 1

def tokenSliceClosedTermOffsetBitBodyCodePolynomial
    (termCode : Nat) : Nat :=
  64 * (bitAtomArityCodePolynomial
    (tokenSliceClosedTermOffsetBitBodyTermCodePolynomial termCode) + 1)

def tokenSliceClosedTermOffsetBodyBoundTermCodePolynomial
    (termCode : Nat) : Nat :=
  16 * termCode + 1

def tokenSliceClosedTermOffsetBodyCodePolynomial
    (termCode : Nat) : Nat :=
  32 * (tokenSliceClosedTermOffsetBitBodyCodePolynomial termCode +
    tokenSliceClosedTermOffsetBodyBoundTermCodePolynomial termCode +
    finiteCaseLessThanFormulaCodeOverhead + 64) + 128

theorem tokenSliceClosedTermOffsetBitTerms_code_le
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm : ValuationTerm)
    (termCode : Nat)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termCode)
    (hwidthCode : (binaryTermCode widthTerm).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode) :
    let offsetTerm : LO.FirstOrder.ArithmeticSemiterm Nat 2 := #1
    let bitTerm : LO.FirstOrder.ArithmeticSemiterm Nat 2 := #0
    let sourceShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
      Rew.bShift (Rew.bShift sourceStartTerm)
    let targetShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
      Rew.bShift (Rew.bShift targetStartTerm)
    let widthShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
      Rew.bShift (Rew.bShift widthTerm)
    let tableShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
      Rew.bShift (Rew.bShift tokenTableTerm)
    let sourceIndex :=
      ‘(!!sourceShift + !!offsetTerm) * !!widthShift + !!bitTerm’
    let targetIndex :=
      ‘(!!targetShift + !!offsetTerm) * !!widthShift + !!bitTerm’
    let termBound :=
      tokenSliceClosedTermOffsetBitBodyTermCodePolynomial termCode
    (binaryTermCode sourceIndex).length <= termBound ∧
      (binaryTermCode targetIndex).length <= termBound ∧
      (binaryTermCode tableShift).length <= termBound := by
  let offsetTerm : LO.FirstOrder.ArithmeticSemiterm Nat 2 := #1
  let bitTerm : LO.FirstOrder.ArithmeticSemiterm Nat 2 := #0
  let sourceShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift sourceStartTerm)
  let targetShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift targetStartTerm)
  let widthShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift widthTerm)
  let tableShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift tokenTableTerm)
  let sourceSum := ‘!!sourceShift + !!offsetTerm’
  let targetSum := ‘!!targetShift + !!offsetTerm’
  let sourceProduct := ‘!!sourceSum * !!widthShift’
  let targetProduct := ‘!!targetSum * !!widthShift’
  let sourceIndex := ‘!!sourceProduct + !!bitTerm’
  let targetIndex := ‘!!targetProduct + !!bitTerm’
  let termBound :=
    tokenSliceClosedTermOffsetBitBodyTermCodePolynomial termCode
  have htableSymbols0 :=
    termSymbolCount_le_binaryTermCode_length tokenTableTerm
  have hwidthSymbols0 :=
    termSymbolCount_le_binaryTermCode_length widthTerm
  have hsourceSymbols0 :=
    termSymbolCount_le_binaryTermCode_length sourceStartTerm
  have htargetSymbols0 :=
    termSymbolCount_le_binaryTermCode_length targetStartTerm
  have htableShift1 :=
    binaryTermCode_bShift_length_le_add_symbols tokenTableTerm
  have hwidthShift1 :=
    binaryTermCode_bShift_length_le_add_symbols widthTerm
  have hsourceShift1 :=
    binaryTermCode_bShift_length_le_add_symbols sourceStartTerm
  have htargetShift1 :=
    binaryTermCode_bShift_length_le_add_symbols targetStartTerm
  have htableSymbols1 :=
    termSymbolCount_le_binaryTermCode_length (Rew.bShift tokenTableTerm)
  have hwidthSymbols1 :=
    termSymbolCount_le_binaryTermCode_length (Rew.bShift widthTerm)
  have hsourceSymbols1 :=
    termSymbolCount_le_binaryTermCode_length (Rew.bShift sourceStartTerm)
  have htargetSymbols1 :=
    termSymbolCount_le_binaryTermCode_length (Rew.bShift targetStartTerm)
  have htableShift2 :=
    binaryTermCode_bShift_length_le_add_symbols (Rew.bShift tokenTableTerm)
  have hwidthShift2 :=
    binaryTermCode_bShift_length_le_add_symbols (Rew.bShift widthTerm)
  have hsourceShift2 :=
    binaryTermCode_bShift_length_le_add_symbols
      (Rew.bShift sourceStartTerm)
  have htargetShift2 :=
    binaryTermCode_bShift_length_le_add_symbols
      (Rew.bShift targetStartTerm)
  have hsourceSum :=
    arithmeticAddTerm_code_length_le_closedOffsetBody sourceShift offsetTerm
  have htargetSum :=
    arithmeticAddTerm_code_length_le_closedOffsetBody targetShift offsetTerm
  have hsourceProduct :=
    arithmeticMulTerm_code_length_le_closedOffsetBody sourceSum widthShift
  have htargetProduct :=
    arithmeticMulTerm_code_length_le_closedOffsetBody targetSum widthShift
  have hsourceIndex :=
    arithmeticAddTerm_code_length_le_closedOffsetBody sourceProduct bitTerm
  have htargetIndex :=
    arithmeticAddTerm_code_length_le_closedOffsetBody targetProduct bitTerm
  dsimp only [sourceIndex, targetIndex, sourceProduct, targetProduct,
    sourceSum, targetSum, sourceShift, targetShift, offsetTerm, widthShift,
    tableShift, bitTerm, termBound,
    tokenSliceClosedTermOffsetBitBodyTermCodePolynomial] at *
  omega

theorem tokenSliceAtValuationOffsetBitBody_code_length_le_closedFixed
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm : ValuationTerm)
    (termCode : Nat)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termCode)
    (hwidthCode : (binaryTermCode widthTerm).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode) :
    (binaryFormulaCode
      (tokenSliceAtValuationOffsetBitBody tokenTableTerm widthTerm
        sourceStartTerm targetStartTerm)).length <=
      tokenSliceClosedTermOffsetBitBodyCodePolynomial termCode := by
  let offsetTerm : LO.FirstOrder.ArithmeticSemiterm Nat 2 := #1
  let bitTerm : LO.FirstOrder.ArithmeticSemiterm Nat 2 := #0
  let sourceShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift sourceStartTerm)
  let targetShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift targetStartTerm)
  let widthShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift widthTerm)
  let tableShift : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift tokenTableTerm)
  let sourceIndex :=
    ‘(!!sourceShift + !!offsetTerm) * !!widthShift + !!bitTerm’
  let targetIndex :=
    ‘(!!targetShift + !!offsetTerm) * !!widthShift + !!bitTerm’
  let termBound :=
    tokenSliceClosedTermOffsetBitBodyTermCodePolynomial termCode
  let sourceAtom := binaryBitAtomAtTerms sourceIndex tableShift
  let targetAtom := binaryBitAtomAtTerms targetIndex tableShift
  have hterms := tokenSliceClosedTermOffsetBitTerms_code_le tokenTableTerm
    widthTerm sourceStartTerm targetStartTerm termCode htableCode hwidthCode
    hsourceCode htargetCode
  have hsource :
      (binaryFormulaCode sourceAtom).length <=
        bitAtomArityCodePolynomial termBound :=
    binaryBitAtomAtTerms_code_length_le_arity sourceIndex tableShift termBound
      hterms.1 hterms.2.2
  have htarget :
      (binaryFormulaCode targetAtom).length <=
        bitAtomArityCodePolynomial termBound :=
    binaryBitAtomAtTerms_code_length_le_arity targetIndex tableShift termBound
      hterms.2.1 hterms.2.2
  have hiff := binaryFormulaCode_iff_length_le sourceAtom targetAtom
  have hformula :
      tokenSliceAtValuationOffsetBitBody tokenTableTerm widthTerm
        sourceStartTerm targetStartTerm = sourceAtom 🡘 targetAtom := by
    rfl
  rw [hformula]
  unfold tokenSliceClosedTermOffsetBitBodyCodePolynomial
  dsimp only [termBound] at hsource htarget
  omega

theorem tokenSliceAtValuationOffsetBody_code_length_le_closedFixed
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm : ValuationTerm)
    (termCode : Nat)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termCode)
    (hwidthCode : (binaryTermCode widthTerm).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode) :
    (binaryFormulaCode
      (tokenSliceAtValuationOffsetBody tokenTableTerm widthTerm
        sourceStartTerm targetStartTerm)).length <=
      tokenSliceClosedTermOffsetBodyCodePolynomial termCode := by
  let innerBody := tokenSliceAtValuationOffsetBitBody tokenTableTerm widthTerm
    sourceStartTerm targetStartTerm
  let boundTerm : LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
    Rew.bShift (Rew.bShift widthTerm)
  let lowerBound := finiteCaseLessThanFormula
    (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2) boundTerm
  let universalBody := lowerBound 🡒 innerBody
  let boundCode :=
    tokenSliceClosedTermOffsetBodyBoundTermCodePolynomial termCode
  let innerCode :=
    tokenSliceClosedTermOffsetBitBodyCodePolynomial termCode
  have hwidthSymbols0 :=
    termSymbolCount_le_binaryTermCode_length widthTerm
  have hwidthShift1 :=
    binaryTermCode_bShift_length_le_add_symbols widthTerm
  have hwidthSymbols1 :=
    termSymbolCount_le_binaryTermCode_length (Rew.bShift widthTerm)
  have hwidthShift2 :=
    binaryTermCode_bShift_length_le_add_symbols (Rew.bShift widthTerm)
  have hboundCode : (binaryTermCode boundTerm).length <= boundCode := by
    dsimp only [boundTerm, boundCode] at *
    unfold tokenSliceClosedTermOffsetBodyBoundTermCodePolynomial
    omega
  have hinnerCode : (binaryFormulaCode innerBody).length <= innerCode := by
    dsimp only [innerBody, innerCode]
    exact tokenSliceAtValuationOffsetBitBody_code_length_le_closedFixed
      tokenTableTerm widthTerm sourceStartTerm targetStartTerm termCode
      htableCode hwidthCode hsourceCode htargetCode
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
      tokenSliceAtValuationOffsetBody tokenTableTerm widthTerm
          sourceStartTerm targetStartTerm =
        ∀⁰ universalBody := by
    unfold tokenSliceAtValuationOffsetBody
    rw [LO.FirstOrder.Semiformula.ballLT,
      LO.FirstOrder.Semiformula.ball_eq]
    unfold universalBody lowerBound
    rw [finiteCaseLessThanFormula_eq_operator]
  rw [halign]
  unfold tokenSliceClosedTermOffsetBodyCodePolynomial
  omega

#print axioms tokenSliceClosedTermOffsetBitTerms_code_le
#print axioms tokenSliceAtValuationOffsetBitBody_code_length_le_closedFixed
#print axioms tokenSliceAtValuationOffsetBody_code_length_le_closedFixed

end FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermBodyFixedBounds
