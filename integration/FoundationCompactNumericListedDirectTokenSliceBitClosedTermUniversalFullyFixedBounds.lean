import integration.FoundationCompactNumericListedDirectTokenSliceBitClosedTermBranchesFixedBounds
import integration.FoundationCompactNumericListedDirectTokenSliceBitBranchesFixedAssembly
import integration.FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
import integration.FoundationCompactPAContextualBranchesFixedAssembly
import integration.FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds

/-!
# Fixed bit universal over arbitrary closed token-slice terms

This module preserves the original closed syntax of composite source and
target starts while charging the complete inner bit universal to explicit
public bounds.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceBitClosedTermUniversalFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABitAtomArityCodeBounds
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualBranchesFixedAssembly
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAFormulaIffCodeBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationContextShiftedCodeSumBounds
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAHybridBranchesLeafResourceMonotonicity
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectTokenSliceBitAtomFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitAtomClosedTermFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitUniversalFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitUniversalTermFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitUniversalOuterVariables
open FoundationCompactNumericListedDirectTokenSliceBitClosedTermBranchesFixedBounds

def tokenSliceClosedTermBitUniversalBodyTermCodePolynomial
    (termCode : Nat) : Nat :=
  let offsetCode :=
    (binaryTermCode
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)).length
  let bitCode :=
    (binaryTermCode
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length
  64 * termCode + 8 * offsetCode + 4 * bitCode +
    4 * binaryFunctionTermCodeOverhead Language.Add.add +
    2 * binaryFunctionTermCodeOverhead Language.Mul.mul + 1

def tokenSliceClosedTermBitUniversalBodyCodePolynomial
    (termCode : Nat) : Nat :=
  64 * (bitAtomArityCodePolynomial
    (tokenSliceClosedTermBitUniversalBodyTermCodePolynomial termCode) + 1)

def tokenSliceClosedTermBitUniversalSyntaxFixedPolynomial
    (numericBound termCode : Nat) : Nat :=
  numericBound + tokenSliceClosedTermBitUniversalBodyCodePolynomial termCode

def tokenSliceClosedTermBitUniversalFormulaFixedPolynomial
    (numericBound termCode : Nat) : Nat :=
  boundedUniversalClosedFormulaEnvelope
      (tokenSliceClosedTermBitUniversalSyntaxFixedPolynomial numericBound
        termCode) +
    2 * tokenSliceClosedTermBitUniversalBodyCodePolynomial termCode

def tokenSliceClosedTermBitUniversalLocalPayloadFixedPolynomial
    (numericBound termCode : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (tokenSliceClosedTermBitUniversalFormulaFixedPolynomial numericBound
        termCode +
      2 * valuationContextFormulaCodeSumEnvelope 1 numericBound
        tokenSliceBitBranchVariableCodeCeiling)

def tokenSliceClosedTermBitUniversalContextFormulaFixedPolynomial
    (numericBound termCode : Nat) : Nat :=
  tokenSliceClosedTermBitUniversalFormulaFixedPolynomial numericBound
      termCode +
    2 * valuationContextFormulaCodeSumEnvelope 1 numericBound
      tokenSliceBitBranchVariableCodeCeiling

def tokenSliceClosedTermBitBranchesFullyFixedPayloadPolynomial
    (numericBound termCode bitBound : Nat) : Nat :=
  (numericBound + 1) *
    (tokenSliceClosedTermBitBranchPayloadSumFixedPolynomial numericBound
        termCode bitBound +
      3 * tokenSliceClosedTermBitUniversalLocalPayloadFixedPolynomial
        numericBound termCode)

private theorem binaryFunctionTerm_code_length_le_closedTermBitUniversal
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

private theorem arithmeticAddTerm_code_length_le_closedTermBitUniversal
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermCode
      (‘!!left + !!right’ :
        LO.FirstOrder.ArithmeticSemiterm Nat arity)).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead Language.Add.add := by
  rw [arithmeticAddTerm_eq_func_tokenSliceUniversalTerm]
  exact binaryFunctionTerm_code_length_le_closedTermBitUniversal
    Language.Add.add left right

private theorem arithmeticMulTerm_code_length_le_closedTermBitUniversal
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermCode
      (‘!!left * !!right’ :
        LO.FirstOrder.ArithmeticSemiterm Nat arity)).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead Language.Mul.mul := by
  rw [arithmeticMulTerm_eq_func_tokenSliceUniversalTerm]
  exact binaryFunctionTerm_code_length_le_closedTermBitUniversal
    Language.Mul.mul left right

theorem tokenSliceClosedTermBitUniversalTerms_code_le
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm : ValuationTerm)
    (termCode : Nat)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termCode)
    (hwidthCode : (binaryTermCode widthTerm).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode) :
    let offsetTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
      Rew.bShift (&0 : ValuationTerm)
    let bitTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1 := #0
    let sourceShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
      Rew.bShift (Rew.shift sourceStartTerm)
    let targetShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
      Rew.bShift (Rew.shift targetStartTerm)
    let widthShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
      Rew.bShift (Rew.shift widthTerm)
    let tableShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
      Rew.bShift (Rew.shift tokenTableTerm)
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
    let termBound :=
      tokenSliceClosedTermBitUniversalBodyTermCodePolynomial termCode
    (binaryTermCode sourceIndex).length <= termBound ∧
      (binaryTermCode targetIndex).length <= termBound ∧
      (binaryTermCode tableShift).length <= termBound := by
  let offsetTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (&0 : ValuationTerm)
  let bitTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1 := #0
  let sourceShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift sourceStartTerm)
  let targetShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift targetStartTerm)
  let widthShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift widthTerm)
  let tableShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift tokenTableTerm)
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
  let termBound :=
    tokenSliceClosedTermBitUniversalBodyTermCodePolynomial termCode
  have htableShift1 := binaryTermCode_shift_length_le tokenTableTerm
  have hwidthShift1 := binaryTermCode_shift_length_le widthTerm
  have hsourceShift1 := binaryTermCode_shift_length_le sourceStartTerm
  have htargetShift1 := binaryTermCode_shift_length_le targetStartTerm
  have htableSymbols :=
    termSymbolCount_le_binaryTermCode_length (Rew.shift tokenTableTerm)
  have hwidthSymbols :=
    termSymbolCount_le_binaryTermCode_length (Rew.shift widthTerm)
  have hsourceSymbols :=
    termSymbolCount_le_binaryTermCode_length (Rew.shift sourceStartTerm)
  have htargetSymbols :=
    termSymbolCount_le_binaryTermCode_length (Rew.shift targetStartTerm)
  have htableShift2 := binaryTermCode_bShift_length_le_add_symbols
    (Rew.shift tokenTableTerm)
  have hwidthShift2 := binaryTermCode_bShift_length_le_add_symbols
    (Rew.shift widthTerm)
  have hsourceShift2 := binaryTermCode_bShift_length_le_add_symbols
    (Rew.shift sourceStartTerm)
  have htargetShift2 := binaryTermCode_bShift_length_le_add_symbols
    (Rew.shift targetStartTerm)
  have hoffsetSymbols :=
    termSymbolCount_le_binaryTermCode_length
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
  have hoffsetBound := binaryTermCode_bShift_length_le_add_symbols
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
  have hsourceSum :=
    arithmeticAddTerm_code_length_le_closedTermBitUniversal sourceShift
      offsetTerm
  have htargetSum :=
    arithmeticAddTerm_code_length_le_closedTermBitUniversal targetShift
      offsetTerm
  have hsourceProduct :=
    arithmeticMulTerm_code_length_le_closedTermBitUniversal sourceSum
      widthShift
  have htargetProduct :=
    arithmeticMulTerm_code_length_le_closedTermBitUniversal targetSum
      widthShift
  have hsourceIndex :=
    arithmeticAddTerm_code_length_le_closedTermBitUniversal sourceProduct
      bitTerm
  have htargetIndex :=
    arithmeticAddTerm_code_length_le_closedTermBitUniversal targetProduct
      bitTerm
  dsimp only [sourceIndex, targetIndex, sourceProduct, targetProduct,
    sourceSum, targetSum, sourceShift, targetShift, offsetTerm, widthShift,
    tableShift, bitTerm, termBound,
    tokenSliceClosedTermBitUniversalBodyTermCodePolynomial] at *
  omega

theorem tokenSliceAtValuationBitBody_code_length_le_closedFixed
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm : ValuationTerm)
    (termCode : Nat)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termCode)
    (hwidthCode : (binaryTermCode widthTerm).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode) :
    (binaryFormulaCode
      (tokenSliceAtValuationBitBody tokenTableTerm widthTerm sourceStartTerm
        targetStartTerm)).length <=
      tokenSliceClosedTermBitUniversalBodyCodePolynomial termCode := by
  let offsetTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (&0 : ValuationTerm)
  let bitTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1 := #0
  let sourceShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift sourceStartTerm)
  let targetShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift targetStartTerm)
  let widthShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift widthTerm)
  let tableShift : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift (Rew.shift tokenTableTerm)
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
  let termBound :=
    tokenSliceClosedTermBitUniversalBodyTermCodePolynomial termCode
  let sourceAtom := binaryBitAtomAtTerms sourceIndex tableShift
  let targetAtom := binaryBitAtomAtTerms targetIndex tableShift
  have hterms := tokenSliceClosedTermBitUniversalTerms_code_le tokenTableTerm
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
  have hbody :
      tokenSliceAtValuationBitBody tokenTableTerm widthTerm sourceStartTerm
        targetStartTerm = sourceAtom 🡘 targetAtom := by
    rfl
  rw [hbody]
  unfold tokenSliceClosedTermBitUniversalBodyCodePolynomial
  dsimp only [termBound] at hsource htarget
  omega

theorem
    tokenSliceAtValuationBitBranchesTransparentEnvelope_le_closedFixed
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm : ValuationTerm)
    (offset numericBound termCode bitBound : Nat)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (hsourceClosed : sourceStartTerm.freeVariables = ∅)
    (htargetClosed : targetStartTerm.freeVariables = ∅)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termCode)
    (hwidthCode : (binaryTermCode widthTerm).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode)
    (hwidth : termValue valuation widthTerm <= numericBound)
    (hsource : termValue valuation sourceStartTerm <= numericBound)
    (htarget : termValue valuation targetStartTerm <= numericBound)
    (hoffset : offset <= numericBound)
    (htableSize : Nat.size (termValue valuation tokenTableTerm) <= bitBound) :
    tokenSliceAtValuationBitBranchesTransparentEnvelope valuation
        tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset <=
      tokenSliceClosedTermBitBranchesFullyFixedPayloadPolynomial numericBound
        termCode bitBound := by
  let branchValuation := extendValuation offset valuation
  let body := tokenSliceAtValuationBitBody tokenTableTerm widthTerm
    sourceStartTerm targetStartTerm
  let boundTerm := Rew.shift widthTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue branchValuation boundTerm
  let leafBound :=
    tokenSliceClosedTermBitBranchPayloadSumFixedPolynomial numericBound
      termCode bitBound
  let exactCore :=
    hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
      branchValuation body
      (tokenSliceAtValuationBitBranchPayloadResourceSum valuation
        tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset)
      bound
  let fixedLeafCore :=
    hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
      branchValuation body leafBound bound
  let Gamma :=
    (valuationContext outerVariables branchValuation).image Rewriting.shift
  let contextualCore :=
    contextualHybridUniversalBranchesPayloadPolynomial Gamma bound bound body
      leafBound
  have hleaf :
      tokenSliceAtValuationBitBranchPayloadResourceSum valuation tokenTableTerm
          widthTerm sourceStartTerm targetStartTerm offset <= leafBound := by
    dsimp only [leafBound]
    exact tokenSliceAtValuationBitBranchPayloadResourceSum_le_closedFixed
      valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm
      offset numericBound termCode bitBound htableClosed hwidthClosed
      hsourceClosed htargetClosed htableCode hwidthCode hsourceCode htargetCode
      hwidth hsource htarget hoffset htableSize
  have hcore : exactCore <= fixedLeafCore := by
    dsimp only [exactCore, fixedLeafCore]
    exact
      hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf
        bound outerVariables branchValuation body hleaf bound
  have hbound : bound <= numericBound := by
    dsimp only [bound, branchValuation, boundTerm]
    simpa only [termValue_shift, extendValuation_succ] using hwidth
  have hboundClosed : boundTerm.freeVariables = ∅ :=
    shiftedTerm_freeVariables_eq_empty_of_closed widthTerm hwidthClosed
  have hsourceVars :
      (tokenSliceAtValuationBitAtom tokenTableTerm sourceStartTerm
        widthTerm).freeVariables ⊆ {0, 1} :=
    tokenSliceClosedTermBitAtom_freeVariables_subset tokenTableTerm widthTerm
      sourceStartTerm htableClosed hwidthClosed hsourceClosed
  have htargetVars :
      (tokenSliceAtValuationBitAtom tokenTableTerm targetStartTerm
        widthTerm).freeVariables ⊆ {0, 1} :=
    tokenSliceClosedTermBitAtom_freeVariables_subset tokenTableTerm widthTerm
      targetStartTerm htableClosed hwidthClosed htargetClosed
  have houter : outerVariables ⊆ {0} := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      tokenSliceAtValuationBitUniversalOuterVariables_subset_singleton_of_atoms
        tokenTableTerm widthTerm sourceStartTerm targetStartTerm boundTerm
        (by rw [hboundClosed]; simp) hsourceVars htargetVars
  have houterCard : outerVariables.card <= 1 :=
    (Finset.card_le_card houter).trans (by simp)
  have hGammaCard : Gamma.card <= 1 := by
    dsimp only [Gamma]
    have hcontext :
        (valuationContext outerVariables branchValuation).card <=
          outerVariables.card := by
      unfold valuationContext
      exact Finset.card_image_le
    exact Finset.card_image_le.trans (hcontext.trans houterCard)
  have hcontextual : fixedLeafCore <= contextualCore := by
    dsimp only [fixedLeafCore, contextualCore]
    exact
      hybridBranchesUniformStructuralPayloadEnvelope_le_contextualPolynomial
        bound outerVariables branchValuation body leafBound hGammaCard
        (caseCount := bound) le_rfl
  have hbody :
      (binaryFormulaCode body).length <=
        tokenSliceClosedTermBitUniversalBodyCodePolynomial termCode := by
    dsimp only [body]
    exact tokenSliceAtValuationBitBody_code_length_le_closedFixed
      tokenTableTerm widthTerm sourceStartTerm targetStartTerm termCode
      htableCode hwidthCode hsourceCode htargetCode
  have hsyntax :
      explicitHybridUniversalSyntaxResource bound body <=
        tokenSliceClosedTermBitUniversalSyntaxFixedPolynomial numericBound
          termCode := by
    unfold explicitHybridUniversalSyntaxResource
      tokenSliceClosedTermBitUniversalSyntaxFixedPolynomial
    exact Nat.add_le_add hbound hbody
  have hformula :
      explicitHybridUniversalFormulaEnvelope bound body <=
        tokenSliceClosedTermBitUniversalFormulaFixedPolynomial numericBound
          termCode := by
    have hclosed :=
      boundedUniversalClosedFormulaEnvelope_mono_completed hsyntax
    unfold explicitHybridUniversalFormulaEnvelope
      tokenSliceClosedTermBitUniversalFormulaFixedPolynomial
    exact Nat.add_le_add hclosed (Nat.mul_le_mul_left 2 hbody)
  have houterValues : forall index, index ∈ outerVariables ->
      branchValuation index <= numericBound := by
    intro index hindex
    have hsmall := houter hindex
    simp only [Finset.mem_singleton] at hsmall
    subst index
    dsimp only [branchValuation]
    simpa only [extendValuation_zero] using hoffset
  have houterVariableCodes : forall index, index ∈ outerVariables ->
      (binaryTermCode (&index : ValuationTerm)).length <=
        tokenSliceBitBranchVariableCodeCeiling := by
    intro index hindex
    have hsmall := houter hindex
    simp only [Finset.mem_singleton] at hsmall
    subst index
    unfold tokenSliceBitBranchVariableCodeCeiling
    omega
  have hGammaCode :
      contextualHybridUniversalFormulaCodeSum Gamma <=
        2 * valuationContextFormulaCodeSumEnvelope 1 numericBound
          tokenSliceBitBranchVariableCodeCeiling := by
    dsimp only [Gamma]
    exact shiftedValuationContext_formulaCodeSum_le_uniform outerVariables
      branchValuation 1 numericBound tokenSliceBitBranchVariableCodeCeiling
      houterCard houterValues houterVariableCodes
  have hcontextFormula :
      contextualHybridUniversalFormulaEnvelope Gamma bound body <=
        tokenSliceClosedTermBitUniversalContextFormulaFixedPolynomial
          numericBound termCode := by
    unfold contextualHybridUniversalFormulaEnvelope
      tokenSliceClosedTermBitUniversalContextFormulaFixedPolynomial
    exact Nat.add_le_add hformula hGammaCode
  have hlocal :
      contextualHybridUniversalLocalPayloadEnvelope Gamma bound body <=
        tokenSliceClosedTermBitUniversalLocalPayloadFixedPolynomial
          numericBound termCode := by
    unfold tokenSliceClosedTermBitUniversalLocalPayloadFixedPolynomial
    exact smallContextAssemblyEnvelope_mono_local hcontextFormula
  have hfixed :
      contextualCore <=
        tokenSliceClosedTermBitBranchesFullyFixedPayloadPolynomial numericBound
          termCode bitBound := by
    unfold contextualCore contextualHybridUniversalBranchesPayloadPolynomial
      tokenSliceClosedTermBitBranchesFullyFixedPayloadPolynomial
    exact Nat.mul_le_mul (by omega) (Nat.add_le_add le_rfl
      (Nat.mul_le_mul_left 3 hlocal))
  have htransparent :
      tokenSliceAtValuationBitBranchesTransparentEnvelope valuation
          tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset =
        exactCore := by
    unfold tokenSliceAtValuationBitBranchesTransparentEnvelope
    rfl
  rw [htransparent]
  exact hcore.trans (hcontextual.trans hfixed)

def tokenSliceClosedTermBitContextualBranchesFullyFixedPayloadPolynomial
    (numericBound termCode bitBound : Nat) : Nat :=
  contextualBranchesFixedAssemblyEnvelope
    (tokenSliceClosedTermBitUniversalSyntaxFixedPolynomial numericBound
      termCode)
    (tokenSliceClosedTermBitUniversalContextFormulaFixedPolynomial
      numericBound termCode)
    (tokenSliceClosedTermBitBranchesFullyFixedPayloadPolynomial numericBound
      termCode bitBound)

theorem
    tokenSliceAtValuationBitContextualBranchesResource_le_closedFixed
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm : ValuationTerm)
    (offset numericBound termCode bitBound : Nat)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (hsourceClosed : sourceStartTerm.freeVariables = ∅)
    (htargetClosed : targetStartTerm.freeVariables = ∅)
    (htableCode : (binaryTermCode tokenTableTerm).length <= termCode)
    (hwidthCode : (binaryTermCode widthTerm).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode)
    (hwidth : termValue valuation widthTerm <= numericBound)
    (hsource : termValue valuation sourceStartTerm <= numericBound)
    (htarget : termValue valuation targetStartTerm <= numericBound)
    (hoffset : offset <= numericBound)
    (htableSize : Nat.size (termValue valuation tokenTableTerm) <= bitBound) :
    let branchValuation := extendValuation offset valuation
    let body := tokenSliceAtValuationBitBody tokenTableTerm widthTerm
      sourceStartTerm targetStartTerm
    let boundTerm := Rew.shift widthTerm
    let outerFormula := ∀⁰ termBoundedUniversalBody
      (Rew.bShift boundTerm) body
    let outerVariables := outerFormula.freeVariables
    let Gamma :=
      (valuationContext outerVariables branchValuation).image
        Rewriting.shift
    contextualBranchesUnderBoundPayloadEnvelope Gamma
        (termValue valuation widthTerm) (Rewriting.free body)
        (tokenSliceAtValuationBitBranchesTransparentEnvelope valuation
          tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset) <=
      tokenSliceClosedTermBitContextualBranchesFullyFixedPayloadPolynomial
        numericBound termCode bitBound := by
  let branchValuation := extendValuation offset valuation
  let body := tokenSliceAtValuationBitBody tokenTableTerm widthTerm
    sourceStartTerm targetStartTerm
  let boundTerm := Rew.shift widthTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma :=
    (valuationContext outerVariables branchValuation).image Rewriting.shift
  let targetFormula := Rewriting.free body
  let caseResource :=
    tokenSliceAtValuationBitBranchesTransparentEnvelope valuation
      tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset
  let syntaxCode :=
    tokenSliceClosedTermBitUniversalSyntaxFixedPolynomial numericBound
      termCode
  let formulaCode :=
    tokenSliceClosedTermBitUniversalContextFormulaFixedPolynomial numericBound
      termCode
  let caseBound :=
    tokenSliceClosedTermBitBranchesFullyFixedPayloadPolynomial numericBound
      termCode bitBound
  have hboundClosed : boundTerm.freeVariables = ∅ :=
    shiftedTerm_freeVariables_eq_empty_of_closed widthTerm hwidthClosed
  have hsourceVars :
      (tokenSliceAtValuationBitAtom tokenTableTerm sourceStartTerm
        widthTerm).freeVariables ⊆ {0, 1} :=
    tokenSliceClosedTermBitAtom_freeVariables_subset tokenTableTerm widthTerm
      sourceStartTerm htableClosed hwidthClosed hsourceClosed
  have htargetVars :
      (tokenSliceAtValuationBitAtom tokenTableTerm targetStartTerm
        widthTerm).freeVariables ⊆ {0, 1} :=
    tokenSliceClosedTermBitAtom_freeVariables_subset tokenTableTerm widthTerm
      targetStartTerm htableClosed hwidthClosed htargetClosed
  have houter : outerVariables ⊆ {0} := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      tokenSliceAtValuationBitUniversalOuterVariables_subset_singleton_of_atoms
        tokenTableTerm widthTerm sourceStartTerm targetStartTerm boundTerm
        (by rw [hboundClosed]; simp) hsourceVars htargetVars
  have houterCard : outerVariables.card <= 1 :=
    (Finset.card_le_card houter).trans (by simp)
  have houterValues : forall index, index ∈ outerVariables ->
      branchValuation index <= numericBound := by
    intro index hindex
    have hsmall := houter hindex
    simp only [Finset.mem_singleton] at hsmall
    subst index
    dsimp only [branchValuation]
    simpa only [extendValuation_zero] using hoffset
  have houterVariableCodes : forall index, index ∈ outerVariables ->
      (binaryTermCode (&index : ValuationTerm)).length <=
        tokenSliceBitBranchVariableCodeCeiling := by
    intro index hindex
    have hsmall := houter hindex
    simp only [Finset.mem_singleton] at hsmall
    subst index
    unfold tokenSliceBitBranchVariableCodeCeiling
    omega
  have hGammaCode :
      contextualHybridUniversalFormulaCodeSum Gamma <=
        2 * valuationContextFormulaCodeSumEnvelope 1 numericBound
          tokenSliceBitBranchVariableCodeCeiling := by
    dsimp only [Gamma]
    exact shiftedValuationContext_formulaCodeSum_le_uniform outerVariables
      branchValuation 1 numericBound tokenSliceBitBranchVariableCodeCeiling
      houterCard houterValues houterVariableCodes
  have hGammaCard : Gamma.card <= 1 := by
    dsimp only [Gamma]
    have hcontext :
        (valuationContext outerVariables branchValuation).card <=
          outerVariables.card := by
      unfold valuationContext
      exact Finset.card_image_le
    exact Finset.card_image_le.trans (hcontext.trans houterCard)
  have hGammaBound : FormulaCodeBound Gamma formulaCode := by
    intro formula hformula
    have hsingle :=
      formulaCode_le_contextualHybridUniversalFormulaCodeSum hformula
    exact hsingle.trans (hGammaCode.trans (by
      dsimp only [formulaCode]
      unfold
        tokenSliceClosedTermBitUniversalContextFormulaFixedPolynomial
      omega))
  have hbody :
      (binaryFormulaCode body).length <=
        tokenSliceClosedTermBitUniversalBodyCodePolynomial termCode := by
    dsimp only [body]
    exact tokenSliceAtValuationBitBody_code_length_le_closedFixed
      tokenTableTerm widthTerm sourceStartTerm targetStartTerm termCode
      htableCode hwidthCode hsourceCode htargetCode
  have hboundSyntax :
      termValue valuation widthTerm <= syntaxCode := by
    dsimp only [syntaxCode]
    unfold tokenSliceClosedTermBitUniversalSyntaxFixedPolynomial
    omega
  have hclosedLe :
      boundedUniversalClosedFormulaEnvelope syntaxCode <= formulaCode := by
    dsimp only [syntaxCode, formulaCode]
    unfold tokenSliceClosedTermBitUniversalContextFormulaFixedPolynomial
      tokenSliceClosedTermBitUniversalFormulaFixedPolynomial
    omega
  have htargetFormulaCode :
      (binaryFormulaCode targetFormula).length <= formulaCode := by
    have hfree := binaryFormulaCode_free_length_le body
    dsimp only [targetFormula, formulaCode]
    unfold tokenSliceClosedTermBitUniversalContextFormulaFixedPolynomial
      tokenSliceClosedTermBitUniversalFormulaFixedPolynomial
    omega
  have hcase : caseResource <= caseBound := by
    dsimp only [caseResource, caseBound]
    exact
      tokenSliceAtValuationBitBranchesTransparentEnvelope_le_closedFixed
        valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm
        offset numericBound termCode bitBound htableClosed hwidthClosed
        hsourceClosed htargetClosed htableCode hwidthCode hsourceCode
        htargetCode hwidth hsource htarget hoffset htableSize
  have hassembled :=
    contextualBranchesUnderBoundPayloadEnvelope_le_fixedAssembly Gamma
      (termValue valuation widthTerm) syntaxCode formulaCode caseResource
      caseBound targetFormula hboundSyntax hclosedLe htargetFormulaCode
      hGammaCard hGammaBound hcase
  unfold tokenSliceClosedTermBitContextualBranchesFullyFixedPayloadPolynomial
  simpa only [branchValuation, body, boundTerm, outerFormula, outerVariables,
    Gamma, targetFormula, caseResource, syntaxCode, formulaCode, caseBound]
    using hassembled

/-
The final short-width universal endpoint lives in
`FoundationCompactNumericListedDirectTokenSliceBitClosedTermUniversalEndpointFixedBounds`.
The block is retained here temporarily while the endpoint is split out.

def tokenSliceClosedTermBitUniversalShellBodyCodePolynomial
    (numericBound termCode : Nat) : Nat :=
  tokenSliceClosedTermBitUniversalBodyCodePolynomial termCode +
    valuationContextFormulaCodeSumEnvelope 1 numericBound
      tokenSliceBitBranchVariableCodeCeiling + 1

def tokenSliceClosedTermBitShiftedBoundFixedScalePolynomial
    (numericBound termCode : Nat) : Nat :=
  numericBound + 4 * termCode + 1

def tokenSliceClosedTermBitUniversalFullyFixedPayloadPolynomial
    (numericBound termCode bitBound : Nat) : Nat :=
  closedShortUniversalShellFixedPayloadPolynomial numericBound bitBound
    (tokenSliceClosedTermBitUniversalSyntaxFixedPolynomial numericBound
      termCode)
    (tokenSliceClosedTermBitUniversalShellBodyCodePolynomial numericBound
      termCode)
    (tokenSliceClosedTermBitContextualBranchesFullyFixedPayloadPolynomial
      numericBound termCode bitBound)
    (compileShiftedBoundEqualityFixedPayloadPolynomial
      (tokenSliceClosedTermBitShiftedBoundFixedScalePolynomial numericBound
        termCode))

theorem
    tokenSliceAtValuationBitUniversalPayloadEnvelope_le_closedFixed
    (valuation : Nat -> Nat)
    (tokenTable width offset numericBound termCode bitBound : Nat)
    (sourceStartTerm targetStartTerm : ValuationTerm)
    (hsourceClosed : sourceStartTerm.freeVariables = ∅)
    (htargetClosed : targetStartTerm.freeVariables = ∅)
    (htableCode :
      (binaryTermCode (shortBinaryNumeralTerm tokenTable)).length <= termCode)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termCode)
    (hsourceCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (htargetCode : (binaryTermCode targetStartTerm).length <= termCode)
    (hwidth : width <= numericBound)
    (hsource : termValue valuation sourceStartTerm <= numericBound)
    (htarget : termValue valuation targetStartTerm <= numericBound)
    (hoffset : offset <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound) :
    tokenSliceAtValuationBitUniversalPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        sourceStartTerm targetStartTerm offset <=
      tokenSliceClosedTermBitUniversalFullyFixedPayloadPolynomial numericBound
        termCode bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let branchValuation := extendValuation offset valuation
  let body := tokenSliceAtValuationBitBody tableTerm widthTerm sourceStartTerm
    targetStartTerm
  let boundTerm := Rew.shift widthTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables branchValuation
  let boundResource := compileShiftedBoundEqualityPayloadResource
    branchValuation outerVariables boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) width (Rewriting.free body)
    (tokenSliceAtValuationBitBranchesTransparentEnvelope valuation tableTerm
      widthTerm sourceStartTerm targetStartTerm offset)
  let syntaxCode :=
    tokenSliceClosedTermBitUniversalSyntaxFixedPolynomial numericBound
      termCode
  let bodyCode :=
    tokenSliceClosedTermBitUniversalShellBodyCodePolynomial numericBound
      termCode
  let branchBound :=
    tokenSliceClosedTermBitContextualBranchesFullyFixedPayloadPolynomial
      numericBound termCode bitBound
  let scale :=
    tokenSliceClosedTermBitShiftedBoundFixedScalePolynomial numericBound
      termCode
  let boundEqualityBound :=
    compileShiftedBoundEqualityFixedPayloadPolynomial scale
  trace "CLOSED-BIT-UNIVERSAL MARK 1: local definitions"
  have htableClosed : tableTerm.freeVariables = ∅ := by
    dsimp only [tableTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  have hwidthClosed : widthTerm.freeVariables = ∅ := by
    dsimp only [widthTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  have hboundClosed : boundTerm.freeVariables = ∅ :=
    shiftedTerm_freeVariables_eq_empty_of_closed widthTerm hwidthClosed
  have hsourceVars :
      (tokenSliceAtValuationBitAtom tableTerm sourceStartTerm
        widthTerm).freeVariables ⊆ {0, 1} :=
    tokenSliceClosedTermBitAtom_freeVariables_subset tableTerm widthTerm
      sourceStartTerm htableClosed hwidthClosed hsourceClosed
  have htargetVars :
      (tokenSliceAtValuationBitAtom tableTerm targetStartTerm
        widthTerm).freeVariables ⊆ {0, 1} :=
    tokenSliceClosedTermBitAtom_freeVariables_subset tableTerm widthTerm
      targetStartTerm htableClosed hwidthClosed htargetClosed
  have houter : outerVariables ⊆ {0} := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      tokenSliceAtValuationBitUniversalOuterVariables_subset_singleton_of_atoms
        tableTerm widthTerm sourceStartTerm targetStartTerm boundTerm
        (by rw [hboundClosed]; simp) hsourceVars htargetVars
  trace "CLOSED-BIT-UNIVERSAL MARK 2: free variables"
  have houterCard : outerVariables.card <= 1 :=
    (Finset.card_le_card houter).trans (by simp)
  have houterValues : forall index, index ∈ outerVariables ->
      branchValuation index <= numericBound := by
    intro index hindex
    have hsmall := houter hindex
    simp only [Finset.mem_singleton] at hsmall
    subst index
    dsimp only [branchValuation]
    simpa only [extendValuation_zero] using hoffset
  have houterVariableCodes : forall index, index ∈ outerVariables ->
      (binaryTermCode (&index : ValuationTerm)).length <=
        tokenSliceBitBranchVariableCodeCeiling := by
    intro index hindex
    have hsmall := houter hindex
    simp only [Finset.mem_singleton] at hsmall
    subst index
    unfold tokenSliceBitBranchVariableCodeCeiling
    omega
  have hGammaSum :
      formulaCodeSum Gamma <=
        valuationContextFormulaCodeSumEnvelope 1 numericBound
          tokenSliceBitBranchVariableCodeCeiling := by
    dsimp only [Gamma]
    exact valuationContext_formulaCodeSum_le_uniform outerVariables
      branchValuation 1 numericBound tokenSliceBitBranchVariableCodeCeiling
      houterCard houterValues houterVariableCodes
  have hGammaCard : Gamma.card <= 1 := by
    dsimp only [Gamma]
    exact Finset.card_image_le.trans houterCard
  have hshiftedGammaSum :
      contextualHybridUniversalFormulaCodeSum
          (Gamma.image Rewriting.shift) <=
        2 * valuationContextFormulaCodeSumEnvelope 1 numericBound
          tokenSliceBitBranchVariableCodeCeiling := by
    dsimp only [Gamma]
    exact shiftedValuationContext_formulaCodeSum_le_uniform outerVariables
      branchValuation 1 numericBound tokenSliceBitBranchVariableCodeCeiling
      houterCard houterValues houterVariableCodes
  trace "CLOSED-BIT-UNIVERSAL MARK 3: valuation context"
  have hbody :
      (binaryFormulaCode body).length <=
        tokenSliceClosedTermBitUniversalBodyCodePolynomial termCode := by
    dsimp only [body, tableTerm, widthTerm]
    exact tokenSliceAtValuationBitBody_code_length_le_closedFixed
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      sourceStartTerm targetStartTerm termCode htableCode hwidthCode
      hsourceCode htargetCode
  have hbodyShell : (binaryFormulaCode body).length <= bodyCode := by
    dsimp only [bodyCode]
    unfold tokenSliceClosedTermBitUniversalShellBodyCodePolynomial
    omega
  have hcontextSource :
      valuationContextFormulaCodeSumEnvelope 1 numericBound
          tokenSliceBitBranchVariableCodeCeiling <=
        closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
          syntaxCode bodyCode := by
    dsimp only [syntaxCode, bodyCode]
    unfold tokenSliceClosedTermBitUniversalShellBodyCodePolynomial
      closedShortUniversalShellSourceFormulaPolynomial
      closedShortUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have hshiftedContextFormula :
      2 * valuationContextFormulaCodeSumEnvelope 1 numericBound
          tokenSliceBitBranchVariableCodeCeiling <=
        closedShortUniversalShellFormulaPolynomial numericBound bitBound
          syntaxCode bodyCode := by
    have hraw := hcontextSource
    dsimp only [syntaxCode, bodyCode] at hraw ⊢
    unfold tokenSliceClosedTermBitUniversalShellBodyCodePolynomial
      closedShortUniversalShellSourceFormulaPolynomial
      closedShortUniversalShellRawFormulaPolynomial at hraw
    unfold tokenSliceClosedTermBitUniversalShellBodyCodePolynomial
      closedShortUniversalShellFormulaPolynomial
      closedShortUniversalShellSourceFormulaPolynomial
      closedShortUniversalShellRawFormulaPolynomial
    dsimp only at hraw ⊢
    omega
  have hGammaSource : FormulaCodeBound Gamma
      (closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
        syntaxCode bodyCode) := by
    intro formula hformula
    have hmember :=
      FoundationCompactPAValuationTermCompilerPublicBounds.formulaCode_le_formulaCodeSum
        hformula
    exact hmember.trans (hGammaSum.trans hcontextSource)
  have hshiftedFormula : FormulaCodeBound (Gamma.image Rewriting.shift)
      (closedShortUniversalShellFormulaPolynomial numericBound bitBound
        syntaxCode bodyCode) := by
    intro formula hformula
    have hmember :=
      formulaCode_le_contextualHybridUniversalFormulaCodeSum hformula
    exact hmember.trans
      (hshiftedGammaSum.trans hshiftedContextFormula)
  trace "CLOSED-BIT-UNIVERSAL MARK 4: body and formula code"
  have hboundResource : boundResource <= boundEqualityBound := by
    have hpublic :=
      compileShiftedBoundEqualityPayloadResource_le_publicPolynomial
        branchValuation outerVariables boundTerm hboundClosed
    have hboundCodeRaw := binaryTermCode_shift_length_le widthTerm
    have hboundCode : (binaryTermCode boundTerm).length <= scale := by
      dsimp only [boundTerm, widthTerm, scale]
      unfold tokenSliceClosedTermBitShiftedBoundFixedScalePolynomial
      omega
    have hfixed :=
      compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq_of_values
        branchValuation outerVariables boundTerm
        (compileShiftedBoundEqualityPayloadPublicPolynomial branchValuation
          outerVariables boundTerm)
        (compileShiftedBoundEqualityFixedPayloadPolynomial scale)
        scale rfl rfl hboundClosed houter
        (by
          intro index hindex
          have hsmall := houter hindex
          simp only [Finset.mem_singleton] at hsmall
          subst index
          dsimp only [branchValuation, scale]
          simp only [extendValuation_zero]
          unfold tokenSliceClosedTermBitShiftedBoundFixedScalePolynomial
          omega)
        (by
          dsimp only [branchValuation, boundTerm, widthTerm, scale]
          simp only [termValue_shift, termValue_shortBinaryNumeralTerm]
          unfold tokenSliceClosedTermBitShiftedBoundFixedScalePolynomial
          omega)
        hboundCode
    exact hpublic.trans hfixed
  trace "CLOSED-BIT-UNIVERSAL MARK 5: shifted bound"
  have hbranchResource : branchResource <= branchBound := by
    dsimp only [branchResource, branchBound, tableTerm, widthTerm,
      branchValuation, body, boundTerm, outerFormula, outerVariables, Gamma]
    exact
      tokenSliceAtValuationBitContextualBranchesResource_le_closedFixed
        valuation (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width) sourceStartTerm targetStartTerm offset
        numericBound termCode bitBound htableClosed hwidthClosed hsourceClosed
        htargetClosed htableCode hwidthCode hsourceCode htargetCode
        (by simpa only [termValue_shortBinaryNumeralTerm] using hwidth)
        hsource htarget hoffset
        (by simpa only [termValue_shortBinaryNumeralTerm] using htableSize)
  trace "CLOSED-BIT-UNIVERSAL MARK 6: contextual branches"
  have hshell :=
    compileContextualTermBoundedUniversalPayloadEnvelope_short_le_fixed_of_context
      body Gamma width numericBound bitBound syntaxCode bodyCode boundResource
      branchResource boundEqualityBound branchBound hwidth hwidthSize
      (by
        dsimp only [syntaxCode]
        unfold tokenSliceClosedTermBitUniversalSyntaxFixedPolynomial
        omega)
      hbodyShell hboundResource hbranchResource hGammaCard hGammaSource
      hshiftedFormula
  trace "CLOSED-BIT-UNIVERSAL MARK 7: universal shell"
  unfold tokenSliceAtValuationBitUniversalPayloadEnvelope
  simp only [termValue_shift, termValue_shortBinaryNumeralTerm]
  rw [show Rew.shift (shortBinaryNumeralTerm width) =
      shortBinaryNumeralTerm width by simp]
  unfold tokenSliceClosedTermBitUniversalFullyFixedPayloadPolynomial
  simpa only [tableTerm, widthTerm, branchValuation, body, boundTerm,
    outerFormula, outerVariables, Gamma, boundResource, branchResource,
    syntaxCode, bodyCode, branchBound, scale, boundEqualityBound] using hshell

-/

#print axioms tokenSliceAtValuationBitBody_code_length_le_closedFixed
#print axioms
  tokenSliceAtValuationBitBranchesTransparentEnvelope_le_closedFixed
#print axioms
  tokenSliceAtValuationBitContextualBranchesResource_le_closedFixed

end FoundationCompactNumericListedDirectTokenSliceBitClosedTermUniversalFullyFixedBounds
