import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds

/-!
# Fixed bounds for the open-index bounded universal

This layer first removes the concrete formula body and shifted valuation
context from the branch ledger.  It then bounds the complete contextual
bounded-universal assembly by the same scalar used for the surrounding
fixed-width entry.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABitMembershipTraceBudgetBounds
open FoundationCompactPABitMembershipValuationCompilerPublicBounds
open FoundationCompactPABitMembershipValuationTransportPolynomialBounds
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAExponentialShortNumeralCompilerBounds
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerLeafPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexScalarBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerFixedPolynomialBounds
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationTermCompilerUniformMonotoneBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds

private theorem binaryAddTerm_code_length_le_openIndexUniversal
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermCode
      (LO.FirstOrder.Semiterm.func Language.ORing.Func.add
        ![left, right])).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead Language.ORing.Func.add := by
  simp [binaryTermCode, binaryFunctionTermCodeOverhead,
    Matrix.fun_eq_vec_two]
  omega

def fixedWidthOpenIndexBitAtomCodePolynomial (termBound : Nat) : Nat :=
  uniformRewritingFormulaFactor (termBound + 4) (termBound + 1)
      (formulaSymbolCount binaryBitEmbeddedFormula) *
    (binaryFormulaCode binaryBitEmbeddedFormula).length

private theorem binaryBitAtomAtTerms_code_length_le_openIndexUniversal
    {arity : Nat}
    (index value : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (termBound : Nat)
    (hindex : (binaryTermCode index).length <= termBound)
    (hvalue : (binaryTermCode value).length <= termBound) :
    (binaryFormulaCode (binaryBitAtomAtTerms index value)).length <=
      fixedWidthOpenIndexBitAtomCodePolynomial termBound := by
  let rewriting : Rew ℒₒᵣ Nat 2 Nat arity := Rew.subst ![index, value]
  have hindexSymbols : termSymbolCount index <= termBound :=
    (termSymbolCount_le_binaryTermCode_length index).trans hindex
  have hvalueSymbols : termSymbolCount value <= termBound :=
    (termSymbolCount_le_binaryTermCode_length value).trans hvalue
  have hbound : UniformRewritingImageBound rewriting (termBound + 4)
      (termBound + 1) := by
    constructor
    · intro coordinate
      cases coordinate using Fin.cases with
      | zero =>
          simp [rewriting, Rew.subst_bvar]
          omega
      | succ coordinate =>
          cases coordinate using Fin.cases with
          | zero =>
              simp [rewriting, Rew.subst_bvar]
              omega
          | succ coordinate => exact Fin.elim0 coordinate
    · constructor
      · intro coordinate
        cases coordinate using Fin.cases with
        | zero =>
            simp [rewriting, Rew.subst_bvar]
            omega
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero =>
                simp [rewriting, Rew.subst_bvar]
                omega
            | succ coordinate => exact Fin.elim0 coordinate
      · exact fun freeIndex => by
          change (Rew.subst ![index, value])
            (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat 2) =
              (&freeIndex : LO.FirstOrder.ArithmeticSemiterm Nat arity)
          exact Rew.subst_fvar ![index, value] freeIndex
  have hraw := binaryFormulaCode_rewriting_length_le_factor
    binaryBitEmbeddedFormula rewriting (by omega) (by omega) hbound
  have hatomEq : binaryBitAtomAtTerms index value =
      rewriting ▹ binaryBitEmbeddedFormula := by
    unfold binaryBitAtomAtTerms binaryBitEmbeddedFormula
    rfl
  rw [hatomEq]
  unfold fixedWidthOpenIndexBitAtomCodePolynomial
  exact hraw

/-- Common code bound for the four terms occurring in the fixed-width bit
equivalence before its bounded universal is closed. -/
def fixedWidthOpenIndexUniversalBodyTermCodePolynomial (scale : Nat) : Nat :=
  8 * scale +
    3 * binaryFunctionTermCodeOverhead Language.Mul.mul +
    binaryFunctionTermCodeOverhead Language.ORing.Func.add +
    (binaryTermCode (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length + 1

/-- Code bound for the complete fixed-width bit equivalence. -/
def fixedWidthOpenIndexUniversalBodyCodePolynomial (scale : Nat) : Nat :=
  64 * (fixedWidthOpenIndexBitAtomCodePolynomial
    (fixedWidthOpenIndexUniversalBodyTermCodePolynomial scale) + 1)

theorem fixedWidthBitBody_code_le_fixed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (scale : Nat)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale) :
    (binaryFormulaCode
      (fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm)).length <=
        fixedWidthOpenIndexUniversalBodyCodePolynomial scale := by
  let indexWidth := fixedWidthIndexWidthTerm widthTerm indexTerm
  let leftIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    .func .add ![Rew.bShift indexWidth, #0]
  let leftValue : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift tableTerm
  let rightIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 := #0
  let rightValue : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift valueTerm
  let termBound := fixedWidthOpenIndexUniversalBodyTermCodePolynomial scale
  let leftAtom := binaryBitAtomAtTerms leftIndex leftValue
  let rightAtom := binaryBitAtomAtTerms rightIndex rightValue
  have htableCode : (binaryTermCode tableTerm).length <= scale := by
    have hraw : (binaryTermCode tableTerm).length <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      unfold fixedWidthOpenIndexAtomicCoordinateScale
      omega
    exact hraw.trans hscale
  have hwidthCode : (binaryTermCode widthTerm).length <= scale := by
    have hraw : (binaryTermCode widthTerm).length <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      unfold fixedWidthOpenIndexAtomicCoordinateScale
      omega
    exact hraw.trans hscale
  have hindexCode : (binaryTermCode indexTerm).length <= scale := by
    have hraw : (binaryTermCode indexTerm).length <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      unfold fixedWidthOpenIndexAtomicCoordinateScale
      omega
    exact hraw.trans hscale
  have hvalueCode : (binaryTermCode valueTerm).length <= scale := by
    have hraw : (binaryTermCode valueTerm).length <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      unfold fixedWidthOpenIndexAtomicCoordinateScale
      omega
    exact hraw.trans hscale
  have hindexWidthRaw := paMulTerm_code_length_le indexTerm widthTerm
  have hindexWidth : (binaryTermCode indexWidth).length <=
      2 * scale + binaryFunctionTermCodeOverhead Language.Mul.mul := by
    dsimp only [indexWidth, fixedWidthIndexWidthTerm]
    omega
  have hindexWidthSymbols := termSymbolCount_le_binaryTermCode_length indexWidth
  have hshiftIndexWidthRaw := binaryTermCode_bShift_length_le_add_symbols
    indexWidth
  have hshiftIndexWidth : (binaryTermCode (Rew.bShift indexWidth)).length <=
      3 * (2 * scale +
        binaryFunctionTermCodeOverhead Language.Mul.mul) := by
    omega
  have hleftIndexRaw : (binaryTermCode leftIndex).length <=
      (binaryTermCode (Rew.bShift indexWidth)).length +
        (binaryTermCode
          (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length +
        binaryFunctionTermCodeOverhead Language.ORing.Func.add := by
    dsimp only [leftIndex]
    exact binaryAddTerm_code_length_le_openIndexUniversal
      (Rew.bShift indexWidth)
        (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)
  have hleftIndex : (binaryTermCode leftIndex).length <= termBound := by
    dsimp only [termBound]
    unfold fixedWidthOpenIndexUniversalBodyTermCodePolynomial
    omega
  have hleftValueRaw := binaryTermCode_bShift_length_le_add_symbols tableTerm
  have htableSymbols := termSymbolCount_le_binaryTermCode_length tableTerm
  have hleftValue : (binaryTermCode leftValue).length <= termBound := by
    dsimp only [leftValue, termBound]
    unfold fixedWidthOpenIndexUniversalBodyTermCodePolynomial
    omega
  have hrightIndex : (binaryTermCode rightIndex).length <= termBound := by
    dsimp only [rightIndex, termBound]
    unfold fixedWidthOpenIndexUniversalBodyTermCodePolynomial
    omega
  have hrightValueRaw := binaryTermCode_bShift_length_le_add_symbols valueTerm
  have hvalueSymbols := termSymbolCount_le_binaryTermCode_length valueTerm
  have hrightValue : (binaryTermCode rightValue).length <= termBound := by
    dsimp only [rightValue, termBound]
    unfold fixedWidthOpenIndexUniversalBodyTermCodePolynomial
    omega
  have hleftAtom : (binaryFormulaCode leftAtom).length <=
      fixedWidthOpenIndexBitAtomCodePolynomial termBound := by
    exact binaryBitAtomAtTerms_code_length_le_openIndexUniversal leftIndex
      leftValue termBound hleftIndex hleftValue
  have hrightAtom : (binaryFormulaCode rightAtom).length <=
      fixedWidthOpenIndexBitAtomCodePolynomial termBound := by
    exact binaryBitAtomAtTerms_code_length_le_openIndexUniversal rightIndex
      rightValue termBound hrightIndex hrightValue
  have hnegLeft := binaryFormulaCode_neg_length_le leftAtom
  have hnegRight := binaryFormulaCode_neg_length_le rightAtom
  change (binaryFormulaCode (LO.FirstOrder.Semiformula.neg leftAtom)).length <=
    2 * (binaryFormulaCode leftAtom).length at hnegLeft
  change (binaryFormulaCode (LO.FirstOrder.Semiformula.neg rightAtom)).length <=
    2 * (binaryFormulaCode rightAtom).length at hnegRight
  have htagFour : (binaryNatCode 4).length <= 8 := by decide
  have htagFive : (binaryNatCode 5).length <= 8 := by decide
  unfold fixedWidthBitBody
  change (binaryFormulaCode (leftAtom 🡘 rightAtom)).length <= _
  simp only [binaryFormulaCode, List.length_append]
  unfold fixedWidthOpenIndexUniversalBodyCodePolynomial
  dsimp only [termBound] at hleftAtom hrightAtom
  omega

private theorem finiteCaseFormulaEnvelope_mono_openIndexUniversal
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    {small large : Nat} (hbound : small <= large) :
    finiteCaseFormulaEnvelope subject small <=
      finiteCaseFormulaEnvelope subject large := by
  have hshift : small + 2 <= large + 2 := by omega
  have hequality := finiteEqualityCasesCodePolynomial_mono subject hshift
  have hlower := finiteLowerBoundFormulaCodePolynomial_mono subject hshift
  have hexhaustion := finiteExhaustionFormulaCodePolynomial_mono subject hshift
  have hsteps : (small + 3) * finiteEqualityCaseStepEnvelope subject <=
      (large + 3) * finiteEqualityCaseStepEnvelope subject :=
    Nat.mul_le_mul_right _ (by omega)
  unfold finiteCaseFormulaEnvelope
  omega

private theorem boundedUniversalClosedFormulaEnvelope_mono_openIndexUniversal
    {small large : Nat} (hbound : small <= large) :
    boundedUniversalClosedFormulaEnvelope small <=
      boundedUniversalClosedFormulaEnvelope large := by
  have hseed : boundedUniversalSyntaxSeed small <=
      boundedUniversalSyntaxSeed large := by
    unfold boundedUniversalSyntaxSeed
    omega
  have hbody := substitutionFormulaCodeEnvelope_mono_local hseed hseed
  have hcase := finiteCaseFormulaEnvelope_mono_openIndexUniversal
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0) hbound
  unfold boundedUniversalClosedFormulaEnvelope
    boundedUniversalClosedBodyCodeEnvelope
  omega

def fixedWidthOpenIndexUniversalContextCodePolynomial (scale : Nat) : Nat :=
  2 * valuationContextFormulaCodeSumEnvelope 1 scale
    (binaryTermCode (&0 : ValuationTerm)).length

def fixedWidthOpenIndexUniversalSyntaxPolynomial (scale : Nat) : Nat :=
  scale + fixedWidthOpenIndexUniversalBodyCodePolynomial scale

def fixedWidthOpenIndexUniversalFormulaPolynomial (scale : Nat) : Nat :=
  boundedUniversalClosedFormulaEnvelope
      (fixedWidthOpenIndexUniversalSyntaxPolynomial scale) +
    2 * fixedWidthOpenIndexUniversalBodyCodePolynomial scale +
    fixedWidthOpenIndexUniversalContextCodePolynomial scale

def fixedWidthOpenIndexUniversalLocalPayloadPolynomial (scale : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (fixedWidthOpenIndexUniversalFormulaPolynomial scale)

def fixedWidthOpenIndexUniversalBranchesFixedPayloadPolynomial
    (scale leafBound : Nat) : Nat :=
  (scale + 1) *
    (leafBound +
      3 * fixedWidthOpenIndexUniversalLocalPayloadPolynomial scale)

def fixedWidthOpenIndexLeafAggregateFixedPayloadPolynomial
    (scale : Nat) : Nat :=
  scale * fixedWidthOpenIndexLeafFixedPayloadPolynomial scale

def fixedWidthOpenIndexUniversalBranchesFullyFixedPayloadPolynomial
    (scale : Nat) : Nat :=
  fixedWidthOpenIndexUniversalBranchesFixedPayloadPolynomial scale
    (fixedWidthOpenIndexLeafAggregateFixedPayloadPolynomial scale)

private theorem fixedWidthOpenIndexSourcePayloadPolynomial_mono_local
    {small large : Nat} (hbound : small <= large) :
    fixedWidthOpenIndexSourcePayloadPolynomial small <=
      fixedWidthOpenIndexSourcePayloadPolynomial large := by
  have hposition : fixedWidthOpenIndexSourcePositionPolynomial small <=
      fixedWidthOpenIndexSourcePositionPolynomial large := by
    unfold fixedWidthOpenIndexSourcePositionPolynomial
    exact Nat.add_le_add (Nat.mul_le_mul hbound hbound) hbound
  unfold fixedWidthOpenIndexSourcePayloadPolynomial
    binaryBitTraceBudgetPayloadPolynomial
  exact binaryBitRecursivePayloadPolynomial_mono (by omega)

private theorem fixedWidthOpenIndexTermCodePolynomial_mono_local
    {small large : Nat} (hbound : small <= large) :
    fixedWidthOpenIndexTermCodePolynomial small <=
      fixedWidthOpenIndexTermCodePolynomial large := by
  have hnumeral := binaryNumeralTermCodeEnvelope_mono_short hbound
  unfold fixedWidthOpenIndexTermCodePolynomial
  omega

private theorem fixedWidthOpenIndexContextCodePolynomial_mono_local
    {small large : Nat} (hbound : small <= large) :
    fixedWidthOpenIndexContextCodePolynomial small <=
      fixedWidthOpenIndexContextCodePolynomial large := by
  unfold fixedWidthOpenIndexContextCodePolynomial
  exact valuationContextFormulaCodeSumEnvelope_mono_numeric_openIndex
    2 fixedWidthBitVariableTermCodeBound hbound

private theorem fixedWidthOpenIndexLeafEqualityPayload_le_scale
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (scale : Nat)
    (hpublic :
      fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthOpenIndexLeafTermEqualityPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm <=
      fixedWidthOpenIndexLeafTermEqualityFixedPayloadPolynomial scale := by
  let publicScale := fixedWidthOpenIndexPublicCoordinateScale valuation
    tableTerm widthTerm indexTerm valueTerm
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  have hterms :=
    FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerContextBounds.fixedWidthBitTerms_freeVariables_of_openIndex
      tableTerm widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  have hleftIndexCard : leftIndexTerm.freeVariables.card <= 4 := by
    have hcard := Finset.card_le_card hterms.1
    dsimp only [leftIndexTerm]
    norm_num at hcard ⊢
    omega
  have hleftValueCard : leftValueTerm.freeVariables.card <= 4 := by
    dsimp only [leftValueTerm]
    rw [hterms.2.1]
    simp
  have hrightIndexCard : rightIndexTerm.freeVariables.card <= 4 := by
    dsimp only [rightIndexTerm]
    rw [hterms.2.2.1]
    simp
  have hrightValueCard : rightValueTerm.freeVariables.card <= 4 := by
    dsimp only [rightValueTerm]
    rw [hterms.2.2.2]
    simp
  have hleftIndexCode : (binaryTermCode leftIndexTerm).length <= scale := by
    have hraw : (binaryTermCode leftIndexTerm).length <= publicScale := by
      dsimp only [leftIndexTerm, publicScale]
      unfold fixedWidthOpenIndexPublicCoordinateScale
      omega
    exact hraw.trans hpublic
  have hleftValueCode : (binaryTermCode leftValueTerm).length <= scale := by
    have hraw : (binaryTermCode leftValueTerm).length <= publicScale := by
      dsimp only [leftValueTerm, publicScale]
      unfold fixedWidthOpenIndexPublicCoordinateScale
      omega
    exact hraw.trans hpublic
  have hrightIndexCode : (binaryTermCode rightIndexTerm).length <= scale := by
    have hraw : (binaryTermCode rightIndexTerm).length <= publicScale := by
      dsimp only [rightIndexTerm, publicScale]
      unfold fixedWidthOpenIndexPublicCoordinateScale
      omega
    exact hraw.trans hpublic
  have hrightValueCode : (binaryTermCode rightValueTerm).length <= scale := by
    have hraw : (binaryTermCode rightValueTerm).length <= publicScale := by
      dsimp only [rightValueTerm, publicScale]
      unfold fixedWidthOpenIndexPublicCoordinateScale
      omega
    exact hraw.trans hpublic
  have hleftIndexMono := compileTermValueEqualityUniformPayloadPolynomial_mono
    hpublic leftIndexTerm
  have hleftValueMono := compileTermValueEqualityUniformPayloadPolynomial_mono
    hpublic leftValueTerm
  have hrightIndexMono := compileTermValueEqualityUniformPayloadPolynomial_mono
    hpublic rightIndexTerm
  have hrightValueMono := compileTermValueEqualityUniformPayloadPolynomial_mono
    hpublic rightValueTerm
  have hleftIndexFixed :=
    compileTermValueEqualityUniformPayloadPolynomial_le_fixed scale scale
      leftIndexTerm hleftIndexCard hleftIndexCode
  have hleftValueFixed :=
    compileTermValueEqualityUniformPayloadPolynomial_le_fixed scale scale
      leftValueTerm hleftValueCard hleftValueCode
  have hrightIndexFixed :=
    compileTermValueEqualityUniformPayloadPolynomial_le_fixed scale scale
      rightIndexTerm hrightIndexCard hrightIndexCode
  have hrightValueFixed :=
    compileTermValueEqualityUniformPayloadPolynomial_le_fixed scale scale
      rightValueTerm hrightValueCard hrightValueCode
  unfold fixedWidthOpenIndexLeafTermEqualityPayloadPolynomial
    fixedWidthOpenIndexLeafTermEqualityFixedPayloadPolynomial
  dsimp only [publicScale, leftIndexTerm, leftValueTerm, rightIndexTerm,
    rightValueTerm] at *
  omega

private theorem fixedWidthOpenIndexLeafPayloadPolynomial_le_scale
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (scale : Nat)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthOpenIndexLeafPayloadPolynomial valuation tableTerm widthTerm
        indexTerm valueTerm <=
      fixedWidthOpenIndexLeafFixedPayloadPolynomial scale := by
  let publicScale := fixedWidthOpenIndexPublicCoordinateScale valuation
    tableTerm widthTerm indexTerm valueTerm
  let oldContext := fixedWidthOpenIndexContextCodePolynomial publicScale
  let newContext := fixedWidthOpenIndexContextCodePolynomial scale
  let oldTerm := fixedWidthOpenIndexTermCodePolynomial publicScale
  let newTerm := fixedWidthOpenIndexTermCodePolynomial scale
  let oldEquality := fixedWidthOpenIndexLeafTermEqualityPayloadPolynomial
    valuation tableTerm widthTerm indexTerm valueTerm
  let newEquality := fixedWidthOpenIndexLeafTermEqualityFixedPayloadPolynomial
    scale
  let oldSyntax := fixedWidthOpenIndexLeafSmallContextSyntaxPolynomial
    publicScale
  let newSyntax := fixedWidthOpenIndexLeafSmallContextSyntaxPolynomial scale
  have hpublic : publicScale <= scale :=
    (fixedWidthOpenIndexPublicCoordinateScale_le_atomicCoordinateScale valuation
      tableTerm widthTerm indexTerm valueTerm).trans hscale
  have hsource := fixedWidthOpenIndexSourcePayloadPolynomial_mono_local hpublic
  have hcontext := fixedWidthOpenIndexContextCodePolynomial_mono_local hpublic
  have hterm := fixedWidthOpenIndexTermCodePolynomial_mono_local hpublic
  have hequality := fixedWidthOpenIndexLeafEqualityPayload_le_scale valuation
    tableTerm widthTerm indexTerm valueTerm scale hpublic htable hwidth hindex
      hvalue
  have hconnector :=
    binaryBitValuationConnectorUniformPolynomial_mono_openIndex hcontext hterm
      hequality
  have hformula := binaryBitValuationFormulaClosureCodeEnvelope_mono_openIndex
    hterm
  have hsyntax : oldSyntax <= newSyntax := by
    unfold oldSyntax newSyntax
      fixedWidthOpenIndexLeafSmallContextSyntaxPolynomial
    omega
  have hassembly := smallContextAssemblyEnvelope_mono_local hsyntax
  unfold fixedWidthOpenIndexLeafPayloadPolynomial
    fixedWidthOpenIndexLeafFixedPayloadPolynomial
  dsimp only [publicScale, oldContext, newContext, oldTerm, newTerm,
    oldEquality, newEquality, oldSyntax, newSyntax] at *
  omega

theorem fixedWidthBitLeafAggregateScalarPayload_le_fixed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (scale : Nat)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthBitLeafAggregateOpenIndexScalarPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm <=
      fixedWidthOpenIndexLeafAggregateFixedPayloadPolynomial scale := by
  have hwidthValue : termValue valuation widthTerm <= scale := by
    have hraw : termValue valuation widthTerm <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      unfold fixedWidthOpenIndexAtomicCoordinateScale
        fixedWidthOpenIndexPublicCoordinateScale
      omega
    exact hraw.trans hscale
  have hleaf := fixedWidthOpenIndexLeafPayloadPolynomial_le_scale valuation
    tableTerm widthTerm indexTerm valueTerm scale hscale htable hwidth hindex
      hvalue
  unfold fixedWidthBitLeafAggregateOpenIndexScalarPayloadPolynomial
    fixedWidthOpenIndexLeafAggregateFixedPayloadPolynomial
  exact Nat.mul_le_mul hwidthValue hleaf

theorem fixedWidthOpenIndexOuterContextFormulaCodeSum_le_fixed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (scale : Nat)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
    let outerFormula := ∀⁰ termBoundedUniversalBody
      (Rew.bShift widthTerm) body
    let outerVariables := outerFormula.freeVariables
    contextualHybridUniversalFormulaCodeSum
        ((valuationContext outerVariables valuation).image Rewriting.shift) <=
      fixedWidthOpenIndexUniversalContextCodePolynomial scale := by
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let baseContext := valuationContext outerVariables valuation
  let Gamma := baseContext.image Rewriting.shift
  let baseBound := valuationContextFormulaCodeSumEnvelope 1 scale
    (binaryTermCode (&0 : ValuationTerm)).length
  have houter : outerVariables ⊆ {0} := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      fixedWidthUniversalOuterFormula_freeVariables_subset_singleton_of_openIndex
        tableTerm widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  have houterCard : outerVariables.card <= 1 :=
    (Finset.card_le_card houter).trans (by simp)
  have hzero : valuation 0 <= scale := by
    have hraw : valuation 0 <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      unfold fixedWidthOpenIndexAtomicCoordinateScale
        fixedWidthOpenIndexPublicCoordinateScale
      omega
    exact hraw.trans hscale
  have hvalues : forall candidate, candidate ∈ outerVariables ->
      valuation candidate <= scale := by
    intro candidate hcandidate
    have hsingle := houter hcandidate
    simp only [Finset.mem_singleton] at hsingle
    subst candidate
    exact hzero
  have hvariables : forall candidate, candidate ∈ outerVariables ->
      (binaryTermCode (&candidate : ValuationTerm)).length <=
        (binaryTermCode (&0 : ValuationTerm)).length := by
    intro candidate hcandidate
    have hsingle := houter hcandidate
    simp only [Finset.mem_singleton] at hsingle
    subst candidate
    exact le_rfl
  have hbaseSum : formulaCodeSum baseContext <= baseBound := by
    dsimp only [baseContext, baseBound]
    exact valuationContext_formulaCodeSum_le_uniform outerVariables valuation 1
      scale (binaryTermCode (&0 : ValuationTerm)).length houterCard hvalues
        hvariables
  have hGammaCard : Gamma.card <= 1 := by
    have hbaseCard : baseContext.card <= outerVariables.card := by
      dsimp only [baseContext]
      unfold valuationContext
      exact Finset.card_image_le
    exact Finset.card_image_le.trans (hbaseCard.trans houterCard)
  have hGammaFormula : forall formula, formula ∈ Gamma ->
      (binaryFormulaCode formula).length <= 2 * baseBound := by
    intro formula hformula
    rcases Finset.mem_image.mp hformula with
      ⟨sourceFormula, hsourceFormula, rfl⟩
    have hsource :=
      (formulaCode_le_formulaCodeSum hsourceFormula).trans hbaseSum
    exact (binaryFormulaCode_shift_length_le sourceFormula).trans (by omega)
  have hsum := Gamma.sum_le_card_nsmul
    (fun formula => (binaryFormulaCode formula).length) (2 * baseBound)
      hGammaFormula
  have hcardProduct : Gamma.card * (2 * baseBound) <= 2 * baseBound := by
    exact (Nat.mul_le_mul_right (2 * baseBound) hGammaCard).trans (by omega)
  unfold contextualHybridUniversalFormulaCodeSum
    fixedWidthOpenIndexUniversalContextCodePolynomial
  dsimp only [body, outerFormula, outerVariables, baseContext, Gamma, baseBound]
    at hsum hcardProduct ⊢
  simpa only [nsmul_eq_mul] using hsum.trans hcardProduct

theorem fixedWidthBitBranchesResource_le_fixed_of_eq
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (resource target scale : Nat)
    (hresource : resource =
      fixedWidthBitBranchesOpenIndexEqualityExposedPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm)
    (htarget : target =
      fixedWidthOpenIndexUniversalBranchesFullyFixedPayloadPolynomial scale)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    Nat.le resource target := by
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma :=
    (valuationContext outerVariables valuation).image Rewriting.shift
  let bound := termValue valuation widthTerm
  let oldLeaf := fixedWidthBitLeafAggregateOpenIndexScalarPayloadPolynomial
    valuation tableTerm widthTerm indexTerm valueTerm
  let newLeaf := fixedWidthOpenIndexLeafAggregateFixedPayloadPolynomial scale
  let oldFormula := contextualHybridUniversalFormulaEnvelope Gamma bound body
  let newFormula := fixedWidthOpenIndexUniversalFormulaPolynomial scale
  have hbound : bound <= scale := by
    have hraw : bound <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      dsimp only [bound]
      unfold fixedWidthOpenIndexAtomicCoordinateScale
        fixedWidthOpenIndexPublicCoordinateScale
      omega
    exact hraw.trans hscale
  have hbody := fixedWidthBitBody_code_le_fixed valuation tableTerm widthTerm
    indexTerm valueTerm scale hscale
  have hsyntax : explicitHybridUniversalSyntaxResource bound body <=
      fixedWidthOpenIndexUniversalSyntaxPolynomial scale := by
    unfold explicitHybridUniversalSyntaxResource
      fixedWidthOpenIndexUniversalSyntaxPolynomial
    dsimp only [body] at hbody ⊢
    omega
  have hclosedEnvelope :=
    boundedUniversalClosedFormulaEnvelope_mono_openIndexUniversal hsyntax
  have hcontext := fixedWidthOpenIndexOuterContextFormulaCodeSum_le_fixed
    valuation tableTerm widthTerm indexTerm valueTerm scale hscale htable hwidth
      hindex hvalue
  have hformula : oldFormula <= newFormula := by
    unfold oldFormula newFormula contextualHybridUniversalFormulaEnvelope
      explicitHybridUniversalFormulaEnvelope
      fixedWidthOpenIndexUniversalFormulaPolynomial
    dsimp only [Gamma, outerVariables, outerFormula, body, bound] at hclosedEnvelope hbody hcontext ⊢
    omega
  have hlocal := smallContextAssemblyEnvelope_mono_local hformula
  have hleaf : oldLeaf <= newLeaf := by
    dsimp only [oldLeaf, newLeaf]
    exact fixedWidthBitLeafAggregateScalarPayload_le_fixed valuation tableTerm
      widthTerm indexTerm valueTerm scale hscale htable hwidth hindex hvalue
  rw [hresource, htarget]
  unfold fixedWidthBitBranchesOpenIndexEqualityExposedPayloadPolynomial
    contextualHybridUniversalBranchesPayloadPolynomial
    contextualHybridUniversalLocalPayloadEnvelope
    fixedWidthOpenIndexUniversalBranchesFullyFixedPayloadPolynomial
    fixedWidthOpenIndexUniversalBranchesFixedPayloadPolynomial
    fixedWidthOpenIndexUniversalLocalPayloadPolynomial
  dsimp only [body, outerFormula, outerVariables, Gamma, bound, oldLeaf,
    newLeaf, oldFormula, newFormula] at hleaf hbound hlocal ⊢
  exact Nat.mul_le_mul (by omega) (by omega)

#print axioms fixedWidthBitBody_code_le_fixed
#print axioms fixedWidthBitBranchesResource_le_fixed_of_eq

end FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalFixedBounds
