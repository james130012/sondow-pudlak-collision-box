import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
import integration.FoundationCompactPAValuationTermCompilerUniformMonotoneBounds
import integration.FoundationCompactPAValuationTermCompilerFixedPolynomialBounds

/-!
# Scalar bounds for a fixed-width entry at an open row index

The transparent open-index compiler already replaces the per-bit finite sum by
`width * leafBound`.  This file puts its remaining numeric and syntax
coordinates under one public scalar.  No proof object or checked branch occurs
in that scalar.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexScalarBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABitMembershipTraceBudgetBounds
open FoundationCompactPABitMembershipValuationCompilerPublicBounds
open FoundationCompactPABitMembershipValuationTransportPolynomialBounds
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAExponentialShortNumeralCompilerBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerContextBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerLeafPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationTermCompilerUniformBounds
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPAValuationTermCompilerUniformMonotoneBounds
open FoundationCompactPAValuationTermCompilerFixedPolynomialBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds

/-- One proof-independent coordinate for the open-index fixed-width compiler.
The row index and width occur numerically because the verifier visits
`index * width + width` bit positions.  Table and cell values occur only by
binary width. -/
def fixedWidthOpenIndexPublicCoordinateScale
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  termValue valuation widthTerm +
    termValue valuation indexTerm + valuation 0 +
    Nat.size (termValue valuation tableTerm) +
    2 * Nat.size (termValue valuation widthTerm) +
    Nat.size (termValue valuation indexTerm) +
    Nat.size (termValue valuation valueTerm) +
    (binaryTermCode
      (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length +
    (binaryTermCode
      (fixedWidthLeftBitValueTerm tableTerm)).length +
    (binaryTermCode fixedWidthRightBitIndexTerm).length +
    (binaryTermCode
      (fixedWidthRightBitValueTerm valueTerm)).length + 2

theorem fixedWidthOpenIndexPublicCoordinateScale_pos
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    1 <= fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm
      widthTerm indexTerm valueTerm := by
  unfold fixedWidthOpenIndexPublicCoordinateScale
  omega

theorem fixedWidthBitPublicScale_le_openIndexCoordinateScale
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    fixedWidthBitPublicScale valuation tableTerm widthTerm indexTerm
        valueTerm <=
      fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm widthTerm
        indexTerm valueTerm := by
  unfold fixedWidthBitPublicScale fixedWidthOpenIndexPublicCoordinateScale
  omega

theorem fixedWidthBitValuationContextNumericBound_le_openIndexCoordinateScale
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    fixedWidthBitValuationContextNumericBound valuation widthTerm <=
      fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm widthTerm
        indexTerm valueTerm := by
  unfold fixedWidthBitValuationContextNumericBound
    fixedWidthOpenIndexPublicCoordinateScale
  omega

theorem fixedWidthBitSourceCoordinateBound_le_openIndexCoordinateScale
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    fixedWidthBitSourceCoordinateBound valuation tableTerm valueTerm <=
      fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm widthTerm
        indexTerm valueTerm := by
  unfold fixedWidthBitSourceCoordinateBound
    fixedWidthOpenIndexPublicCoordinateScale
  omega

def fixedWidthOpenIndexSourcePositionPolynomial (scale : Nat) : Nat :=
  scale * scale + scale

theorem fixedWidthBitSourceIndexBound_le_openIndexPositionPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    fixedWidthBitSourceIndexBound valuation widthTerm indexTerm <=
      fixedWidthOpenIndexSourcePositionPolynomial
        (fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm
          widthTerm indexTerm valueTerm) := by
  let scale := fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm
    widthTerm indexTerm valueTerm
  have hwidth : termValue valuation widthTerm <= scale := by
    dsimp only [scale]
    unfold fixedWidthOpenIndexPublicCoordinateScale
    omega
  have hindex : termValue valuation indexTerm <= scale := by
    dsimp only [scale]
    unfold fixedWidthOpenIndexPublicCoordinateScale
    omega
  have hmul : termValue valuation indexTerm * termValue valuation widthTerm <=
      scale * scale := Nat.mul_le_mul hindex hwidth
  unfold fixedWidthBitSourceIndexBound
    fixedWidthOpenIndexSourcePositionPolynomial
  dsimp only [scale] at hwidth hmul ⊢
  omega

def fixedWidthOpenIndexSourcePayloadPolynomial (scale : Nat) : Nat :=
  binaryBitTraceBudgetPayloadPolynomial scale
    (fixedWidthOpenIndexSourcePositionPolynomial scale)

theorem fixedWidthBitSourcePayloadPolynomial_le_openIndexScalar
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    fixedWidthBitSourcePayloadPolynomial valuation tableTerm widthTerm
        indexTerm valueTerm <=
      fixedWidthOpenIndexSourcePayloadPolynomial
        (fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm
          widthTerm indexTerm valueTerm) := by
  let scale := fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm
    widthTerm indexTerm valueTerm
  have hcoordinate :=
    fixedWidthBitSourceCoordinateBound_le_openIndexCoordinateScale valuation
      tableTerm widthTerm indexTerm valueTerm
  have hposition :=
    fixedWidthBitSourceIndexBound_le_openIndexPositionPolynomial valuation
      tableTerm widthTerm indexTerm valueTerm
  unfold fixedWidthBitSourcePayloadPolynomial
    fixedWidthOpenIndexSourcePayloadPolynomial
    binaryBitTraceBudgetPayloadPolynomial
  apply binaryBitRecursivePayloadPolynomial_mono
  exact Nat.add_le_add_right (Nat.add_le_add hcoordinate hposition) 1

def fixedWidthOpenIndexTermCodePolynomial (scale : Nat) : Nat :=
  2 * binaryNumeralTermCodeEnvelope scale + 4 * scale + 1

theorem fixedWidthBitValuationTermCodeUniformResource_le_openIndexScalar
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    fixedWidthBitValuationTermCodeUniformResource valuation tableTerm
        widthTerm indexTerm valueTerm <=
      fixedWidthOpenIndexTermCodePolynomial
        (fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm
          widthTerm indexTerm valueTerm) := by
  let scale := fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm
    widthTerm indexTerm valueTerm
  have hpublicScale : fixedWidthBitPublicScale valuation tableTerm widthTerm
      indexTerm valueTerm <= scale := by
    simpa only [scale] using
      fixedWidthBitPublicScale_le_openIndexCoordinateScale valuation tableTerm
        widthTerm indexTerm valueTerm
  have hnumeral := binaryNumeralTermCodeEnvelope_mono_short hpublicScale
  have hleftIndex :
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <= scale := by
    dsimp only [scale]
    unfold fixedWidthOpenIndexPublicCoordinateScale
    omega
  have hleftValue :
      (binaryTermCode
        (fixedWidthLeftBitValueTerm tableTerm)).length <= scale := by
    dsimp only [scale]
    unfold fixedWidthOpenIndexPublicCoordinateScale
    omega
  have hrightIndex :
      (binaryTermCode fixedWidthRightBitIndexTerm).length <= scale := by
    dsimp only [scale]
    unfold fixedWidthOpenIndexPublicCoordinateScale
    omega
  have hrightValue :
      (binaryTermCode
        (fixedWidthRightBitValueTerm valueTerm)).length <= scale := by
    dsimp only [scale]
    unfold fixedWidthOpenIndexPublicCoordinateScale
    omega
  unfold fixedWidthBitValuationTermCodeUniformResource
    fixedWidthOpenIndexTermCodePolynomial
  simp only [scale] at *
  omega

theorem valuationContextFormulaCodeSumEnvelope_mono_numeric_openIndex
    (cardBound variableTermCodeBound : Nat)
    {small large : Nat} (hbound : small <= large) :
    valuationContextFormulaCodeSumEnvelope cardBound small
        variableTermCodeBound <=
      valuationContextFormulaCodeSumEnvelope cardBound large
        variableTermCodeBound := by
  have hterm := iteratedSuccessorTermCodePolynomial_mono 0 hbound
  unfold valuationContextFormulaCodeSumEnvelope
    valuationEqualityAssumptionFormulaCodeEnvelope
  exact Nat.mul_le_mul_left cardBound (by omega)

def fixedWidthOpenIndexContextCodePolynomial (scale : Nat) : Nat :=
  valuationContextFormulaCodeSumEnvelope 2 scale
    fixedWidthBitVariableTermCodeBound

theorem
    fixedWidthBitValuationContextFormulaCodeUniformResource_le_openIndexScalar
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    fixedWidthBitValuationContextFormulaCodeUniformResource valuation
        widthTerm <=
      fixedWidthOpenIndexContextCodePolynomial
        (fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm
          widthTerm indexTerm valueTerm) := by
  have hnumeric :=
    fixedWidthBitValuationContextNumericBound_le_openIndexCoordinateScale
      valuation tableTerm widthTerm indexTerm valueTerm
  unfold fixedWidthBitValuationContextFormulaCodeUniformResource
    fixedWidthOpenIndexContextCodePolynomial
  exact valuationContextFormulaCodeSumEnvelope_mono_numeric_openIndex
    2 fixedWidthBitVariableTermCodeBound hnumeric

theorem binaryBitValuationFormulaClosureCodeEnvelope_mono_openIndex
    {small large : Nat} (hbound : small <= large) :
    binaryBitValuationFormulaClosureCodeEnvelope small <=
      binaryBitValuationFormulaClosureCodeEnvelope large := by
  have hfirst : binaryBitAtomFirstSubstitutionEnvelope small <=
      binaryBitAtomFirstSubstitutionEnvelope large := by
    unfold binaryBitAtomFirstSubstitutionEnvelope
    gcongr
  have hatom : binaryBitAtomFormulaCodeEnvelope small <=
      binaryBitAtomFormulaCodeEnvelope large := by
    unfold binaryBitAtomFormulaCodeEnvelope
    exact substitutionFormulaCodeEnvelope_mono_local hfirst hbound
  have hliteral : binaryBitLiteralFormulaCodeEnvelope small <=
      binaryBitLiteralFormulaCodeEnvelope large := by
    unfold binaryBitLiteralFormulaCodeEnvelope
    omega
  have hinstantiated := instantiatedFormulaCodeEnvelope_mono_local hbound
  have hequality : paEqualityFormulaCodeEnvelope small <=
      paEqualityFormulaCodeEnvelope large := by
    unfold paEqualityFormulaCodeEnvelope
    omega
  have hpa : paFormulaCodeEnvelope small <=
      paFormulaCodeEnvelope large := by
    unfold paFormulaCodeEnvelope
    omega
  unfold binaryBitValuationFormulaClosureCodeEnvelope
    binaryBitValuationFormulaStageTwoCodeEnvelope
    binaryBitValuationFormulaStageOneCodeEnvelope
    binaryBitValuationFormulaBaseCodeEnvelope
  omega

theorem binaryBitValuationConnectorFormulaResourceEnvelope_mono_openIndex
    {smallContext largeContext smallTerm largeTerm : Nat}
    (hcontext : smallContext <= largeContext)
    (hterm : smallTerm <= largeTerm) :
    binaryBitValuationConnectorFormulaResourceEnvelope smallContext
        smallTerm <=
      binaryBitValuationConnectorFormulaResourceEnvelope largeContext
        largeTerm := by
  have hformula :=
    binaryBitValuationFormulaClosureCodeEnvelope_mono_openIndex hterm
  unfold binaryBitValuationConnectorFormulaResourceEnvelope
  omega

theorem binaryBitValuationConnectorUniformPolynomial_mono_openIndex
    {smallContext largeContext smallTerm largeTerm
      smallEquality largeEquality : Nat}
    (hcontext : smallContext <= largeContext)
    (hterm : smallTerm <= largeTerm)
    (hequality : smallEquality <= largeEquality) :
    binaryBitValuationConnectorUniformPolynomial smallContext smallTerm
        smallEquality <=
      binaryBitValuationConnectorUniformPolynomial largeContext largeTerm
        largeEquality := by
  have hindex := binaryBitIndexTransportPayloadTermPolynomial_mono hterm
  have hvalue := binaryBitValueTransportPayloadTermPolynomial_mono hterm
  have hsymmetry := binaryBitEqualitySymmetryPayloadTermPolynomial_mono hterm
  have hformula :=
    binaryBitValuationConnectorFormulaResourceEnvelope_mono_openIndex
      hcontext hterm
  have hassembly := smallContextAssemblyEnvelope_mono_local hformula
  unfold binaryBitValuationConnectorUniformPolynomial
  omega

def fixedWidthOpenIndexLeafTermEqualityPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let numericBound := fixedWidthOpenIndexPublicCoordinateScale valuation
    tableTerm widthTerm indexTerm valueTerm
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  compileTermValueEqualityUniformPayloadPolynomial numericBound leftIndexTerm +
    compileTermValueEqualityUniformPayloadPolynomial numericBound
      leftValueTerm +
    compileTermValueEqualityUniformPayloadPolynomial numericBound
      rightIndexTerm +
    compileTermValueEqualityUniformPayloadPolynomial numericBound
      rightValueTerm + 1

theorem
    fixedWidthBitLeafTermEqualityUniformPayloadBound_le_openIndexScalar
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    fixedWidthBitLeafTermEqualityUniformPayloadBound valuation tableTerm
        widthTerm indexTerm valueTerm <=
      fixedWidthOpenIndexLeafTermEqualityPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm := by
  let oldNumericBound :=
    fixedWidthBitTermEqualityNumericBound valuation widthTerm
  let newNumericBound := fixedWidthOpenIndexPublicCoordinateScale valuation
    tableTerm widthTerm indexTerm valueTerm
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  have hnumeric : oldNumericBound <= newNumericBound := by
    dsimp only [oldNumericBound, newNumericBound]
    exact
      fixedWidthBitValuationContextNumericBound_le_openIndexCoordinateScale
        valuation tableTerm widthTerm indexTerm valueTerm
  have hleftIndex := compileTermValueEqualityUniformPayloadPolynomial_mono
    hnumeric leftIndexTerm
  have hleftValue := compileTermValueEqualityUniformPayloadPolynomial_mono
    hnumeric leftValueTerm
  have hrightIndex := compileTermValueEqualityUniformPayloadPolynomial_mono
    hnumeric rightIndexTerm
  have hrightValue := compileTermValueEqualityUniformPayloadPolynomial_mono
    hnumeric rightValueTerm
  unfold fixedWidthBitLeafTermEqualityUniformPayloadBound
    fixedWidthOpenIndexLeafTermEqualityPayloadPolynomial
  dsimp only [oldNumericBound, newNumericBound, leftIndexTerm, leftValueTerm,
    rightIndexTerm, rightValueTerm] at *
  omega

def fixedWidthOpenIndexLeafTermEqualityFixedPayloadPolynomial
    (scale : Nat) : Nat :=
  4 * compileTermValueEqualityFixedPayloadPolynomial scale scale + 1

theorem
    fixedWidthOpenIndexLeafTermEqualityPayloadPolynomial_le_fixed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthOpenIndexLeafTermEqualityPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm <=
      fixedWidthOpenIndexLeafTermEqualityFixedPayloadPolynomial
        (fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm
          widthTerm indexTerm valueTerm) := by
  let scale := fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm
    widthTerm indexTerm valueTerm
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  have hterms := fixedWidthBitTerms_freeVariables_of_openIndex tableTerm
    widthTerm indexTerm valueTerm htable hwidth hindex hvalue
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
    dsimp only [leftIndexTerm, scale]
    unfold fixedWidthOpenIndexPublicCoordinateScale
    omega
  have hleftValueCode : (binaryTermCode leftValueTerm).length <= scale := by
    dsimp only [leftValueTerm, scale]
    unfold fixedWidthOpenIndexPublicCoordinateScale
    omega
  have hrightIndexCode : (binaryTermCode rightIndexTerm).length <= scale := by
    dsimp only [rightIndexTerm, scale]
    unfold fixedWidthOpenIndexPublicCoordinateScale
    omega
  have hrightValueCode : (binaryTermCode rightValueTerm).length <= scale := by
    dsimp only [rightValueTerm, scale]
    unfold fixedWidthOpenIndexPublicCoordinateScale
    omega
  have hleftIndex :=
    compileTermValueEqualityUniformPayloadPolynomial_le_fixed scale scale
      leftIndexTerm hleftIndexCard hleftIndexCode
  have hleftValue :=
    compileTermValueEqualityUniformPayloadPolynomial_le_fixed scale scale
      leftValueTerm hleftValueCard hleftValueCode
  have hrightIndex :=
    compileTermValueEqualityUniformPayloadPolynomial_le_fixed scale scale
      rightIndexTerm hrightIndexCard hrightIndexCode
  have hrightValue :=
    compileTermValueEqualityUniformPayloadPolynomial_le_fixed scale scale
      rightValueTerm hrightValueCard hrightValueCode
  unfold fixedWidthOpenIndexLeafTermEqualityPayloadPolynomial
    fixedWidthOpenIndexLeafTermEqualityFixedPayloadPolynomial
  dsimp only [scale, leftIndexTerm, leftValueTerm, rightIndexTerm,
    rightValueTerm] at *
  omega

def fixedWidthOpenIndexLeafSmallContextSyntaxPolynomial (scale : Nat) : Nat :=
  7 * fixedWidthOpenIndexContextCodePolynomial scale +
    9 * binaryBitValuationFormulaClosureCodeEnvelope
      (fixedWidthOpenIndexTermCodePolynomial scale) + 1

theorem
    fixedWidthBitLeafSmallContextSyntaxUniformResource_le_openIndexScalar
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    fixedWidthBitLeafSmallContextSyntaxUniformResource valuation tableTerm
        widthTerm indexTerm valueTerm <=
      fixedWidthOpenIndexLeafSmallContextSyntaxPolynomial
        (fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm
          widthTerm indexTerm valueTerm) := by
  have hcontext :=
    fixedWidthBitValuationContextFormulaCodeUniformResource_le_openIndexScalar
      valuation tableTerm widthTerm indexTerm valueTerm
  have hterm :=
    fixedWidthBitValuationTermCodeUniformResource_le_openIndexScalar valuation
      tableTerm widthTerm indexTerm valueTerm
  have hformula :=
    binaryBitValuationFormulaClosureCodeEnvelope_mono_openIndex hterm
  unfold fixedWidthBitLeafSmallContextSyntaxUniformResource
    fixedWidthOpenIndexLeafSmallContextSyntaxPolynomial
  dsimp only
  omega

def fixedWidthOpenIndexLeafPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let scale := fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm
    widthTerm indexTerm valueTerm
  let contextBound := fixedWidthOpenIndexContextCodePolynomial scale
  let termBound := fixedWidthOpenIndexTermCodePolynomial scale
  let equalityBound :=
    fixedWidthOpenIndexLeafTermEqualityPayloadPolynomial valuation tableTerm
      widthTerm indexTerm valueTerm
  let connectorBound := binaryBitValuationConnectorUniformPolynomial
    contextBound termBound equalityBound
  4 * fixedWidthOpenIndexSourcePayloadPolynomial scale +
    4 * connectorBound +
    13 * smallContextAssemblyEnvelope
      (fixedWidthOpenIndexLeafSmallContextSyntaxPolynomial scale)

def fixedWidthOpenIndexLeafFixedPayloadPolynomial (scale : Nat) : Nat :=
  let contextBound := fixedWidthOpenIndexContextCodePolynomial scale
  let termBound := fixedWidthOpenIndexTermCodePolynomial scale
  let equalityBound :=
    fixedWidthOpenIndexLeafTermEqualityFixedPayloadPolynomial scale
  let connectorBound := binaryBitValuationConnectorUniformPolynomial
    contextBound termBound equalityBound
  4 * fixedWidthOpenIndexSourcePayloadPolynomial scale +
    4 * connectorBound +
    13 * smallContextAssemblyEnvelope
      (fixedWidthOpenIndexLeafSmallContextSyntaxPolynomial scale)

theorem fixedWidthOpenIndexLeafPayloadPolynomial_le_fixed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthOpenIndexLeafPayloadPolynomial valuation tableTerm widthTerm
        indexTerm valueTerm <=
      fixedWidthOpenIndexLeafFixedPayloadPolynomial
        (fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm
          widthTerm indexTerm valueTerm) := by
  let scale := fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm
    widthTerm indexTerm valueTerm
  let contextBound := fixedWidthOpenIndexContextCodePolynomial scale
  let termBound := fixedWidthOpenIndexTermCodePolynomial scale
  let oldEquality := fixedWidthOpenIndexLeafTermEqualityPayloadPolynomial
    valuation tableTerm widthTerm indexTerm valueTerm
  let newEquality :=
    fixedWidthOpenIndexLeafTermEqualityFixedPayloadPolynomial scale
  have hequality : oldEquality <= newEquality := by
    dsimp only [oldEquality, newEquality, scale]
    exact fixedWidthOpenIndexLeafTermEqualityPayloadPolynomial_le_fixed
      valuation tableTerm widthTerm indexTerm valueTerm htable hwidth hindex
      hvalue
  have hconnector :=
    binaryBitValuationConnectorUniformPolynomial_mono_openIndex
      (smallContext := contextBound) (largeContext := contextBound)
      (smallTerm := termBound) (largeTerm := termBound)
      (smallEquality := oldEquality) (largeEquality := newEquality)
      le_rfl le_rfl hequality
  unfold fixedWidthOpenIndexLeafPayloadPolynomial
    fixedWidthOpenIndexLeafFixedPayloadPolynomial
  dsimp only [scale, contextBound, termBound, oldEquality, newEquality] at *
  omega

theorem fixedWidthBitLeafUniformPayloadPolynomial_le_openIndexScalar
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    fixedWidthBitLeafUniformPayloadPolynomial valuation tableTerm widthTerm
        indexTerm valueTerm <=
      fixedWidthOpenIndexLeafPayloadPolynomial valuation tableTerm widthTerm
        indexTerm valueTerm := by
  let scale := fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm
    widthTerm indexTerm valueTerm
  let oldContext :=
    fixedWidthBitValuationContextFormulaCodeUniformResource valuation widthTerm
  let newContext := fixedWidthOpenIndexContextCodePolynomial scale
  let oldTerm := fixedWidthBitValuationTermCodeUniformResource valuation
    tableTerm widthTerm indexTerm valueTerm
  let newTerm := fixedWidthOpenIndexTermCodePolynomial scale
  let oldEquality :=
    fixedWidthBitLeafTermEqualityUniformPayloadBound valuation tableTerm
      widthTerm indexTerm valueTerm
  let newEquality :=
    fixedWidthOpenIndexLeafTermEqualityPayloadPolynomial valuation tableTerm
      widthTerm indexTerm valueTerm
  have hsource := fixedWidthBitSourcePayloadPolynomial_le_openIndexScalar
    valuation tableTerm widthTerm indexTerm valueTerm
  have hcontext : oldContext <= newContext := by
    simpa only [oldContext, newContext, scale] using
      fixedWidthBitValuationContextFormulaCodeUniformResource_le_openIndexScalar
        valuation tableTerm widthTerm indexTerm valueTerm
  have hterm : oldTerm <= newTerm := by
    simpa only [oldTerm, newTerm, scale] using
      fixedWidthBitValuationTermCodeUniformResource_le_openIndexScalar
        valuation tableTerm widthTerm indexTerm valueTerm
  have hequality : oldEquality <= newEquality := by
    simpa only [oldEquality, newEquality] using
      fixedWidthBitLeafTermEqualityUniformPayloadBound_le_openIndexScalar
        valuation tableTerm widthTerm indexTerm valueTerm
  have hconnector :=
    binaryBitValuationConnectorUniformPolynomial_mono_openIndex
      hcontext hterm hequality
  have hsyntax :=
    fixedWidthBitLeafSmallContextSyntaxUniformResource_le_openIndexScalar
      valuation tableTerm widthTerm indexTerm valueTerm
  have hassembly := smallContextAssemblyEnvelope_mono_local hsyntax
  unfold fixedWidthBitLeafUniformPayloadPolynomial
    fixedWidthOpenIndexLeafPayloadPolynomial
  dsimp only [scale, oldContext, newContext, oldTerm, newTerm,
    oldEquality, newEquality] at hsource hconnector hassembly ⊢
  omega

def fixedWidthBitLeafAggregateOpenIndexScalarPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  termValue valuation widthTerm *
    fixedWidthOpenIndexLeafPayloadPolynomial valuation tableTerm widthTerm
      indexTerm valueTerm

def fixedWidthBitLeafAggregateOpenIndexFixedPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let scale := fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm
    widthTerm indexTerm valueTerm
  termValue valuation widthTerm *
    fixedWidthOpenIndexLeafFixedPayloadPolynomial scale

theorem
    fixedWidthBitLeafAggregateOpenIndexScalarPayloadPolynomial_le_fixed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthBitLeafAggregateOpenIndexScalarPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm <=
      fixedWidthBitLeafAggregateOpenIndexFixedPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm := by
  unfold fixedWidthBitLeafAggregateOpenIndexScalarPayloadPolynomial
    fixedWidthBitLeafAggregateOpenIndexFixedPayloadPolynomial
  dsimp only
  exact Nat.mul_le_mul_left (termValue valuation widthTerm)
    (fixedWidthOpenIndexLeafPayloadPolynomial_le_fixed valuation tableTerm
      widthTerm indexTerm valueTerm htable hwidth hindex hvalue)

theorem
    fixedWidthBitLeafAggregateUniformPayloadBound_le_openIndexScalar
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    fixedWidthBitLeafAggregateUniformPayloadBound valuation tableTerm
        widthTerm indexTerm valueTerm <=
      fixedWidthBitLeafAggregateOpenIndexScalarPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm := by
  unfold fixedWidthBitLeafAggregateUniformPayloadBound
    fixedWidthBitLeafAggregateOpenIndexScalarPayloadPolynomial
  exact Nat.mul_le_mul_left (termValue valuation widthTerm)
    (fixedWidthBitLeafUniformPayloadPolynomial_le_openIndexScalar valuation
      tableTerm widthTerm indexTerm valueTerm)

def fixedWidthBitBranchesOpenIndexEqualityExposedPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma :=
    (valuationContext outerVariables valuation).image Rewriting.shift
  let bound := termValue valuation widthTerm
  contextualHybridUniversalBranchesPayloadPolynomial Gamma bound bound body
    (fixedWidthBitLeafAggregateOpenIndexScalarPayloadPolynomial valuation
      tableTerm widthTerm indexTerm valueTerm)

theorem
    fixedWidthBitBranchesOpenIndexStructuralPayloadPolynomial_le_equalityExposed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    fixedWidthBitBranchesOpenIndexStructuralPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm <=
      fixedWidthBitBranchesOpenIndexEqualityExposedPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm := by
  have hleaf :=
    fixedWidthBitLeafAggregateUniformPayloadBound_le_openIndexScalar valuation
      tableTerm widthTerm indexTerm valueTerm
  unfold fixedWidthBitBranchesOpenIndexStructuralPayloadPolynomial
    fixedWidthBitBranchesOpenIndexEqualityExposedPayloadPolynomial
    contextualHybridUniversalBranchesPayloadPolynomial
  dsimp only
  exact Nat.mul_le_mul_left (termValue valuation widthTerm + 1)
    (Nat.add_le_add_right hleaf _)

def fixedWidthBitBranchesOpenIndexFixedPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma :=
    (valuationContext outerVariables valuation).image Rewriting.shift
  let bound := termValue valuation widthTerm
  contextualHybridUniversalBranchesPayloadPolynomial Gamma bound bound body
    (fixedWidthBitLeafAggregateOpenIndexFixedPayloadPolynomial valuation
      tableTerm widthTerm indexTerm valueTerm)

theorem
    fixedWidthBitBranchesOpenIndexEqualityExposedPayloadPolynomial_le_fixed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthBitBranchesOpenIndexEqualityExposedPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm <=
      fixedWidthBitBranchesOpenIndexFixedPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm := by
  have hleaf :=
    fixedWidthBitLeafAggregateOpenIndexScalarPayloadPolynomial_le_fixed
      valuation tableTerm widthTerm indexTerm valueTerm htable hwidth hindex
      hvalue
  unfold fixedWidthBitBranchesOpenIndexEqualityExposedPayloadPolynomial
    fixedWidthBitBranchesOpenIndexFixedPayloadPolynomial
    contextualHybridUniversalBranchesPayloadPolynomial
  dsimp only
  exact Nat.mul_le_mul_left (termValue valuation widthTerm + 1)
    (Nat.add_le_add_right hleaf _)

theorem fixedWidthBitBranchesOpenIndexStructuralPayloadPolynomial_le_fixed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthBitBranchesOpenIndexStructuralPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm <=
      fixedWidthBitBranchesOpenIndexFixedPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm :=
  (fixedWidthBitBranchesOpenIndexStructuralPayloadPolynomial_le_equalityExposed
    valuation tableTerm widthTerm indexTerm valueTerm).trans
      (fixedWidthBitBranchesOpenIndexEqualityExposedPayloadPolynomial_le_fixed
        valuation tableTerm widthTerm indexTerm valueTerm htable hwidth hindex
        hvalue)

def fixedWidthUniversalOpenIndexEqualityExposedPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let bound := termValue valuation widthTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (fixedWidthBitBranchesOpenIndexEqualityExposedPayloadPolynomial valuation
      tableTerm widthTerm indexTerm valueTerm)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift widthTerm) body
    (compileShiftedBoundEqualityPayloadPublicPolynomial valuation
      outerVariables widthTerm)
    branchResource

theorem
    fixedWidthUniversalOpenIndexStructuralPayloadPolynomial_le_equalityExposed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    fixedWidthUniversalOpenIndexStructuralPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm <=
      fixedWidthUniversalOpenIndexEqualityExposedPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm := by
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let bound := termValue valuation widthTerm
  let oldCore := fixedWidthBitBranchesOpenIndexStructuralPayloadPolynomial
    valuation tableTerm widthTerm indexTerm valueTerm
  let newCore :=
    fixedWidthBitBranchesOpenIndexEqualityExposedPayloadPolynomial valuation
      tableTerm widthTerm indexTerm valueTerm
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newCore
  let boundResource := compileShiftedBoundEqualityPayloadPublicPolynomial
    valuation outerVariables widthTerm
  have hcore : oldCore <= newCore := by
    dsimp only [oldCore, newCore]
    exact
      fixedWidthBitBranchesOpenIndexStructuralPayloadPolynomial_le_equalityExposed
        valuation tableTerm widthTerm indexTerm valueTerm
  have hbranch : oldBranchResource <= newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldCore newCore hcore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift widthTerm) body
    boundResource oldBranchResource boundResource newBranchResource
    le_rfl hbranch
  simpa only [fixedWidthUniversalOpenIndexStructuralPayloadPolynomial,
    fixedWidthUniversalOpenIndexEqualityExposedPayloadPolynomial,
    body, outerFormula, outerVariables, Gamma, bound, oldCore, newCore,
    oldBranchResource, newBranchResource, boundResource] using htotal

def fixedWidthUniversalOpenIndexFixedPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let bound := termValue valuation widthTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (fixedWidthBitBranchesOpenIndexFixedPayloadPolynomial valuation tableTerm
      widthTerm indexTerm valueTerm)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift widthTerm) body
    (compileShiftedBoundEqualityPayloadPublicPolynomial valuation
      outerVariables widthTerm)
    branchResource

theorem
    fixedWidthUniversalOpenIndexEqualityExposedPayloadPolynomial_le_fixed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthUniversalOpenIndexEqualityExposedPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm <=
      fixedWidthUniversalOpenIndexFixedPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm := by
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let bound := termValue valuation widthTerm
  let oldCore := fixedWidthBitBranchesOpenIndexEqualityExposedPayloadPolynomial
    valuation tableTerm widthTerm indexTerm valueTerm
  let newCore := fixedWidthBitBranchesOpenIndexFixedPayloadPolynomial valuation
    tableTerm widthTerm indexTerm valueTerm
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newCore
  let boundResource := compileShiftedBoundEqualityPayloadPublicPolynomial
    valuation outerVariables widthTerm
  have hcore : oldCore <= newCore := by
    dsimp only [oldCore, newCore]
    exact
      fixedWidthBitBranchesOpenIndexEqualityExposedPayloadPolynomial_le_fixed
        valuation tableTerm widthTerm indexTerm valueTerm htable hwidth hindex
        hvalue
  have hbranch : oldBranchResource <= newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldCore newCore hcore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift widthTerm) body
    boundResource oldBranchResource boundResource newBranchResource
    le_rfl hbranch
  simpa only [fixedWidthUniversalOpenIndexEqualityExposedPayloadPolynomial,
    fixedWidthUniversalOpenIndexFixedPayloadPolynomial, body, outerFormula,
    outerVariables, Gamma, bound, oldCore, newCore, oldBranchResource,
    newBranchResource, boundResource] using htotal

theorem fixedWidthUniversalOpenIndexStructuralPayloadPolynomial_le_fixed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthUniversalOpenIndexStructuralPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm <=
      fixedWidthUniversalOpenIndexFixedPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm :=
  (fixedWidthUniversalOpenIndexStructuralPayloadPolynomial_le_equalityExposed
    valuation tableTerm widthTerm indexTerm valueTerm).trans
      (fixedWidthUniversalOpenIndexEqualityExposedPayloadPolynomial_le_fixed
        valuation tableTerm widthTerm indexTerm valueTerm htable hwidth hindex
        hvalue)

private theorem hybridConjunctionStructuralPayloadEnvelope_mono_openIndex
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    {leftSmall leftLarge rightSmall rightLarge : Nat}
    (hleft : leftSmall <= leftLarge)
    (hright : rightSmall <= rightLarge) :
    hybridConjunctionStructuralPayloadEnvelope valuation left right
        leftSmall rightSmall <=
      hybridConjunctionStructuralPayloadEnvelope valuation left right
        leftLarge rightLarge := by
  unfold hybridConjunctionStructuralPayloadEnvelope
  dsimp only
  omega

private theorem hybridExistsWitnessStructuralPayloadEnvelope_mono_openIndex
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : Nat) {small large : Nat} (hresource : small <= large) :
    hybridExistsWitnessStructuralPayloadEnvelope valuation body witness small <=
      hybridExistsWitnessStructuralPayloadEnvelope valuation body witness
        large := by
  unfold hybridExistsWitnessStructuralPayloadEnvelope
  dsimp only
  omega

def fixedWidthOpenIndexPostWitnessEqualityExposedPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let size := Nat.size (termValue valuation valueTerm)
  let guardFormula := fixedWidthWitnessGuard size valueTerm
  let lengthFormula := fixedWidthLengthFormula size valueTerm
  let sizeGuardFormula := fixedWidthSizeGuard size widthTerm
  let universalFormula := fixedWidthUniversalFormula
    tableTerm widthTerm indexTerm valueTerm
  let innerFormula := sizeGuardFormula ⋏ universalFormula
  let middleFormula := lengthFormula ⋏ innerFormula
  let innerResource := hybridConjunctionStructuralPayloadEnvelope valuation
    sizeGuardFormula universalFormula
    (fixedWidthSizeGuardStructuralPayloadPolynomial valuation widthTerm
      valueTerm)
    (fixedWidthUniversalOpenIndexEqualityExposedPayloadPolynomial valuation
      tableTerm widthTerm indexTerm valueTerm)
  let middleResource := hybridConjunctionStructuralPayloadEnvelope valuation
    lengthFormula innerFormula
    (fixedWidthLengthStructuralPayloadPolynomial valuation valueTerm)
    innerResource
  hybridConjunctionStructuralPayloadEnvelope valuation guardFormula
    middleFormula
    (fixedWidthWitnessGuardStructuralPayloadPolynomial valuation valueTerm)
    middleResource

theorem
    fixedWidthOpenIndexPostWitnessStructuralPayloadPolynomial_le_equalityExposed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    fixedWidthOpenIndexPostWitnessStructuralPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm <=
      fixedWidthOpenIndexPostWitnessEqualityExposedPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm := by
  let size := Nat.size (termValue valuation valueTerm)
  let guardFormula := fixedWidthWitnessGuard size valueTerm
  let lengthFormula := fixedWidthLengthFormula size valueTerm
  let sizeGuardFormula := fixedWidthSizeGuard size widthTerm
  let universalFormula := fixedWidthUniversalFormula
    tableTerm widthTerm indexTerm valueTerm
  have huniversal :=
    fixedWidthUniversalOpenIndexStructuralPayloadPolynomial_le_equalityExposed
      valuation tableTerm widthTerm indexTerm valueTerm
  unfold fixedWidthOpenIndexPostWitnessStructuralPayloadPolynomial
    fixedWidthOpenIndexPostWitnessEqualityExposedPayloadPolynomial
    hybridConjunctionStructuralPayloadEnvelope
  dsimp only [size, guardFormula, lengthFormula, sizeGuardFormula,
    universalFormula]
  omega

def fixedWidthOpenIndexPostWitnessFixedPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let size := Nat.size (termValue valuation valueTerm)
  let guardFormula := fixedWidthWitnessGuard size valueTerm
  let lengthFormula := fixedWidthLengthFormula size valueTerm
  let sizeGuardFormula := fixedWidthSizeGuard size widthTerm
  let universalFormula := fixedWidthUniversalFormula
    tableTerm widthTerm indexTerm valueTerm
  let innerFormula := sizeGuardFormula ⋏ universalFormula
  let middleFormula := lengthFormula ⋏ innerFormula
  let innerResource := hybridConjunctionStructuralPayloadEnvelope valuation
    sizeGuardFormula universalFormula
    (fixedWidthSizeGuardStructuralPayloadPolynomial valuation widthTerm
      valueTerm)
    (fixedWidthUniversalOpenIndexFixedPayloadPolynomial valuation tableTerm
      widthTerm indexTerm valueTerm)
  let middleResource := hybridConjunctionStructuralPayloadEnvelope valuation
    lengthFormula innerFormula
    (fixedWidthLengthStructuralPayloadPolynomial valuation valueTerm)
    innerResource
  hybridConjunctionStructuralPayloadEnvelope valuation guardFormula
    middleFormula
    (fixedWidthWitnessGuardStructuralPayloadPolynomial valuation valueTerm)
    middleResource

theorem
    fixedWidthOpenIndexPostWitnessEqualityExposedPayloadPolynomial_le_fixed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthOpenIndexPostWitnessEqualityExposedPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm <=
      fixedWidthOpenIndexPostWitnessFixedPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm := by
  have huniversal :=
    fixedWidthUniversalOpenIndexEqualityExposedPayloadPolynomial_le_fixed
      valuation tableTerm widthTerm indexTerm valueTerm htable hwidth hindex
      hvalue
  unfold fixedWidthOpenIndexPostWitnessEqualityExposedPayloadPolynomial
    fixedWidthOpenIndexPostWitnessFixedPayloadPolynomial
    hybridConjunctionStructuralPayloadEnvelope
  dsimp only
  omega

theorem fixedWidthOpenIndexPostWitnessStructuralPayloadPolynomial_le_fixed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthOpenIndexPostWitnessStructuralPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm <=
      fixedWidthOpenIndexPostWitnessFixedPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm :=
  (fixedWidthOpenIndexPostWitnessStructuralPayloadPolynomial_le_equalityExposed
    valuation tableTerm widthTerm indexTerm valueTerm).trans
      (fixedWidthOpenIndexPostWitnessEqualityExposedPayloadPolynomial_le_fixed
        valuation tableTerm widthTerm indexTerm valueTerm htable hwidth hindex
        hvalue)

def compactFixedWidthEntryAtValuationOpenIndexEqualityExposedPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let size := Nat.size (termValue valuation valueTerm)
  let body := compactFixedWidthEntryAtValuationWitnessBody
    tableTerm widthTerm indexTerm valueTerm
  hybridExistsWitnessStructuralPayloadEnvelope valuation body size
    (fixedWidthOpenIndexPostWitnessEqualityExposedPayloadPolynomial valuation
      tableTerm widthTerm indexTerm valueTerm)

theorem
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_equalityExposed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation tableTerm widthTerm indexTerm valueTerm <=
      compactFixedWidthEntryAtValuationOpenIndexEqualityExposedPayloadPolynomial
        valuation tableTerm widthTerm indexTerm valueTerm := by
  let size := Nat.size (termValue valuation valueTerm)
  let body := compactFixedWidthEntryAtValuationWitnessBody
    tableTerm widthTerm indexTerm valueTerm
  have hpost :=
    fixedWidthOpenIndexPostWitnessStructuralPayloadPolynomial_le_equalityExposed
      valuation tableTerm widthTerm indexTerm valueTerm
  simpa only [compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial,
    compactFixedWidthEntryAtValuationOpenIndexEqualityExposedPayloadPolynomial,
    size, body] using
      (hybridExistsWitnessStructuralPayloadEnvelope_mono_openIndex valuation
        body size hpost)

def compactFixedWidthEntryAtValuationOpenIndexFixedPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let size := Nat.size (termValue valuation valueTerm)
  let body := compactFixedWidthEntryAtValuationWitnessBody
    tableTerm widthTerm indexTerm valueTerm
  hybridExistsWitnessStructuralPayloadEnvelope valuation body size
    (fixedWidthOpenIndexPostWitnessFixedPayloadPolynomial valuation tableTerm
      widthTerm indexTerm valueTerm)

theorem
    compactFixedWidthEntryAtValuationOpenIndexEqualityExposedPayloadPolynomial_le_fixed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    compactFixedWidthEntryAtValuationOpenIndexEqualityExposedPayloadPolynomial
        valuation tableTerm widthTerm indexTerm valueTerm <=
      compactFixedWidthEntryAtValuationOpenIndexFixedPayloadPolynomial
        valuation tableTerm widthTerm indexTerm valueTerm := by
  let size := Nat.size (termValue valuation valueTerm)
  let body := compactFixedWidthEntryAtValuationWitnessBody
    tableTerm widthTerm indexTerm valueTerm
  have hpost :=
    fixedWidthOpenIndexPostWitnessEqualityExposedPayloadPolynomial_le_fixed
      valuation tableTerm widthTerm indexTerm valueTerm htable hwidth hindex
      hvalue
  simpa only [
    compactFixedWidthEntryAtValuationOpenIndexEqualityExposedPayloadPolynomial,
    compactFixedWidthEntryAtValuationOpenIndexFixedPayloadPolynomial, size,
    body] using
      (hybridExistsWitnessStructuralPayloadEnvelope_mono_openIndex valuation
        body size hpost)

theorem
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fixed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation tableTerm widthTerm indexTerm valueTerm <=
      compactFixedWidthEntryAtValuationOpenIndexFixedPayloadPolynomial
        valuation tableTerm widthTerm indexTerm valueTerm :=
  (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_equalityExposed
    valuation tableTerm widthTerm indexTerm valueTerm).trans
      (compactFixedWidthEntryAtValuationOpenIndexEqualityExposedPayloadPolynomial_le_fixed
        valuation tableTerm widthTerm indexTerm valueTerm htable hwidth hindex
        hvalue)

#print axioms fixedWidthBitPublicScale_le_openIndexCoordinateScale
#print axioms
  fixedWidthBitValuationContextNumericBound_le_openIndexCoordinateScale
#print axioms fixedWidthBitSourceIndexBound_le_openIndexPositionPolynomial
#print axioms fixedWidthBitSourcePayloadPolynomial_le_openIndexScalar
#print axioms
  fixedWidthBitValuationTermCodeUniformResource_le_openIndexScalar
#print axioms
  fixedWidthBitValuationContextFormulaCodeUniformResource_le_openIndexScalar
#print axioms
  fixedWidthBitLeafSmallContextSyntaxUniformResource_le_openIndexScalar
#print axioms
  fixedWidthBitLeafTermEqualityUniformPayloadBound_le_openIndexScalar
#print axioms fixedWidthBitLeafUniformPayloadPolynomial_le_openIndexScalar
#print axioms
  fixedWidthBitLeafAggregateUniformPayloadBound_le_openIndexScalar
#print axioms
  fixedWidthBitBranchesOpenIndexStructuralPayloadPolynomial_le_equalityExposed
#print axioms
  fixedWidthUniversalOpenIndexStructuralPayloadPolynomial_le_equalityExposed
#print axioms
  compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_equalityExposed
#print axioms
  fixedWidthOpenIndexLeafTermEqualityPayloadPolynomial_le_fixed
#print axioms fixedWidthOpenIndexLeafPayloadPolynomial_le_fixed
#print axioms
  compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fixed

end FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexScalarBounds
