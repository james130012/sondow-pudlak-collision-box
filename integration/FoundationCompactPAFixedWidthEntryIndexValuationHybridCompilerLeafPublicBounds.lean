import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerContextBounds
import integration.FoundationCompactPABitMembershipValuationCompilerPublicBounds
import integration.FoundationCompactPAValuationTermCompilerUniformBounds

/-!
# Public payload bound for one fixed-width bit leaf

The outer thirteen connectors and all four positive/negative bit-literal
compilers are charged to input-computable syntax resources here.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerLeafPublicBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationTermCompilerUniformBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitMembershipValuationContextCompiler
open FoundationCompactPABitMembershipValuationCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerContextBounds

def fixedWidthBitLeafPublicPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat) : Nat :=
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  compileBinaryBitLiteralAtValuationPayloadPolynomial true
      branchValuation leftIndexTerm leftValueTerm +
    compileBinaryBitLiteralAtValuationPayloadPolynomial false
      branchValuation leftIndexTerm leftValueTerm +
    compileBinaryBitLiteralAtValuationPayloadPolynomial true
      branchValuation rightIndexTerm rightValueTerm +
    compileBinaryBitLiteralAtValuationPayloadPolynomial false
      branchValuation rightIndexTerm rightValueTerm +
    13 * smallContextAssemblyEnvelope
      (fixedWidthBitLeafSmallContextSyntaxResource valuation tableTerm
        widthTerm indexTerm valueTerm bitIndex)

theorem fixedWidthBitLeafUniformStructuralEnvelope_le_publicPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthBitLeafUniformStructuralEnvelope valuation tableTerm widthTerm
        indexTerm valueTerm bitIndex <=
      fixedWidthBitLeafPublicPayloadPolynomial valuation tableTerm widthTerm
        indexTerm valueTerm bitIndex := by
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  have hterms := fixedWidthBitTerms_freeVariables_of_closed
    tableTerm widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  have hleftIndexVars : leftIndexTerm.freeVariables ⊆ {0} := by
    rw [hterms.1]
  have hleftValueVars : leftValueTerm.freeVariables ⊆ {0} := by
    rw [hterms.2.1]
    simp
  have hrightIndexVars : rightIndexTerm.freeVariables ⊆ {0} := by
    rw [hterms.2.2.1]
  have hrightValueVars : rightValueTerm.freeVariables ⊆ {0} := by
    rw [hterms.2.2.2]
    simp
  have houter :=
    fixedWidthBitLeafUniformStructuralEnvelope_le_smallContext_of_closed
      valuation tableTerm widthTerm indexTerm valueTerm bitIndex
      htable hwidth hindex hvalue
  have hleftTrue :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial
      true branchValuation leftIndexTerm leftValueTerm
      hleftIndexVars hleftValueVars
  have hleftFalse :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial
      false branchValuation leftIndexTerm leftValueTerm
      hleftIndexVars hleftValueVars
  have hrightTrue :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial
      true branchValuation rightIndexTerm rightValueTerm
      hrightIndexVars hrightValueVars
  have hrightFalse :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial
      false branchValuation rightIndexTerm rightValueTerm
      hrightIndexVars hrightValueVars
  unfold fixedWidthBitLeafSmallContextPayloadEnvelope at houter
  unfold fixedWidthBitLeafPublicPayloadPolynomial
  dsimp only [branchValuation, leftIndexTerm, leftValueTerm,
    rightIndexTerm, rightValueTerm] at *
  omega

theorem fixedWidthBitLeafUniformStructuralEnvelope_le_publicPolynomial_of_openIndex
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthBitLeafUniformStructuralEnvelope valuation tableTerm widthTerm
        indexTerm valueTerm bitIndex <=
      fixedWidthBitLeafPublicPayloadPolynomial valuation tableTerm widthTerm
        indexTerm valueTerm bitIndex := by
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  have htermCards := fixedWidthBitTermUnionCards_of_openIndex
    tableTerm widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  have houter :=
    fixedWidthBitLeafUniformStructuralEnvelope_le_smallContext_of_openIndex
      valuation tableTerm widthTerm indexTerm valueTerm bitIndex
      htable hwidth hindex hvalue
  have hleftTrue :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial_of_card
      true branchValuation leftIndexTerm leftValueTerm htermCards.1
  have hleftFalse :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial_of_card
      false branchValuation leftIndexTerm leftValueTerm htermCards.1
  have hrightTrue :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial_of_card
      true branchValuation rightIndexTerm rightValueTerm htermCards.2
  have hrightFalse :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial_of_card
      false branchValuation rightIndexTerm rightValueTerm htermCards.2
  unfold fixedWidthBitLeafSmallContextPayloadEnvelope at houter
  unfold fixedWidthBitLeafPublicPayloadPolynomial
  dsimp only [branchValuation, leftIndexTerm, leftValueTerm,
    rightIndexTerm, rightValueTerm] at *
  omega

def fixedWidthBitLeafSourceBoundedPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat) : Nat :=
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  4 * fixedWidthBitSourcePayloadPolynomial valuation tableTerm widthTerm
      indexTerm valueTerm +
    compileBinaryBitLiteralAtValuationConnectorPolynomial true
      branchValuation leftIndexTerm leftValueTerm +
    compileBinaryBitLiteralAtValuationConnectorPolynomial false
      branchValuation leftIndexTerm leftValueTerm +
    compileBinaryBitLiteralAtValuationConnectorPolynomial true
      branchValuation rightIndexTerm rightValueTerm +
    compileBinaryBitLiteralAtValuationConnectorPolynomial false
      branchValuation rightIndexTerm rightValueTerm +
    13 * smallContextAssemblyEnvelope
      (fixedWidthBitLeafSmallContextSyntaxResource valuation tableTerm
        widthTerm indexTerm valueTerm bitIndex)

theorem
    fixedWidthBitLeafUniformStructuralEnvelope_le_sourceBoundedPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅)
    (hbitIndex : bitIndex < termValue valuation widthTerm) :
    fixedWidthBitLeafUniformStructuralEnvelope valuation tableTerm widthTerm
        indexTerm valueTerm bitIndex <=
      fixedWidthBitLeafSourceBoundedPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm bitIndex := by
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  let sourceBound := fixedWidthBitSourcePayloadPolynomial valuation
    tableTerm widthTerm indexTerm valueTerm
  have hterms := fixedWidthBitTerms_freeVariables_of_closed
    tableTerm widthTerm indexTerm valueTerm htable hwidth hindexClosed hvalue
  have hleftIndexVars : leftIndexTerm.freeVariables ⊆ {0} := by
    rw [hterms.1]
  have hleftValueVars : leftValueTerm.freeVariables ⊆ {0} := by
    rw [hterms.2.1]
    simp
  have hrightIndexVars : rightIndexTerm.freeVariables ⊆ {0} := by
    rw [hterms.2.2.1]
  have hrightValueVars : rightValueTerm.freeVariables ⊆ {0} := by
    rw [hterms.2.2.2]
    simp
  have hleftSource := fixedWidthLeftBitSourcePayload_le_publicPolynomial
    valuation tableTerm widthTerm indexTerm valueTerm bitIndex hbitIndex
  have hrightSource := fixedWidthRightBitSourcePayload_le_publicPolynomial
    valuation tableTerm widthTerm indexTerm valueTerm bitIndex hbitIndex
  have hleftTrue :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_sourceBound
      true branchValuation leftIndexTerm leftValueTerm sourceBound
      hleftIndexVars hleftValueVars hleftSource
  have hleftFalse :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_sourceBound
      false branchValuation leftIndexTerm leftValueTerm sourceBound
      hleftIndexVars hleftValueVars hleftSource
  have hrightTrue :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_sourceBound
      true branchValuation rightIndexTerm rightValueTerm sourceBound
      hrightIndexVars hrightValueVars hrightSource
  have hrightFalse :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_sourceBound
      false branchValuation rightIndexTerm rightValueTerm sourceBound
      hrightIndexVars hrightValueVars hrightSource
  have houter :=
    fixedWidthBitLeafUniformStructuralEnvelope_le_smallContext_of_closed
      valuation tableTerm widthTerm indexTerm valueTerm bitIndex
      htable hwidth hindexClosed hvalue
  unfold fixedWidthBitLeafSmallContextPayloadEnvelope at houter
  unfold fixedWidthBitLeafSourceBoundedPayloadPolynomial
  dsimp only [branchValuation, leftIndexTerm, leftValueTerm,
    rightIndexTerm, rightValueTerm, sourceBound] at *
  omega

theorem
    fixedWidthBitLeafUniformStructuralEnvelope_le_sourceBoundedPolynomial_of_openIndex
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅)
    (hbitIndex : bitIndex < termValue valuation widthTerm) :
    fixedWidthBitLeafUniformStructuralEnvelope valuation tableTerm widthTerm
        indexTerm valueTerm bitIndex <=
      fixedWidthBitLeafSourceBoundedPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm bitIndex := by
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  let sourceBound := fixedWidthBitSourcePayloadPolynomial valuation
    tableTerm widthTerm indexTerm valueTerm
  have htermCards := fixedWidthBitTermUnionCards_of_openIndex
    tableTerm widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  have hleftSource := fixedWidthLeftBitSourcePayload_le_publicPolynomial
    valuation tableTerm widthTerm indexTerm valueTerm bitIndex hbitIndex
  have hrightSource := fixedWidthRightBitSourcePayload_le_publicPolynomial
    valuation tableTerm widthTerm indexTerm valueTerm bitIndex hbitIndex
  have hleftTrue :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_sourceBound_of_card
      true branchValuation leftIndexTerm leftValueTerm sourceBound
      htermCards.1 hleftSource
  have hleftFalse :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_sourceBound_of_card
      false branchValuation leftIndexTerm leftValueTerm sourceBound
      htermCards.1 hleftSource
  have hrightTrue :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_sourceBound_of_card
      true branchValuation rightIndexTerm rightValueTerm sourceBound
      htermCards.2 hrightSource
  have hrightFalse :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_sourceBound_of_card
      false branchValuation rightIndexTerm rightValueTerm sourceBound
      htermCards.2 hrightSource
  have houter :=
    fixedWidthBitLeafUniformStructuralEnvelope_le_smallContext_of_openIndex
      valuation tableTerm widthTerm indexTerm valueTerm bitIndex
      htable hwidth hindex hvalue
  unfold fixedWidthBitLeafSmallContextPayloadEnvelope at houter
  unfold fixedWidthBitLeafSourceBoundedPayloadPolynomial
  dsimp only [branchValuation, leftIndexTerm, leftValueTerm,
    rightIndexTerm, rightValueTerm, sourceBound] at *
  omega

/-! ## Uniform term-code coordinate across all bit positions -/

/-- One input-computable term-code coordinate for both bit literals in every
branch position below the fixed width.  The only numeric dependence is the
already public branch scale; no proof payload enters this definition. -/
def fixedWidthBitValuationTermCodeUniformResource
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let scale := fixedWidthBitPublicScale valuation tableTerm widthTerm
    indexTerm valueTerm
  let numeralCodeBound :=
    FoundationCompactPABinaryNumeralAdditionBounds.binaryNumeralTermCodeEnvelope
      scale
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  2 * numeralCodeBound +
    (binaryTermCode leftIndexTerm).length +
    (binaryTermCode leftValueTerm).length +
    (binaryTermCode rightIndexTerm).length +
    (binaryTermCode rightValueTerm).length + 1

theorem fixedWidthBitValuationTermCodeResources_le_uniform
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (hbitIndex : bitIndex < termValue valuation widthTerm) :
    let branchValuation := extendValuation bitIndex valuation
    let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
    let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
    let rightIndexTerm := fixedWidthRightBitIndexTerm
    let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
    binaryBitValuationTermCodeResource branchValuation
        leftIndexTerm leftValueTerm <=
          fixedWidthBitValuationTermCodeUniformResource valuation tableTerm
            widthTerm indexTerm valueTerm ∧
      binaryBitValuationTermCodeResource branchValuation
        rightIndexTerm rightValueTerm <=
          fixedWidthBitValuationTermCodeUniformResource valuation tableTerm
            widthTerm indexTerm valueTerm := by
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  let scale := fixedWidthBitPublicScale valuation tableTerm widthTerm
    indexTerm valueTerm
  let numeralCodeBound :=
    FoundationCompactPABinaryNumeralAdditionBounds.binaryNumeralTermCodeEnvelope
      scale
  have hvalues := fixedWidthBitTermValues_size_le_publicScale
    valuation tableTerm widthTerm indexTerm valueTerm bitIndex hbitIndex
  have hleftIndexNumeral :=
    FoundationCompactPABinaryNumeralAdditionBounds.binaryNumeralTerm_code_length_le_envelope
      (termValue branchValuation leftIndexTerm) scale hvalues.1
  have hleftValueNumeral :=
    FoundationCompactPABinaryNumeralAdditionBounds.binaryNumeralTerm_code_length_le_envelope
      (termValue branchValuation leftValueTerm) scale hvalues.2.1
  have hrightIndexNumeral :=
    FoundationCompactPABinaryNumeralAdditionBounds.binaryNumeralTerm_code_length_le_envelope
      (termValue branchValuation rightIndexTerm) scale hvalues.2.2.1
  have hrightValueNumeral :=
    FoundationCompactPABinaryNumeralAdditionBounds.binaryNumeralTerm_code_length_le_envelope
      (termValue branchValuation rightValueTerm) scale hvalues.2.2.2
  unfold binaryBitValuationTermCodeResource
    fixedWidthBitValuationTermCodeUniformResource
  dsimp only [branchValuation, leftIndexTerm, leftValueTerm,
    rightIndexTerm, rightValueTerm, scale, numeralCodeBound] at *
  constructor <;> omega

/-- Numeric coordinate for every valuation assumption in an open-index bit
leaf.  Variable `0` is the bit position and variable `1` is the outer row
index, so their unary codes are bounded directly by this sum. -/
def fixedWidthBitValuationContextNumericBound
    (valuation : Nat -> Nat) (widthTerm : ValuationTerm) : Nat :=
  termValue valuation widthTerm + valuation 0 + 1

/-- Both possible free-variable terms (`0` and `1`) fit this fixed syntax
coordinate. -/
def fixedWidthBitVariableTermCodeBound : Nat :=
  (binaryTermCode (&0 : ValuationTerm)).length +
    (binaryTermCode (&1 : ValuationTerm)).length + 1

def fixedWidthBitValuationContextFormulaCodeUniformResource
    (valuation : Nat -> Nat) (widthTerm : ValuationTerm) : Nat :=
  FoundationCompactPAValuationTermCompilerPublicBounds.valuationContextFormulaCodeSumEnvelope
    2 (fixedWidthBitValuationContextNumericBound valuation widthTerm)
      fixedWidthBitVariableTermCodeBound

theorem fixedWidthBitValuationContext_formulaCodeSum_le_uniform
    (valuation : Nat -> Nat) (widthTerm : ValuationTerm)
    (vars : Finset Nat) (bitIndex : Nat)
    (hvars : vars ⊆ ({0, 1} : Finset Nat))
    (hbitIndex : bitIndex < termValue valuation widthTerm) :
    FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum
        (valuationContext vars (extendValuation bitIndex valuation)) <=
      fixedWidthBitValuationContextFormulaCodeUniformResource valuation
        widthTerm := by
  let branchValuation := extendValuation bitIndex valuation
  let numericBound :=
    fixedWidthBitValuationContextNumericBound valuation widthTerm
  have hcardRaw := Finset.card_le_card hvars
  have hcard : vars.card <= 2 := by
    norm_num at hcardRaw ⊢
    exact hcardRaw
  have hvalues : forall index, index ∈ vars ->
      branchValuation index <= numericBound := by
    intro index hindex
    have hpair := hvars hindex
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
    rcases hpair with rfl | rfl
    · simp only [branchValuation, numericBound,
        fixedWidthBitValuationContextNumericBound, extendValuation_zero]
      omega
    · simp only [branchValuation, numericBound,
        fixedWidthBitValuationContextNumericBound, extendValuation_succ]
      omega
  have hvariables : forall index, index ∈ vars ->
      (binaryTermCode (&index : ValuationTerm)).length <=
        fixedWidthBitVariableTermCodeBound := by
    intro index hindex
    have hpair := hvars hindex
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
    rcases hpair with rfl | rfl <;>
      unfold fixedWidthBitVariableTermCodeBound <;> omega
  have hbound :=
    FoundationCompactPAValuationTermCompilerPublicBounds.valuationContext_formulaCodeSum_le_uniform
      vars branchValuation 2 numericBound fixedWidthBitVariableTermCodeBound
      hcard hvalues hvariables
  unfold fixedWidthBitValuationContextFormulaCodeUniformResource
  simpa only [branchValuation, numericBound] using hbound

theorem fixedWidthBitLiteralContextFormulaCodeSums_le_uniform_of_openIndex
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅)
    (hbitIndex : bitIndex < termValue valuation widthTerm) :
    let branchValuation := extendValuation bitIndex valuation
    let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
    let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
    let rightIndexTerm := fixedWidthRightBitIndexTerm
    let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
    FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum
        (binaryBitValuationContext branchValuation
          leftIndexTerm leftValueTerm) <=
          fixedWidthBitValuationContextFormulaCodeUniformResource valuation
            widthTerm ∧
      FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum
        (binaryBitValuationContext branchValuation
          rightIndexTerm rightValueTerm) <=
          fixedWidthBitValuationContextFormulaCodeUniformResource valuation
            widthTerm := by
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  have hterms := fixedWidthBitTerms_freeVariables_of_openIndex
    tableTerm widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  have hleftVars : leftIndexTerm.freeVariables ∪ leftValueTerm.freeVariables ⊆
      ({0, 1} : Finset Nat) := by
    exact Finset.union_subset hterms.1 (by rw [hterms.2.1]; simp)
  have hrightVars :
      rightIndexTerm.freeVariables ∪ rightValueTerm.freeVariables ⊆
        ({0, 1} : Finset Nat) := by
    rw [hterms.2.2.1, hterms.2.2.2]
    simp
  constructor
  · unfold binaryBitValuationContext
    exact fixedWidthBitValuationContext_formulaCodeSum_le_uniform
      valuation widthTerm
      (leftIndexTerm.freeVariables ∪ leftValueTerm.freeVariables)
      bitIndex hleftVars hbitIndex
  · unfold binaryBitValuationContext
    exact fixedWidthBitValuationContext_formulaCodeSum_le_uniform
      valuation widthTerm
      (rightIndexTerm.freeVariables ∪ rightValueTerm.freeVariables)
      bitIndex hrightVars hbitIndex

def fixedWidthBitLeafSmallContextSyntaxUniformResource
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let contextBound :=
    fixedWidthBitValuationContextFormulaCodeUniformResource valuation
      widthTerm
  let termBound :=
    fixedWidthBitValuationTermCodeUniformResource valuation tableTerm
      widthTerm indexTerm valueTerm
  let formulaBound :=
    binaryBitValuationFormulaClosureCodeEnvelope termBound
  7 * contextBound + 9 * formulaBound + 1

theorem
    fixedWidthBitLeafSmallContextSyntaxResource_le_uniform_of_openIndex
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅)
    (hbitIndex : bitIndex < termValue valuation widthTerm) :
    fixedWidthBitLeafSmallContextSyntaxResource valuation tableTerm widthTerm
        indexTerm valueTerm bitIndex <=
      fixedWidthBitLeafSmallContextSyntaxUniformResource valuation tableTerm
        widthTerm indexTerm valueTerm := by
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  let leftAtom := binaryBitAtomAtTerms leftIndexTerm leftValueTerm
  let rightAtom := binaryBitAtomAtTerms rightIndexTerm rightValueTerm
  let leftTrue := binaryBitAtValuationFormula true
    leftIndexTerm leftValueTerm
  let leftFalse := binaryBitAtValuationFormula false
    leftIndexTerm leftValueTerm
  let rightTrue := binaryBitAtValuationFormula true
    rightIndexTerm rightValueTerm
  let rightFalse := binaryBitAtValuationFormula false
    rightIndexTerm rightValueTerm
  let forward := (∼leftAtom ⋎ rightAtom)
  let backward := (∼rightAtom ⋎ leftAtom)
  let target := forward ⋏ backward
  let contextBound :=
    fixedWidthBitValuationContextFormulaCodeUniformResource valuation
      widthTerm
  let termBound :=
    fixedWidthBitValuationTermCodeUniformResource valuation tableTerm
      widthTerm indexTerm valueTerm
  let baseBound := binaryBitValuationFormulaBaseCodeEnvelope termBound
  let stageOneBound :=
    binaryBitValuationFormulaStageOneCodeEnvelope termBound
  let formulaBound :=
    binaryBitValuationFormulaClosureCodeEnvelope termBound
  have hterms := fixedWidthBitTerms_freeVariables_of_openIndex
    tableTerm widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  have hleftTerms :
      leftIndexTerm.freeVariables ∪ leftValueTerm.freeVariables ⊆
        ({0, 1} : Finset Nat) := by
    exact Finset.union_subset hterms.1 (by rw [hterms.2.1]; simp)
  have hrightTerms :
      rightIndexTerm.freeVariables ∪ rightValueTerm.freeVariables ⊆
        ({0, 1} : Finset Nat) := by
    rw [hterms.2.2.1, hterms.2.2.2]
    simp
  have htermResources :=
    fixedWidthBitValuationTermCodeResources_le_uniform
      valuation tableTerm widthTerm indexTerm valueTerm bitIndex hbitIndex
  dsimp only [branchValuation, leftIndexTerm, leftValueTerm,
    rightIndexTerm, rightValueTerm] at htermResources
  have hleftCodes := binaryBitValuationTermCodes_le_resource
    branchValuation leftIndexTerm leftValueTerm
  have hrightCodes := binaryBitValuationTermCodes_le_resource
    branchValuation rightIndexTerm rightValueTerm
  have hleftShortIndex := hleftCodes.1.trans htermResources.1
  have hleftIndex := hleftCodes.2.1.trans htermResources.1
  have hleftShortValue := hleftCodes.2.2.1.trans htermResources.1
  have hleftValue := hleftCodes.2.2.2.trans htermResources.1
  have hrightShortIndex := hrightCodes.1.trans htermResources.2
  have hrightIndex := hrightCodes.2.1.trans htermResources.2
  have hrightShortValue := hrightCodes.2.2.1.trans htermResources.2
  have hrightValue := hrightCodes.2.2.2.trans htermResources.2
  have hleftAtomBase :
      (binaryFormulaCode leftAtom).length <= baseBound := by
    have hraw := binaryBitAtomAtTerms_code_length_le_uniform
      leftIndexTerm leftValueTerm termBound hleftIndex hleftValue
    unfold baseBound binaryBitValuationFormulaBaseCodeEnvelope
    exact hraw.trans (by omega)
  have hrightAtomBase :
      (binaryFormulaCode rightAtom).length <= baseBound := by
    have hraw := binaryBitAtomAtTerms_code_length_le_uniform
      rightIndexTerm rightValueTerm termBound hrightIndex hrightValue
    unfold baseBound binaryBitValuationFormulaBaseCodeEnvelope
    exact hraw.trans (by omega)
  have hleftTrueBase :
      (binaryFormulaCode leftTrue).length <= baseBound := by
    have hraw := binaryBitLiteralAtTerms_code_length_le_uniform true
      leftIndexTerm leftValueTerm termBound hleftIndex hleftValue
    unfold leftTrue binaryBitAtValuationFormula
      baseBound binaryBitValuationFormulaBaseCodeEnvelope
    exact hraw.trans (by omega)
  have hleftFalseBase :
      (binaryFormulaCode leftFalse).length <= baseBound := by
    have hraw := binaryBitLiteralAtTerms_code_length_le_uniform false
      leftIndexTerm leftValueTerm termBound hleftIndex hleftValue
    unfold leftFalse binaryBitAtValuationFormula
      baseBound binaryBitValuationFormulaBaseCodeEnvelope
    exact hraw.trans (by omega)
  have hrightTrueBase :
      (binaryFormulaCode rightTrue).length <= baseBound := by
    have hraw := binaryBitLiteralAtTerms_code_length_le_uniform true
      rightIndexTerm rightValueTerm termBound hrightIndex hrightValue
    unfold rightTrue binaryBitAtValuationFormula
      baseBound binaryBitValuationFormulaBaseCodeEnvelope
    exact hraw.trans (by omega)
  have hrightFalseBase :
      (binaryFormulaCode rightFalse).length <= baseBound := by
    have hraw := binaryBitLiteralAtTerms_code_length_le_uniform false
      rightIndexTerm rightValueTerm termBound hrightIndex hrightValue
    unfold rightFalse binaryBitAtValuationFormula
      baseBound binaryBitValuationFormulaBaseCodeEnvelope
    exact hraw.trans (by omega)
  have hforwardStage :
      (binaryFormulaCode forward).length <= stageOneBound := by
    have hraw := binaryBitValuation_implication_base_code_le_stageOne
      leftAtom rightAtom termBound hleftAtomBase hrightAtomBase
    simpa only [forward, DeMorgan.imply, stageOneBound] using hraw
  have hbackwardStage :
      (binaryFormulaCode backward).length <= stageOneBound := by
    have hraw := binaryBitValuation_implication_base_code_le_stageOne
      rightAtom leftAtom termBound hrightAtomBase hleftAtomBase
    simpa only [backward, DeMorgan.imply, stageOneBound] using hraw
  have htargetStageTwo :
      (binaryFormulaCode target).length <=
        binaryBitValuationFormulaStageTwoCodeEnvelope termBound := by
    have hraw :=
      FoundationCompactPABinaryNumeralAdditionBounds.binaryFormulaCode_and_length_le_local
        forward backward
    unfold target binaryBitValuationFormulaStageTwoCodeEnvelope
      stageOneBound binaryBitValuationFormulaStageOneCodeEnvelope at *
    omega
  have hbaseClosure := binaryBitValuation_base_le_closure termBound
  have hstageTwoClosure :=
    binaryBitValuation_stageTwo_le_closure termBound
  have hleftAtomClosure :
      (binaryFormulaCode leftAtom).length <= formulaBound :=
    hleftAtomBase.trans (by simpa only [baseBound, formulaBound] using
      hbaseClosure)
  have hrightAtomClosure :
      (binaryFormulaCode rightAtom).length <= formulaBound :=
    hrightAtomBase.trans (by simpa only [baseBound, formulaBound] using
      hbaseClosure)
  have hleftTrueClosure :
      (binaryFormulaCode leftTrue).length <= formulaBound :=
    hleftTrueBase.trans (by simpa only [baseBound, formulaBound] using
      hbaseClosure)
  have hleftFalseClosure :
      (binaryFormulaCode leftFalse).length <= formulaBound :=
    hleftFalseBase.trans (by simpa only [baseBound, formulaBound] using
      hbaseClosure)
  have hrightTrueClosure :
      (binaryFormulaCode rightTrue).length <= formulaBound :=
    hrightTrueBase.trans (by simpa only [baseBound, formulaBound] using
      hbaseClosure)
  have hrightFalseClosure :
      (binaryFormulaCode rightFalse).length <= formulaBound :=
    hrightFalseBase.trans (by simpa only [baseBound, formulaBound] using
      hbaseClosure)
  have hforwardClosure :
      (binaryFormulaCode forward).length <= formulaBound := by
    exact hforwardStage.trans (by
      unfold stageOneBound formulaBound
        binaryBitValuationFormulaClosureCodeEnvelope
        binaryBitValuationFormulaStageTwoCodeEnvelope
      omega)
  have hbackwardClosure :
      (binaryFormulaCode backward).length <= formulaBound := by
    exact hbackwardStage.trans (by
      unfold stageOneBound formulaBound
        binaryBitValuationFormulaClosureCodeEnvelope
        binaryBitValuationFormulaStageTwoCodeEnvelope
      omega)
  have htargetClosure :
      (binaryFormulaCode target).length <= formulaBound :=
    htargetStageTwo.trans (by simpa only [formulaBound] using
      hstageTwoClosure)
  have hleftTrueVars :=
    (binaryBitAtValuationFormula_freeVariables_subset
      true leftIndexTerm leftValueTerm).trans hleftTerms
  have hleftFalseVars :=
    (binaryBitAtValuationFormula_freeVariables_subset
      false leftIndexTerm leftValueTerm).trans hleftTerms
  have hrightTrueVars :=
    (binaryBitAtValuationFormula_freeVariables_subset
      true rightIndexTerm rightValueTerm).trans hrightTerms
  have hrightFalseVars :=
    (binaryBitAtValuationFormula_freeVariables_subset
      false rightIndexTerm rightValueTerm).trans hrightTerms
  have hleftAtomVars :
      leftAtom.freeVariables ⊆ ({0, 1} : Finset Nat) := by
    simpa [leftAtom, leftTrue, binaryBitAtValuationFormula,
      binaryBitLiteralAtTerms] using hleftTrueVars
  have hrightAtomVars :
      rightAtom.freeVariables ⊆ ({0, 1} : Finset Nat) := by
    simpa [rightAtom, rightTrue, binaryBitAtValuationFormula,
      binaryBitLiteralAtTerms] using hrightTrueVars
  have hforwardVars :
      forward.freeVariables ⊆ ({0, 1} : Finset Nat) := by
    simpa [forward] using
      (Finset.union_subset hleftAtomVars hrightAtomVars)
  have hbackwardVars :
      backward.freeVariables ⊆ ({0, 1} : Finset Nat) := by
    simpa [backward] using
      (Finset.union_subset hrightAtomVars hleftAtomVars)
  have htargetVars :
      target.freeVariables ⊆ ({0, 1} : Finset Nat) := by
    simpa [target] using
      (Finset.union_subset hforwardVars hbackwardVars)
  have hcontextSum (vars : Finset Nat)
      (hvars : vars ⊆ ({0, 1} : Finset Nat)) :
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerContextBounds.formulaCodeSum
          (valuationContext vars branchValuation) <= contextBound := by
    have hraw := fixedWidthBitValuationContext_formulaCodeSum_le_uniform
      valuation widthTerm vars bitIndex hvars hbitIndex
    simpa only [
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerContextBounds.formulaCodeSum,
      FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum,
      contextBound] using hraw
  have hleftTrueContext := hcontextSum leftTrue.freeVariables hleftTrueVars
  have hleftFalseContext :=
    hcontextSum leftFalse.freeVariables hleftFalseVars
  have hrightTrueContext :=
    hcontextSum rightTrue.freeVariables hrightTrueVars
  have hrightFalseContext :=
    hcontextSum rightFalse.freeVariables hrightFalseVars
  have hforwardContext := hcontextSum forward.freeVariables hforwardVars
  have hbackwardContext := hcontextSum backward.freeVariables hbackwardVars
  have htargetContext := hcontextSum target.freeVariables htargetVars
  unfold fixedWidthBitLeafSmallContextSyntaxResource
    fixedWidthBitLeafSmallContextSyntaxUniformResource
  dsimp only [branchValuation, leftIndexTerm, leftValueTerm,
    rightIndexTerm, rightValueTerm, leftAtom, rightAtom, leftTrue,
    leftFalse, rightTrue, rightFalse, forward, backward, target,
    contextBound, termBound, formulaBound] at *
  omega

/-! ## Isolating the remaining term-equality coordinate -/

def fixedWidthBitTermEqualityNumericBound
    (valuation : Nat -> Nat) (widthTerm : ValuationTerm) : Nat :=
  fixedWidthBitValuationContextNumericBound valuation widthTerm

def fixedWidthBitTermEqualityTermCodeUniformResource
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let numericBound := fixedWidthBitTermEqualityNumericBound valuation widthTerm
  fixedWidthBitValuationTermCodeUniformResource valuation tableTerm widthTerm
      indexTerm valueTerm +
    FoundationCompactPAFiniteExhaustionPolynomialBounds.iteratedSuccessorTermCodePolynomial
      0 numericBound + 1

def fixedWidthRightBitIndexTermEqualityUniformPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  valuationFvarTermEqualityUniformPayloadPolynomial
    (fixedWidthBitTermEqualityNumericBound valuation widthTerm)
    (fixedWidthBitValuationContextFormulaCodeUniformResource valuation
      widthTerm)
    (fixedWidthBitTermEqualityTermCodeUniformResource valuation tableTerm
      widthTerm indexTerm valueTerm)

theorem
    fixedWidthRightBitIndexTermEqualityPayloadPolynomial_le_uniform
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (hbitIndex : bitIndex < termValue valuation widthTerm) :
    compileTermValueEqualityPayloadPolynomial
        (extendValuation bitIndex valuation) fixedWidthRightBitIndexTerm <=
      fixedWidthRightBitIndexTermEqualityUniformPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm := by
  let branchValuation := extendValuation bitIndex valuation
  let numericBound := fixedWidthBitTermEqualityNumericBound valuation widthTerm
  let contextBound :=
    fixedWidthBitValuationContextFormulaCodeUniformResource valuation
      widthTerm
  let bitTermBound :=
    fixedWidthBitValuationTermCodeUniformResource valuation tableTerm
      widthTerm indexTerm valueTerm
  let termBound :=
    fixedWidthBitTermEqualityTermCodeUniformResource valuation tableTerm
      widthTerm indexTerm valueTerm
  have hnumeric : branchValuation 0 <= numericBound := by
    simp only [branchValuation, numericBound,
      fixedWidthBitTermEqualityNumericBound,
      fixedWidthBitValuationContextNumericBound, extendValuation_zero]
    omega
  have hcontext :
      FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum
      (valuationContext ({0} : Finset Nat) branchValuation) <=
        contextBound := by
    exact fixedWidthBitValuationContext_formulaCodeSum_le_uniform
      valuation widthTerm ({0} : Finset Nat) bitIndex (by simp) hbitIndex
  have hresources := fixedWidthBitValuationTermCodeResources_le_uniform
    valuation tableTerm widthTerm indexTerm valueTerm bitIndex hbitIndex
  rcases binaryBitValuationTermCodes_le_resource branchValuation
      fixedWidthRightBitIndexTerm (fixedWidthRightBitValueTerm valueTerm) with
    ⟨hshortRaw, hvariableRaw, _hshortValueRaw, _hvalueRaw⟩
  have hbitToTerm : bitTermBound <= termBound := by
    unfold bitTermBound termBound
      fixedWidthBitTermEqualityTermCodeUniformResource
    dsimp only [numericBound]
    omega
  have hshort := hshortRaw.trans (hresources.2.trans hbitToTerm)
  have hvariable := hvariableRaw.trans (hresources.2.trans hbitToTerm)
  have hiteratedRaw :=
    FoundationCompactPAFiniteExhaustionPolynomialBounds.iteratedSuccessorTerm_code_length_le_polynomial
      0 (branchValuation 0)
  have hiteratedMono :=
    FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds.iteratedSuccessorTermCodePolynomial_mono
      0 hnumeric
  have hiterated :
      (binaryTermCode
        (iteratedSuccessorTerm 0 (branchValuation 0))).length <= termBound := by
    have hcode := hiteratedRaw.trans hiteratedMono
    unfold termBound fixedWidthBitTermEqualityTermCodeUniformResource
    dsimp only [numericBound] at hcode ⊢
    omega
  unfold fixedWidthRightBitIndexTermEqualityUniformPayloadPolynomial
    fixedWidthRightBitIndexTerm
  exact compileTermValueEqualityPayloadPolynomial_fvar_le_uniform
    branchValuation 0 numericBound contextBound termBound hnumeric hcontext
    hshort hiterated hvariable

/-- Exact sum of the four term-equality compiler coordinates in one bit leaf.
Every other connector coordinate has already been made independent of the bit
position. -/
def fixedWidthBitLeafTermEqualityPayloadBound
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat) : Nat :=
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  compileTermValueEqualityPayloadPolynomial branchValuation leftIndexTerm +
    compileTermValueEqualityPayloadPolynomial branchValuation leftValueTerm +
    compileTermValueEqualityPayloadPolynomial branchValuation rightIndexTerm +
    compileTermValueEqualityPayloadPolynomial branchValuation rightValueTerm + 1

def fixedWidthBitLeafTermEqualityUniformPayloadBound
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let numericBound := fixedWidthBitTermEqualityNumericBound valuation widthTerm
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  compileTermValueEqualityUniformPayloadPolynomial numericBound leftIndexTerm +
    compileTermValueEqualityUniformPayloadPolynomial numericBound leftValueTerm +
    compileTermValueEqualityUniformPayloadPolynomial numericBound rightIndexTerm +
    compileTermValueEqualityUniformPayloadPolynomial numericBound rightValueTerm + 1

theorem fixedWidthBitLeafTermEqualityPayloadBound_le_uniform
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅)
    (hbitIndex : bitIndex < termValue valuation widthTerm) :
    fixedWidthBitLeafTermEqualityPayloadBound valuation tableTerm widthTerm
        indexTerm valueTerm bitIndex <=
      fixedWidthBitLeafTermEqualityUniformPayloadBound valuation tableTerm
        widthTerm indexTerm valueTerm := by
  let branchValuation := extendValuation bitIndex valuation
  let numericBound := fixedWidthBitTermEqualityNumericBound valuation widthTerm
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  have hterms := fixedWidthBitTerms_freeVariables_of_openIndex tableTerm
    widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  have hbranchBound : forall index, index ∈ ({0, 1} : Finset Nat) ->
      branchValuation index <= numericBound := by
    intro index hmember
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmember
    rcases hmember with rfl | rfl
    · simp only [branchValuation, numericBound,
        fixedWidthBitTermEqualityNumericBound,
        fixedWidthBitValuationContextNumericBound, extendValuation_zero]
      omega
    · simp only [branchValuation, numericBound,
        fixedWidthBitTermEqualityNumericBound,
        fixedWidthBitValuationContextNumericBound, extendValuation_succ]
      omega
  have hcompile : forall term : ValuationTerm,
      term.freeVariables ⊆ ({0, 1} : Finset Nat) ->
      compileTermValueEqualityPayloadPolynomial branchValuation term <=
        compileTermValueEqualityUniformPayloadPolynomial numericBound term := by
    intro term hsubset
    apply compileTermValueEqualityPayloadPolynomial_le_coordinate
    · have hcard := Finset.card_le_card hsubset
      norm_num at hcard ⊢
      omega
    · intro index hmember
      exact hbranchBound index (hsubset hmember)
  have hleftIndex := hcompile leftIndexTerm hterms.1
  have hleftValue := hcompile leftValueTerm (by
    rw [hterms.2.1]
    simp)
  have hrightIndex := hcompile rightIndexTerm (by
    rw [hterms.2.2.1]
    simp)
  have hrightValue := hcompile rightValueTerm (by
    rw [hterms.2.2.2]
    simp)
  unfold fixedWidthBitLeafTermEqualityPayloadBound
    fixedWidthBitLeafTermEqualityUniformPayloadBound
  dsimp only [branchValuation, numericBound, leftIndexTerm, leftValueTerm,
    rightIndexTerm, rightValueTerm] at *
  omega

/-- All non-equality work in a bit leaf is now charged to bit-position-free
coordinates.  The exact equality sum remains visible so this endpoint cannot
be mistaken for the final closed polynomial. -/
def fixedWidthBitLeafEqualityIsolatedPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat) : Nat :=
  let contextBound :=
    fixedWidthBitValuationContextFormulaCodeUniformResource valuation
      widthTerm
  let termBound :=
    fixedWidthBitValuationTermCodeUniformResource valuation tableTerm
      widthTerm indexTerm valueTerm
  let equalityBound :=
    fixedWidthBitLeafTermEqualityPayloadBound valuation tableTerm widthTerm
      indexTerm valueTerm bitIndex
  let connectorBound := binaryBitValuationConnectorUniformPolynomial
    contextBound termBound equalityBound
  4 * fixedWidthBitSourcePayloadPolynomial valuation tableTerm widthTerm
      indexTerm valueTerm +
    4 * connectorBound +
    13 * smallContextAssemblyEnvelope
      (fixedWidthBitLeafSmallContextSyntaxUniformResource valuation tableTerm
        widthTerm indexTerm valueTerm)

def fixedWidthBitLeafUniformPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let contextBound :=
    fixedWidthBitValuationContextFormulaCodeUniformResource valuation
      widthTerm
  let termBound :=
    fixedWidthBitValuationTermCodeUniformResource valuation tableTerm
      widthTerm indexTerm valueTerm
  let equalityBound :=
    fixedWidthBitLeafTermEqualityUniformPayloadBound valuation tableTerm
      widthTerm indexTerm valueTerm
  let connectorBound := binaryBitValuationConnectorUniformPolynomial
    contextBound termBound equalityBound
  4 * fixedWidthBitSourcePayloadPolynomial valuation tableTerm widthTerm
      indexTerm valueTerm +
    4 * connectorBound +
    13 * smallContextAssemblyEnvelope
      (fixedWidthBitLeafSmallContextSyntaxUniformResource valuation tableTerm
        widthTerm indexTerm valueTerm)

theorem
    fixedWidthBitLeafSourceBoundedPayloadPolynomial_le_equalityIsolated_of_openIndex
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅)
    (hbitIndex : bitIndex < termValue valuation widthTerm) :
    fixedWidthBitLeafSourceBoundedPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm bitIndex <=
      fixedWidthBitLeafEqualityIsolatedPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm bitIndex := by
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  let contextBound :=
    fixedWidthBitValuationContextFormulaCodeUniformResource valuation
      widthTerm
  let termBound :=
    fixedWidthBitValuationTermCodeUniformResource valuation tableTerm
      widthTerm indexTerm valueTerm
  let equalityBound :=
    fixedWidthBitLeafTermEqualityPayloadBound valuation tableTerm widthTerm
      indexTerm valueTerm bitIndex
  let connectorBound := binaryBitValuationConnectorUniformPolynomial
    contextBound termBound equalityBound
  have hterms := fixedWidthBitValuationTermCodeResources_le_uniform
    valuation tableTerm widthTerm indexTerm valueTerm bitIndex hbitIndex
  have hcontexts :=
    fixedWidthBitLiteralContextFormulaCodeSums_le_uniform_of_openIndex
      valuation tableTerm widthTerm indexTerm valueTerm bitIndex
      htable hwidth hindex hvalue hbitIndex
  have hleftIndexEquality :
      compileTermValueEqualityPayloadPolynomial branchValuation
          leftIndexTerm <= equalityBound := by
    unfold equalityBound fixedWidthBitLeafTermEqualityPayloadBound
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm,
      rightIndexTerm, rightValueTerm]
    omega
  have hleftValueEquality :
      compileTermValueEqualityPayloadPolynomial branchValuation
          leftValueTerm <= equalityBound := by
    unfold equalityBound fixedWidthBitLeafTermEqualityPayloadBound
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm,
      rightIndexTerm, rightValueTerm]
    omega
  have hrightIndexEquality :
      compileTermValueEqualityPayloadPolynomial branchValuation
          rightIndexTerm <= equalityBound := by
    unfold equalityBound fixedWidthBitLeafTermEqualityPayloadBound
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm,
      rightIndexTerm, rightValueTerm]
    omega
  have hrightValueEquality :
      compileTermValueEqualityPayloadPolynomial branchValuation
          rightValueTerm <= equalityBound := by
    unfold equalityBound fixedWidthBitLeafTermEqualityPayloadBound
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm,
      rightIndexTerm, rightValueTerm]
    omega
  have hleftTrue :=
    compileBinaryBitLiteralAtValuationConnectorPolynomial_le_uniform
      true branchValuation leftIndexTerm leftValueTerm contextBound termBound
      equalityBound hcontexts.1 hterms.1 hleftIndexEquality
      hleftValueEquality
  have hleftFalse :=
    compileBinaryBitLiteralAtValuationConnectorPolynomial_le_uniform
      false branchValuation leftIndexTerm leftValueTerm contextBound termBound
      equalityBound hcontexts.1 hterms.1 hleftIndexEquality
      hleftValueEquality
  have hrightTrue :=
    compileBinaryBitLiteralAtValuationConnectorPolynomial_le_uniform
      true branchValuation rightIndexTerm rightValueTerm contextBound termBound
      equalityBound hcontexts.2 hterms.2 hrightIndexEquality
      hrightValueEquality
  have hrightFalse :=
    compileBinaryBitLiteralAtValuationConnectorPolynomial_le_uniform
      false branchValuation rightIndexTerm rightValueTerm contextBound
      termBound equalityBound hcontexts.2 hterms.2 hrightIndexEquality
      hrightValueEquality
  have hsyntax :=
    fixedWidthBitLeafSmallContextSyntaxResource_le_uniform_of_openIndex
      valuation tableTerm widthTerm indexTerm valueTerm bitIndex
      htable hwidth hindex hvalue hbitIndex
  have hsmall :=
    FoundationCompactPAUnaryAtomicTransportPolynomialBounds.smallContextAssemblyEnvelope_mono_local
      hsyntax
  unfold fixedWidthBitLeafSourceBoundedPayloadPolynomial
    fixedWidthBitLeafEqualityIsolatedPayloadPolynomial
  dsimp only [branchValuation, leftIndexTerm, leftValueTerm,
    rightIndexTerm, rightValueTerm, contextBound, termBound, equalityBound,
    connectorBound] at *
  omega

theorem fixedWidthBitLeafSourceBoundedPayloadPolynomial_le_uniform_of_openIndex
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅)
    (hbitIndex : bitIndex < termValue valuation widthTerm) :
    fixedWidthBitLeafSourceBoundedPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm bitIndex <=
      fixedWidthBitLeafUniformPayloadPolynomial valuation tableTerm widthTerm
        indexTerm valueTerm := by
  have hisolated :=
    fixedWidthBitLeafSourceBoundedPayloadPolynomial_le_equalityIsolated_of_openIndex
      valuation tableTerm widthTerm indexTerm valueTerm bitIndex htable hwidth
      hindex hvalue hbitIndex
  have hequality := fixedWidthBitLeafTermEqualityPayloadBound_le_uniform
    valuation tableTerm widthTerm indexTerm valueTerm bitIndex htable hwidth
    hindex hvalue hbitIndex
  unfold fixedWidthBitLeafEqualityIsolatedPayloadPolynomial at hisolated
  unfold fixedWidthBitLeafUniformPayloadPolynomial
  dsimp only at hisolated ⊢
  unfold binaryBitValuationConnectorUniformPolynomial at hisolated ⊢
  omega

def fixedWidthBitLeafAggregatePayloadBound
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  (Finset.range (termValue valuation widthTerm)).sum fun bitIndex =>
    fixedWidthBitLeafSourceBoundedPayloadPolynomial valuation tableTerm
      widthTerm indexTerm valueTerm bitIndex

def fixedWidthBitLeafAggregateUniformPayloadBound
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  termValue valuation widthTerm *
    fixedWidthBitLeafUniformPayloadPolynomial valuation tableTerm widthTerm
      indexTerm valueTerm

theorem fixedWidthBitLeafAggregatePayloadBound_le_uniform_of_openIndex
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthBitLeafAggregatePayloadBound valuation tableTerm widthTerm
        indexTerm valueTerm <=
      fixedWidthBitLeafAggregateUniformPayloadBound valuation tableTerm
        widthTerm indexTerm valueTerm := by
  unfold fixedWidthBitLeafAggregatePayloadBound
    fixedWidthBitLeafAggregateUniformPayloadBound
  calc
    (Finset.range (termValue valuation widthTerm)).sum (fun bitIndex =>
        fixedWidthBitLeafSourceBoundedPayloadPolynomial valuation tableTerm
          widthTerm indexTerm valueTerm bitIndex) <=
      (Finset.range (termValue valuation widthTerm)).sum (fun _ =>
        fixedWidthBitLeafUniformPayloadPolynomial valuation tableTerm
          widthTerm indexTerm valueTerm) := by
        apply Finset.sum_le_sum
        intro bitIndex hmember
        exact
          fixedWidthBitLeafSourceBoundedPayloadPolynomial_le_uniform_of_openIndex
            valuation tableTerm widthTerm indexTerm valueTerm bitIndex htable
            hwidth hindex hvalue (Finset.mem_range.mp hmember)
    _ = termValue valuation widthTerm *
        fixedWidthBitLeafUniformPayloadPolynomial valuation tableTerm
          widthTerm indexTerm valueTerm := by simp

theorem fixedWidthBitLeafSourceBoundedPayloadPolynomial_le_aggregate
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (hbitIndex : bitIndex < termValue valuation widthTerm) :
    fixedWidthBitLeafSourceBoundedPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm bitIndex <=
      fixedWidthBitLeafAggregatePayloadBound valuation tableTerm widthTerm
        indexTerm valueTerm := by
  unfold fixedWidthBitLeafAggregatePayloadBound
  exact Finset.single_le_sum
    (fun candidate _ => Nat.zero_le
      (fixedWidthBitLeafSourceBoundedPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm candidate))
    (Finset.mem_range.mpr hbitIndex)

theorem fixedWidthBitHybridBranches_aggregateLeafPayloadBound
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tableTerm).testBit
          (termValue valuation indexTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation valueTerm).testBit bitIndex) :
    HybridBranchesLeafPayloadBound
      (fixedWidthBitLeafAggregatePayloadBound valuation tableTerm widthTerm
        indexTerm valueTerm)
      (fixedWidthBitHybridBranches valuation tableTerm widthTerm indexTerm
        valueTerm (termValue valuation widthTerm) hbits) := by
  exact fixedWidthBitHybridBranches_leafPayloadBound
    valuation tableTerm widthTerm indexTerm valueTerm
    (termValue valuation widthTerm)
    (fixedWidthBitLeafAggregatePayloadBound valuation tableTerm widthTerm
      indexTerm valueTerm)
    hbits
    (fun bitIndex hbitIndex =>
      (fixedWidthBitLeafUniformStructuralEnvelope_le_sourceBoundedPolynomial
          valuation tableTerm widthTerm indexTerm valueTerm bitIndex
          htable hwidth hindexClosed hvalue hbitIndex).trans
        (fixedWidthBitLeafSourceBoundedPayloadPolynomial_le_aggregate
          valuation tableTerm widthTerm indexTerm valueTerm bitIndex
          hbitIndex))

theorem fixedWidthBitHybridBranches_aggregateLeafPayloadBound_of_openIndex
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tableTerm).testBit
          (termValue valuation indexTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation valueTerm).testBit bitIndex) :
    HybridBranchesLeafPayloadBound
      (fixedWidthBitLeafAggregatePayloadBound valuation tableTerm widthTerm
        indexTerm valueTerm)
      (fixedWidthBitHybridBranches valuation tableTerm widthTerm indexTerm
        valueTerm (termValue valuation widthTerm) hbits) := by
  exact fixedWidthBitHybridBranches_leafPayloadBound
    valuation tableTerm widthTerm indexTerm valueTerm
    (termValue valuation widthTerm)
    (fixedWidthBitLeafAggregatePayloadBound valuation tableTerm widthTerm
      indexTerm valueTerm)
    hbits
    (fun bitIndex hbitIndex =>
      (fixedWidthBitLeafUniformStructuralEnvelope_le_sourceBoundedPolynomial_of_openIndex
          valuation tableTerm widthTerm indexTerm valueTerm bitIndex
          htable hwidth hindex hvalue hbitIndex).trans
        (fixedWidthBitLeafSourceBoundedPayloadPolynomial_le_aggregate
          valuation tableTerm widthTerm indexTerm valueTerm bitIndex
          hbitIndex))

theorem
    fixedWidthBitHybridBranches_aggregateUniformLeafPayloadBound_of_openIndex
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tableTerm).testBit
          (termValue valuation indexTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation valueTerm).testBit bitIndex) :
    HybridBranchesLeafPayloadBound
      (fixedWidthBitLeafAggregateUniformPayloadBound valuation tableTerm
        widthTerm indexTerm valueTerm)
      (fixedWidthBitHybridBranches valuation tableTerm widthTerm indexTerm
        valueTerm (termValue valuation widthTerm) hbits) := by
  have haggregate :=
    fixedWidthBitLeafAggregatePayloadBound_le_uniform_of_openIndex valuation
      tableTerm widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  exact fixedWidthBitHybridBranches_leafPayloadBound valuation tableTerm
    widthTerm indexTerm valueTerm (termValue valuation widthTerm)
    (fixedWidthBitLeafAggregateUniformPayloadBound valuation tableTerm
      widthTerm indexTerm valueTerm)
    hbits
    (fun bitIndex hbitIndex =>
      ((fixedWidthBitLeafUniformStructuralEnvelope_le_sourceBoundedPolynomial_of_openIndex
          valuation tableTerm widthTerm indexTerm valueTerm bitIndex htable
          hwidth hindex hvalue hbitIndex).trans
        (fixedWidthBitLeafSourceBoundedPayloadPolynomial_le_aggregate
          valuation tableTerm widthTerm indexTerm valueTerm bitIndex
          hbitIndex)).trans haggregate)

def fixedWidthBitBranchesStructuralPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  explicitHybridUniversalBranchesPayloadPolynomial
    (termValue valuation widthTerm)
    (fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm)
    (fixedWidthBitLeafAggregatePayloadBound valuation tableTerm widthTerm
      indexTerm valueTerm)

theorem fixedWidthBitBranchesStructuralPayloadEnvelope_le_publicPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tableTerm).testBit
          (termValue valuation indexTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation valueTerm).testBit bitIndex) :
    hybridBranchesStructuralPayloadEnvelope
      (termValue valuation widthTerm) ∅
      (fixedWidthBitHybridBranches valuation tableTerm widthTerm indexTerm
        valueTerm (termValue valuation widthTerm) hbits) <=
      fixedWidthBitBranchesStructuralPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm := by
  have hleaves := fixedWidthBitHybridBranches_aggregateLeafPayloadBound
    valuation tableTerm widthTerm indexTerm valueTerm htable hwidth
    hindexClosed hvalue hbits
  unfold fixedWidthBitBranchesStructuralPayloadPolynomial
  exact hybridBranchesStructuralPayloadEnvelope_le_polynomial
    (fixedWidthBitLeafAggregatePayloadBound valuation tableTerm widthTerm
      indexTerm valueTerm)
    (fixedWidthBitHybridBranches valuation tableTerm widthTerm indexTerm
      valueTerm (termValue valuation widthTerm) hbits)
    hleaves

#print axioms
  fixedWidthBitLeafUniformStructuralEnvelope_le_publicPolynomial
#print axioms
  fixedWidthBitLeafUniformStructuralEnvelope_le_publicPolynomial_of_openIndex
#print axioms
  fixedWidthBitLeafUniformStructuralEnvelope_le_sourceBoundedPolynomial
#print axioms
  fixedWidthBitLeafUniformStructuralEnvelope_le_sourceBoundedPolynomial_of_openIndex
#print axioms fixedWidthBitValuationTermCodeResources_le_uniform
#print axioms fixedWidthBitValuationContext_formulaCodeSum_le_uniform
#print axioms
  fixedWidthBitLiteralContextFormulaCodeSums_le_uniform_of_openIndex
#print axioms
  fixedWidthBitLeafSmallContextSyntaxResource_le_uniform_of_openIndex
#print axioms
  fixedWidthRightBitIndexTermEqualityPayloadPolynomial_le_uniform
#print axioms fixedWidthBitLeafTermEqualityPayloadBound_le_uniform
#print axioms
  fixedWidthBitLeafSourceBoundedPayloadPolynomial_le_equalityIsolated_of_openIndex
#print axioms
  fixedWidthBitLeafSourceBoundedPayloadPolynomial_le_uniform_of_openIndex
#print axioms
  fixedWidthBitLeafAggregatePayloadBound_le_uniform_of_openIndex
#print axioms fixedWidthBitHybridBranches_aggregateLeafPayloadBound
#print axioms
  fixedWidthBitHybridBranches_aggregateLeafPayloadBound_of_openIndex
#print axioms
  fixedWidthBitHybridBranches_aggregateUniformLeafPayloadBound_of_openIndex
#print axioms
  fixedWidthBitBranchesStructuralPayloadEnvelope_le_publicPolynomial

end FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerLeafPublicBounds
