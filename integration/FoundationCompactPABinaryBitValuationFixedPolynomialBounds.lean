import integration.FoundationCompactPABitMembershipValuationCompilerPublicBounds
import integration.FoundationCompactPABitMembershipTraceBudgetBounds
import integration.FoundationCompactPAValuationTermCompilerFixedPolynomialBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds

/-!
# Fixed polynomial bound for an open valuation bit literal

This theorem accepts up to four free valuation coordinates and replaces the
actual valuation, terms, and bit values by explicit numeric, syntax, trace,
and bit-width coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactPABinaryBitValuationFixedPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABitMembershipRuleCompilerBounds
open FoundationCompactPABitMembershipTraceBudgetBounds
open FoundationCompactPABitMembershipValuationContextCompiler
open FoundationCompactPABitMembershipValuationContextCompilerBounds
open FoundationCompactPABitMembershipValuationCompilerPublicBounds
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationTermCompilerUniformBounds
open FoundationCompactPAValuationTermCompilerFixedPolynomialBounds

def binaryBitValuationFixedValueWidth
    (traceWidth bitBound : Nat) : Nat :=
  traceWidth + bitBound + 1

def binaryBitValuationFixedContextPolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  valuationContextFormulaCodeSumEnvelope 4 numericBound
    (4 * termCodeBound)

def binaryBitValuationFixedTermResourcePolynomial
    (termCodeBound traceWidth bitBound : Nat) : Nat :=
  2 * binaryNumeralTermCodeEnvelope
      (binaryBitValuationFixedValueWidth traceWidth bitBound) +
    2 * termCodeBound + 1

def binaryBitValuationFixedEqualityPayloadPolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  compileTermValueEqualityFixedPayloadPolynomial numericBound termCodeBound

def binaryBitValuationFixedConnectorPayloadPolynomial
    (numericBound termCodeBound traceWidth bitBound : Nat) : Nat :=
  binaryBitValuationConnectorUniformPolynomial
    (binaryBitValuationFixedContextPolynomial numericBound termCodeBound)
    (binaryBitValuationFixedTermResourcePolynomial termCodeBound traceWidth
      bitBound)
    (binaryBitValuationFixedEqualityPayloadPolynomial numericBound
      termCodeBound)

def binaryBitValuationFixedLiteralPayloadPolynomial
    (numericBound termCodeBound traceWidth bitBound : Nat) : Nat :=
  binaryBitTraceBudgetPayloadPolynomial bitBound traceWidth +
    binaryBitValuationFixedConnectorPayloadPolynomial numericBound
      termCodeBound traceWidth bitBound

def binaryBitValuationFixedAtomSyntaxPolynomial
    (numericBound termCodeBound : Nat) : Nat :=
  binaryBitValuationFixedContextPolynomial numericBound termCodeBound +
    binaryBitLiteralFormulaCodeEnvelope termCodeBound + 1

def binaryBitValuationFixedAtomPayloadPolynomial
    (numericBound termCodeBound traceWidth bitBound : Nat) : Nat :=
  binaryBitValuationFixedLiteralPayloadPolynomial numericBound termCodeBound
      traceWidth bitBound +
    generalContextAssemblyEnvelope
      (binaryBitValuationFixedAtomSyntaxPolynomial numericBound termCodeBound)

theorem valuationVariableCode_le_termCode_of_union
    (indexTerm valueTerm : ValuationTerm) (termCodeBound : Nat)
    (hindexCode : (binaryTermCode indexTerm).length <= termCodeBound)
    (hvalueCode : (binaryTermCode valueTerm).length <= termCodeBound) :
    forall coordinate,
      coordinate ∈ indexTerm.freeVariables ∪ valueTerm.freeVariables ->
      (binaryTermCode (&coordinate : ValuationTerm)).length <=
        termCodeBound := by
  intro coordinate hcoordinate
  rcases Finset.mem_union.mp hcoordinate with hindex | hvalue
  · exact
      (freeVariableTermCode_length_le_termCode_length coordinate indexTerm
        hindex).trans hindexCode
  · exact
      (freeVariableTermCode_length_le_termCode_length coordinate valueTerm
        hvalue).trans hvalueCode

theorem binaryBitValuationContext_formulaCodeSum_le_fixed
    (valuation : Nat -> Nat) (indexTerm valueTerm : ValuationTerm)
    (numericBound termCodeBound : Nat)
    (hcard :
      (indexTerm.freeVariables ∪ valueTerm.freeVariables).card <= 4)
    (hvalues : forall coordinate,
      coordinate ∈ indexTerm.freeVariables ∪ valueTerm.freeVariables ->
        valuation coordinate <= numericBound)
    (hindexCode : (binaryTermCode indexTerm).length <= termCodeBound)
    (hvalueCode : (binaryTermCode valueTerm).length <= termCodeBound) :
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
        (binaryBitValuationContext valuation indexTerm valueTerm) <=
      binaryBitValuationFixedContextPolynomial numericBound
        termCodeBound := by
  let vars := indexTerm.freeVariables ∪ valueTerm.freeVariables
  have hvariableCodes : forall coordinate, coordinate ∈ vars ->
      (binaryTermCode (&coordinate : ValuationTerm)).length <=
        4 * termCodeBound := by
    intro coordinate hcoordinate
    have hraw := valuationVariableCode_le_termCode_of_union indexTerm
      valueTerm termCodeBound hindexCode hvalueCode coordinate hcoordinate
    omega
  have hraw := valuationContext_formulaCodeSum_le_uniform vars valuation 4
    numericBound (4 * termCodeBound) hcard hvalues hvariableCodes
  simpa only [binaryBitValuationContext, vars,
    binaryBitValuationFixedContextPolynomial,
    FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum,
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum]
    using hraw

theorem compileBinaryBitLiteralAtValuationPayloadPolynomial_le_fixed
    (expected : Bool) (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm)
    (numericBound termCodeBound traceWidth bitBound : Nat)
    (hcard :
      (indexTerm.freeVariables ∪ valueTerm.freeVariables).card <= 4)
    (hvalues : forall coordinate,
      coordinate ∈ indexTerm.freeVariables ∪ valueTerm.freeVariables ->
        valuation coordinate <= numericBound)
    (hindexCode : (binaryTermCode indexTerm).length <= termCodeBound)
    (hvalueCode : (binaryTermCode valueTerm).length <= termCodeBound)
    (hindexValue : termValue valuation indexTerm < traceWidth)
    (hvalueSize : Nat.size (termValue valuation valueTerm) <= bitBound) :
    compileBinaryBitLiteralAtValuationPayloadPolynomial expected valuation
        indexTerm valueTerm <=
      binaryBitValuationFixedLiteralPayloadPolynomial numericBound
        termCodeBound traceWidth bitBound := by
  let vars := indexTerm.freeVariables ∪ valueTerm.freeVariables
  let contextBound :=
    binaryBitValuationFixedContextPolynomial numericBound termCodeBound
  let termBound :=
    binaryBitValuationFixedTermResourcePolynomial termCodeBound traceWidth
      bitBound
  let equalityBound :=
    binaryBitValuationFixedEqualityPayloadPolynomial numericBound
      termCodeBound
  let connectorBound :=
    binaryBitValuationFixedConnectorPayloadPolynomial numericBound
      termCodeBound traceWidth bitBound
  let valueWidth := binaryBitValuationFixedValueWidth traceWidth bitBound
  have hvariableCodes : forall coordinate, coordinate ∈ vars ->
      (binaryTermCode (&coordinate : ValuationTerm)).length <=
        4 * termCodeBound := by
    intro coordinate hcoordinate
    have hraw := valuationVariableCode_le_termCode_of_union indexTerm
      valueTerm termCodeBound hindexCode hvalueCode coordinate hcoordinate
    omega
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (binaryBitValuationContext valuation indexTerm valueTerm) <=
        contextBound := by
    exact binaryBitValuationContext_formulaCodeSum_le_fixed valuation
      indexTerm valueTerm numericBound termCodeBound hcard hvalues hindexCode
      hvalueCode
  have hindexSize :
      Nat.size (termValue valuation indexTerm) <= valueWidth := by
    have hself :=
      natSize_le_self_uniform (termValue valuation indexTerm)
    dsimp only [valueWidth]
    unfold binaryBitValuationFixedValueWidth
    omega
  have hvalueSizeWide :
      Nat.size (termValue valuation valueTerm) <= valueWidth := by
    dsimp only [valueWidth]
    unfold binaryBitValuationFixedValueWidth
    omega
  have hindexNumeral :=
    binaryNumeralTerm_code_length_le_envelope
      (termValue valuation indexTerm) valueWidth hindexSize
  have hvalueNumeral :=
    binaryNumeralTerm_code_length_le_envelope
      (termValue valuation valueTerm) valueWidth hvalueSizeWide
  dsimp only [valueWidth] at hindexNumeral hvalueNumeral
  have htermResource :
      binaryBitValuationTermCodeResource valuation indexTerm valueTerm <=
        termBound := by
    unfold binaryBitValuationTermCodeResource
    dsimp only [termBound]
    unfold binaryBitValuationFixedTermResourcePolynomial
    omega
  have hindexCard : indexTerm.freeVariables.card <= 4 :=
    (Finset.card_le_card (Finset.subset_union_left)).trans hcard
  have hvalueCard : valueTerm.freeVariables.card <= 4 :=
    (Finset.card_le_card (Finset.subset_union_right)).trans hcard
  have hindexValues : forall coordinate,
      coordinate ∈ indexTerm.freeVariables ->
        valuation coordinate <= numericBound := by
    intro coordinate hcoordinate
    exact hvalues coordinate (Finset.mem_union_left _ hcoordinate)
  have hvalueValues : forall coordinate,
      coordinate ∈ valueTerm.freeVariables ->
        valuation coordinate <= numericBound := by
    intro coordinate hcoordinate
    exact hvalues coordinate (Finset.mem_union_right _ hcoordinate)
  have hindexEqualityCoordinate :=
    compileTermValueEqualityPayloadPolynomial_le_coordinate valuation
      numericBound indexTerm hindexCard hindexValues
  have hindexEqualityFixed :=
    compileTermValueEqualityUniformPayloadPolynomial_le_fixed numericBound
      termCodeBound indexTerm hindexCard hindexCode
  have hindexEquality :
      compileTermValueEqualityPayloadPolynomial valuation indexTerm <=
        equalityBound := by
    dsimp only [equalityBound,
      binaryBitValuationFixedEqualityPayloadPolynomial]
    exact hindexEqualityCoordinate.trans hindexEqualityFixed
  have hvalueEqualityCoordinate :=
    compileTermValueEqualityPayloadPolynomial_le_coordinate valuation
      numericBound valueTerm hvalueCard hvalueValues
  have hvalueEqualityFixed :=
    compileTermValueEqualityUniformPayloadPolynomial_le_fixed numericBound
      termCodeBound valueTerm hvalueCard hvalueCode
  have hvalueEquality :
      compileTermValueEqualityPayloadPolynomial valuation valueTerm <=
        equalityBound := by
    dsimp only [equalityBound,
      binaryBitValuationFixedEqualityPayloadPolynomial]
    exact hvalueEqualityCoordinate.trans hvalueEqualityFixed
  have hconnector :=
    compileBinaryBitLiteralAtValuationConnectorPolynomial_le_uniform
      expected valuation indexTerm valueTerm contextBound termBound
      equalityBound hcontext htermResource hindexEquality hvalueEquality
  have hsource :
      binaryBitLiteralPayloadPolynomial (termValue valuation indexTerm)
          (termValue valuation valueTerm) <=
        binaryBitTraceBudgetPayloadPolynomial bitBound traceWidth :=
    binaryBitLiteralPayloadPolynomial_le_traceBudget hindexValue hvalueSize
  cases expected with
  | false =>
      have hnegative :
          compileNegativeBinaryBitAtValuationConnectorPolynomial valuation
              indexTerm valueTerm <= connectorBound := by
        simpa only [compileBinaryBitLiteralAtValuationConnectorPolynomial,
          Bool.false_eq_true, ↓reduceIte, connectorBound,
          binaryBitValuationFixedConnectorPayloadPolynomial] using hconnector
      simp only [compileBinaryBitLiteralAtValuationPayloadPolynomial,
        Bool.false_eq_true, ↓reduceIte]
      unfold compileNegativeBinaryBitAtValuationPayloadPolynomial
        binaryBitValuationFixedLiteralPayloadPolynomial
      exact Nat.add_le_add hsource hnegative
  | true =>
      have hpositive :
          compilePositiveBinaryBitAtValuationConnectorPolynomial valuation
              indexTerm valueTerm <= connectorBound := by
        simpa only [compileBinaryBitLiteralAtValuationConnectorPolynomial,
          ↓reduceIte, connectorBound,
          binaryBitValuationFixedConnectorPayloadPolynomial] using hconnector
      simp only [compileBinaryBitLiteralAtValuationPayloadPolynomial,
        ↓reduceIte]
      unfold compilePositiveBinaryBitAtValuationPayloadPolynomial
        binaryBitValuationFixedLiteralPayloadPolynomial
      exact Nat.add_le_add hsource hpositive

theorem binaryBitLiteralAtValuationStructuralEnvelope_le_fixed
    (expected : Bool) (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm)
    (numericBound termCodeBound traceWidth bitBound : Nat)
    (hcard :
      (indexTerm.freeVariables ∪ valueTerm.freeVariables).card <= 4)
    (hvalues : forall coordinate,
      coordinate ∈ indexTerm.freeVariables ∪ valueTerm.freeVariables ->
        valuation coordinate <= numericBound)
    (hindexCode : (binaryTermCode indexTerm).length <= termCodeBound)
    (hvalueCode : (binaryTermCode valueTerm).length <= termCodeBound)
    (hindexValue : termValue valuation indexTerm < traceWidth)
    (hvalueSize : Nat.size (termValue valuation valueTerm) <= bitBound) :
    let formula :=
      binaryBitAtValuationFormula expected indexTerm valueTerm
    let Gamma := valuationContext formula.freeVariables valuation
    compileBinaryBitLiteralAtValuationPayloadResource expected valuation
          indexTerm valueTerm +
        weakeningFullAssemblyCost (insert formula Gamma) <=
      binaryBitValuationFixedAtomPayloadPolynomial numericBound termCodeBound
        traceWidth bitBound := by
  let formula := binaryBitAtValuationFormula expected indexTerm valueTerm
  let Gamma := valuationContext formula.freeVariables valuation
  let contextBound :=
    binaryBitValuationFixedContextPolynomial numericBound termCodeBound
  let literalCode := binaryBitLiteralFormulaCodeEnvelope termCodeBound
  let syntaxCode :=
    binaryBitValuationFixedAtomSyntaxPolynomial numericBound termCodeBound
  let literalBound :=
    binaryBitValuationFixedLiteralPayloadPolynomial numericBound termCodeBound
      traceWidth bitBound
  have hformulaVars :
      formula.freeVariables ⊆
        indexTerm.freeVariables ∪ valueTerm.freeVariables := by
    dsimp only [formula]
    exact binaryBitAtValuationFormula_freeVariables_subset expected indexTerm
      valueTerm
  have hformulaCard : formula.freeVariables.card <= 4 :=
    (Finset.card_le_card hformulaVars).trans hcard
  have hformulaValues : forall coordinate,
      coordinate ∈ formula.freeVariables ->
        valuation coordinate <= numericBound := by
    intro coordinate hcoordinate
    exact hvalues coordinate (hformulaVars hcoordinate)
  have hformulaVariableCodes : forall coordinate,
      coordinate ∈ formula.freeVariables ->
      (binaryTermCode (&coordinate : ValuationTerm)).length <=
        4 * termCodeBound := by
    intro coordinate hcoordinate
    have hraw := valuationVariableCode_le_termCode_of_union indexTerm
      valueTerm termCodeBound hindexCode hvalueCode coordinate
      (hformulaVars hcoordinate)
    omega
  have hGamma :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
        Gamma <= contextBound := by
    have hraw := valuationContext_formulaCodeSum_le_uniform
      formula.freeVariables valuation 4 numericBound (4 * termCodeBound)
      hformulaCard hformulaValues hformulaVariableCodes
    simpa only [Gamma, contextBound,
      binaryBitValuationFixedContextPolynomial,
      FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum,
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum]
      using hraw
  have hformulaCode : (binaryFormulaCode formula).length <= literalCode := by
    dsimp only [formula, literalCode]
    simpa only [binaryBitAtValuationFormula] using
      binaryBitLiteralAtTerms_code_length_le_uniform expected indexTerm
        valueTerm termCodeBound hindexCode hvalueCode
  have hsyntaxPositive : 1 <= syntaxCode := by
    unfold syntaxCode binaryBitValuationFixedAtomSyntaxPolynomial
    omega
  have hGammaSyntax :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
        Gamma <= syntaxCode :=
    hGamma.trans (by
      unfold syntaxCode binaryBitValuationFixedAtomSyntaxPolynomial
      omega)
  have hformulaSyntax :
      (binaryFormulaCode formula).length <= syntaxCode :=
    hformulaCode.trans (by
      unfold syntaxCode binaryBitValuationFixedAtomSyntaxPolynomial
      omega)
  have hinsert :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (insert formula Gamma) <=
        generalContextCoordinate syntaxCode := by
    have hraw := formulaCodeSum_insert_le Gamma formula
    unfold generalContextCoordinate
    omega
  have hweak := weakeningFullAssemblyCost_le_general
    (insert formula Gamma) syntaxCode hinsert
  have hresourcePublic :=
    compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial_of_card
      expected valuation indexTerm valueTerm hcard
  have hresourceFixed :=
    compileBinaryBitLiteralAtValuationPayloadPolynomial_le_fixed expected
      valuation indexTerm valueTerm numericBound termCodeBound traceWidth
      bitBound hcard hvalues hindexCode hvalueCode hindexValue hvalueSize
  have hresource :
      compileBinaryBitLiteralAtValuationPayloadResource expected valuation
          indexTerm valueTerm <= literalBound :=
    hresourcePublic.trans hresourceFixed
  unfold binaryBitValuationFixedAtomPayloadPolynomial
  apply Nat.add_le_add hresource
  simpa only [formula, Gamma, syntaxCode] using hweak

#print axioms compileBinaryBitLiteralAtValuationPayloadPolynomial_le_fixed
#print axioms binaryBitLiteralAtValuationStructuralEnvelope_le_fixed

end FoundationCompactPABinaryBitValuationFixedPolynomialBounds
