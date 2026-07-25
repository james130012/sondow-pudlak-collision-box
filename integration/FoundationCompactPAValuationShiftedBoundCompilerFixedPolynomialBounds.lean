import integration.FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
import integration.FoundationCompactPAValuationTermCompilerUniformBounds
import integration.FoundationCompactPAValuationTermCompilerFixedPolynomialBounds
import integration.FoundationCompactPABitMembershipValuationTransportPolynomialBounds

/-!
# Fixed polynomial bound for shifted valuation bounds

This file removes the remaining valuation-, context-, and term-shaped
coordinates from `compileShiftedBoundEqualityPayloadPublicPolynomial`.  A
closed source term and an outer variable set contained in `{0}` are charged to
one numeric/code scale.  No proof object or proof-length premise occurs in the
resulting bound.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABitMembershipValuationTransportPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerBounds
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationTermCompilerUniformBounds
open FoundationCompactPAValuationTermCompilerFixedPolynomialBounds
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPACertifiedContextEquality
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactSyntaxTransformationCodeBounds

/-- One term-code envelope for the short numeral, unary numeral, and shifted
source term used by the shifted-bound compiler. -/
def shiftedBoundFixedTermCodePolynomial (scale : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope scale +
    iteratedSuccessorTermCodePolynomial 0 scale + 2 * scale + 1

/-- The source/middle code sum consumed by the equality-symmetry compiler. -/
def shiftedBoundFixedSymmetryTermCodePolynomial (scale : Nat) : Nat :=
  2 * shiftedBoundFixedTermCodePolynomial scale + 1

/-- Formula-code envelope for both the empty local context and the shifted
outer valuation context. -/
def shiftedBoundFixedFormulaCodePolynomial (scale : Nat) : Nat :=
  let contextBound := valuationContextFormulaCodeSumEnvelope 1 scale
    (binaryTermCode (&0 : ValuationTerm)).length
  let termBound := shiftedBoundFixedTermCodePolynomial scale
  2 * contextBound + termEqualityFormulaClosureCodeEnvelope termBound + 1

/-- Fully scalar payload bound for a shifted closed bound equality. -/
def compileShiftedBoundEqualityFixedPayloadPolynomial (scale : Nat) : Nat :=
  let termBound := shiftedBoundFixedTermCodePolynomial scale
  let formulaBound := shiftedBoundFixedFormulaCodePolynomial scale
  let equalityBound := compileTermValueEqualityFixedPayloadPolynomial scale
    termBound
  let bridgeBound :=
    binaryBitEqualitySymmetryPayloadTermPolynomial
        (shiftedBoundFixedSymmetryTermCodePolynomial scale) +
      shortToIteratedPayloadPolynomial scale +
      3 * smallContextAssemblyEnvelope formulaBound
  contextualEqualityTransitivityUniformPayloadBound 0 termBound bridgeBound
      equalityBound +
    smallContextAssemblyEnvelope formulaBound

private theorem shiftedBound_value_size_le_scale
    (value scale : Nat) (hvalue : value <= scale) :
    Nat.size value <= scale :=
  (natSize_le_self_uniform value).trans hvalue

private theorem shiftedBound_source_code_le
    (value scale : Nat) (hvalue : value <= scale) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      shiftedBoundFixedTermCodePolynomial scale := by
  have hsize := shiftedBound_value_size_le_scale value scale hvalue
  have hraw := binaryNumeralTerm_code_length_le_envelope value scale hsize
  unfold shiftedBoundFixedTermCodePolynomial
  omega

private theorem shiftedBound_middle_code_le
    (value scale : Nat) (hvalue : value <= scale) :
    (binaryTermCode (iteratedSuccessorTerm 0 value)).length <=
      shiftedBoundFixedTermCodePolynomial scale := by
  have hraw := iteratedSuccessorTerm_code_length_le_polynomial 0 value
  have hmono := iteratedSuccessorTermCodePolynomial_mono 0 hvalue
  unfold shiftedBoundFixedTermCodePolynomial
  omega

private theorem shiftedBound_target_code_le
    (boundSource : ValuationTerm) (scale : Nat)
    (hcode : (binaryTermCode boundSource).length <= scale) :
    (binaryTermCode (Rew.shift boundSource)).length <=
      shiftedBoundFixedTermCodePolynomial scale := by
  have hshift := binaryTermCode_shift_length_le boundSource
  unfold shiftedBoundFixedTermCodePolynomial
  omega

private theorem shiftedBound_outer_context_code_sum_le
    (valuation : Nat -> Nat) (outerVariables : Finset Nat) (scale : Nat)
    (houter : outerVariables ⊆ {0})
    (hvalues : forall index, index ∈ outerVariables ->
      valuation index <= scale) :
    formulaCodeSum (valuationContext outerVariables valuation) <=
      valuationContextFormulaCodeSumEnvelope 1 scale
        (binaryTermCode (&0 : ValuationTerm)).length := by
  have hcard : outerVariables.card <= 1 := by
    exact (Finset.card_le_card houter).trans (by simp)
  have hvariables : forall index, index ∈ outerVariables ->
      (binaryTermCode (&index : ValuationTerm)).length <=
        (binaryTermCode (&0 : ValuationTerm)).length := by
    intro index hindex
    have hsingle := houter hindex
    simp only [Finset.mem_singleton] at hsingle
    subst index
    exact le_rfl
  exact valuationContext_formulaCodeSum_le_uniform outerVariables valuation 1
    scale (binaryTermCode (&0 : ValuationTerm)).length hcard hvalues hvariables

private theorem shiftedBound_outer_context_card_le_one
    (valuation : Nat -> Nat) (outerVariables : Finset Nat)
    (houter : outerVariables ⊆ {0}) :
    ((valuationContext outerVariables valuation).image Rewriting.shift).card <=
      1 := by
  have hvars : outerVariables.card <= 1 :=
    (Finset.card_le_card houter).trans (by simp)
  have hcontext : (valuationContext outerVariables valuation).card <=
      outerVariables.card := by
    unfold valuationContext
    exact Finset.card_image_le
  exact Finset.card_image_le.trans (hcontext.trans hvars)

private theorem shiftedBound_equality_formula_code_le
    (left right : ValuationTerm) (scale : Nat)
    (hleft : (binaryTermCode left).length <=
      shiftedBoundFixedTermCodePolynomial scale)
    (hright : (binaryTermCode right).length <=
      shiftedBoundFixedTermCodePolynomial scale) :
    (binaryFormulaCode
      (“!!left = !!right” : ValuationFormula)).length <=
        shiftedBoundFixedFormulaCodePolynomial scale := by
  let termBound := shiftedBoundFixedTermCodePolynomial scale
  have hraw := equalityFormula_code_length_le_paEnvelope left right termBound
    hleft hright
  have hclosure : paFormulaCodeEnvelope termBound <=
      termEqualityFormulaClosureCodeEnvelope termBound := by
    unfold termEqualityFormulaClosureCodeEnvelope
      termEqualityFormulaStageTwoCodeEnvelope
      termEqualityFormulaStageOneCodeEnvelope
    omega
  have hfinal : termEqualityFormulaClosureCodeEnvelope termBound <=
      shiftedBoundFixedFormulaCodePolynomial scale := by
    unfold shiftedBoundFixedFormulaCodePolynomial
    dsimp only [termBound]
    omega
  exact hraw.trans (hclosure.trans hfinal)

private theorem shiftedBound_implication_formula_code_le
    (left right : ValuationFormula) (scale : Nat)
    (hleft : (binaryFormulaCode left).length <=
      paFormulaCodeEnvelope (shiftedBoundFixedTermCodePolynomial scale))
    (hright : (binaryFormulaCode right).length <=
      paFormulaCodeEnvelope (shiftedBoundFixedTermCodePolynomial scale)) :
    (binaryFormulaCode (left 🡒 right)).length <=
      shiftedBoundFixedFormulaCodePolynomial scale := by
  let termBound := shiftedBoundFixedTermCodePolynomial scale
  have hraw := binaryFormulaCode_implication_length_le left right
  have hstage : (binaryFormulaCode (left 🡒 right)).length <=
      termEqualityFormulaStageOneCodeEnvelope termBound := by
    unfold termEqualityFormulaStageOneCodeEnvelope
    dsimp only [termBound] at hleft hright ⊢
    omega
  have hclosure : termEqualityFormulaStageOneCodeEnvelope termBound <=
      termEqualityFormulaClosureCodeEnvelope termBound := by
    unfold termEqualityFormulaClosureCodeEnvelope
      termEqualityFormulaStageTwoCodeEnvelope
    omega
  exact (hstage.trans hclosure).trans (by
    unfold shiftedBoundFixedFormulaCodePolynomial
    dsimp only [termBound]
    omega)

private theorem shiftedBound_negated_formula_code_le
    (formula : ValuationFormula) (scale : Nat)
    (hformula : (binaryFormulaCode formula).length <=
      termEqualityFormulaStageOneCodeEnvelope
        (shiftedBoundFixedTermCodePolynomial scale)) :
    (binaryFormulaCode (∼formula)).length <=
      shiftedBoundFixedFormulaCodePolynomial scale := by
  let termBound := shiftedBoundFixedTermCodePolynomial scale
  have hraw := binaryFormulaCode_neg_length_le formula
  have hclosure : (binaryFormulaCode (∼formula)).length <=
      termEqualityFormulaClosureCodeEnvelope termBound := by
    unfold termEqualityFormulaClosureCodeEnvelope
      termEqualityFormulaStageTwoCodeEnvelope
    dsimp only [termBound] at hformula ⊢
    omega
  exact hclosure.trans (by
    unfold shiftedBoundFixedFormulaCodePolynomial
    dsimp only [termBound]
    omega)

/-- Resource-explicit fixed endpoint.  The two equality hypotheses expose
transparent definitions and are discharged by `rfl` by callers. -/
theorem
    compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq_of_values
    (valuation : Nat -> Nat) (outerVariables : Finset Nat)
    (boundSource : ValuationTerm) (resource target scale : Nat)
    (hresource : resource =
      compileShiftedBoundEqualityPayloadPublicPolynomial valuation
        outerVariables boundSource)
    (htarget : target =
      compileShiftedBoundEqualityFixedPayloadPolynomial scale)
    (hclosed : boundSource.freeVariables = ∅)
    (houter : outerVariables ⊆ {0})
    (houterValues : forall index, index ∈ outerVariables ->
      valuation index <= scale)
    (hvalue : termValue valuation boundSource <= scale)
    (hcode : (binaryTermCode boundSource).length <= scale) :
    Nat.le resource target := by
  let shiftedValuation := extendValuation 0 valuation
  let localContext := valuationContext
    (Rew.shift boundSource).freeVariables shiftedValuation
  let outerContext :=
    (valuationContext outerVariables valuation).image Rewriting.shift
  let value := termValue valuation boundSource
  let source := shortBinaryNumeralTerm value
  let middle := iteratedSuccessorTerm 0 value
  let targetTerm := Rew.shift boundSource
  let bridgeFormula := (“!!source = !!middle” : ValuationFormula)
  let backwardFormula := (“!!middle = !!source” : ValuationFormula)
  let resultFormula := (“!!middle = !!targetTerm” : ValuationFormula)
  let termBound := shiftedBoundFixedTermCodePolynomial scale
  let formulaBound := shiftedBoundFixedFormulaCodePolynomial scale
  let equalityBound := compileTermValueEqualityFixedPayloadPolynomial scale
    termBound
  let symmetryTermBound := shiftedBoundFixedSymmetryTermCodePolynomial scale
  let bridgeBound :=
    binaryBitEqualitySymmetryPayloadTermPolynomial symmetryTermBound +
      shortToIteratedPayloadPolynomial scale +
      3 * smallContextAssemblyEnvelope formulaBound
  have hsource : (binaryTermCode source).length <= termBound := by
    dsimp only [source, value, termBound]
    exact shiftedBound_source_code_le _ _ hvalue
  have hmiddle : (binaryTermCode middle).length <= termBound := by
    dsimp only [middle, value, termBound]
    exact shiftedBound_middle_code_le _ _ hvalue
  have htargetTerm : (binaryTermCode targetTerm).length <= termBound := by
    dsimp only [targetTerm, termBound]
    exact shiftedBound_target_code_le boundSource scale hcode
  have hshiftClosed := shiftedTerm_freeVariables_eq_empty_of_closed
    boundSource hclosed
  have hlocalEmpty : localContext = ∅ := by
    dsimp only [localContext]
    rw [hshiftClosed]
    simp [valuationContext]
  have hlocalCard : localContext.card <= 4 := by
    rw [hlocalEmpty]
    simp
  have hlocalCodeSum : formulaCodeSum localContext <= 0 := by
    rw [hlocalEmpty]
    simp [formulaCodeSum]
  have hlocalFormula : FormulaCodeBound localContext formulaBound := by
    rw [hlocalEmpty]
    intro formula hformula
    simp at hformula
  have htargetCard : targetTerm.freeVariables.card <= 4 := by
    dsimp only [targetTerm]
    rw [hshiftClosed]
    simp
  have htargetValues : forall index, index ∈ targetTerm.freeVariables ->
      shiftedValuation index <= scale := by
    intro index hindex
    dsimp only [targetTerm] at hindex
    rw [hshiftClosed] at hindex
    simp at hindex
  have htermCoordinate :=
    compileTermValueEqualityPayloadPolynomial_le_coordinate shiftedValuation
      scale targetTerm htargetCard htargetValues
  have htermFixed :=
    compileTermValueEqualityUniformPayloadPolynomial_le_fixed scale termBound
      targetTerm htargetCard htargetTerm
  have hterm : compileTermValueEqualityPayloadPolynomial shiftedValuation
      targetTerm <= equalityBound := by
    exact htermCoordinate.trans htermFixed
  have htermCodeResource :
      closedShiftedBoundTermCodeResource valuation boundSource <=
        symmetryTermBound := by
    dsimp only [symmetryTermBound]
    unfold closedShiftedBoundTermCodeResource
      shiftedBoundFixedSymmetryTermCodePolynomial
    dsimp only [value, source, middle, termBound] at *
    omega
  have hsymmetry := binaryBitEqualitySymmetryPayloadTermPolynomial_mono
    htermCodeResource
  have hshort := shortToIteratedPayloadPolynomial_mono_public hvalue
  have hbridgeFormulaBase : (binaryFormulaCode bridgeFormula).length <=
      paFormulaCodeEnvelope termBound := by
    dsimp only [bridgeFormula]
    exact equalityFormula_code_length_le_paEnvelope source middle termBound
      hsource hmiddle
  have hbackwardFormulaBase : (binaryFormulaCode backwardFormula).length <=
      paFormulaCodeEnvelope termBound := by
    dsimp only [backwardFormula]
    exact equalityFormula_code_length_le_paEnvelope middle source termBound
      hmiddle hsource
  have hbridgeFormula : (binaryFormulaCode bridgeFormula).length <=
      formulaBound := by
    dsimp only [formulaBound, bridgeFormula, termBound]
    exact shiftedBound_equality_formula_code_le source middle scale hsource
      hmiddle
  have hbackwardFormula : (binaryFormulaCode backwardFormula).length <=
      formulaBound := by
    dsimp only [formulaBound, backwardFormula, termBound]
    exact shiftedBound_equality_formula_code_le middle source scale hmiddle
      hsource
  have hresultFormula : (binaryFormulaCode resultFormula).length <=
      formulaBound := by
    dsimp only [formulaBound, resultFormula, termBound]
    exact shiftedBound_equality_formula_code_le middle targetTerm scale hmiddle
      htargetTerm
  have himplication :
      (binaryFormulaCode (bridgeFormula 🡒 backwardFormula)).length <=
        formulaBound := by
    dsimp only [formulaBound, termBound]
    exact shiftedBound_implication_formula_code_le bridgeFormula
      backwardFormula scale hbridgeFormulaBase hbackwardFormulaBase
  have himplicationStage :
      (binaryFormulaCode (bridgeFormula 🡒 backwardFormula)).length <=
        termEqualityFormulaStageOneCodeEnvelope termBound := by
    have hraw := binaryFormulaCode_implication_length_le bridgeFormula
      backwardFormula
    unfold termEqualityFormulaStageOneCodeEnvelope
    omega
  have hnegImplication :
      (binaryFormulaCode (∼(bridgeFormula 🡒 backwardFormula))).length <=
        formulaBound := by
    dsimp only [formulaBound, termBound]
    exact shiftedBound_negated_formula_code_le
      (bridgeFormula 🡒 backwardFormula) scale himplicationStage
  have hbackwardStage : (binaryFormulaCode backwardFormula).length <=
      termEqualityFormulaStageOneCodeEnvelope termBound := by
    unfold termEqualityFormulaStageOneCodeEnvelope
    omega
  have hnegBackward : (binaryFormulaCode (∼backwardFormula)).length <=
      formulaBound := by
    dsimp only [formulaBound, termBound]
    exact shiftedBound_negated_formula_code_le backwardFormula scale
      hbackwardStage
  have hbridgeInsert := hlocalFormula.insert hbridgeFormula
  have himplicationInsert := hlocalFormula.insert himplication
  have hbridgeInsertCard : (insert bridgeFormula localContext).card <= 8 := by
    have hstep := Finset.card_insert_le bridgeFormula localContext
    omega
  have himplicationInsertCard :
      (insert (bridgeFormula 🡒 backwardFormula) localContext).card <= 8 := by
    have hstep := Finset.card_insert_le
      (bridgeFormula 🡒 backwardFormula) localContext
    omega
  have hweakBridge := weakeningFullAssemblyCost_le_small
    (insert bridgeFormula localContext) formulaBound hbridgeInsertCard
      hbridgeInsert
  have hweakImplication := weakeningFullAssemblyCost_le_small
    (insert (bridgeFormula 🡒 backwardFormula) localContext) formulaBound
      himplicationInsertCard himplicationInsert
  have hmp := contextualModusPonensFullAssemblyCost_le_small localContext
    bridgeFormula backwardFormula formulaBound hlocalCard hlocalFormula
      hbridgeFormula hbackwardFormula himplication hnegImplication hnegBackward
  have hbridge :
      binaryBitEqualitySymmetryPayloadTermPolynomial
          (closedShiftedBoundTermCodeResource valuation boundSource) +
        weakeningFullAssemblyCost
          (insert (bridgeFormula 🡒 backwardFormula) localContext) +
        (shortToIteratedPayloadPolynomial value +
          weakeningFullAssemblyCost (insert bridgeFormula localContext)) +
        contextualModusPonensFullAssemblyCost localContext bridgeFormula
          backwardFormula <= bridgeBound := by
    dsimp only [bridgeBound, symmetryTermBound, formulaBound, value] at *
    omega
  have htransMono := contextualEqualityTransitivityStructuralPayloadBound_mono
    localContext middle source targetTerm
      (binaryBitEqualitySymmetryPayloadTermPolynomial
          (closedShiftedBoundTermCodeResource valuation boundSource) +
        weakeningFullAssemblyCost
          (insert (bridgeFormula 🡒 backwardFormula) localContext) +
        (shortToIteratedPayloadPolynomial value +
          weakeningFullAssemblyCost (insert bridgeFormula localContext)) +
        contextualModusPonensFullAssemblyCost localContext bridgeFormula
          backwardFormula)
      (compileTermValueEqualityPayloadPolynomial shiftedValuation targetTerm)
      bridgeBound equalityBound hbridge hterm
  have htransUniform :=
    contextualEqualityTransitivityStructuralPayloadBound_le_uniform
      localContext middle source targetTerm bridgeBound equalityBound 0
        termBound hlocalCard hlocalCodeSum hmiddle hsource htargetTerm
  have htrans :
      contextualEqualityTransitivityStructuralPayloadBound localContext middle
          source targetTerm
          (binaryBitEqualitySymmetryPayloadTermPolynomial
              (closedShiftedBoundTermCodeResource valuation boundSource) +
            weakeningFullAssemblyCost
              (insert (bridgeFormula 🡒 backwardFormula) localContext) +
            (shortToIteratedPayloadPolynomial value +
              weakeningFullAssemblyCost (insert bridgeFormula localContext)) +
            contextualModusPonensFullAssemblyCost localContext bridgeFormula
              backwardFormula)
          (compileTermValueEqualityPayloadPolynomial shiftedValuation
            targetTerm) <=
        contextualEqualityTransitivityUniformPayloadBound 0 termBound
          bridgeBound equalityBound := htransMono.trans htransUniform
  have houterCodeSum := shiftedBound_outer_context_code_sum_le valuation
    outerVariables scale houter houterValues
  have houterFormula : FormulaCodeBound outerContext formulaBound := by
    intro formula hformula
    rcases Finset.mem_image.mp hformula with
      ⟨sourceFormula, hsourceFormula, rfl⟩
    have hsourceCode :=
      (formulaCode_le_formulaCodeSum hsourceFormula).trans houterCodeSum
    have hshiftCode := binaryFormulaCode_shift_length_le sourceFormula
    unfold formulaBound shiftedBoundFixedFormulaCodePolynomial
    dsimp only
    omega
  have houterCard : outerContext.card <= 1 := by
    dsimp only [outerContext]
    exact shiftedBound_outer_context_card_le_one valuation outerVariables houter
  have hresultInsert := houterFormula.insert hresultFormula
  have hresultInsertCard : (insert resultFormula outerContext).card <= 8 := by
    have hstep := Finset.card_insert_le resultFormula outerContext
    omega
  have hfinal := weakeningFullAssemblyCost_le_small
    (insert resultFormula outerContext) formulaBound hresultInsertCard
      hresultInsert
  have htotal := Nat.add_le_add htrans hfinal
  rw [hresource, htarget]
  change compileShiftedBoundEqualityPayloadPublicPolynomial valuation
      outerVariables boundSource <=
    compileShiftedBoundEqualityFixedPayloadPolynomial scale
  simpa only [compileShiftedBoundEqualityPayloadPublicPolynomial,
    compileShiftedBoundEqualityFixedPayloadPolynomial, shiftedValuation,
    localContext, outerContext, value, source, middle, targetTerm,
    bridgeFormula, backwardFormula, resultFormula, termBound, formulaBound,
    equalityBound, symmetryTermBound, bridgeBound] using htotal

/-- Compatibility endpoint for callers whose only possible outer variable is
`0`. -/
theorem compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq
    (valuation : Nat -> Nat) (outerVariables : Finset Nat)
    (boundSource : ValuationTerm) (resource target scale : Nat)
    (hresource : resource =
      compileShiftedBoundEqualityPayloadPublicPolynomial valuation
        outerVariables boundSource)
    (htarget : target =
      compileShiftedBoundEqualityFixedPayloadPolynomial scale)
    (hclosed : boundSource.freeVariables = ∅)
    (houter : outerVariables ⊆ {0})
    (hzero : valuation 0 <= scale)
    (hvalue : termValue valuation boundSource <= scale)
    (hcode : (binaryTermCode boundSource).length <= scale) :
    Nat.le resource target := by
  apply
    compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq_of_values
      valuation outerVariables boundSource resource target scale hresource
        htarget hclosed houter
  · intro index hindex
    have hsingle := houter hindex
    simp only [Finset.mem_singleton] at hsingle
    subst index
    exact hzero
  · exact hvalue
  · exact hcode

#print axioms
  compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq_of_values
#print axioms
  compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq

end FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds
