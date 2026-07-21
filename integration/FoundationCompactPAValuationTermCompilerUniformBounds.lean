import integration.FoundationCompactPAValuationTermCompilerPublicBounds

/-!
# Uniform coordinates for valuation-term compilation

This file removes the remaining dependence of the public valuation-term
compiler on one exact valuation.  A scalar bound for all free-variable values
is propagated through the real term syntax; no proof payload or caller-supplied
proof bound enters the recursion.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAValuationTermCompilerUniformBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABinaryNumeralMultiplicationBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAExponentialShortNumeralCompilerBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAQuantitativeFunctionCongruence
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerBounds
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds

/-! ## Semantic and syntax coordinates -/

def valuationTermValueEnvelope (numericBound : Nat) : ValuationTerm -> Nat
  | #index => Fin.elim0 index
  | &_ => numericBound
  | .func .zero _ => 0
  | .func .one _ => 1
  | .func .add args =>
      valuationTermValueEnvelope numericBound (args 0) +
        valuationTermValueEnvelope numericBound (args 1)
  | .func .mul args =>
      valuationTermValueEnvelope numericBound (args 0) *
        valuationTermValueEnvelope numericBound (args 1)

theorem termValue_le_valuationTermValueEnvelope
    (valuation : Nat -> Nat) (numericBound : Nat) :
    (term : ValuationTerm) ->
      (forall index, index ∈ term.freeVariables ->
        valuation index <= numericBound) ->
      termValue valuation term <= valuationTermValueEnvelope numericBound term
  | #index, _ => Fin.elim0 index
  | &index, hvalues => by
      simpa only [termValue_fvar, valuationTermValueEnvelope] using
        hvalues index (by simp)
  | .func .zero args, _ => by
      simp only [termValue_zero, valuationTermValueEnvelope]
      exact le_rfl
  | .func .one args, _ => by
      simp only [termValue_one, valuationTermValueEnvelope]
      exact le_rfl
  | .func .add args, hvalues => by
      have hleftVars : forall index, index ∈ (args 0).freeVariables ->
          valuation index <= numericBound := by
        intro index hindex
        exact hvalues index
          (freeVariables_arg_subset_func Language.Add.add args 0 hindex)
      have hrightVars : forall index, index ∈ (args 1).freeVariables ->
          valuation index <= numericBound := by
        intro index hindex
        exact hvalues index
          (freeVariables_arg_subset_func Language.Add.add args 1 hindex)
      have hleft := termValue_le_valuationTermValueEnvelope
        valuation numericBound (args 0) hleftVars
      have hright := termValue_le_valuationTermValueEnvelope
        valuation numericBound (args 1) hrightVars
      simp only [termValue_add, valuationTermValueEnvelope]
      exact Nat.add_le_add hleft hright
  | .func .mul args, hvalues => by
      have hleftVars : forall index, index ∈ (args 0).freeVariables ->
          valuation index <= numericBound := by
        intro index hindex
        exact hvalues index
          (freeVariables_arg_subset_func Language.Mul.mul args 0 hindex)
      have hrightVars : forall index, index ∈ (args 1).freeVariables ->
          valuation index <= numericBound := by
        intro index hindex
        exact hvalues index
          (freeVariables_arg_subset_func Language.Mul.mul args 1 hindex)
      have hleft := termValue_le_valuationTermValueEnvelope
        valuation numericBound (args 0) hleftVars
      have hright := termValue_le_valuationTermValueEnvelope
        valuation numericBound (args 1) hrightVars
      simp only [termValue_mul, valuationTermValueEnvelope]
      exact Nat.mul_le_mul hleft hright

def instantiatedValuationTermCodeEnvelope
    (numericBound : Nat) : ValuationTerm -> Nat
  | #index => Fin.elim0 index
  | &_ => iteratedSuccessorTermCodePolynomial 0 numericBound
  | .func .zero args =>
      (binaryTermCode (.func .zero args : ValuationTerm)).length
  | .func .one args =>
      (binaryTermCode (.func .one args : ValuationTerm)).length
  | .func .add args =>
      instantiatedValuationTermCodeEnvelope numericBound (args 0) +
        instantiatedValuationTermCodeEnvelope numericBound (args 1) +
        binaryFunctionTermCodeOverhead Language.Add.add
  | .func .mul args =>
      instantiatedValuationTermCodeEnvelope numericBound (args 0) +
        instantiatedValuationTermCodeEnvelope numericBound (args 1) +
        binaryFunctionTermCodeOverhead Language.Mul.mul

theorem instantiateTerm_code_length_le_uniform
    (valuation : Nat -> Nat) (numericBound : Nat) :
    (term : ValuationTerm) ->
      (forall index, index ∈ term.freeVariables ->
        valuation index <= numericBound) ->
      (binaryTermCode (instantiateTerm valuation term)).length <=
        instantiatedValuationTermCodeEnvelope numericBound term
  | #index, _ => Fin.elim0 index
  | &index, hvalues => by
      have hvalue := hvalues index (by simp)
      have hraw := iteratedSuccessorTerm_code_length_le_polynomial
        0 (valuation index)
      have hmono := iteratedSuccessorTermCodePolynomial_mono 0 hvalue
      simpa only [instantiateTerm, instantiatedValuationTermCodeEnvelope] using
        hraw.trans hmono
  | .func .zero args, _ => by
      simp only [instantiateTerm, instantiatedValuationTermCodeEnvelope]
      exact le_rfl
  | .func .one args, _ => by
      simp only [instantiateTerm, instantiatedValuationTermCodeEnvelope]
      exact le_rfl
  | .func .add args, hvalues => by
      have hleftVars : forall index, index ∈ (args 0).freeVariables ->
          valuation index <= numericBound := by
        intro index hindex
        exact hvalues index
          (freeVariables_arg_subset_func Language.Add.add args 0 hindex)
      have hrightVars : forall index, index ∈ (args 1).freeVariables ->
          valuation index <= numericBound := by
        intro index hindex
        exact hvalues index
          (freeVariables_arg_subset_func Language.Add.add args 1 hindex)
      have hleft := instantiateTerm_code_length_le_uniform
        valuation numericBound (args 0) hleftVars
      have hright := instantiateTerm_code_length_le_uniform
        valuation numericBound (args 1) hrightVars
      have hcode := paAddTerm_code_length_le
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1))
      simp only [instantiateTerm, instantiatedValuationTermCodeEnvelope]
      exact hcode.trans (by omega)
  | .func .mul args, hvalues => by
      have hleftVars : forall index, index ∈ (args 0).freeVariables ->
          valuation index <= numericBound := by
        intro index hindex
        exact hvalues index
          (freeVariables_arg_subset_func Language.Mul.mul args 0 hindex)
      have hrightVars : forall index, index ∈ (args 1).freeVariables ->
          valuation index <= numericBound := by
        intro index hindex
        exact hvalues index
          (freeVariables_arg_subset_func Language.Mul.mul args 1 hindex)
      have hleft := instantiateTerm_code_length_le_uniform
        valuation numericBound (args 0) hleftVars
      have hright := instantiateTerm_code_length_le_uniform
        valuation numericBound (args 1) hrightVars
      have hcode := paMulTerm_code_length_le
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1))
      simp only [instantiateTerm, instantiatedValuationTermCodeEnvelope]
      exact hcode.trans (by omega)

def valuationTermShortNumeralCodeEnvelope
    (numericBound : Nat) (term : ValuationTerm) : Nat :=
  binaryNumeralTermCodeEnvelope
    (valuationTermValueEnvelope numericBound term)

theorem natSize_le_self_uniform (value : Nat) :
    Nat.size value <= value := by
  rw [Nat.size_le]
  exact value.lt_two_pow_self

theorem shortNumeralTerm_code_length_le_uniform
    (valuation : Nat -> Nat) (numericBound : Nat) (term : ValuationTerm)
    (hvalues : forall index, index ∈ term.freeVariables ->
      valuation index <= numericBound) :
    (binaryTermCode
      (shortBinaryNumeralTerm (termValue valuation term))).length <=
        valuationTermShortNumeralCodeEnvelope numericBound term := by
  have hvalue := termValue_le_valuationTermValueEnvelope
    valuation numericBound term hvalues
  have hsize : Nat.size (termValue valuation term) <=
      valuationTermValueEnvelope numericBound term :=
    (natSize_le_self_uniform _).trans hvalue
  exact binaryNumeralTerm_code_length_le_envelope
    (termValue valuation term)
    (valuationTermValueEnvelope numericBound term) hsize

def valuationTermEqualityTermCodeEnvelope
    (numericBound : Nat) (term : ValuationTerm) : Nat :=
  valuationTermShortNumeralCodeEnvelope numericBound term +
    instantiatedValuationTermCodeEnvelope numericBound term +
    (binaryTermCode term).length + 1

theorem valuationTermEqualityTermCodes_le_envelope
    (valuation : Nat -> Nat) (numericBound : Nat) (term : ValuationTerm)
    (hvalues : forall index, index ∈ term.freeVariables ->
      valuation index <= numericBound) :
    (binaryTermCode
        (shortBinaryNumeralTerm (termValue valuation term))).length <=
          valuationTermEqualityTermCodeEnvelope numericBound term ∧
      (binaryTermCode (instantiateTerm valuation term)).length <=
          valuationTermEqualityTermCodeEnvelope numericBound term ∧
      (binaryTermCode term).length <=
          valuationTermEqualityTermCodeEnvelope numericBound term := by
  have hshort := shortNumeralTerm_code_length_le_uniform
    valuation numericBound term hvalues
  have hinstantiated := instantiateTerm_code_length_le_uniform
    valuation numericBound term hvalues
  unfold valuationTermEqualityTermCodeEnvelope
  omega

def valuationTermVariableCodeEnvelope (term : ValuationTerm) : Nat :=
  term.freeVariables.sum fun index =>
    (binaryTermCode (&index : ValuationTerm)).length

def valuationTermContextFormulaCodeEnvelope
    (numericBound : Nat) (term : ValuationTerm) : Nat :=
  valuationContextFormulaCodeSumEnvelope term.freeVariables.card numericBound
    (valuationTermVariableCodeEnvelope term)

theorem valuationTermContext_formulaCodeSum_le_envelope
    (valuation : Nat -> Nat) (numericBound : Nat) (term : ValuationTerm)
    (hvalues : forall index, index ∈ term.freeVariables ->
      valuation index <= numericBound) :
    formulaCodeSum (valuationContext term.freeVariables valuation) <=
      valuationTermContextFormulaCodeEnvelope numericBound term := by
  have hvariables : forall index, index ∈ term.freeVariables ->
      (binaryTermCode (&index : ValuationTerm)).length <=
        valuationTermVariableCodeEnvelope term := by
    intro index hindex
    unfold valuationTermVariableCodeEnvelope
    exact Finset.single_le_sum
      (fun candidate _ =>
        Nat.zero_le (binaryTermCode (&candidate : ValuationTerm)).length)
      hindex
  exact valuationContext_formulaCodeSum_le_uniform term.freeVariables
    valuation term.freeVariables.card numericBound
    (valuationTermVariableCodeEnvelope term) le_rfl hvalues hvariables

/-! ## Monotonic arithmetic ledgers -/

theorem binaryNumeralAdditionPayloadPolynomial_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    binaryNumeralAdditionPayloadPolynomial small <=
      binaryNumeralAdditionPayloadPolynomial large := by
  have hwork : paAdditionWorkWidth small <= paAdditionWorkWidth large := by
    unfold paAdditionWorkWidth
    omega
  have halgebraStep := paAlgebraStepCostEnvelope_mono_short hwork
  have hincrement :=
    binaryNumeralIncrementPayloadPolynomial_mono_short hwork
  have halgebra : paAdditionAlgebraCostEnvelope small <=
      paAdditionAlgebraCostEnvelope large := by
    unfold paAdditionAlgebraCostEnvelope
    gcongr
  have hlocal : paAdditionLocalCostEnvelope small <=
      paAdditionLocalCostEnvelope large := by
    unfold paAdditionLocalCostEnvelope
    gcongr
  unfold binaryNumeralAdditionPayloadPolynomial
  gcongr

theorem paMultiplicationWorkWidth_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    paMultiplicationWorkWidth small <= paMultiplicationWorkWidth large := by
  unfold paMultiplicationWorkWidth
  omega

theorem paMultiplicationTermCodeEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    paMultiplicationTermCodeEnvelope small <=
      paMultiplicationTermCodeEnvelope large := by
  unfold paMultiplicationTermCodeEnvelope
  exact paGeneratedTermCodeEnvelope_mono_short
    (paMultiplicationWorkWidth_mono_uniform hbound)

theorem multiplicationFormulaStageOne_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    multiplicationFormulaStage1 small <=
      multiplicationFormulaStage1 large := by
  exact substitutionFormulaCodeEnvelope_mono_short le_rfl hbound

theorem multiplicationFormulaStageTwo_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    multiplicationFormulaStage2 small <=
      multiplicationFormulaStage2 large := by
  exact substitutionFormulaCodeEnvelope_mono_short
    (multiplicationFormulaStageOne_mono_uniform hbound) hbound

theorem multiplicationFormulaCodeEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    multiplicationFormulaCodeEnvelope small <=
      multiplicationFormulaCodeEnvelope large := by
  have hstageOne := multiplicationFormulaStageOne_mono_uniform hbound
  have hstageTwo := multiplicationFormulaStageTwo_mono_uniform hbound
  unfold multiplicationFormulaCodeEnvelope
  omega

theorem multiplicationSpecializationCostEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    multiplicationSpecializationCostEnvelope small <=
      multiplicationSpecializationCostEnvelope large := by
  have hformula := multiplicationFormulaCodeEnvelope_mono_uniform hbound
  have hscale : multiplicationSpecializationScaleEnvelope small <=
      multiplicationSpecializationScaleEnvelope large := by
    unfold multiplicationSpecializationScaleEnvelope
    omega
  unfold multiplicationSpecializationCostEnvelope
  gcongr

theorem paMultiplicationPrimitiveCostEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    paMultiplicationPrimitiveCostEnvelope small <=
      paMultiplicationPrimitiveCostEnvelope large := by
  have hterms := paMultiplicationTermCodeEnvelope_mono_uniform hbound
  have hspecialization :=
    multiplicationSpecializationCostEnvelope_mono_uniform hterms
  have hprimitive := paPrimitiveCostEnvelope_mono_short hterms
  unfold paMultiplicationPrimitiveCostEnvelope
  dsimp only
  omega

theorem paBinaryOneBaseCostEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    paBinaryOneBaseCostEnvelope small <=
      paBinaryOneBaseCostEnvelope large := by
  have halgebra := paAlgebraStepCostEnvelope_mono_short hbound
  unfold paBinaryOneBaseCostEnvelope
  omega

theorem paMultiplicationLocalCostEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    paMultiplicationLocalCostEnvelope small <=
      paMultiplicationLocalCostEnvelope large := by
  have hprimitive := paMultiplicationPrimitiveCostEnvelope_mono_uniform hbound
  have hwork := paMultiplicationWorkWidth_mono_uniform hbound
  have haddition := binaryNumeralAdditionPayloadPolynomial_mono_uniform hwork
  have hone := paBinaryOneBaseCostEnvelope_mono_uniform hwork
  unfold paMultiplicationLocalCostEnvelope
  omega

theorem paMultiplicationStepCostEnvelope_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    paMultiplicationStepCostEnvelope small <=
      paMultiplicationStepCostEnvelope large := by
  have hlocal := paMultiplicationLocalCostEnvelope_mono_uniform hbound
  unfold paMultiplicationStepCostEnvelope
  omega

theorem binaryNumeralMultiplicationPayloadPolynomial_mono_uniform
    {small large : Nat} (hbound : small <= large) :
    binaryNumeralMultiplicationPayloadPolynomial small <=
      binaryNumeralMultiplicationPayloadPolynomial large := by
  have hstep := paMultiplicationStepCostEnvelope_mono_uniform hbound
  unfold binaryNumeralMultiplicationPayloadPolynomial
  gcongr

/-! ## Uniform normalization recursion -/

def additionNormalizationStepTermCodeUniformEnvelope
    (numericBound : Nat) (args : Fin 2 -> ValuationTerm) : Nat :=
  let leftNumeralBound :=
    valuationTermShortNumeralCodeEnvelope numericBound (args 0)
  let rightNumeralBound :=
    valuationTermShortNumeralCodeEnvelope numericBound (args 1)
  let leftInstantiatedBound :=
    instantiatedValuationTermCodeEnvelope numericBound (args 0)
  let rightInstantiatedBound :=
    instantiatedValuationTermCodeEnvelope numericBound (args 1)
  let sourceBound := leftNumeralBound + rightNumeralBound +
    binaryFunctionTermCodeOverhead Language.Add.add
  let middleBound := leftInstantiatedBound + rightInstantiatedBound +
    binaryFunctionTermCodeOverhead Language.Add.add
  let resultBound := valuationTermShortNumeralCodeEnvelope numericBound
    (.func .add args : ValuationTerm)
  leftNumeralBound + rightNumeralBound + leftInstantiatedBound +
    rightInstantiatedBound + sourceBound + middleBound + resultBound + 1

def multiplicationNormalizationStepTermCodeUniformEnvelope
    (numericBound : Nat) (args : Fin 2 -> ValuationTerm) : Nat :=
  let leftNumeralBound :=
    valuationTermShortNumeralCodeEnvelope numericBound (args 0)
  let rightNumeralBound :=
    valuationTermShortNumeralCodeEnvelope numericBound (args 1)
  let leftInstantiatedBound :=
    instantiatedValuationTermCodeEnvelope numericBound (args 0)
  let rightInstantiatedBound :=
    instantiatedValuationTermCodeEnvelope numericBound (args 1)
  let sourceBound := leftNumeralBound + rightNumeralBound +
    binaryFunctionTermCodeOverhead Language.Mul.mul
  let middleBound := leftInstantiatedBound + rightInstantiatedBound +
    binaryFunctionTermCodeOverhead Language.Mul.mul
  let resultBound := valuationTermShortNumeralCodeEnvelope numericBound
    (.func .mul args : ValuationTerm)
  leftNumeralBound + rightNumeralBound + leftInstantiatedBound +
    rightInstantiatedBound + sourceBound + middleBound + resultBound + 1

theorem additionNormalizationStepTermCodeResource_le_uniform
    (valuation : Nat -> Nat) (numericBound : Nat)
    (args : Fin 2 -> ValuationTerm)
    (hvalues : forall index,
      index ∈ (.func .add args : ValuationTerm).freeVariables ->
        valuation index <= numericBound) :
    additionNormalizationStepTermCodeResource valuation args <=
      additionNormalizationStepTermCodeUniformEnvelope numericBound args := by
  have hleftVars : forall index, index ∈ (args 0).freeVariables ->
      valuation index <= numericBound := by
    intro index hindex
    exact hvalues index
      (freeVariables_arg_subset_func Language.Add.add args 0 hindex)
  have hrightVars : forall index, index ∈ (args 1).freeVariables ->
      valuation index <= numericBound := by
    intro index hindex
    exact hvalues index
      (freeVariables_arg_subset_func Language.Add.add args 1 hindex)
  have hleftNumeral := shortNumeralTerm_code_length_le_uniform
    valuation numericBound (args 0) hleftVars
  have hrightNumeral := shortNumeralTerm_code_length_le_uniform
    valuation numericBound (args 1) hrightVars
  have hleftInstantiated := instantiateTerm_code_length_le_uniform
    valuation numericBound (args 0) hleftVars
  have hrightInstantiated := instantiateTerm_code_length_le_uniform
    valuation numericBound (args 1) hrightVars
  have hsource := paAddTerm_code_length_le
    (shortBinaryNumeralTerm (termValue valuation (args 0)))
    (shortBinaryNumeralTerm (termValue valuation (args 1)))
  have hmiddle := paAddTerm_code_length_le
    (instantiateTerm valuation (args 0))
    (instantiateTerm valuation (args 1))
  have hresult := shortNumeralTerm_code_length_le_uniform valuation
    numericBound (.func .add args : ValuationTerm) hvalues
  simp only [termValue_add] at hresult
  unfold additionNormalizationStepTermCodeResource
    additionNormalizationStepTermCodeUniformEnvelope
  dsimp only
  omega

theorem multiplicationNormalizationStepTermCodeResource_le_uniform
    (valuation : Nat -> Nat) (numericBound : Nat)
    (args : Fin 2 -> ValuationTerm)
    (hvalues : forall index,
      index ∈ (.func .mul args : ValuationTerm).freeVariables ->
        valuation index <= numericBound) :
    multiplicationNormalizationStepTermCodeResource valuation args <=
      multiplicationNormalizationStepTermCodeUniformEnvelope numericBound
        args := by
  have hleftVars : forall index, index ∈ (args 0).freeVariables ->
      valuation index <= numericBound := by
    intro index hindex
    exact hvalues index
      (freeVariables_arg_subset_func Language.Mul.mul args 0 hindex)
  have hrightVars : forall index, index ∈ (args 1).freeVariables ->
      valuation index <= numericBound := by
    intro index hindex
    exact hvalues index
      (freeVariables_arg_subset_func Language.Mul.mul args 1 hindex)
  have hleftNumeral := shortNumeralTerm_code_length_le_uniform
    valuation numericBound (args 0) hleftVars
  have hrightNumeral := shortNumeralTerm_code_length_le_uniform
    valuation numericBound (args 1) hrightVars
  have hleftInstantiated := instantiateTerm_code_length_le_uniform
    valuation numericBound (args 0) hleftVars
  have hrightInstantiated := instantiateTerm_code_length_le_uniform
    valuation numericBound (args 1) hrightVars
  have hsource := paMulTerm_code_length_le
    (shortBinaryNumeralTerm (termValue valuation (args 0)))
    (shortBinaryNumeralTerm (termValue valuation (args 1)))
  have hmiddle := paMulTerm_code_length_le
    (instantiateTerm valuation (args 0))
    (instantiateTerm valuation (args 1))
  have hresult := shortNumeralTerm_code_length_le_uniform valuation
    numericBound (.func .mul args : ValuationTerm) hvalues
  simp only [termValue_mul] at hresult
  unfold multiplicationNormalizationStepTermCodeResource
    multiplicationNormalizationStepTermCodeUniformEnvelope
  dsimp only
  omega

def instantiatedTermNormalizationUniformPolynomial
    (numericBound : Nat) : ValuationTerm -> Nat
  | #index => Fin.elim0 index
  | &_ => shortToIteratedPayloadPolynomial numericBound
  | .func .zero _ => shortToIteratedPayloadPolynomial 0
  | .func .one _ => paMultiplicationLocalCostEnvelope 0
  | .func .add args =>
      instantiatedTermNormalizationUniformPolynomial numericBound (args 0) +
        instantiatedTermNormalizationUniformPolynomial numericBound (args 1) +
        binaryNumeralAdditionPayloadPolynomial
          (valuationTermValueEnvelope numericBound (args 0) +
            valuationTermValueEnvelope numericBound (args 1)) +
        3 * paPrimitiveCostEnvelope
          (additionNormalizationStepTermCodeUniformEnvelope numericBound args)
  | .func .mul args =>
      instantiatedTermNormalizationUniformPolynomial numericBound (args 0) +
        instantiatedTermNormalizationUniformPolynomial numericBound (args 1) +
        binaryNumeralMultiplicationPayloadPolynomial
          (valuationTermValueEnvelope numericBound (args 0) +
            valuationTermValueEnvelope numericBound (args 1)) +
        3 * paPrimitiveCostEnvelope
          (multiplicationNormalizationStepTermCodeUniformEnvelope
            numericBound args)

theorem instantiatedTermNormalizationPayloadPolynomial_le_uniform
    (valuation : Nat -> Nat) (numericBound : Nat) :
    (term : ValuationTerm) ->
      (forall index, index ∈ term.freeVariables ->
        valuation index <= numericBound) ->
      instantiatedTermNormalizationPayloadPolynomial valuation term <=
        instantiatedTermNormalizationUniformPolynomial numericBound term
  | #index, _ => Fin.elim0 index
  | &index, hvalues => by
      have hvalue := hvalues index (by simp)
      simpa only [instantiatedTermNormalizationPayloadPolynomial,
        instantiatedTermNormalizationUniformPolynomial] using
        shortToIteratedPayloadPolynomial_mono_public hvalue
  | .func .zero args, _ => by
      simp only [instantiatedTermNormalizationPayloadPolynomial,
        instantiatedTermNormalizationUniformPolynomial]
      exact le_rfl
  | .func .one args, _ => by
      simp only [instantiatedTermNormalizationPayloadPolynomial,
        instantiatedTermNormalizationUniformPolynomial]
      exact le_rfl
  | .func .add args, hvalues => by
      have hleftVars : forall index, index ∈ (args 0).freeVariables ->
          valuation index <= numericBound := by
        intro index hindex
        exact hvalues index
          (freeVariables_arg_subset_func Language.Add.add args 0 hindex)
      have hrightVars : forall index, index ∈ (args 1).freeVariables ->
          valuation index <= numericBound := by
        intro index hindex
        exact hvalues index
          (freeVariables_arg_subset_func Language.Add.add args 1 hindex)
      have hleft := instantiatedTermNormalizationPayloadPolynomial_le_uniform
        valuation numericBound (args 0) hleftVars
      have hright := instantiatedTermNormalizationPayloadPolynomial_le_uniform
        valuation numericBound (args 1) hrightVars
      have hleftValue := termValue_le_valuationTermValueEnvelope
        valuation numericBound (args 0) hleftVars
      have hrightValue := termValue_le_valuationTermValueEnvelope
        valuation numericBound (args 1) hrightVars
      have hwidth : Nat.size (termValue valuation (args 0)) +
          Nat.size (termValue valuation (args 1)) <=
        valuationTermValueEnvelope numericBound (args 0) +
          valuationTermValueEnvelope numericBound (args 1) := by
        have hleftSize :=
          (natSize_le_self_uniform _).trans hleftValue
        have hrightSize :=
          (natSize_le_self_uniform _).trans hrightValue
        omega
      have harithmetic :=
        binaryNumeralAdditionPayloadPolynomial_mono_uniform hwidth
      have htermResource :=
        additionNormalizationStepTermCodeResource_le_uniform valuation
          numericBound args hvalues
      have hprimitive := paPrimitiveCostEnvelope_mono_short htermResource
      simp only [instantiatedTermNormalizationPayloadPolynomial,
        instantiatedTermNormalizationUniformPolynomial]
      omega

  | .func .mul args, hvalues => by
      have hleftVars : forall index, index ∈ (args 0).freeVariables ->
          valuation index <= numericBound := by
        intro index hindex
        exact hvalues index
          (freeVariables_arg_subset_func Language.Mul.mul args 0 hindex)
      have hrightVars : forall index, index ∈ (args 1).freeVariables ->
          valuation index <= numericBound := by
        intro index hindex
        exact hvalues index
          (freeVariables_arg_subset_func Language.Mul.mul args 1 hindex)
      have hleft := instantiatedTermNormalizationPayloadPolynomial_le_uniform
        valuation numericBound (args 0) hleftVars
      have hright := instantiatedTermNormalizationPayloadPolynomial_le_uniform
        valuation numericBound (args 1) hrightVars
      have hleftValue := termValue_le_valuationTermValueEnvelope
        valuation numericBound (args 0) hleftVars
      have hrightValue := termValue_le_valuationTermValueEnvelope
        valuation numericBound (args 1) hrightVars
      have hwidth : Nat.size (termValue valuation (args 0)) +
          Nat.size (termValue valuation (args 1)) <=
        valuationTermValueEnvelope numericBound (args 0) +
          valuationTermValueEnvelope numericBound (args 1) := by
        have hleftSize :=
          (natSize_le_self_uniform _).trans hleftValue
        have hrightSize :=
          (natSize_le_self_uniform _).trans hrightValue
        omega
      have harithmetic :=
        binaryNumeralMultiplicationPayloadPolynomial_mono_uniform hwidth
      have htermResource :=
        multiplicationNormalizationStepTermCodeResource_le_uniform valuation
          numericBound args hvalues
      have hprimitive := paPrimitiveCostEnvelope_mono_short htermResource
      simp only [instantiatedTermNormalizationPayloadPolynomial,
        instantiatedTermNormalizationUniformPolynomial]
      omega

/-! ## Contextualized normalization -/

def valuationTermEqualityFormulaResourceEnvelope
    (numericBound : Nat) (term : ValuationTerm) : Nat :=
  valuationTermContextFormulaCodeEnvelope numericBound term +
    paFormulaCodeEnvelope
      (valuationTermEqualityTermCodeEnvelope numericBound term) + 1

def contextualizedNormalizationUniformPayloadPolynomial
    (numericBound : Nat) (term : ValuationTerm) : Nat :=
  instantiatedTermNormalizationUniformPolynomial numericBound term +
    smallContextAssemblyEnvelope
      (valuationTermEqualityFormulaResourceEnvelope numericBound term)

theorem contextualizedNormalizationPayloadSyntaxPolynomial_le_uniform
    (valuation : Nat -> Nat) (numericBound : Nat) (term : ValuationTerm)
    (hvalues : forall index, index ∈ term.freeVariables ->
      valuation index <= numericBound) :
    contextualizedNormalizationPayloadSyntaxPolynomial valuation term <=
      contextualizedNormalizationUniformPayloadPolynomial numericBound
        term := by
  let Gamma := valuationContext term.freeVariables valuation
  let shortTerm := shortBinaryNumeralTerm (termValue valuation term)
  let instantiatedTerm := instantiateTerm valuation term
  let formula :=
    (“!!shortTerm = !!instantiatedTerm” : ValuationFormula)
  let termBound := valuationTermEqualityTermCodeEnvelope numericBound term
  let formulaResource :=
    valuationTermEqualityFormulaResourceEnvelope numericBound term
  have hcodes := valuationTermEqualityTermCodes_le_envelope valuation
    numericBound term hvalues
  have hformula : (binaryFormulaCode formula).length <=
      paFormulaCodeEnvelope termBound := by
    simpa only [formula, shortTerm, instantiatedTerm] using
      equalityFormula_code_length_le_paEnvelope shortTerm instantiatedTerm
        termBound hcodes.1 hcodes.2.1
  have hcontext := valuationTermContext_formulaCodeSum_le_envelope
    valuation numericBound term hvalues
  have hresource : contextFormulaResource Gamma formula <=
      formulaResource := by
    unfold contextFormulaResource formulaResource
      valuationTermEqualityFormulaResourceEnvelope
    dsimp only [Gamma, termBound] at hcontext hformula ⊢
    omega
  have hassembly := smallContextAssemblyEnvelope_mono_local hresource
  have hnormalization :=
    instantiatedTermNormalizationPayloadPolynomial_le_uniform
      valuation numericBound term hvalues
  unfold contextualizedNormalizationPayloadSyntaxPolynomial
    contextualizedNormalizationUniformPayloadPolynomial
  dsimp only [Gamma, shortTerm, instantiatedTerm, formula, termBound,
    formulaResource] at *
  omega

/-! ## Uniform function-congruence node -/

def valuationTermFunctionApplicationCodeEnvelope (termBound : Nat) : Nat :=
  2 * termBound + binaryFunctionTermCodeOverhead Language.Add.add +
    binaryFunctionTermCodeOverhead Language.Mul.mul + 1

def valuationTermCongruenceBaseFormulaCodeEnvelope (termBound : Nat) : Nat :=
  paFormulaCodeEnvelope
      (valuationTermFunctionApplicationCodeEnvelope termBound) +
    fixedPAFormulaSeed + 1

def valuationTermCongruenceInnerFormulaCodeEnvelope (termBound : Nat) : Nat :=
  2 * valuationTermCongruenceBaseFormulaCodeEnvelope termBound +
    (binaryNatCode 4).length

def valuationTermCongruenceAntecedentCodeEnvelope (termBound : Nat) : Nat :=
  valuationTermCongruenceBaseFormulaCodeEnvelope termBound +
    valuationTermCongruenceInnerFormulaCodeEnvelope termBound +
    (binaryNatCode 4).length

def valuationTermCongruenceImplicationCodeEnvelope (termBound : Nat) : Nat :=
  2 * valuationTermCongruenceAntecedentCodeEnvelope termBound +
    valuationTermCongruenceBaseFormulaCodeEnvelope termBound +
    (binaryNatCode 5).length

def valuationTermCongruenceFormulaClosureCodeEnvelope
    (termBound : Nat) : Nat :=
  4 * (valuationTermCongruenceBaseFormulaCodeEnvelope termBound +
    valuationTermCongruenceInnerFormulaCodeEnvelope termBound +
    valuationTermCongruenceAntecedentCodeEnvelope termBound +
    valuationTermCongruenceImplicationCodeEnvelope termBound + 1)

def valuationTermCongruenceFormulaResourceEnvelope
    (contextBound termBound : Nat) : Nat :=
  contextBound +
    9 * valuationTermCongruenceFormulaClosureCodeEnvelope termBound + 1

def valuationTermCongruenceTermResourceEnvelope (termBound : Nat) : Nat :=
  4 * termBound + 1

def contextualBinaryFunctionCongruenceLocalUniformEnvelope
    (contextBound termBound : Nat) : Nat :=
  2 * paPrimitiveCostEnvelope
      (valuationTermCongruenceTermResourceEnvelope termBound) +
    5 * smallContextAssemblyEnvelope
      (valuationTermCongruenceFormulaResourceEnvelope contextBound termBound)

theorem contextualBinaryFunctionCongruenceFormulaResource_le_uniform
    (Gamma : Finset ValuationFormula)
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond : ValuationTerm)
    (contextBound termBound : Nat)
    (hfunction : functionSymbol = Language.Add.add ∨
      functionSymbol = Language.Mul.mul)
    (hcontext : formulaCodeSum Gamma <= contextBound)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    contextualBinaryFunctionCongruenceFormulaResource Gamma functionSymbol
        leftFirst leftSecond rightFirst rightSecond <=
      valuationTermCongruenceFormulaResourceEnvelope contextBound
        termBound := by
  let firstFormula :=
    (“!!leftFirst = !!rightFirst” : ValuationFormula)
  let secondFormula :=
    (“!!leftSecond = !!rightSecond” : ValuationFormula)
  let truthFormula := (⊤ : ValuationFormula)
  let innerFormula := secondFormula ⋏ truthFormula
  let antecedentFormula := binaryFunctionCongruenceAntecedent
    leftFirst leftSecond rightFirst rightSecond
  let leftApplication :=
    binaryFunctionTerm functionSymbol leftFirst leftSecond
  let rightApplication :=
    binaryFunctionTerm functionSymbol rightFirst rightSecond
  let conclusionFormula := binaryFunctionCongruenceConclusion functionSymbol
    leftFirst leftSecond rightFirst rightSecond
  let implicationFormula := antecedentFormula 🡒 conclusionFormula
  let applicationBound :=
    valuationTermFunctionApplicationCodeEnvelope termBound
  let baseBound := valuationTermCongruenceBaseFormulaCodeEnvelope termBound
  let closureBound :=
    valuationTermCongruenceFormulaClosureCodeEnvelope termBound
  have hoverhead : binaryFunctionTermCodeOverhead functionSymbol <=
      binaryFunctionTermCodeOverhead Language.Add.add +
        binaryFunctionTermCodeOverhead Language.Mul.mul + 1 := by
    rcases hfunction with rfl | rfl <;> omega
  have htermToApplication : termBound <= applicationBound := by
    unfold applicationBound valuationTermFunctionApplicationCodeEnvelope
    omega
  have hleftApplication : (binaryTermCode leftApplication).length <=
      applicationBound := by
    have hraw := binaryFunctionTerm_code_length_le functionSymbol
      leftFirst leftSecond
    unfold leftApplication applicationBound
      valuationTermFunctionApplicationCodeEnvelope
    omega
  have hrightApplication : (binaryTermCode rightApplication).length <=
      applicationBound := by
    have hraw := binaryFunctionTerm_code_length_le functionSymbol
      rightFirst rightSecond
    unfold rightApplication applicationBound
      valuationTermFunctionApplicationCodeEnvelope
    omega
  have hfirstFormula : (binaryFormulaCode firstFormula).length <=
      baseBound := by
    have hraw := equalityFormula_code_length_le_paEnvelope leftFirst
      rightFirst applicationBound
      (hleftFirst.trans htermToApplication)
      (hrightFirst.trans htermToApplication)
    dsimp only [firstFormula, applicationBound] at hraw ⊢
    unfold baseBound valuationTermCongruenceBaseFormulaCodeEnvelope
    omega
  have hsecondFormula : (binaryFormulaCode secondFormula).length <=
      baseBound := by
    have hraw := equalityFormula_code_length_le_paEnvelope leftSecond
      rightSecond applicationBound
      (hleftSecond.trans htermToApplication)
      (hrightSecond.trans htermToApplication)
    dsimp only [secondFormula, applicationBound] at hraw ⊢
    unfold baseBound valuationTermCongruenceBaseFormulaCodeEnvelope
    omega
  have htruthFormula : (binaryFormulaCode truthFormula).length <=
      baseBound := by
    have hraw := truthFormula_code_length_le_seed
    dsimp only [truthFormula] at hraw ⊢
    unfold baseBound valuationTermCongruenceBaseFormulaCodeEnvelope
    omega
  have hinnerFormula : (binaryFormulaCode innerFormula).length <=
      valuationTermCongruenceInnerFormulaCodeEnvelope termBound := by
    have hraw := binaryFormulaCode_and_length_le_local
      secondFormula truthFormula
    dsimp only [innerFormula] at hraw ⊢
    dsimp only [baseBound] at hsecondFormula htruthFormula
    unfold valuationTermCongruenceInnerFormulaCodeEnvelope
    omega
  have hantecedentFormula :
      (binaryFormulaCode antecedentFormula).length <=
        valuationTermCongruenceAntecedentCodeEnvelope termBound := by
    have hraw := binaryFormulaCode_and_length_le_local
      firstFormula innerFormula
    have heq : antecedentFormula = firstFormula ⋏ innerFormula := by
      simp [antecedentFormula, firstFormula, innerFormula, secondFormula,
        truthFormula, binaryFunctionCongruenceAntecedent]
    rw [heq]
    dsimp only [baseBound] at hfirstFormula
    unfold valuationTermCongruenceAntecedentCodeEnvelope
    omega
  have hconclusionFormula :
      (binaryFormulaCode conclusionFormula).length <= baseBound := by
    have hraw := equalityFormula_code_length_le_paEnvelope leftApplication
      rightApplication applicationBound hleftApplication hrightApplication
    have heq : conclusionFormula =
        (“!!leftApplication = !!rightApplication” : ValuationFormula) := by
      simp [conclusionFormula, leftApplication, rightApplication,
        binaryFunctionCongruenceConclusion]
    rw [heq]
    dsimp only [applicationBound] at hraw
    unfold baseBound valuationTermCongruenceBaseFormulaCodeEnvelope
    omega
  have himplicationFormula :
      (binaryFormulaCode implicationFormula).length <=
        valuationTermCongruenceImplicationCodeEnvelope termBound := by
    have hraw := binaryFormulaCode_implication_length_le antecedentFormula
      conclusionFormula
    dsimp only [implicationFormula] at hraw ⊢
    dsimp only [baseBound] at hconclusionFormula
    unfold valuationTermCongruenceImplicationCodeEnvelope
    omega
  have hbaseClosure : baseBound <= closureBound := by
    unfold baseBound closureBound
      valuationTermCongruenceFormulaClosureCodeEnvelope
    omega
  have hinnerClosure :
      valuationTermCongruenceInnerFormulaCodeEnvelope termBound <=
        closureBound := by
    unfold closureBound valuationTermCongruenceFormulaClosureCodeEnvelope
    omega
  have hantecedentClosure :
      valuationTermCongruenceAntecedentCodeEnvelope termBound <=
        closureBound := by
    unfold closureBound valuationTermCongruenceFormulaClosureCodeEnvelope
    omega
  have himplicationClosure :
      valuationTermCongruenceImplicationCodeEnvelope termBound <=
        closureBound := by
    unfold closureBound valuationTermCongruenceFormulaClosureCodeEnvelope
    omega
  have hnegatedImplication :
      (binaryFormulaCode (∼implicationFormula)).length <= closureBound := by
    have hraw :=
      FoundationCompactSyntaxTransformationCodeBounds.binaryFormulaCode_neg_length_le
        implicationFormula
    unfold closureBound valuationTermCongruenceFormulaClosureCodeEnvelope
    omega
  have hnegatedConclusion :
      (binaryFormulaCode (∼conclusionFormula)).length <= closureBound := by
    have hraw :=
      FoundationCompactSyntaxTransformationCodeBounds.binaryFormulaCode_neg_length_le
        conclusionFormula
    unfold closureBound valuationTermCongruenceFormulaClosureCodeEnvelope
    omega
  have hfirstClosure := hfirstFormula.trans hbaseClosure
  have hsecondClosure := hsecondFormula.trans hbaseClosure
  have htruthClosure := htruthFormula.trans hbaseClosure
  have hinnerClosure' := hinnerFormula.trans hinnerClosure
  have hantecedentClosure' := hantecedentFormula.trans hantecedentClosure
  have hconclusionClosure := hconclusionFormula.trans hbaseClosure
  have himplicationClosure' := himplicationFormula.trans himplicationClosure
  unfold contextualBinaryFunctionCongruenceFormulaResource
    valuationTermCongruenceFormulaResourceEnvelope
  dsimp only [firstFormula, secondFormula, truthFormula, innerFormula,
    antecedentFormula, conclusionFormula, implicationFormula,
    applicationBound, baseBound, closureBound] at *
  omega

theorem contextualBinaryFunctionCongruenceLocalEnvelope_le_uniform
    (Gamma : Finset ValuationFormula)
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (leftFirst leftSecond rightFirst rightSecond : ValuationTerm)
    (contextBound termBound : Nat)
    (hfunction : functionSymbol = Language.Add.add ∨
      functionSymbol = Language.Mul.mul)
    (hcontext : formulaCodeSum Gamma <= contextBound)
    (hleftFirst : (binaryTermCode leftFirst).length <= termBound)
    (hleftSecond : (binaryTermCode leftSecond).length <= termBound)
    (hrightFirst : (binaryTermCode rightFirst).length <= termBound)
    (hrightSecond : (binaryTermCode rightSecond).length <= termBound) :
    contextualBinaryFunctionCongruenceLocalEnvelope Gamma functionSymbol
        leftFirst leftSecond rightFirst rightSecond <=
      contextualBinaryFunctionCongruenceLocalUniformEnvelope contextBound
        termBound := by
  have htermResource :
      contextualBinaryFunctionCongruenceTermResource leftFirst leftSecond
          rightFirst rightSecond <=
        valuationTermCongruenceTermResourceEnvelope termBound := by
    unfold contextualBinaryFunctionCongruenceTermResource
      valuationTermCongruenceTermResourceEnvelope
    omega
  have hformulaResource :=
    contextualBinaryFunctionCongruenceFormulaResource_le_uniform Gamma
      functionSymbol leftFirst leftSecond rightFirst rightSecond contextBound
      termBound hfunction hcontext hleftFirst hleftSecond hrightFirst
      hrightSecond
  have hprimitive := paPrimitiveCostEnvelope_mono_short htermResource
  have hassembly := smallContextAssemblyEnvelope_mono_local hformulaResource
  unfold contextualBinaryFunctionCongruenceLocalEnvelope
    contextualBinaryFunctionCongruenceLocalUniformEnvelope
  omega

/-! ## Uniform instantiated-term transport node -/

def valuationTermTransportNodeTermCodeEnvelope
    (numericBound : Nat) (args : Fin 2 -> ValuationTerm) : Nat :=
  instantiatedValuationTermCodeEnvelope numericBound (args 0) +
    instantiatedValuationTermCodeEnvelope numericBound (args 1) +
    (binaryTermCode (args 0)).length +
    (binaryTermCode (args 1)).length + 1

def instantiatedTermTransportNodeUniformPolynomial
    (numericBound : Nat)
    (term : ValuationTerm)
    (args : Fin 2 -> ValuationTerm)
    (leftPayloadBound rightPayloadBound : Nat) : Nat :=
  let contextBound := valuationTermContextFormulaCodeEnvelope numericBound term
  let termBound := valuationTermTransportNodeTermCodeEnvelope numericBound args
  leftPayloadBound + rightPayloadBound +
    2 * smallContextAssemblyEnvelope
      (valuationTermCongruenceFormulaResourceEnvelope contextBound termBound) +
    contextualBinaryFunctionCongruenceLocalUniformEnvelope contextBound
      termBound

theorem instantiatedTermTransportNodePayloadPolynomial_le_uniform
    (valuation : Nat -> Nat)
    (numericBound : Nat)
    (term : ValuationTerm)
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (leftPayloadBound rightPayloadBound : Nat)
    (leftUniformBound rightUniformBound : Nat)
    (hfunction : functionSymbol = Language.Add.add ∨
      functionSymbol = Language.Mul.mul)
    (hvalues : forall index, index ∈ term.freeVariables ->
      valuation index <= numericBound)
    (hleftValues : forall index, index ∈ (args 0).freeVariables ->
      valuation index <= numericBound)
    (hrightValues : forall index, index ∈ (args 1).freeVariables ->
      valuation index <= numericBound)
    (hleftPayload : leftPayloadBound <= leftUniformBound)
    (hrightPayload : rightPayloadBound <= rightUniformBound) :
    instantiatedTermTransportNodePayloadPolynomial valuation term
        functionSymbol args leftPayloadBound rightPayloadBound <=
      instantiatedTermTransportNodeUniformPolynomial numericBound term
        args leftUniformBound rightUniformBound := by
  let Gamma := valuationContext term.freeVariables valuation
  let leftFirst := instantiateTerm valuation (args 0)
  let leftSecond := instantiateTerm valuation (args 1)
  let rightFirst := args 0
  let rightSecond := args 1
  let contextBound := valuationTermContextFormulaCodeEnvelope numericBound term
  let termBound := valuationTermTransportNodeTermCodeEnvelope numericBound args
  let formulaResource :=
    contextualBinaryFunctionCongruenceFormulaResource Gamma functionSymbol
      leftFirst leftSecond rightFirst rightSecond
  let uniformFormulaResource :=
    valuationTermCongruenceFormulaResourceEnvelope contextBound termBound
  have hcontext : formulaCodeSum Gamma <= contextBound := by
    dsimp only [Gamma, contextBound]
    exact valuationTermContext_formulaCodeSum_le_envelope valuation
      numericBound term hvalues
  have hleftFirstRaw := instantiateTerm_code_length_le_uniform valuation
    numericBound (args 0) hleftValues
  have hleftSecondRaw := instantiateTerm_code_length_le_uniform valuation
    numericBound (args 1) hrightValues
  have hleftFirst : (binaryTermCode leftFirst).length <= termBound := by
    dsimp only [leftFirst, termBound]
    unfold valuationTermTransportNodeTermCodeEnvelope
    omega
  have hleftSecond : (binaryTermCode leftSecond).length <= termBound := by
    dsimp only [leftSecond, termBound]
    unfold valuationTermTransportNodeTermCodeEnvelope
    omega
  have hrightFirst : (binaryTermCode rightFirst).length <= termBound := by
    dsimp only [rightFirst, termBound]
    unfold valuationTermTransportNodeTermCodeEnvelope
    omega
  have hrightSecond : (binaryTermCode rightSecond).length <= termBound := by
    dsimp only [rightSecond, termBound]
    unfold valuationTermTransportNodeTermCodeEnvelope
    omega
  have hformulaResource : formulaResource <= uniformFormulaResource := by
    dsimp only [formulaResource, uniformFormulaResource]
    exact contextualBinaryFunctionCongruenceFormulaResource_le_uniform
      Gamma functionSymbol leftFirst leftSecond rightFirst rightSecond
      contextBound termBound hfunction hcontext hleftFirst hleftSecond
      hrightFirst hrightSecond
  have hassembly := smallContextAssemblyEnvelope_mono_local hformulaResource
  have hlocal := contextualBinaryFunctionCongruenceLocalEnvelope_le_uniform
    Gamma functionSymbol leftFirst leftSecond rightFirst rightSecond
    contextBound termBound hfunction hcontext hleftFirst hleftSecond
    hrightFirst hrightSecond
  unfold instantiatedTermTransportNodePayloadPolynomial
    instantiatedTermTransportNodeUniformPolynomial
  dsimp only [Gamma, leftFirst, leftSecond, rightFirst, rightSecond,
    contextBound, termBound, formulaResource, uniformFormulaResource] at *
  omega

/-! ## Uniform instantiated-term transport recursion -/

theorem instantiatedTermTransportContextFormulaResource_le_uniform
    (valuation : Nat -> Nat) (numericBound : Nat) (term : ValuationTerm)
    (hvalues : forall index, index ∈ term.freeVariables ->
      valuation index <= numericBound) :
    contextFormulaResource
        (valuationContext term.freeVariables valuation)
        (“!!(instantiateTerm valuation term) = !!term” : ValuationFormula) <=
      valuationTermEqualityFormulaResourceEnvelope numericBound term := by
  let instantiatedTerm := instantiateTerm valuation term
  let formula :=
    (“!!instantiatedTerm = !!term” : ValuationFormula)
  let termBound := valuationTermEqualityTermCodeEnvelope numericBound term
  have hcodes := valuationTermEqualityTermCodes_le_envelope valuation
    numericBound term hvalues
  have hformula : (binaryFormulaCode formula).length <=
      paFormulaCodeEnvelope termBound := by
    simpa only [formula, instantiatedTerm] using
      equalityFormula_code_length_le_paEnvelope instantiatedTerm term
        termBound hcodes.2.1 hcodes.2.2
  have hcontext := valuationTermContext_formulaCodeSum_le_envelope valuation
    numericBound term hvalues
  unfold contextFormulaResource valuationTermEqualityFormulaResourceEnvelope
  dsimp only [instantiatedTerm, formula, termBound] at hformula
  omega

def instantiatedTermTransportUniformPolynomial
    (numericBound : Nat) : ValuationTerm -> Nat
  | #index => Fin.elim0 index
  | &index =>
      smallContextAssemblyEnvelope
        (valuationTermEqualityFormulaResourceEnvelope numericBound
          (&index : ValuationTerm))
  | .func .zero args =>
      let term := (.func .zero args : ValuationTerm)
      paPrimitiveCostEnvelope
          (valuationTermEqualityTermCodeEnvelope numericBound term) +
        smallContextAssemblyEnvelope
          (valuationTermEqualityFormulaResourceEnvelope numericBound term)
  | .func .one args =>
      let term := (.func .one args : ValuationTerm)
      paPrimitiveCostEnvelope
          (valuationTermEqualityTermCodeEnvelope numericBound term) +
        smallContextAssemblyEnvelope
          (valuationTermEqualityFormulaResourceEnvelope numericBound term)
  | .func .add args =>
      instantiatedTermTransportNodeUniformPolynomial numericBound
        (.func .add args : ValuationTerm) args
        (instantiatedTermTransportUniformPolynomial numericBound (args 0))
        (instantiatedTermTransportUniformPolynomial numericBound (args 1))
  | .func .mul args =>
      instantiatedTermTransportNodeUniformPolynomial numericBound
        (.func .mul args : ValuationTerm) args
        (instantiatedTermTransportUniformPolynomial numericBound (args 0))
        (instantiatedTermTransportUniformPolynomial numericBound (args 1))

theorem instantiatedTermTransportPayloadPolynomial_le_uniform
    (valuation : Nat -> Nat) (numericBound : Nat) :
    (term : ValuationTerm) ->
      (forall index, index ∈ term.freeVariables ->
        valuation index <= numericBound) ->
      instantiatedTermTransportPayloadPolynomial valuation term <=
        instantiatedTermTransportUniformPolynomial numericBound term
  | #index, _ => Fin.elim0 index
  | &index, hvalues => by
      have hresource :=
        instantiatedTermTransportContextFormulaResource_le_uniform valuation
          numericBound (&index : ValuationTerm) hvalues
      have hassembly := smallContextAssemblyEnvelope_mono_local hresource
      simpa only [instantiatedTermTransportPayloadPolynomial,
        instantiatedTermTransportUniformPolynomial, instantiateTerm,
        Semiterm.freeVariables_fvar] using hassembly
  | .func .zero args, hvalues => by
      let term := (.func .zero args : ValuationTerm)
      have hresource :=
        instantiatedTermTransportContextFormulaResource_le_uniform valuation
          numericBound term hvalues
      have hassembly := smallContextAssemblyEnvelope_mono_local hresource
      have hcodes := valuationTermEqualityTermCodes_le_envelope valuation
        numericBound term hvalues
      have hprimitive := paPrimitiveCostEnvelope_mono_short hcodes.2.2
      simp only [instantiatedTermTransportPayloadPolynomial,
        instantiatedTermTransportUniformPolynomial]
      dsimp only [term] at hassembly hprimitive ⊢
      omega
  | .func .one args, hvalues => by
      let term := (.func .one args : ValuationTerm)
      have hresource :=
        instantiatedTermTransportContextFormulaResource_le_uniform valuation
          numericBound term hvalues
      have hassembly := smallContextAssemblyEnvelope_mono_local hresource
      have hcodes := valuationTermEqualityTermCodes_le_envelope valuation
        numericBound term hvalues
      have hprimitive := paPrimitiveCostEnvelope_mono_short hcodes.2.2
      simp only [instantiatedTermTransportPayloadPolynomial,
        instantiatedTermTransportUniformPolynomial]
      dsimp only [term] at hassembly hprimitive ⊢
      omega
  | .func .add args, hvalues => by
      have hleftValues : forall index, index ∈ (args 0).freeVariables ->
          valuation index <= numericBound := by
        intro index hindex
        exact hvalues index
          (freeVariables_arg_subset_func Language.Add.add args 0 hindex)
      have hrightValues : forall index, index ∈ (args 1).freeVariables ->
          valuation index <= numericBound := by
        intro index hindex
        exact hvalues index
          (freeVariables_arg_subset_func Language.Add.add args 1 hindex)
      have hleft := instantiatedTermTransportPayloadPolynomial_le_uniform
        valuation numericBound (args 0) hleftValues
      have hright := instantiatedTermTransportPayloadPolynomial_le_uniform
        valuation numericBound (args 1) hrightValues
      simpa only [instantiatedTermTransportPayloadPolynomial,
        instantiatedTermTransportUniformPolynomial] using
        instantiatedTermTransportNodePayloadPolynomial_le_uniform valuation
          numericBound (.func .add args : ValuationTerm) Language.Add.add args
          (instantiatedTermTransportPayloadPolynomial valuation (args 0))
          (instantiatedTermTransportPayloadPolynomial valuation (args 1))
          (instantiatedTermTransportUniformPolynomial numericBound (args 0))
          (instantiatedTermTransportUniformPolynomial numericBound (args 1))
          (Or.inl rfl) hvalues hleftValues hrightValues hleft hright
  | .func .mul args, hvalues => by
      have hleftValues : forall index, index ∈ (args 0).freeVariables ->
          valuation index <= numericBound := by
        intro index hindex
        exact hvalues index
          (freeVariables_arg_subset_func Language.Mul.mul args 0 hindex)
      have hrightValues : forall index, index ∈ (args 1).freeVariables ->
          valuation index <= numericBound := by
        intro index hindex
        exact hvalues index
          (freeVariables_arg_subset_func Language.Mul.mul args 1 hindex)
      have hleft := instantiatedTermTransportPayloadPolynomial_le_uniform
        valuation numericBound (args 0) hleftValues
      have hright := instantiatedTermTransportPayloadPolynomial_le_uniform
        valuation numericBound (args 1) hrightValues
      simpa only [instantiatedTermTransportPayloadPolynomial,
        instantiatedTermTransportUniformPolynomial] using
        instantiatedTermTransportNodePayloadPolynomial_le_uniform valuation
          numericBound (.func .mul args : ValuationTerm) Language.Mul.mul args
          (instantiatedTermTransportPayloadPolynomial valuation (args 0))
          (instantiatedTermTransportPayloadPolynomial valuation (args 1))
          (instantiatedTermTransportUniformPolynomial numericBound (args 0))
          (instantiatedTermTransportUniformPolynomial numericBound (args 1))
          (Or.inr rfl) hvalues hleftValues hrightValues hleft hright

/-! ## Closed uniform term-equality compiler -/

def compileTermValueEqualityUniformPayloadPolynomial
    (numericBound : Nat) (term : ValuationTerm) : Nat :=
  contextualEqualityTransitivityUniformPayloadBound
    (valuationTermContextFormulaCodeEnvelope numericBound term)
    (valuationTermEqualityTermCodeEnvelope numericBound term)
    (contextualizedNormalizationUniformPayloadPolynomial numericBound term)
    (instantiatedTermTransportUniformPolynomial numericBound term)

theorem compileTermValueEqualityPayloadPolynomial_le_coordinate
    (valuation : Nat -> Nat) (numericBound : Nat) (term : ValuationTerm)
    (hcard : term.freeVariables.card <= 4)
    (hvalues : forall index, index ∈ term.freeVariables ->
      valuation index <= numericBound) :
    compileTermValueEqualityPayloadPolynomial valuation term <=
      compileTermValueEqualityUniformPayloadPolynomial numericBound term := by
  have hcontextCard :
      (valuationContext term.freeVariables valuation).card <= 4 :=
    valuationContext_card_le_four_of_card_le_four term.freeVariables valuation
      hcard
  have hcontext := valuationTermContext_formulaCodeSum_le_envelope valuation
    numericBound term hvalues
  have hcodes := valuationTermEqualityTermCodes_le_envelope valuation
    numericBound term hvalues
  have hnormalization :=
    contextualizedNormalizationPayloadSyntaxPolynomial_le_uniform valuation
      numericBound term hvalues
  have htransport :=
    instantiatedTermTransportPayloadPolynomial_le_uniform valuation
      numericBound term hvalues
  unfold compileTermValueEqualityUniformPayloadPolynomial
  exact compileTermValueEqualityPayloadPolynomial_le_uniform valuation term
    (valuationTermContextFormulaCodeEnvelope numericBound term)
    (valuationTermEqualityTermCodeEnvelope numericBound term)
    (contextualizedNormalizationUniformPayloadPolynomial numericBound term)
    (instantiatedTermTransportUniformPolynomial numericBound term)
    hcontextCard hcontext hcodes.1 hcodes.2.1 hcodes.2.2 hnormalization
    htransport

#print axioms termValue_le_valuationTermValueEnvelope
#print axioms instantiateTerm_code_length_le_uniform
#print axioms shortNumeralTerm_code_length_le_uniform
#print axioms valuationTermContext_formulaCodeSum_le_envelope
#print axioms binaryNumeralMultiplicationPayloadPolynomial_mono_uniform
#print axioms additionNormalizationStepTermCodeResource_le_uniform
#print axioms multiplicationNormalizationStepTermCodeResource_le_uniform
#print axioms instantiatedTermNormalizationPayloadPolynomial_le_uniform
#print axioms
  contextualizedNormalizationPayloadSyntaxPolynomial_le_uniform
#print axioms
  contextualBinaryFunctionCongruenceFormulaResource_le_uniform
#print axioms
  contextualBinaryFunctionCongruenceLocalEnvelope_le_uniform
#print axioms
  instantiatedTermTransportNodePayloadPolynomial_le_uniform
#print axioms
  instantiatedTermTransportContextFormulaResource_le_uniform
#print axioms
  instantiatedTermTransportPayloadPolynomial_le_uniform
#print axioms
  compileTermValueEqualityPayloadPolynomial_le_coordinate

end FoundationCompactPAValuationTermCompilerUniformBounds
