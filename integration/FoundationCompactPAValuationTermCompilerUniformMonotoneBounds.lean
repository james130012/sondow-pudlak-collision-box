import integration.FoundationCompactPAValuationTermCompilerUniformBounds

/-!
# Monotonicity of uniform valuation-term compiler resources

For a fixed valuation term, every uniform compiler coordinate is monotone in
the common numeric bound.  This is the bridge needed to replace the four
fixed-width bit-leaf equality coordinates by one public row scale.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactPAValuationTermCompilerUniformMonotoneBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAExponentialShortNumeralCompilerBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerBounds
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationTermCompilerUniformBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds

theorem valuationTermValueEnvelope_mono
    {small large : Nat} (hbound : small <= large) :
    (term : ValuationTerm) ->
      valuationTermValueEnvelope small term <=
        valuationTermValueEnvelope large term
  | #index => Fin.elim0 index
  | &_ => hbound
  | .func .zero _ => le_rfl
  | .func .one _ => le_rfl
  | .func .add args => by
      simp only [valuationTermValueEnvelope]
      exact Nat.add_le_add
        (valuationTermValueEnvelope_mono hbound (args 0))
        (valuationTermValueEnvelope_mono hbound (args 1))
  | .func .mul args => by
      simp only [valuationTermValueEnvelope]
      exact Nat.mul_le_mul
        (valuationTermValueEnvelope_mono hbound (args 0))
        (valuationTermValueEnvelope_mono hbound (args 1))

theorem instantiatedValuationTermCodeEnvelope_mono
    {small large : Nat} (hbound : small <= large) :
    (term : ValuationTerm) ->
      instantiatedValuationTermCodeEnvelope small term <=
        instantiatedValuationTermCodeEnvelope large term
  | #index => Fin.elim0 index
  | &_ => iteratedSuccessorTermCodePolynomial_mono 0 hbound
  | .func .zero _ => le_rfl
  | .func .one _ => le_rfl
  | .func .add args => by
      simp only [instantiatedValuationTermCodeEnvelope]
      exact Nat.add_le_add_right
        (Nat.add_le_add
          (instantiatedValuationTermCodeEnvelope_mono hbound (args 0))
          (instantiatedValuationTermCodeEnvelope_mono hbound (args 1))) _
  | .func .mul args => by
      simp only [instantiatedValuationTermCodeEnvelope]
      exact Nat.add_le_add_right
        (Nat.add_le_add
          (instantiatedValuationTermCodeEnvelope_mono hbound (args 0))
          (instantiatedValuationTermCodeEnvelope_mono hbound (args 1))) _

theorem valuationTermShortNumeralCodeEnvelope_mono
    {small large : Nat} (hbound : small <= large)
    (term : ValuationTerm) :
    valuationTermShortNumeralCodeEnvelope small term <=
      valuationTermShortNumeralCodeEnvelope large term := by
  unfold valuationTermShortNumeralCodeEnvelope
  exact binaryNumeralTermCodeEnvelope_mono_short
    (Nat.size_le_size (valuationTermValueEnvelope_mono hbound term))

theorem valuationTermEqualityTermCodeEnvelope_mono
    {small large : Nat} (hbound : small <= large)
    (term : ValuationTerm) :
    valuationTermEqualityTermCodeEnvelope small term <=
      valuationTermEqualityTermCodeEnvelope large term := by
  have hshort := valuationTermShortNumeralCodeEnvelope_mono hbound term
  have hinstantiated := instantiatedValuationTermCodeEnvelope_mono hbound term
  unfold valuationTermEqualityTermCodeEnvelope
  omega

theorem valuationContextFormulaCodeSumEnvelope_mono_numeric_uniform
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

theorem valuationTermContextFormulaCodeEnvelope_mono
    {small large : Nat} (hbound : small <= large)
    (term : ValuationTerm) :
    valuationTermContextFormulaCodeEnvelope small term <=
      valuationTermContextFormulaCodeEnvelope large term := by
  unfold valuationTermContextFormulaCodeEnvelope
  exact valuationContextFormulaCodeSumEnvelope_mono_numeric_uniform
    term.freeVariables.card (valuationTermVariableCodeEnvelope term) hbound

theorem additionNormalizationStepTermCodeUniformEnvelope_mono
    {small large : Nat} (hbound : small <= large)
    (args : Fin 2 -> ValuationTerm) :
    additionNormalizationStepTermCodeUniformEnvelope small args <=
      additionNormalizationStepTermCodeUniformEnvelope large args := by
  have hshortLeft := valuationTermShortNumeralCodeEnvelope_mono
    hbound (args 0)
  have hshortRight := valuationTermShortNumeralCodeEnvelope_mono
    hbound (args 1)
  have hinstantiatedLeft := instantiatedValuationTermCodeEnvelope_mono
    hbound (args 0)
  have hinstantiatedRight := instantiatedValuationTermCodeEnvelope_mono
    hbound (args 1)
  have hresult := valuationTermShortNumeralCodeEnvelope_mono hbound
    (.func .add args : ValuationTerm)
  unfold additionNormalizationStepTermCodeUniformEnvelope
  dsimp only
  omega

theorem multiplicationNormalizationStepTermCodeUniformEnvelope_mono
    {small large : Nat} (hbound : small <= large)
    (args : Fin 2 -> ValuationTerm) :
    multiplicationNormalizationStepTermCodeUniformEnvelope small args <=
      multiplicationNormalizationStepTermCodeUniformEnvelope large args := by
  have hshortLeft := valuationTermShortNumeralCodeEnvelope_mono
    hbound (args 0)
  have hshortRight := valuationTermShortNumeralCodeEnvelope_mono
    hbound (args 1)
  have hinstantiatedLeft := instantiatedValuationTermCodeEnvelope_mono
    hbound (args 0)
  have hinstantiatedRight := instantiatedValuationTermCodeEnvelope_mono
    hbound (args 1)
  have hresult := valuationTermShortNumeralCodeEnvelope_mono hbound
    (.func .mul args : ValuationTerm)
  unfold multiplicationNormalizationStepTermCodeUniformEnvelope
  dsimp only
  omega

theorem instantiatedTermNormalizationUniformPolynomial_mono
    {small large : Nat} (hbound : small <= large) :
    (term : ValuationTerm) ->
      instantiatedTermNormalizationUniformPolynomial small term <=
        instantiatedTermNormalizationUniformPolynomial large term
  | #index => Fin.elim0 index
  | &_ => shortToIteratedPayloadPolynomial_mono_public hbound
  | .func .zero _ => le_rfl
  | .func .one _ => le_rfl
  | .func .add args => by
      have hleft := instantiatedTermNormalizationUniformPolynomial_mono
        hbound (args 0)
      have hright := instantiatedTermNormalizationUniformPolynomial_mono
        hbound (args 1)
      have hleftValue := valuationTermValueEnvelope_mono hbound (args 0)
      have hrightValue := valuationTermValueEnvelope_mono hbound (args 1)
      have harithmetic := binaryNumeralAdditionPayloadPolynomial_mono_uniform
        (Nat.add_le_add (Nat.size_le_size hleftValue)
          (Nat.size_le_size hrightValue))
      have hterm := additionNormalizationStepTermCodeUniformEnvelope_mono
        hbound args
      have hprimitive := paPrimitiveCostEnvelope_mono_short hterm
      simp only [instantiatedTermNormalizationUniformPolynomial]
      omega
  | .func .mul args => by
      have hleft := instantiatedTermNormalizationUniformPolynomial_mono
        hbound (args 0)
      have hright := instantiatedTermNormalizationUniformPolynomial_mono
        hbound (args 1)
      have hleftValue := valuationTermValueEnvelope_mono hbound (args 0)
      have hrightValue := valuationTermValueEnvelope_mono hbound (args 1)
      have harithmetic :=
        binaryNumeralMultiplicationPayloadPolynomial_mono_uniform
          (Nat.add_le_add (Nat.size_le_size hleftValue)
            (Nat.size_le_size hrightValue))
      have hterm := multiplicationNormalizationStepTermCodeUniformEnvelope_mono
        hbound args
      have hprimitive := paPrimitiveCostEnvelope_mono_short hterm
      simp only [instantiatedTermNormalizationUniformPolynomial]
      omega

theorem valuationTermEqualityFormulaResourceEnvelope_mono
    {small large : Nat} (hbound : small <= large)
    (term : ValuationTerm) :
    valuationTermEqualityFormulaResourceEnvelope small term <=
      valuationTermEqualityFormulaResourceEnvelope large term := by
  have hcontext := valuationTermContextFormulaCodeEnvelope_mono hbound term
  have hterm := valuationTermEqualityTermCodeEnvelope_mono hbound term
  have hformula := paFormulaCodeEnvelope_mono_local hterm
  unfold valuationTermEqualityFormulaResourceEnvelope
  omega

theorem contextualizedNormalizationUniformPayloadPolynomial_mono
    {small large : Nat} (hbound : small <= large)
    (term : ValuationTerm) :
    contextualizedNormalizationUniformPayloadPolynomial small term <=
      contextualizedNormalizationUniformPayloadPolynomial large term := by
  have hnormalization := instantiatedTermNormalizationUniformPolynomial_mono
    hbound term
  have hformula := valuationTermEqualityFormulaResourceEnvelope_mono
    hbound term
  have hassembly := smallContextAssemblyEnvelope_mono_local hformula
  unfold contextualizedNormalizationUniformPayloadPolynomial
  omega

theorem valuationTermFunctionApplicationCodeEnvelope_mono
    {small large : Nat} (hbound : small <= large) :
    valuationTermFunctionApplicationCodeEnvelope small <=
      valuationTermFunctionApplicationCodeEnvelope large := by
  unfold valuationTermFunctionApplicationCodeEnvelope
  omega

theorem valuationTermCongruenceFormulaClosureCodeEnvelope_mono
    {small large : Nat} (hbound : small <= large) :
    valuationTermCongruenceFormulaClosureCodeEnvelope small <=
      valuationTermCongruenceFormulaClosureCodeEnvelope large := by
  have happlication := valuationTermFunctionApplicationCodeEnvelope_mono
    hbound
  have hbase : valuationTermCongruenceBaseFormulaCodeEnvelope small <=
      valuationTermCongruenceBaseFormulaCodeEnvelope large := by
    have hformula := paFormulaCodeEnvelope_mono_local happlication
    unfold valuationTermCongruenceBaseFormulaCodeEnvelope
    omega
  have hinner : valuationTermCongruenceInnerFormulaCodeEnvelope small <=
      valuationTermCongruenceInnerFormulaCodeEnvelope large := by
    unfold valuationTermCongruenceInnerFormulaCodeEnvelope
    omega
  have hantecedent :
      valuationTermCongruenceAntecedentCodeEnvelope small <=
        valuationTermCongruenceAntecedentCodeEnvelope large := by
    unfold valuationTermCongruenceAntecedentCodeEnvelope
    omega
  have himplication :
      valuationTermCongruenceImplicationCodeEnvelope small <=
        valuationTermCongruenceImplicationCodeEnvelope large := by
    unfold valuationTermCongruenceImplicationCodeEnvelope
    omega
  unfold valuationTermCongruenceFormulaClosureCodeEnvelope
  omega

theorem valuationTermCongruenceFormulaResourceEnvelope_mono
    {smallContext largeContext smallTerm largeTerm : Nat}
    (hcontext : smallContext <= largeContext)
    (hterm : smallTerm <= largeTerm) :
    valuationTermCongruenceFormulaResourceEnvelope smallContext smallTerm <=
      valuationTermCongruenceFormulaResourceEnvelope largeContext
        largeTerm := by
  have hclosure := valuationTermCongruenceFormulaClosureCodeEnvelope_mono
    hterm
  unfold valuationTermCongruenceFormulaResourceEnvelope
  omega

theorem valuationTermCongruenceTermResourceEnvelope_mono
    {small large : Nat} (hbound : small <= large) :
    valuationTermCongruenceTermResourceEnvelope small <=
      valuationTermCongruenceTermResourceEnvelope large := by
  unfold valuationTermCongruenceTermResourceEnvelope
  omega

theorem contextualBinaryFunctionCongruenceLocalUniformEnvelope_mono
    {smallContext largeContext smallTerm largeTerm : Nat}
    (hcontext : smallContext <= largeContext)
    (hterm : smallTerm <= largeTerm) :
    contextualBinaryFunctionCongruenceLocalUniformEnvelope smallContext
        smallTerm <=
      contextualBinaryFunctionCongruenceLocalUniformEnvelope largeContext
        largeTerm := by
  have htermResource := valuationTermCongruenceTermResourceEnvelope_mono hterm
  have hprimitive := paPrimitiveCostEnvelope_mono_short htermResource
  have hformula := valuationTermCongruenceFormulaResourceEnvelope_mono
    hcontext hterm
  have hassembly := smallContextAssemblyEnvelope_mono_local hformula
  unfold contextualBinaryFunctionCongruenceLocalUniformEnvelope
  omega

theorem valuationTermTransportNodeTermCodeEnvelope_mono
    {small large : Nat} (hbound : small <= large)
    (args : Fin 2 -> ValuationTerm) :
    valuationTermTransportNodeTermCodeEnvelope small args <=
      valuationTermTransportNodeTermCodeEnvelope large args := by
  have hleft := instantiatedValuationTermCodeEnvelope_mono hbound (args 0)
  have hright := instantiatedValuationTermCodeEnvelope_mono hbound (args 1)
  unfold valuationTermTransportNodeTermCodeEnvelope
  omega

theorem instantiatedTermTransportNodeUniformPolynomial_mono
    {small large smallLeft largeLeft smallRight largeRight : Nat}
    (hbound : small <= large)
    (term : ValuationTerm) (args : Fin 2 -> ValuationTerm)
    (hleft : smallLeft <= largeLeft)
    (hright : smallRight <= largeRight) :
    instantiatedTermTransportNodeUniformPolynomial small term args
        smallLeft smallRight <=
      instantiatedTermTransportNodeUniformPolynomial large term args
        largeLeft largeRight := by
  have hcontext := valuationTermContextFormulaCodeEnvelope_mono hbound term
  have hterm := valuationTermTransportNodeTermCodeEnvelope_mono hbound args
  have hformula := valuationTermCongruenceFormulaResourceEnvelope_mono
    hcontext hterm
  have hassembly := smallContextAssemblyEnvelope_mono_local hformula
  have hlocal :=
    contextualBinaryFunctionCongruenceLocalUniformEnvelope_mono
      hcontext hterm
  unfold instantiatedTermTransportNodeUniformPolynomial
  dsimp only
  omega

theorem instantiatedTermTransportUniformPolynomial_mono
    {small large : Nat} (hbound : small <= large) :
    (term : ValuationTerm) ->
      instantiatedTermTransportUniformPolynomial small term <=
        instantiatedTermTransportUniformPolynomial large term
  | #index => Fin.elim0 index
  | &index => by
      have hformula := valuationTermEqualityFormulaResourceEnvelope_mono
        hbound (&index : ValuationTerm)
      have hassembly := smallContextAssemblyEnvelope_mono_local hformula
      simpa only [instantiatedTermTransportUniformPolynomial] using hassembly
  | .func .zero args => by
      let term := (.func .zero args : ValuationTerm)
      have hterm := valuationTermEqualityTermCodeEnvelope_mono hbound term
      have hprimitive := paPrimitiveCostEnvelope_mono_short hterm
      have hformula := valuationTermEqualityFormulaResourceEnvelope_mono
        hbound term
      have hassembly := smallContextAssemblyEnvelope_mono_local hformula
      simp only [instantiatedTermTransportUniformPolynomial]
      dsimp only [term] at hprimitive hassembly ⊢
      omega
  | .func .one args => by
      let term := (.func .one args : ValuationTerm)
      have hterm := valuationTermEqualityTermCodeEnvelope_mono hbound term
      have hprimitive := paPrimitiveCostEnvelope_mono_short hterm
      have hformula := valuationTermEqualityFormulaResourceEnvelope_mono
        hbound term
      have hassembly := smallContextAssemblyEnvelope_mono_local hformula
      simp only [instantiatedTermTransportUniformPolynomial]
      dsimp only [term] at hprimitive hassembly ⊢
      omega
  | .func .add args => by
      have hleft := instantiatedTermTransportUniformPolynomial_mono
        hbound (args 0)
      have hright := instantiatedTermTransportUniformPolynomial_mono
        hbound (args 1)
      simpa only [instantiatedTermTransportUniformPolynomial] using
        instantiatedTermTransportNodeUniformPolynomial_mono hbound
          (.func .add args : ValuationTerm) args hleft hright
  | .func .mul args => by
      have hleft := instantiatedTermTransportUniformPolynomial_mono
        hbound (args 0)
      have hright := instantiatedTermTransportUniformPolynomial_mono
        hbound (args 1)
      simpa only [instantiatedTermTransportUniformPolynomial] using
        instantiatedTermTransportNodeUniformPolynomial_mono hbound
          (.func .mul args : ValuationTerm) args hleft hright

theorem termEqualityFormulaClosureCodeEnvelope_mono
    {small large : Nat} (hbound : small <= large) :
    termEqualityFormulaClosureCodeEnvelope small <=
      termEqualityFormulaClosureCodeEnvelope large := by
  have hformula := paFormulaCodeEnvelope_mono_local hbound
  unfold termEqualityFormulaClosureCodeEnvelope
    termEqualityFormulaStageTwoCodeEnvelope
    termEqualityFormulaStageOneCodeEnvelope
  omega

theorem termEqualityContextFormulaResourceEnvelope_mono
    {smallContext largeContext smallTerm largeTerm : Nat}
    (hcontext : smallContext <= largeContext)
    (hterm : smallTerm <= largeTerm) :
    termEqualityContextFormulaResourceEnvelope smallContext smallTerm <=
      termEqualityContextFormulaResourceEnvelope largeContext largeTerm := by
  have hclosure := termEqualityFormulaClosureCodeEnvelope_mono hterm
  unfold termEqualityContextFormulaResourceEnvelope
  omega

theorem contextualEqualityTransitivityUniformPayloadBound_mono
    {smallContext largeContext smallTerm largeTerm
      smallLeft largeLeft smallRight largeRight : Nat}
    (hcontext : smallContext <= largeContext)
    (hterm : smallTerm <= largeTerm)
    (hleft : smallLeft <= largeLeft)
    (hright : smallRight <= largeRight) :
    contextualEqualityTransitivityUniformPayloadBound smallContext smallTerm
        smallLeft smallRight <=
      contextualEqualityTransitivityUniformPayloadBound largeContext
        largeTerm largeLeft largeRight := by
  have hprimitive := paPrimitiveCostEnvelope_mono_short hterm
  have hformula := termEqualityContextFormulaResourceEnvelope_mono
    hcontext hterm
  have hassembly := smallContextAssemblyEnvelope_mono_local hformula
  unfold contextualEqualityTransitivityUniformPayloadBound
  omega

theorem compileTermValueEqualityUniformPayloadPolynomial_mono
    {small large : Nat} (hbound : small <= large)
    (term : ValuationTerm) :
    compileTermValueEqualityUniformPayloadPolynomial small term <=
      compileTermValueEqualityUniformPayloadPolynomial large term := by
  have hcontext := valuationTermContextFormulaCodeEnvelope_mono hbound term
  have hterm := valuationTermEqualityTermCodeEnvelope_mono hbound term
  have hnormalization :=
    contextualizedNormalizationUniformPayloadPolynomial_mono hbound term
  have htransport := instantiatedTermTransportUniformPolynomial_mono
    hbound term
  unfold compileTermValueEqualityUniformPayloadPolynomial
  exact contextualEqualityTransitivityUniformPayloadBound_mono hcontext hterm
    hnormalization htransport

#print axioms valuationTermValueEnvelope_mono
#print axioms instantiatedValuationTermCodeEnvelope_mono
#print axioms valuationTermEqualityTermCodeEnvelope_mono
#print axioms instantiatedTermNormalizationUniformPolynomial_mono
#print axioms contextualizedNormalizationUniformPayloadPolynomial_mono
#print axioms instantiatedTermTransportUniformPolynomial_mono
#print axioms compileTermValueEqualityUniformPayloadPolynomial_mono

end FoundationCompactPAValuationTermCompilerUniformMonotoneBounds
