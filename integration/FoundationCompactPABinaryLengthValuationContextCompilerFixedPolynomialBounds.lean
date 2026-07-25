import integration.FoundationCompactPABinaryLengthValuationContextCompilerPublicBounds
import integration.FoundationCompactPAValuationTermCompilerFixedPolynomialBounds

/-!
# Fixed polynomial bounds for binary length at valuation terms

The public binary-length compiler exposes every local proof and connector
resource.  This layer first proves that its closed short-numeral polynomial is
monotone in bit width, then bounds the valuation terms, transport proofs and
context assembly by proof-independent numeric and syntax coordinates.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactPABinaryLengthValuationContextCompilerFixedPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExponentialRuleCompilerBounds
open FoundationCompactPAExponentialShortNumeralCompilerBounds
open FoundationCompactPABinaryLengthRuleCompilerBounds
open FoundationCompactPABinaryLengthValueTransport
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationTermCompilerUniformBounds
open FoundationCompactPAValuationTermCompilerFixedPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPABinaryLengthValuationContextCompiler
open FoundationCompactPABinaryLengthValuationContextCompilerBounds
open FoundationCompactPABinaryLengthValuationContextCompilerPublicBounds

theorem binaryLengthTermCodeEnvelope_mono_fixed :
    Monotone binaryLengthTermCodeEnvelope := by
  intro small large h
  unfold binaryLengthTermCodeEnvelope
  exact exponentialShortTermCodeEnvelope_mono h

private theorem binaryLengthRuleFormulaStageOne_mono_fixed
    {small large : Nat} (h : small <= large) :
    binaryLengthRuleFormulaStageOne small <=
      binaryLengthRuleFormulaStageOne large := by
  exact substitutionFormulaCodeEnvelope_mono_exponential le_rfl h

private theorem binaryLengthRuleFormulaStageTwo_mono_fixed
    {small large : Nat} (h : small <= large) :
    binaryLengthRuleFormulaStageTwo small <=
      binaryLengthRuleFormulaStageTwo large := by
  exact substitutionFormulaCodeEnvelope_mono_exponential
    (binaryLengthRuleFormulaStageOne_mono_fixed h) h

private theorem binaryLengthEvenImplicationPayloadEnvelope_mono_fixed
    {small large : Nat} (h : small <= large) :
    binaryLengthEvenImplicationPayloadEnvelope small <=
      binaryLengthEvenImplicationPayloadEnvelope large := by
  have hstage := binaryLengthRuleFormulaStageOne_mono_fixed h
  have hfirst := exponentialSpecializationCostEnvelope_mono
    (smallFormula := binaryLengthRuleFormulaSeed)
    (largeFormula := binaryLengthRuleFormulaSeed) le_rfl h
  have hsecond := exponentialSpecializationCostEnvelope_mono hstage h
  unfold binaryLengthEvenImplicationPayloadEnvelope
  omega

private theorem binaryLengthOddImplicationPayloadEnvelope_mono_fixed
    {small large : Nat} (h : small <= large) :
    binaryLengthOddImplicationPayloadEnvelope small <=
      binaryLengthOddImplicationPayloadEnvelope large := by
  have hstage := binaryLengthRuleFormulaStageOne_mono_fixed h
  have hfirst := exponentialSpecializationCostEnvelope_mono
    (smallFormula := binaryLengthRuleFormulaSeed)
    (largeFormula := binaryLengthRuleFormulaSeed) le_rfl h
  have hsecond := exponentialSpecializationCostEnvelope_mono hstage h
  unfold binaryLengthOddImplicationPayloadEnvelope
  omega

private theorem binaryLengthPositivePayloadCumulative_mono_fixed
    {small large : Nat} (h : small <= large) :
    binaryLengthPositivePayloadCumulative small <=
      binaryLengthPositivePayloadCumulative large := by
  have hrange : Finset.range (small + 1) ⊆ Finset.range (large + 1) := by
    intro candidate hcandidate
    simp only [Finset.mem_range] at hcandidate ⊢
    omega
  unfold binaryLengthPositivePayloadCumulative
  exact Finset.sum_le_sum_of_subset hrange

private theorem binaryLengthMPPayloadEnvelope_mono_fixed
    {small large : Nat} (h : small <= large) :
    binaryLengthMPPayloadEnvelope small <=
      binaryLengthMPPayloadEnvelope large := by
  have hformula : binaryLengthMPFormulaEnvelope small <=
      binaryLengthMPFormulaEnvelope large := by
    unfold binaryLengthMPFormulaEnvelope
    exact Nat.mul_le_mul_left 2
      (binaryLengthRuleFormulaStageTwo_mono_fixed h)
  have hsyntax := paAssemblySyntaxEnvelope_mono_short hformula
  unfold binaryLengthMPPayloadEnvelope
  omega

private theorem binaryLengthRecursiveStepPayloadEnvelope_mono_fixed
    {small large : Nat} (h : small <= large) :
    binaryLengthRecursiveStepPayloadEnvelope small <=
      binaryLengthRecursiveStepPayloadEnvelope large := by
  have hterm := binaryLengthTermCodeEnvelope_mono_fixed h
  have heven := binaryLengthEvenImplicationPayloadEnvelope_mono_fixed hterm
  have hodd := binaryLengthOddImplicationPayloadEnvelope_mono_fixed hterm
  have hpositive := binaryLengthPositivePayloadCumulative_mono_fixed h
  have hmp := binaryLengthMPPayloadEnvelope_mono_fixed hterm
  simp only [binaryLengthRecursiveStepPayloadEnvelope]
  omega

theorem binaryLengthRecursivePayloadPolynomial_mono_fixed :
    Monotone binaryLengthRecursivePayloadPolynomial := by
  intro small large h
  have hcumulative := binaryLengthRecursiveStepPayloadCumulative_mono h
  have hproduct :
      small * binaryLengthRecursiveStepPayloadCumulative small <=
        large * binaryLengthRecursiveStepPayloadCumulative large :=
    Nat.mul_le_mul h hcumulative
  unfold binaryLengthRecursivePayloadPolynomial
  omega

private theorem binaryLengthTransportFormulaStageOne_mono_fixed
    {small large : Nat} (h : small <= large) :
    binaryLengthTransportFormulaStageOne small <=
      binaryLengthTransportFormulaStageOne large := by
  exact substitutionFormulaCodeEnvelope_mono_exponential le_rfl h

private theorem binaryLengthTransportFormulaStageTwo_mono_fixed
    {small large : Nat} (h : small <= large) :
    binaryLengthTransportFormulaStageTwo small <=
      binaryLengthTransportFormulaStageTwo large := by
  exact substitutionFormulaCodeEnvelope_mono_exponential
    (binaryLengthTransportFormulaStageOne_mono_fixed h) h

private theorem binaryLengthTransportPayloadEnvelope_mono_fixed
    {small large : Nat} (h : small <= large) :
    binaryLengthTransportPayloadEnvelope small <=
      binaryLengthTransportPayloadEnvelope large := by
  have hstageOne := binaryLengthTransportFormulaStageOne_mono_fixed h
  have hstageTwo := binaryLengthTransportFormulaStageTwo_mono_fixed h
  have hfirst := exponentialSpecializationCostEnvelope_mono
    (smallFormula := binaryLengthTransportFormulaSeed)
    (largeFormula := binaryLengthTransportFormulaSeed) le_rfl h
  have hsecond := exponentialSpecializationCostEnvelope_mono hstageOne h
  have hthird := exponentialSpecializationCostEnvelope_mono hstageTwo h
  unfold binaryLengthTransportPayloadEnvelope
  omega

private theorem binaryLengthTransportMPPayloadEnvelope_mono_fixed
    {small large : Nat} (h : small <= large) :
    binaryLengthTransportMPPayloadEnvelope small <=
      binaryLengthTransportMPPayloadEnvelope large := by
  have hstageTwo := binaryLengthTransportFormulaStageTwo_mono_fixed h
  have hstageThree := substitutionFormulaCodeEnvelope_mono_exponential
    hstageTwo h
  have hformula : binaryLengthTransportMPFormulaEnvelope small <=
      binaryLengthTransportMPFormulaEnvelope large := by
    unfold binaryLengthTransportMPFormulaEnvelope
    exact Nat.mul_le_mul_left 2 hstageThree
  have hsyntax := paAssemblySyntaxEnvelope_mono_short hformula
  unfold binaryLengthTransportMPPayloadEnvelope
  omega

private theorem exponentialExponentShortDirectPayloadPolynomial_mono_fixed :
    Monotone exponentialExponentShortDirectPayloadPolynomial := by
  intro small large h
  have hstep := exponentialShortDirectStepPayloadEnvelope_mono h
  have hproduct : small * exponentialShortDirectStepPayloadEnvelope small <=
      large * exponentialShortDirectStepPayloadEnvelope large :=
    Nat.mul_le_mul h hstep
  unfold exponentialExponentShortDirectPayloadPolynomial
  omega

private theorem
    exponentialExponentRecursiveToShortPayloadPolynomial_mono_fixed :
    Monotone exponentialExponentRecursiveToShortPayloadPolynomial := by
  intro small large h
  have hdirect :=
    exponentialExponentShortDirectPayloadPolynomial_mono_fixed h
  have hterm := exponentialShortTermCodeEnvelope_mono h
  have hprimitive := paPrimitiveCostEnvelope_mono_short hterm
  unfold exponentialExponentRecursiveToShortPayloadPolynomial
  omega

theorem binaryLengthAtShortNumeralsPayloadPolynomial_mono_fixed :
    Monotone binaryLengthAtShortNumeralsPayloadPolynomial := by
  intro small large h
  have hterm := binaryLengthTermCodeEnvelope_mono_fixed h
  have htransport := binaryLengthTransportPayloadEnvelope_mono_fixed hterm
  have hexponential :=
    exponentialExponentRecursiveToShortPayloadPolynomial_mono_fixed h
  have hrecursive := binaryLengthRecursivePayloadPolynomial_mono_fixed h
  have hmp := binaryLengthTransportMPPayloadEnvelope_mono_fixed hterm
  simp only [binaryLengthAtShortNumeralsPayloadPolynomial]
  omega

/-! ## Fixed value-transport envelope -/

def binaryLengthValueTransportFormulaSeedFixed : Nat :=
  (binaryFormulaCode binaryLengthValueTransportOuterBody).length

def binaryLengthValueTransportFormulaStageOneFixed (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope binaryLengthValueTransportFormulaSeedFixed
    termBound

def binaryLengthValueTransportFormulaStageTwoFixed (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    (binaryLengthValueTransportFormulaStageOneFixed termBound) termBound

def binaryLengthValueTransportFormulaStageThreeFixed (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    (binaryLengthValueTransportFormulaStageTwoFixed termBound) termBound

private theorem binaryLengthValueTransportMiddleBody_code_le_stageOneFixed
    (size : ValuationTerm) (termBound : Nat)
    (hsize : (binaryTermCode size).length <= termBound) :
    (binaryFormulaCode
      (binaryLengthValueTransportMiddleBody size)).length <=
        binaryLengthValueTransportFormulaStageOneFixed termBound := by
  exact instantiatedBodyCode_le_nextStage
    binaryLengthValueTransportOuterBody
    (binaryLengthValueTransportMiddleBody size) size
    binaryLengthValueTransportFormulaSeedFixed termBound le_rfl hsize
    (binaryLengthValueTransportAfterFirst_formula size)

private theorem binaryLengthValueTransportInnerBody_code_le_stageTwoFixed
    (size leftValue : ValuationTerm) (termBound : Nat)
    (hsize : (binaryTermCode size).length <= termBound)
    (hleft : (binaryTermCode leftValue).length <= termBound) :
    (binaryFormulaCode
      (binaryLengthValueTransportInnerBody size leftValue)).length <=
        binaryLengthValueTransportFormulaStageTwoFixed termBound := by
  exact instantiatedBodyCode_le_nextStage
    (binaryLengthValueTransportMiddleBody size)
    (binaryLengthValueTransportInnerBody size leftValue) leftValue
    (binaryLengthValueTransportFormulaStageOneFixed termBound) termBound
    (binaryLengthValueTransportMiddleBody_code_le_stageOneFixed size termBound
      hsize) hleft
    (binaryLengthValueTransportAfterSecond_formula size leftValue)

theorem binaryLengthValueTransportFinalFormula_code_le_fixed
    (size leftValue rightValue : ValuationTerm) (termBound : Nat)
    (hsize : (binaryTermCode size).length <= termBound)
    (hleft : (binaryTermCode leftValue).length <= termBound)
    (hright : (binaryTermCode rightValue).length <= termBound) :
    (binaryFormulaCode
      (“!!leftValue = !!rightValue →
        (!lengthDef !!size !!leftValue →
          !lengthDef !!size !!rightValue)” :
        LO.FirstOrder.ArithmeticProposition)).length <=
      binaryLengthValueTransportFormulaStageThreeFixed termBound := by
  have hinner := binaryLengthValueTransportInnerBody_code_le_stageTwoFixed
    size leftValue termBound hsize hleft
  have hsubstitution := binaryFormulaCode_substitution_one_length_le_envelope
    (binaryLengthValueTransportInnerBody size leftValue) rightValue
    (binaryLengthValueTransportFormulaStageTwoFixed termBound) termBound
    hinner hright
  rw [binaryLengthValueTransportFinal_formula size leftValue rightValue]
    at hsubstitution
  exact hsubstitution

def binaryLengthValueTransportFixedPayloadEnvelope (termBound : Nat) : Nat :=
  binaryLengthValueTransportUniversalProof.payloadLength +
    exponentialSpecializationCostEnvelope
      binaryLengthValueTransportFormulaSeedFixed termBound +
    exponentialSpecializationCostEnvelope
      (binaryLengthValueTransportFormulaStageOneFixed termBound) termBound +
    exponentialSpecializationCostEnvelope
      (binaryLengthValueTransportFormulaStageTwoFixed termBound) termBound

theorem binaryLengthValueTransportPayloadResource_le_fixed
    (size leftValue rightValue : ValuationTerm) (termBound : Nat)
    (hsize : (binaryTermCode size).length <= termBound)
    (hleft : (binaryTermCode leftValue).length <= termBound)
    (hright : (binaryTermCode rightValue).length <= termBound) :
    binaryLengthValueTransportPayloadResource size leftValue rightValue <=
      binaryLengthValueTransportFixedPayloadEnvelope termBound := by
  have hmiddle := binaryLengthValueTransportMiddleBody_code_le_stageOneFixed
    size termBound hsize
  have hinner := binaryLengthValueTransportInnerBody_code_le_stageTwoFixed
    size leftValue termBound hsize hleft
  have hfirst := specializationCost_le_exponentialEnvelope
    binaryLengthValueTransportOuterBody size
    binaryLengthValueTransportFormulaSeedFixed termBound le_rfl hsize
  have hsecond := specializationCost_le_exponentialEnvelope
    (binaryLengthValueTransportMiddleBody size) leftValue
    (binaryLengthValueTransportFormulaStageOneFixed termBound) termBound
    hmiddle hleft
  have hthird := specializationCost_le_exponentialEnvelope
    (binaryLengthValueTransportInnerBody size leftValue) rightValue
    (binaryLengthValueTransportFormulaStageTwoFixed termBound) termBound
    hinner hright
  unfold binaryLengthValueTransportPayloadResource
    binaryLengthValueTransportFixedPayloadEnvelope
  omega

/-! ## Complete valuation-context bound -/

def binaryLengthValuationFixedTermCodePolynomial
    (numericBound inputTermCodeBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope numericBound + inputTermCodeBound + 1

def binaryLengthValuationTransportTermCodePolynomial
    (numericBound inputTermCodeBound : Nat) : Nat :=
  4 * binaryLengthValuationFixedTermCodePolynomial numericBound
    inputTermCodeBound + 1

def binaryLengthValuationBaseFormulaCodePolynomial
    (numericBound inputTermCodeBound : Nat) : Nat :=
  let termBound := binaryLengthValuationFixedTermCodePolynomial numericBound
    inputTermCodeBound
  2 * (binaryLengthTransportFormulaStageThree termBound +
    binaryLengthValueTransportFormulaStageThreeFixed termBound) + 1

def binaryLengthValuationAssemblyFormulaCodePolynomial
    (numericBound inputTermCodeBound : Nat) : Nat :=
  2 * binaryLengthValuationBaseFormulaCodePolynomial numericBound
    inputTermCodeBound + 1

def compileBinaryLengthAtValuationFixedPayloadPolynomial
    (numericBound inputTermCodeBound : Nat) : Nat :=
  let termBound := binaryLengthValuationFixedTermCodePolynomial numericBound
    inputTermCodeBound
  let transportTermBound :=
    binaryLengthValuationTransportTermCodePolynomial numericBound
      inputTermCodeBound
  let formulaBound :=
    binaryLengthValuationAssemblyFormulaCodePolynomial numericBound
      inputTermCodeBound
  binaryLengthAtShortNumeralsPayloadPolynomial numericBound +
    2 * compileTermValueEqualityFixedPayloadPolynomial numericBound termBound +
    binaryLengthTransportPayloadEnvelope transportTermBound +
    binaryLengthValueTransportFixedPayloadEnvelope termBound +
    9 * smallContextAssemblyEnvelope formulaBound + 1

private theorem compileTermValueEqualityPayloadPolynomial_le_fixed_closed
    (valuation : Nat -> Nat) (numericBound termCodeBound : Nat)
    (term : ValuationTerm) (hclosed : term.freeVariables = ∅)
    (hcode : (binaryTermCode term).length <= termCodeBound) :
    compileTermValueEqualityPayloadPolynomial valuation term <=
      compileTermValueEqualityFixedPayloadPolynomial numericBound
        termCodeBound := by
  have hcard : term.freeVariables.card <= 4 := by
    rw [hclosed]
    simp
  have hvalues : forall index, index ∈ term.freeVariables ->
      valuation index <= numericBound := by
    intro index hindex
    rw [hclosed] at hindex
    simp at hindex
  exact
    (compileTermValueEqualityPayloadPolynomial_le_coordinate valuation
      numericBound term hcard hvalues).trans
        (compileTermValueEqualityUniformPayloadPolynomial_le_fixed numericBound
          termCodeBound term hcard hcode)

private theorem contextualModusPonensFullAssemblyCost_le_binaryLengthFixed
    (Gamma : Finset ValuationFormula) (antecedent consequent : ValuationFormula)
    (baseBound assemblyBound : Nat)
    (hdouble : 2 * baseBound <= assemblyBound)
    (hcard : Gamma.card <= 4)
    (hcontext : FormulaCodeBound Gamma assemblyBound)
    (hantecedent : (binaryFormulaCode antecedent).length <= baseBound)
    (hconsequent : (binaryFormulaCode consequent).length <= baseBound)
    (himplication :
      (binaryFormulaCode (antecedent 🡒 consequent)).length <= baseBound) :
    contextualModusPonensFullAssemblyCost Gamma antecedent consequent <=
      smallContextAssemblyEnvelope assemblyBound := by
  have hbase : baseBound <= assemblyBound := by omega
  have hantecedentLarge := hantecedent.trans hbase
  have hconsequentLarge := hconsequent.trans hbase
  have himplicationLarge := himplication.trans hbase
  have hnegatedImplicationRaw :=
    binaryFormulaCode_neg_length_le (antecedent 🡒 consequent)
  have hnegatedImplication :
      (binaryFormulaCode (∼(antecedent 🡒 consequent))).length <=
        assemblyBound := by omega
  have hnegatedConsequentRaw := binaryFormulaCode_neg_length_le consequent
  have hnegatedConsequent :
      (binaryFormulaCode (∼consequent)).length <= assemblyBound := by omega
  exact contextualModusPonensFullAssemblyCost_le_small Gamma antecedent
    consequent assemblyBound hcard hcontext hantecedentLarge hconsequentLarge
    himplicationLarge hnegatedImplication hnegatedConsequent

/-- The complete public binary-length payload is bounded by one fixed
coordinate polynomial.  `hresource` and `htarget` are transparent definition
equations used only to keep elaboration from eagerly unfolding the full sum. -/
theorem compileBinaryLengthAtValuationPayloadPolynomial_le_fixed_of_eq
    (valuation : Nat -> Nat) (sizeTerm valueTerm : ValuationTerm)
    (resource target numericBound inputTermCodeBound : Nat)
    (hresource :
      resource = compileBinaryLengthAtValuationPayloadPolynomial valuation
        sizeTerm valueTerm)
    (htarget :
      target = compileBinaryLengthAtValuationFixedPayloadPolynomial numericBound
        inputTermCodeBound)
    (hsizeClosed : sizeTerm.freeVariables = ∅)
    (hvalueClosed : valueTerm.freeVariables = ∅)
    (hsizeWidth : Nat.size (termValue valuation sizeTerm) <= numericBound)
    (hvalueWidth : Nat.size (termValue valuation valueTerm) <= numericBound)
    (hsizeCode : (binaryTermCode sizeTerm).length <= inputTermCodeBound)
    (hvalueCode : (binaryTermCode valueTerm).length <= inputTermCodeBound) :
    Nat.le resource target := by
  let termBound := binaryLengthValuationFixedTermCodePolynomial numericBound
    inputTermCodeBound
  let transportTermBound := 4 * termBound + 1
  let baseFormulaBound :=
    2 * (binaryLengthTransportFormulaStageThree termBound +
      binaryLengthValueTransportFormulaStageThreeFixed termBound) + 1
  let formulaBound := 2 * baseFormulaBound + 1
  let shortSize := shortBinaryNumeralTerm (termValue valuation sizeTerm)
  let shortValue := shortBinaryNumeralTerm (termValue valuation valueTerm)
  let Gamma := binaryLengthValuationContext valuation sizeTerm valueTerm
  let sourceFormula := binaryLengthValuationSourceFormula valuation sizeTerm
    valueTerm
  let sizeEqualityFormula := binaryLengthValuationSizeEqualityFormula valuation
    sizeTerm
  let sizeFactFormula := binaryLengthValuationSizeFactFormula valuation sizeTerm
    valueTerm
  let valueEqualityFormula := binaryLengthValuationValueEqualityFormula valuation
    valueTerm
  let resultFormula := binaryLengthAtValuationFormula sizeTerm valueTerm
  let sizeTransportConsequent := sourceFormula 🡒 sizeFactFormula
  let valueTransportConsequent := sizeFactFormula 🡒 resultFormula
  have hshortSizeRaw := binaryNumeralTerm_code_length_le_envelope
    (termValue valuation sizeTerm) numericBound hsizeWidth
  have hshortValueRaw := binaryNumeralTerm_code_length_le_envelope
    (termValue valuation valueTerm) numericBound hvalueWidth
  have hshortSize : (binaryTermCode shortSize).length <= termBound := by
    exact hshortSizeRaw.trans (by
      unfold termBound binaryLengthValuationFixedTermCodePolynomial
      omega)
  have hshortValue : (binaryTermCode shortValue).length <= termBound := by
    exact hshortValueRaw.trans (by
      unfold termBound binaryLengthValuationFixedTermCodePolynomial
      omega)
  have hsizeTerm : (binaryTermCode sizeTerm).length <= termBound := by
    exact hsizeCode.trans (by
      unfold termBound binaryLengthValuationFixedTermCodePolynomial
      omega)
  have hvalueTerm : (binaryTermCode valueTerm).length <= termBound := by
    exact hvalueCode.trans (by
      unfold termBound binaryLengthValuationFixedTermCodePolynomial
      omega)
  have hexactTermBound :
      binaryLengthValuationTermCodeEnvelope valuation sizeTerm valueTerm <=
        transportTermBound := by
    change
      (binaryTermCode shortSize).length +
          (binaryTermCode shortValue).length +
          (binaryTermCode sizeTerm).length +
          (binaryTermCode valueTerm).length + 1 <= transportTermBound
    dsimp only [transportTermBound]
    omega
  have hshortPayload :=
    binaryLengthAtShortNumeralsPayloadPolynomial_mono_fixed hvalueWidth
  have hsizeEquality :=
    compileTermValueEqualityPayloadPolynomial_le_fixed_closed valuation
      numericBound termBound sizeTerm hsizeClosed hsizeTerm
  have hvalueEquality :=
    compileTermValueEqualityPayloadPolynomial_le_fixed_closed valuation
      numericBound termBound valueTerm hvalueClosed hvalueTerm
  have hsizeTransport :=
    binaryLengthTransportPayloadEnvelope_mono_fixed hexactTermBound
  have hvalueTransport :=
    binaryLengthValueTransportPayloadResource_le_fixed sizeTerm shortValue
      valueTerm termBound hsizeTerm hshortValue hvalueTerm
  have hsizeTransportFull :
      (binaryFormulaCode
        (sizeEqualityFormula 🡒 sizeTransportConsequent)).length <=
          binaryLengthTransportFormulaStageThree termBound := by
    simpa only [sizeEqualityFormula, sizeTransportConsequent, sourceFormula,
      sizeFactFormula, shortSize, shortValue,
      binaryLengthValuationSizeEqualityFormula,
      binaryLengthValuationSourceFormula,
      binaryLengthValuationSizeFactFormula] using
        (binaryLengthSizeTransportFormula_code_le_stageThree shortSize sizeTerm
          shortValue termBound hshortSize hsizeTerm hshortValue)
  have hvalueTransportFull :
      (binaryFormulaCode
        (valueEqualityFormula 🡒 valueTransportConsequent)).length <=
          binaryLengthValueTransportFormulaStageThreeFixed termBound := by
    simpa only [valueEqualityFormula, valueTransportConsequent,
      sizeFactFormula, resultFormula, shortValue,
      binaryLengthValuationValueEqualityFormula,
      binaryLengthValuationSizeFactFormula,
      binaryLengthAtValuationFormula] using
        (binaryLengthValueTransportFinalFormula_code_le_fixed sizeTerm
          shortValue valueTerm termBound hsizeTerm hshortValue hvalueTerm)
  have hsizeEqualityBase :
      (binaryFormulaCode sizeEqualityFormula).length <= baseFormulaBound := by
    have hraw := binaryFormulaCode_antecedent_le_implication
      sizeEqualityFormula sizeTransportConsequent
    dsimp only [baseFormulaBound]
    omega
  have hsizeConsequentStage :
      (binaryFormulaCode sizeTransportConsequent).length <=
        binaryLengthTransportFormulaStageThree termBound := by
    exact (binaryFormulaCode_consequent_le_implication sizeEqualityFormula
      sizeTransportConsequent).trans hsizeTransportFull
  have hsizeConsequentBase :
      (binaryFormulaCode sizeTransportConsequent).length <=
        baseFormulaBound := by
    dsimp only [baseFormulaBound]
    omega
  have hsourceBase : (binaryFormulaCode sourceFormula).length <=
      baseFormulaBound := by
    have hraw := binaryFormulaCode_antecedent_le_implication sourceFormula
      sizeFactFormula
    dsimp only [sizeTransportConsequent] at hsizeConsequentStage
    dsimp only [baseFormulaBound]
    omega
  have hsizeFactBase : (binaryFormulaCode sizeFactFormula).length <=
      baseFormulaBound := by
    have hraw := binaryFormulaCode_consequent_le_implication sourceFormula
      sizeFactFormula
    dsimp only [sizeTransportConsequent] at hsizeConsequentStage
    have htight := hraw.trans hsizeConsequentStage
    dsimp only [baseFormulaBound]
    omega
  have hsizeTransportFullBase :
      (binaryFormulaCode
        (sizeEqualityFormula 🡒 sizeTransportConsequent)).length <=
          baseFormulaBound := by
    dsimp only [baseFormulaBound]
    omega
  have hvalueEqualityBase :
      (binaryFormulaCode valueEqualityFormula).length <= baseFormulaBound := by
    have hraw := binaryFormulaCode_antecedent_le_implication
      valueEqualityFormula valueTransportConsequent
    dsimp only [baseFormulaBound]
    omega
  have hvalueConsequentStage :
      (binaryFormulaCode valueTransportConsequent).length <=
        binaryLengthValueTransportFormulaStageThreeFixed termBound := by
    exact (binaryFormulaCode_consequent_le_implication valueEqualityFormula
      valueTransportConsequent).trans hvalueTransportFull
  have hvalueConsequentBase :
      (binaryFormulaCode valueTransportConsequent).length <=
        baseFormulaBound := by
    dsimp only [baseFormulaBound]
    omega
  have hresultBase : (binaryFormulaCode resultFormula).length <=
      baseFormulaBound := by
    have hraw := binaryFormulaCode_consequent_le_implication sizeFactFormula
      resultFormula
    dsimp only [valueTransportConsequent] at hvalueConsequentStage
    have htight := hraw.trans hvalueConsequentStage
    dsimp only [baseFormulaBound]
    omega
  have hvalueTransportFullBase :
      (binaryFormulaCode
        (valueEqualityFormula 🡒 valueTransportConsequent)).length <=
          baseFormulaBound := by
    dsimp only [baseFormulaBound]
    omega
  have hdouble : 2 * baseFormulaBound <= formulaBound := by
    dsimp only [formulaBound]
    omega
  have hbaseLarge : baseFormulaBound <= formulaBound := by omega
  have hGammaEmpty : Gamma = ∅ := by
    unfold Gamma binaryLengthValuationContext
    rw [hsizeClosed, hvalueClosed]
    simp [valuationContext]
  have hcontext : FormulaCodeBound Gamma formulaBound := by
    rw [hGammaEmpty]
    intro formula hformula
    simp at hformula
  have hcontextCard : Gamma.card <= 4 := by
    rw [hGammaEmpty]
    simp
  have hweakSource := weakeningFullAssemblyCost_le_small
    (insert sourceFormula Gamma) formulaBound (by
      have hstep := Finset.card_insert_le sourceFormula Gamma
      omega) (hcontext.insert (hsourceBase.trans hbaseLarge))
  have hweakSizeEquality := weakeningFullAssemblyCost_le_small
    (insert sizeEqualityFormula Gamma) formulaBound (by
      have hstep := Finset.card_insert_le sizeEqualityFormula Gamma
      omega) (hcontext.insert (hsizeEqualityBase.trans hbaseLarge))
  have hweakSizeTransport := weakeningFullAssemblyCost_le_small
    (insert (sizeEqualityFormula 🡒 sizeTransportConsequent) Gamma)
      formulaBound (by
        have hstep := Finset.card_insert_le
          (sizeEqualityFormula 🡒 sizeTransportConsequent) Gamma
        omega) (hcontext.insert (hsizeTransportFullBase.trans hbaseLarge))
  have hweakValueEquality := weakeningFullAssemblyCost_le_small
    (insert valueEqualityFormula Gamma) formulaBound (by
      have hstep := Finset.card_insert_le valueEqualityFormula Gamma
      omega) (hcontext.insert (hvalueEqualityBase.trans hbaseLarge))
  have hweakValueTransport := weakeningFullAssemblyCost_le_small
    (insert (valueEqualityFormula 🡒 valueTransportConsequent) Gamma)
      formulaBound (by
        have hstep := Finset.card_insert_le
          (valueEqualityFormula 🡒 valueTransportConsequent) Gamma
        omega) (hcontext.insert (hvalueTransportFullBase.trans hbaseLarge))
  have hmpSizeEquality :=
    contextualModusPonensFullAssemblyCost_le_binaryLengthFixed Gamma
      sizeEqualityFormula sizeTransportConsequent baseFormulaBound formulaBound
      hdouble hcontextCard hcontext hsizeEqualityBase hsizeConsequentBase
      hsizeTransportFullBase
  have hmpSource :=
    contextualModusPonensFullAssemblyCost_le_binaryLengthFixed Gamma
      sourceFormula sizeFactFormula baseFormulaBound formulaBound hdouble
      hcontextCard hcontext hsourceBase hsizeFactBase hsizeConsequentBase
  have hmpValueEquality :=
    contextualModusPonensFullAssemblyCost_le_binaryLengthFixed Gamma
      valueEqualityFormula valueTransportConsequent baseFormulaBound
      formulaBound hdouble hcontextCard hcontext hvalueEqualityBase
      hvalueConsequentBase hvalueTransportFullBase
  have hmpSizeFact :=
    contextualModusPonensFullAssemblyCost_le_binaryLengthFixed Gamma
      sizeFactFormula resultFormula baseFormulaBound formulaBound hdouble
      hcontextCard hcontext hsizeFactBase hresultBase hvalueConsequentBase
  rw [hresource, htarget]
  change
    binaryLengthAtShortNumeralsPayloadPolynomial
          (Nat.size (termValue valuation valueTerm)) +
        weakeningFullAssemblyCost (insert sourceFormula Gamma) +
        compileTermValueEqualityPayloadPolynomial valuation sizeTerm +
        weakeningFullAssemblyCost (insert sizeEqualityFormula Gamma) +
        binaryLengthTransportPayloadEnvelope
          (binaryLengthValuationTermCodeEnvelope valuation sizeTerm valueTerm) +
        weakeningFullAssemblyCost
          (insert (sizeEqualityFormula 🡒 sizeTransportConsequent) Gamma) +
        compileTermValueEqualityPayloadPolynomial valuation valueTerm +
        weakeningFullAssemblyCost (insert valueEqualityFormula Gamma) +
        binaryLengthValueTransportPayloadResource sizeTerm shortValue valueTerm +
        weakeningFullAssemblyCost
          (insert (valueEqualityFormula 🡒 valueTransportConsequent) Gamma) +
        contextualModusPonensFullAssemblyCost Gamma sizeEqualityFormula
          sizeTransportConsequent +
        contextualModusPonensFullAssemblyCost Gamma sourceFormula
          sizeFactFormula +
        contextualModusPonensFullAssemblyCost Gamma valueEqualityFormula
          valueTransportConsequent +
        contextualModusPonensFullAssemblyCost Gamma sizeFactFormula
          resultFormula <=
      binaryLengthAtShortNumeralsPayloadPolynomial numericBound +
        2 * compileTermValueEqualityFixedPayloadPolynomial numericBound
          termBound +
        binaryLengthTransportPayloadEnvelope transportTermBound +
        binaryLengthValueTransportFixedPayloadEnvelope termBound +
        9 * smallContextAssemblyEnvelope formulaBound + 1
  omega

#print axioms binaryLengthTermCodeEnvelope_mono_fixed
#print axioms binaryLengthRecursivePayloadPolynomial_mono_fixed
#print axioms binaryLengthAtShortNumeralsPayloadPolynomial_mono_fixed
#print axioms binaryLengthValueTransportFinalFormula_code_le_fixed
#print axioms binaryLengthValueTransportPayloadResource_le_fixed
#print axioms compileBinaryLengthAtValuationPayloadPolynomial_le_fixed_of_eq

end FoundationCompactPABinaryLengthValuationContextCompilerFixedPolynomialBounds
