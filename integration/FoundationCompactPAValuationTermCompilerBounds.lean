import integration.FoundationCompactPAValuationTermCompiler
import integration.FoundationCompactPABinaryNumeralAdditionBounds
import integration.FoundationCompactPABinaryNumeralMultiplicationBounds
import integration.FoundationCompactPAContextCostPolynomialBounds
import integration.FoundationCompactPAExponentialShortNumeralCompilerBounds
import integration.FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds

/-!
# Explicit payload bounds for the valuation term compiler

The resource functions in this file are closed recursions on the input value
or term.  In particular, they do not accept a proof, a proof length, or a
caller-supplied bound.  The normalization budget charges closed PA primitives
through their established polynomial envelopes.  The transport budget keeps
the exact structural context costs, since its context can contain arbitrarily
many free-variable assumptions.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAValuationTermCompilerBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeEqualityTransitivity
open FoundationCompactPAQuantitativeFunctionCongruence
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABinaryNumeralMultiplication
open FoundationCompactPABinaryNumeralMultiplicationBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPACertifiedContextEquality
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAExponentialShortNumeralCompilerBounds
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAValuationTermCompiler

/-! ## Short-binary to unary-numeral bridge -/

/-- A proof-free term-code coordinate covering every term used by one
successor step of `proveShortBinaryNumeralEqualsIterated`. -/
def shortToIteratedStepTermCodeResource (value : Nat) : Nat :=
  let binaryValue := shortBinaryNumeralTerm value
  let binaryOne := shortBinaryNumeralTerm 1
  let iteratedValue := iteratedSuccessorTerm 0 value
  let one := finiteCaseOneTerm 0
  let source := paAddTerm binaryValue binaryOne
  let middle := paAddTerm iteratedValue one
  let result := shortBinaryNumeralTerm (value + 1)
  (binaryTermCode binaryValue).length +
    (binaryTermCode binaryOne).length +
    (binaryTermCode iteratedValue).length +
    (binaryTermCode one).length +
    (binaryTermCode source).length +
    (binaryTermCode middle).length +
    (binaryTermCode result).length + 1

/-- Explicit recursion for the short-binary/unary bridge.  Its recursion on
`value` reflects the recursion of the compiler proof itself. -/
def shortToIteratedPayloadResource : Nat -> Nat
  | 0 => paPrimitiveCostEnvelope
      (binaryTermCode (shortBinaryNumeralTerm 0)).length
  | value + 1 =>
      shortToIteratedPayloadResource value +
        paMultiplicationLocalCostEnvelope 0 +
        binaryNumeralAdditionPayloadPolynomial
          (Nat.size value + Nat.size 1) +
        3 * paPrimitiveCostEnvelope
          (shortToIteratedStepTermCodeResource value)

theorem proveShortBinaryNumeralEqualsIterated_payloadLength_le_resource
    (value : Nat) :
    (proveShortBinaryNumeralEqualsIterated value).payloadLength <=
      shortToIteratedPayloadResource value := by
  induction value with
  | zero =>
      let raw := proveEqualityReflexivityAtTerm (shortBinaryNumeralTerm 0)
      have hformula :
          (“!!(shortBinaryNumeralTerm 0) =
            !!(shortBinaryNumeralTerm 0)” :
            LO.FirstOrder.ArithmeticProposition) =
          (“!!(shortBinaryNumeralTerm 0) =
            !!(iteratedSuccessorTerm 0 0)” :
            LO.FirstOrder.ArithmeticProposition) := by
        simp [shortBinaryNumeralTerm,
          FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero,
          finiteCaseZeroTerm, paZeroTerm, arithmeticZeroTerm]
      have hpayload :
          (proveShortBinaryNumeralEqualsIterated 0).payloadLength =
            raw.payloadLength := by
        change (CertifiedPAProof.cast hformula raw).payloadLength = _
        exact CertifiedPAProof.cast_payloadLength _ _
      have hproof : raw.payloadLength <=
          paPrimitiveCostEnvelope
            (binaryTermCode (shortBinaryNumeralTerm 0)).length :=
        proveEqualityReflexivityAtTerm_payloadLength_le_primitive
          (shortBinaryNumeralTerm 0)
          (binaryTermCode (shortBinaryNumeralTerm 0)).length le_rfl
      rw [hpayload]
      exact hproof
  | succ value inductionHypothesis =>
      let inductionProof := proveShortBinaryNumeralEqualsIterated value
      let oneRaw := proveShortBinaryOneEqualsPaOne
      let oneProof : CertifiedPAProof
          (“!!(shortBinaryNumeralTerm 1) =
            !!(finiteCaseOneTerm 0)” :
            LO.FirstOrder.ArithmeticProposition) := by
        simpa [finiteCaseOneTerm, paOneTerm, arithmeticOneTerm] using oneRaw
      let source := paAddTerm
        (shortBinaryNumeralTerm value) (shortBinaryNumeralTerm 1)
      let middle := paAddTerm
        (iteratedSuccessorTerm 0 value) (finiteCaseOneTerm 0)
      let congruenceRaw := proveAddCongruence
        (shortBinaryNumeralTerm value) (shortBinaryNumeralTerm 1)
        (iteratedSuccessorTerm 0 value) (finiteCaseOneTerm 0)
        inductionProof oneProof
      let congruence : CertifiedPAProof
          (“!!source = !!middle” :
            LO.FirstOrder.ArithmeticProposition) := by
        exact CertifiedPAProof.cast
          (addEqualityAsTerm_formula
            (shortBinaryNumeralTerm value) (shortBinaryNumeralTerm 1)
            (iteratedSuccessorTerm 0 value) (finiteCaseOneTerm 0))
          congruenceRaw
      let arithmetic := proveBinaryNumeralAddition value 1
      let arithmeticBackward := proveEqualitySymmetry
        source (shortBinaryNumeralTerm (value + 1)) arithmetic
      let through := proveEqualityTransitivity
        (shortBinaryNumeralTerm (value + 1)) source middle
        arithmeticBackward congruence
      let termBound := shortToIteratedStepTermCodeResource value
      have hbinaryValue :
          (binaryTermCode (shortBinaryNumeralTerm value)).length <=
            termBound := by
        simp only [termBound, shortToIteratedStepTermCodeResource]
        omega
      have hbinaryOne :
          (binaryTermCode (shortBinaryNumeralTerm 1)).length <=
            termBound := by
        simp only [termBound, shortToIteratedStepTermCodeResource]
        omega
      have hiteratedValue :
          (binaryTermCode (iteratedSuccessorTerm 0 value)).length <=
            termBound := by
        simp only [termBound, shortToIteratedStepTermCodeResource]
        omega
      have hone :
          (binaryTermCode (finiteCaseOneTerm 0)).length <= termBound := by
        simp only [termBound, shortToIteratedStepTermCodeResource]
        omega
      have hsource : (binaryTermCode source).length <= termBound := by
        simp only [termBound, shortToIteratedStepTermCodeResource,
          source]
        omega
      have hmiddle : (binaryTermCode middle).length <= termBound := by
        simp only [termBound, shortToIteratedStepTermCodeResource,
          middle]
        omega
      have hresult :
          (binaryTermCode (shortBinaryNumeralTerm (value + 1))).length <=
            termBound := by
        simp only [termBound, shortToIteratedStepTermCodeResource]
        omega
      have honeProof : oneProof.payloadLength <=
          paMultiplicationLocalCostEnvelope 0 := by
        have honeFormula :
            (“!!(shortBinaryNumeralTerm 1) = !!paOneTerm” :
              LO.FirstOrder.ArithmeticProposition) =
            (“!!(shortBinaryNumeralTerm 1) =
              !!(finiteCaseOneTerm 0)” :
              LO.FirstOrder.ArithmeticProposition) := by
          simp [finiteCaseOneTerm, paOneTerm, arithmeticOneTerm]
        have honePayload : oneProof.payloadLength = oneRaw.payloadLength := by
          change (CertifiedPAProof.cast honeFormula oneRaw).payloadLength = _
          exact CertifiedPAProof.cast_payloadLength _ _
        rw [honePayload]
        exact proveShortBinaryOneEqualsPaOne_payloadLength_le_local 0
      have hcongruenceRaw :=
        proveAddCongruence_payloadLength_le_primitive
          (shortBinaryNumeralTerm value) (shortBinaryNumeralTerm 1)
          (iteratedSuccessorTerm 0 value) (finiteCaseOneTerm 0)
          inductionProof oneProof termBound
          hbinaryValue hbinaryOne hiteratedValue hone
      have hcongruence : congruence.payloadLength <=
          inductionProof.payloadLength + oneProof.payloadLength +
            paPrimitiveCostEnvelope termBound := by
        have hcast : congruence.payloadLength =
            congruenceRaw.payloadLength := by
          change (CertifiedPAProof.cast _ congruenceRaw).payloadLength = _
          exact CertifiedPAProof.cast_payloadLength _ _
        rw [hcast]
        exact hcongruenceRaw
      have harithmetic : arithmetic.payloadLength <=
          binaryNumeralAdditionPayloadPolynomial
            (Nat.size value + Nat.size 1) := by
        exact proveBinaryNumeralAddition_payloadLength_le_polynomial value 1
      have harithmeticBackward : arithmeticBackward.payloadLength <=
          arithmetic.payloadLength + paPrimitiveCostEnvelope termBound :=
        proveEqualitySymmetry_payloadLength_le_primitive
          source (shortBinaryNumeralTerm (value + 1)) arithmetic
          termBound hsource hresult
      have hthrough : through.payloadLength <=
          arithmeticBackward.payloadLength + congruence.payloadLength +
            paPrimitiveCostEnvelope termBound :=
        proveEqualityTransitivity_payloadLength_le_primitive
          (shortBinaryNumeralTerm (value + 1)) source middle
          arithmeticBackward congruence termBound hresult hsource hmiddle
      have hinduction : inductionProof.payloadLength <=
          shortToIteratedPayloadResource value := inductionHypothesis
      have hmiddle : middle = finiteCaseAddTerm
          (iteratedSuccessorTerm 0 value) (finiteCaseOneTerm 0) := by
        simp [middle, paAddTerm, finiteCaseAddTerm,
          Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
          Matrix.fun_eq_vec_two]
      have hformula :
          (“!!(shortBinaryNumeralTerm (value + 1)) = !!middle” :
            LO.FirstOrder.ArithmeticProposition) =
          (“!!(shortBinaryNumeralTerm (value + 1)) =
            !!(iteratedSuccessorTerm 0 (value + 1))” :
            LO.FirstOrder.ArithmeticProposition) := by
        rw [hmiddle, iteratedSuccessorTerm_succ]
      have houter :
          (proveShortBinaryNumeralEqualsIterated (value + 1)).payloadLength =
            through.payloadLength := by
        change (CertifiedPAProof.cast hformula through).payloadLength = _
        exact CertifiedPAProof.cast_payloadLength _ _
      rw [houter]
      change through.payloadLength <=
        shortToIteratedPayloadResource value +
          paMultiplicationLocalCostEnvelope 0 +
          binaryNumeralAdditionPayloadPolynomial
            (Nat.size value + Nat.size 1) +
          3 * paPrimitiveCostEnvelope termBound
      omega

/-! ## Public polynomial bound for the short-to-iterated bridge -/

private theorem natSize_le_self (value : Nat) :
    Nat.size value <= value := by
  rw [Nat.size_le]
  exact value.lt_two_pow_self

/-- One term-code coordinate for every term generated by a bridge step whose
index is at most `bound`.  It is a fixed polynomial in the numeric public
bound; no generated proof or payload occurs in this coordinate. -/
def shortToIteratedStepTermCodePolynomial (bound : Nat) : Nat :=
  let numeralBound := binaryNumeralTermCodeEnvelope (bound + 1)
  let iteratedBound := iteratedSuccessorTermCodePolynomial 0 bound
  let oneCode := (binaryTermCode (finiteCaseOneTerm 0)).length
  5 * numeralBound + 2 * iteratedBound + 2 * oneCode +
    2 * binaryFunctionTermCodeOverhead Language.Add.add + 1

theorem shortToIteratedStepTermCodeResource_le_polynomial
    (value bound : Nat) (hvalue : value <= bound) :
    shortToIteratedStepTermCodeResource value <=
      shortToIteratedStepTermCodePolynomial bound := by
  let numeralBound := binaryNumeralTermCodeEnvelope (bound + 1)
  let iteratedBound := iteratedSuccessorTermCodePolynomial 0 bound
  let binaryValue := shortBinaryNumeralTerm value
  let binaryOne := shortBinaryNumeralTerm 1
  let iteratedValue := iteratedSuccessorTerm 0 value
  let one := finiteCaseOneTerm 0
  let source := paAddTerm binaryValue binaryOne
  let middle := paAddTerm iteratedValue one
  let result := shortBinaryNumeralTerm (value + 1)
  have hvalueSize : Nat.size value <= bound + 1 := by
    exact (natSize_le_self value).trans (by omega)
  have honeSize : Nat.size 1 <= bound + 1 := by
    simp
  have hresultSize : Nat.size (value + 1) <= bound + 1 := by
    exact (natSize_le_self (value + 1)).trans (by omega)
  have hbinaryValue :
      (binaryTermCode binaryValue).length <= numeralBound := by
    exact binaryNumeralTerm_code_length_le_envelope
      value (bound + 1) hvalueSize
  have hbinaryOne :
      (binaryTermCode binaryOne).length <= numeralBound := by
    exact binaryNumeralTerm_code_length_le_envelope
      1 (bound + 1) honeSize
  have hresult : (binaryTermCode result).length <= numeralBound := by
    exact binaryNumeralTerm_code_length_le_envelope
      (value + 1) (bound + 1) hresultSize
  have hiteratedRaw :=
    iteratedSuccessorTerm_code_length_le_polynomial 0 value
  have hiteratedMono :=
    iteratedSuccessorTermCodePolynomial_mono 0 hvalue
  have hiterated :
      (binaryTermCode iteratedValue).length <= iteratedBound := by
    exact hiteratedRaw.trans hiteratedMono
  have hsource := paAddTerm_code_length_le binaryValue binaryOne
  have hmiddle := paAddTerm_code_length_le iteratedValue one
  unfold shortToIteratedStepTermCodeResource
    shortToIteratedStepTermCodePolynomial
  dsimp only [numeralBound, iteratedBound, binaryValue, binaryOne,
    iteratedValue, one, source, middle, result] at *
  omega

theorem shortToIteratedStepTermCodePolynomial_mono :
    Monotone shortToIteratedStepTermCodePolynomial := by
  intro small large hbound
  have hnumeral := binaryNumeralTermCodeEnvelope_mono_short
    (show small + 1 <= large + 1 by omega)
  have hiterated := iteratedSuccessorTermCodePolynomial_mono 0 hbound
  change
    5 * binaryNumeralTermCodeEnvelope (small + 1) +
          2 * iteratedSuccessorTermCodePolynomial 0 small +
          2 * (binaryTermCode (finiteCaseOneTerm 0)).length +
          2 * binaryFunctionTermCodeOverhead Language.Add.add + 1 <=
      5 * binaryNumeralTermCodeEnvelope (large + 1) +
          2 * iteratedSuccessorTermCodePolynomial 0 large +
          2 * (binaryTermCode (finiteCaseOneTerm 0)).length +
          2 * binaryFunctionTermCodeOverhead Language.Add.add + 1
  omega

private theorem binaryNumeralAdditionPayloadPolynomial_mono
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

/-- Uniform cost of one recursive bridge step below the public numeric bound.
The addition width and every generated term code are independently widened to
that public coordinate. -/
def shortToIteratedStepPayloadPolynomial (bound : Nat) : Nat :=
  paMultiplicationLocalCostEnvelope 0 +
    binaryNumeralAdditionPayloadPolynomial (bound + 1) +
    3 * paPrimitiveCostEnvelope
      (shortToIteratedStepTermCodePolynomial bound)

theorem shortToIteratedStepPayloadPolynomial_mono :
    Monotone shortToIteratedStepPayloadPolynomial := by
  intro small large hbound
  have hadd := binaryNumeralAdditionPayloadPolynomial_mono
    (show small + 1 <= large + 1 by omega)
  have hterms := shortToIteratedStepTermCodePolynomial_mono hbound
  have hprimitive := paPrimitiveCostEnvelope_mono_short hterms
  unfold shortToIteratedStepPayloadPolynomial
  gcongr

theorem shortToIteratedStepPayloadResource_le_polynomial
    (value bound : Nat) (hvalue : value < bound) :
    paMultiplicationLocalCostEnvelope 0 +
        binaryNumeralAdditionPayloadPolynomial
          (Nat.size value + Nat.size 1) +
        3 * paPrimitiveCostEnvelope
          (shortToIteratedStepTermCodeResource value) <=
      shortToIteratedStepPayloadPolynomial bound := by
  have hwidth : Nat.size value + Nat.size 1 <= bound + 1 := by
    have hsize := natSize_le_self value
    simp only [Nat.size_one]
    omega
  have hadd := binaryNumeralAdditionPayloadPolynomial_mono hwidth
  have hterms := shortToIteratedStepTermCodeResource_le_polynomial
    value bound (by omega)
  have hprimitive := paPrimitiveCostEnvelope_mono_short hterms
  unfold shortToIteratedStepPayloadPolynomial
  omega

/-- Fixed public polynomial for the complete unary bridge.  The factor
`bound` pays exactly one local step per successor in the target numeral. -/
def shortToIteratedPayloadPolynomial (bound : Nat) : Nat :=
  paPrimitiveCostEnvelope
      (binaryTermCode (shortBinaryNumeralTerm 0)).length +
    bound * shortToIteratedStepPayloadPolynomial bound

theorem shortToIteratedPayloadResource_le_publicPolynomial_of_le
    (value bound : Nat) (hvalue : value <= bound) :
    shortToIteratedPayloadResource value <=
      shortToIteratedPayloadPolynomial bound := by
  induction value generalizing bound with
  | zero =>
      simp [shortToIteratedPayloadResource,
        shortToIteratedPayloadPolynomial]
  | succ value inductionHypothesis =>
      have hvalueBound : value <= bound := by omega
      have hrecursive := inductionHypothesis value le_rfl
      have hstepMono := shortToIteratedStepPayloadPolynomial_mono
        hvalueBound
      have hrecursiveWiden : shortToIteratedPayloadResource value <=
          paPrimitiveCostEnvelope
              (binaryTermCode (shortBinaryNumeralTerm 0)).length +
            value * shortToIteratedStepPayloadPolynomial bound := by
        exact hrecursive.trans (Nat.add_le_add_left
          (Nat.mul_le_mul_left value hstepMono) _)
      have hstep := shortToIteratedStepPayloadResource_le_polynomial
        value bound (by omega)
      simp only [shortToIteratedPayloadResource]
      unfold shortToIteratedPayloadPolynomial at hrecursive ⊢
      calc
        _ <= paPrimitiveCostEnvelope
                (binaryTermCode (shortBinaryNumeralTerm 0)).length +
              value * shortToIteratedStepPayloadPolynomial bound +
              shortToIteratedStepPayloadPolynomial bound := by
          omega
        _ = paPrimitiveCostEnvelope
                (binaryTermCode (shortBinaryNumeralTerm 0)).length +
              (value + 1) * shortToIteratedStepPayloadPolynomial bound := by
          ring
        _ <= paPrimitiveCostEnvelope
                (binaryTermCode (shortBinaryNumeralTerm 0)).length +
              bound * shortToIteratedStepPayloadPolynomial bound := by
          exact Nat.add_le_add_left
            (Nat.mul_le_mul_right _ hvalue) _

theorem shortToIteratedPayloadResource_le_publicPolynomial (value : Nat) :
    shortToIteratedPayloadResource value <=
      shortToIteratedPayloadPolynomial value :=
  shortToIteratedPayloadResource_le_publicPolynomial_of_le
    value value le_rfl

theorem proveShortBinaryNumeralEqualsIterated_payloadLength_le_publicPolynomial
    (value : Nat) :
    (proveShortBinaryNumeralEqualsIterated value).payloadLength <=
      shortToIteratedPayloadPolynomial value :=
  (proveShortBinaryNumeralEqualsIterated_payloadLength_le_resource value).trans
    (shortToIteratedPayloadResource_le_publicPolynomial value)

/-! ## Closed normalization recursion -/

def additionNormalizationStepTermCodeResource
    (valuation : Nat -> Nat) (args : Fin 2 -> ValuationTerm) : Nat :=
  let leftValue := termValue valuation (args 0)
  let rightValue := termValue valuation (args 1)
  let leftNumeral := shortBinaryNumeralTerm leftValue
  let rightNumeral := shortBinaryNumeralTerm rightValue
  let leftTerm := instantiateTerm valuation (args 0)
  let rightTerm := instantiateTerm valuation (args 1)
  let source := paAddTerm leftNumeral rightNumeral
  let middle := paAddTerm leftTerm rightTerm
  let result := shortBinaryNumeralTerm (leftValue + rightValue)
  (binaryTermCode leftNumeral).length +
    (binaryTermCode rightNumeral).length +
    (binaryTermCode leftTerm).length +
    (binaryTermCode rightTerm).length +
    (binaryTermCode source).length +
    (binaryTermCode middle).length +
    (binaryTermCode result).length + 1

def multiplicationNormalizationStepTermCodeResource
    (valuation : Nat -> Nat) (args : Fin 2 -> ValuationTerm) : Nat :=
  let leftValue := termValue valuation (args 0)
  let rightValue := termValue valuation (args 1)
  let leftNumeral := shortBinaryNumeralTerm leftValue
  let rightNumeral := shortBinaryNumeralTerm rightValue
  let leftTerm := instantiateTerm valuation (args 0)
  let rightTerm := instantiateTerm valuation (args 1)
  let source := paMulTerm leftNumeral rightNumeral
  let middle := paMulTerm leftTerm rightTerm
  let result := shortBinaryNumeralTerm (leftValue * rightValue)
  (binaryTermCode leftNumeral).length +
    (binaryTermCode rightNumeral).length +
    (binaryTermCode leftTerm).length +
    (binaryTermCode rightTerm).length +
    (binaryTermCode source).length +
    (binaryTermCode middle).length +
    (binaryTermCode result).length + 1

/-- Recursive normalization budget.  Arithmetic nodes depend only on the
fixed syntax below them and on the bit widths of the two actual subterm
values. -/
def instantiatedTermNormalizationPayloadResource
    (valuation : Nat -> Nat) : ValuationTerm -> Nat
  | #index => Fin.elim0 index
  | &index => shortToIteratedPayloadResource (valuation index)
  | .func .zero _ => shortToIteratedPayloadResource 0
  | .func .one _ => paMultiplicationLocalCostEnvelope 0
  | .func .add args =>
      instantiatedTermNormalizationPayloadResource valuation (args 0) +
        instantiatedTermNormalizationPayloadResource valuation (args 1) +
        binaryNumeralAdditionPayloadPolynomial
          (Nat.size (termValue valuation (args 0)) +
            Nat.size (termValue valuation (args 1))) +
        3 * paPrimitiveCostEnvelope
          (additionNormalizationStepTermCodeResource valuation args)
  | .func .mul args =>
      instantiatedTermNormalizationPayloadResource valuation (args 0) +
        instantiatedTermNormalizationPayloadResource valuation (args 1) +
        binaryNumeralMultiplicationPayloadPolynomial
          (Nat.size (termValue valuation (args 0)) +
            Nat.size (termValue valuation (args 1))) +
        3 * paPrimitiveCostEnvelope
          (multiplicationNormalizationStepTermCodeResource valuation args)

theorem compileInstantiatedTermNormalization_payloadLength_le_resource
    (valuation : Nat -> Nat) :
    (term : ValuationTerm) ->
    (compileInstantiatedTermNormalization valuation term).payloadLength <=
      instantiatedTermNormalizationPayloadResource valuation term
  | #index => Fin.elim0 index
  | &index => by
      let raw := proveShortBinaryNumeralEqualsIterated (valuation index)
      have hinstantiate :
          instantiateTerm valuation (&index : ValuationTerm) =
            iteratedSuccessorTerm 0 (valuation index) := rfl
      have hformula :
          (“!!(shortBinaryNumeralTerm (valuation index)) =
            !!(iteratedSuccessorTerm 0 (valuation index))” :
            ValuationFormula) =
          (“!!(shortBinaryNumeralTerm
              (termValue valuation (&index : ValuationTerm))) =
            !!(instantiateTerm valuation (&index : ValuationTerm))” :
            ValuationFormula) := by
        rw [termValue_fvar, hinstantiate]
      have hpayload :
          (compileInstantiatedTermNormalization valuation
            (&index : ValuationTerm)).payloadLength = raw.payloadLength := by
        change (CertifiedPAProof.cast hformula raw).payloadLength = _
        exact CertifiedPAProof.cast_payloadLength _ _
      rw [hpayload]
      exact
        proveShortBinaryNumeralEqualsIterated_payloadLength_le_resource
          (valuation index)
  | .func .zero args => by
      let raw := proveShortBinaryNumeralEqualsIterated 0
      have hclosed : instantiateTerm valuation (.func .zero args) =
          iteratedSuccessorTerm 0 0 := by
        simp only [instantiateTerm, iteratedSuccessorTerm_zero]
        unfold finiteCaseZeroTerm
        congr 1
        funext index
        exact Fin.elim0 index
      have hformula :
          (“!!(shortBinaryNumeralTerm 0) =
            !!(iteratedSuccessorTerm 0 0)” : ValuationFormula) =
          (“!!(shortBinaryNumeralTerm
              (termValue valuation (.func .zero args))) =
            !!(instantiateTerm valuation (.func .zero args))” :
            ValuationFormula) := by
        rw [termValue_zero, hclosed]
      have hpayload :
          (compileInstantiatedTermNormalization valuation
            (.func .zero args)).payloadLength = raw.payloadLength := by
        change (CertifiedPAProof.cast hformula raw).payloadLength = _
        exact CertifiedPAProof.cast_payloadLength _ _
      rw [hpayload]
      exact
        proveShortBinaryNumeralEqualsIterated_payloadLength_le_resource 0
  | .func .one args => by
      let raw := proveShortBinaryOneEqualsPaOne
      have hclosed : instantiateTerm valuation (.func .one args) =
          paOneTerm := by
        calc
          instantiateTerm valuation (.func .one args) =
              (.func .one args : ValuationTerm) := rfl
          _ = finiteCaseOneTerm 0 := by
            unfold finiteCaseOneTerm
            congr 1
            funext index
            exact Fin.elim0 index
          _ = paOneTerm := by rfl
      have hformula :
          (“!!(shortBinaryNumeralTerm 1) = !!paOneTerm” :
            ValuationFormula) =
          (“!!(shortBinaryNumeralTerm
              (termValue valuation (.func .one args))) =
            !!(instantiateTerm valuation (.func .one args))” :
            ValuationFormula) := by
        rw [termValue_one, hclosed]
      have hpayload :
          (compileInstantiatedTermNormalization valuation
            (.func .one args)).payloadLength = raw.payloadLength := by
        change (CertifiedPAProof.cast hformula raw).payloadLength = _
        exact CertifiedPAProof.cast_payloadLength _ _
      rw [hpayload]
      exact proveShortBinaryOneEqualsPaOne_payloadLength_le_local 0
  | .func .add args => by
      let leftValue := termValue valuation (args 0)
      let rightValue := termValue valuation (args 1)
      let leftProof := compileInstantiatedTermNormalization
        valuation (args 0)
      let rightProof := compileInstantiatedTermNormalization
        valuation (args 1)
      let source := paAddTerm
        (shortBinaryNumeralTerm leftValue)
        (shortBinaryNumeralTerm rightValue)
      let middle := paAddTerm
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1))
      let result := shortBinaryNumeralTerm (leftValue + rightValue)
      let congruenceRaw := proveAddCongruence
        (shortBinaryNumeralTerm leftValue)
        (shortBinaryNumeralTerm rightValue)
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1)) leftProof rightProof
      let congruence : CertifiedPAProof
          (“!!source = !!middle” : ValuationFormula) :=
        CertifiedPAProof.cast
          (addEqualityAsTerm_formula
            (shortBinaryNumeralTerm leftValue)
            (shortBinaryNumeralTerm rightValue)
            (instantiateTerm valuation (args 0))
            (instantiateTerm valuation (args 1))) congruenceRaw
      let arithmetic := proveBinaryNumeralAddition leftValue rightValue
      let arithmeticBackward := proveEqualitySymmetry
        source result arithmetic
      let through := proveEqualityTransitivity
        result source middle arithmeticBackward congruence
      let termBound := additionNormalizationStepTermCodeResource
        valuation args
      have hleftNumeral :
          (binaryTermCode (shortBinaryNumeralTerm leftValue)).length <=
            termBound := by
        simp only [termBound, additionNormalizationStepTermCodeResource,
          leftValue, rightValue]
        omega
      have hrightNumeral :
          (binaryTermCode (shortBinaryNumeralTerm rightValue)).length <=
            termBound := by
        simp only [termBound, additionNormalizationStepTermCodeResource,
          leftValue, rightValue]
        omega
      have hleftTerm :
          (binaryTermCode (instantiateTerm valuation (args 0))).length <=
            termBound := by
        simp only [termBound, additionNormalizationStepTermCodeResource,
          leftValue, rightValue]
        omega
      have hrightTerm :
          (binaryTermCode (instantiateTerm valuation (args 1))).length <=
            termBound := by
        simp only [termBound, additionNormalizationStepTermCodeResource,
          leftValue, rightValue]
        omega
      have hsource : (binaryTermCode source).length <= termBound := by
        simp only [termBound, additionNormalizationStepTermCodeResource,
          source, leftValue, rightValue]
        omega
      have hmiddle : (binaryTermCode middle).length <= termBound := by
        simp only [termBound, additionNormalizationStepTermCodeResource,
          middle, leftValue, rightValue]
        omega
      have hresult : (binaryTermCode result).length <= termBound := by
        simp only [termBound, additionNormalizationStepTermCodeResource,
          result, leftValue, rightValue]
        omega
      have hleft : leftProof.payloadLength <=
          instantiatedTermNormalizationPayloadResource
            valuation (args 0) :=
        compileInstantiatedTermNormalization_payloadLength_le_resource
          valuation (args 0)
      have hright : rightProof.payloadLength <=
          instantiatedTermNormalizationPayloadResource
            valuation (args 1) :=
        compileInstantiatedTermNormalization_payloadLength_le_resource
          valuation (args 1)
      have hcongruenceRaw := proveAddCongruence_payloadLength_le_primitive
        (shortBinaryNumeralTerm leftValue)
        (shortBinaryNumeralTerm rightValue)
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1)) leftProof rightProof
        termBound hleftNumeral hrightNumeral hleftTerm hrightTerm
      have hcongruence : congruence.payloadLength <=
          leftProof.payloadLength + rightProof.payloadLength +
            paPrimitiveCostEnvelope termBound := by
        have hcast : congruence.payloadLength =
            congruenceRaw.payloadLength := by
          change (CertifiedPAProof.cast _ congruenceRaw).payloadLength = _
          exact CertifiedPAProof.cast_payloadLength _ _
        rw [hcast]
        exact hcongruenceRaw
      have harithmetic : arithmetic.payloadLength <=
          binaryNumeralAdditionPayloadPolynomial
            (Nat.size leftValue + Nat.size rightValue) := by
        exact proveBinaryNumeralAddition_payloadLength_le_polynomial
          leftValue rightValue
      have harithmeticBackward : arithmeticBackward.payloadLength <=
          arithmetic.payloadLength + paPrimitiveCostEnvelope termBound :=
        proveEqualitySymmetry_payloadLength_le_primitive
          source result arithmetic termBound hsource hresult
      have hthrough : through.payloadLength <=
          arithmeticBackward.payloadLength + congruence.payloadLength +
            paPrimitiveCostEnvelope termBound :=
        proveEqualityTransitivity_payloadLength_le_primitive
          result source middle arithmeticBackward congruence
          termBound hresult hsource hmiddle
      have hclosed : instantiateTerm valuation (.func .add args) =
          middle := by
        calc
          instantiateTerm valuation (.func .add args) =
              finiteCaseAddTerm
                (instantiateTerm valuation (args 0))
                (instantiateTerm valuation (args 1)) := rfl
          _ = middle := by
            exact finiteCaseAddTerm_eq_paAddTerm _ _
      have hformula :
          (“!!(shortBinaryNumeralTerm (leftValue + rightValue)) =
            !!middle” : ValuationFormula) =
          (“!!(shortBinaryNumeralTerm
                (termValue valuation (.func .add args))) =
            !!(instantiateTerm valuation (.func .add args))” :
            ValuationFormula) := by
        rw [termValue_add, hclosed]
      have houter :
          (compileInstantiatedTermNormalization valuation
            (.func .add args)).payloadLength = through.payloadLength := by
        change (CertifiedPAProof.cast hformula through).payloadLength = _
        exact CertifiedPAProof.cast_payloadLength _ _
      rw [houter]
      change through.payloadLength <=
        instantiatedTermNormalizationPayloadResource valuation (args 0) +
          instantiatedTermNormalizationPayloadResource valuation (args 1) +
          binaryNumeralAdditionPayloadPolynomial
            (Nat.size leftValue + Nat.size rightValue) +
          3 * paPrimitiveCostEnvelope termBound
      omega

  | .func .mul args => by
      let leftValue := termValue valuation (args 0)
      let rightValue := termValue valuation (args 1)
      let leftProof := compileInstantiatedTermNormalization
        valuation (args 0)
      let rightProof := compileInstantiatedTermNormalization
        valuation (args 1)
      let source := paMulTerm
        (shortBinaryNumeralTerm leftValue)
        (shortBinaryNumeralTerm rightValue)
      let middle := paMulTerm
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1))
      let result := shortBinaryNumeralTerm (leftValue * rightValue)
      let congruenceRaw := proveMulCongruence
        (shortBinaryNumeralTerm leftValue)
        (shortBinaryNumeralTerm rightValue)
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1)) leftProof rightProof
      let congruence : CertifiedPAProof
          (“!!source = !!middle” : ValuationFormula) :=
        CertifiedPAProof.cast
          (mulEqualityAsTerm_formula
            (shortBinaryNumeralTerm leftValue)
            (shortBinaryNumeralTerm rightValue)
            (instantiateTerm valuation (args 0))
            (instantiateTerm valuation (args 1))) congruenceRaw
      let arithmetic := proveBinaryNumeralMultiplication leftValue rightValue
      let arithmeticBackward := proveEqualitySymmetry
        source result arithmetic
      let through := proveEqualityTransitivity
        result source middle arithmeticBackward congruence
      let termBound := multiplicationNormalizationStepTermCodeResource
        valuation args
      have hleftNumeral :
          (binaryTermCode (shortBinaryNumeralTerm leftValue)).length <=
            termBound := by
        simp only [termBound,
          multiplicationNormalizationStepTermCodeResource,
          leftValue, rightValue]
        omega
      have hrightNumeral :
          (binaryTermCode (shortBinaryNumeralTerm rightValue)).length <=
            termBound := by
        simp only [termBound,
          multiplicationNormalizationStepTermCodeResource,
          leftValue, rightValue]
        omega
      have hleftTerm :
          (binaryTermCode (instantiateTerm valuation (args 0))).length <=
            termBound := by
        simp only [termBound,
          multiplicationNormalizationStepTermCodeResource,
          leftValue, rightValue]
        omega
      have hrightTerm :
          (binaryTermCode (instantiateTerm valuation (args 1))).length <=
            termBound := by
        simp only [termBound,
          multiplicationNormalizationStepTermCodeResource,
          leftValue, rightValue]
        omega
      have hsource : (binaryTermCode source).length <= termBound := by
        simp only [termBound,
          multiplicationNormalizationStepTermCodeResource,
          source, leftValue, rightValue]
        omega
      have hmiddle : (binaryTermCode middle).length <= termBound := by
        simp only [termBound,
          multiplicationNormalizationStepTermCodeResource,
          middle, leftValue, rightValue]
        omega
      have hresult : (binaryTermCode result).length <= termBound := by
        simp only [termBound,
          multiplicationNormalizationStepTermCodeResource,
          result, leftValue, rightValue]
        omega
      have hleft : leftProof.payloadLength <=
          instantiatedTermNormalizationPayloadResource
            valuation (args 0) :=
        compileInstantiatedTermNormalization_payloadLength_le_resource
          valuation (args 0)
      have hright : rightProof.payloadLength <=
          instantiatedTermNormalizationPayloadResource
            valuation (args 1) :=
        compileInstantiatedTermNormalization_payloadLength_le_resource
          valuation (args 1)
      have hcongruenceRaw := proveMulCongruence_payloadLength_le_primitive
        (shortBinaryNumeralTerm leftValue)
        (shortBinaryNumeralTerm rightValue)
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1)) leftProof rightProof
        termBound hleftNumeral hrightNumeral hleftTerm hrightTerm
      have hcongruence : congruence.payloadLength <=
          leftProof.payloadLength + rightProof.payloadLength +
            paPrimitiveCostEnvelope termBound := by
        have hcast : congruence.payloadLength =
            congruenceRaw.payloadLength := by
          change (CertifiedPAProof.cast _ congruenceRaw).payloadLength = _
          exact CertifiedPAProof.cast_payloadLength _ _
        rw [hcast]
        exact hcongruenceRaw
      have harithmetic : arithmetic.payloadLength <=
          binaryNumeralMultiplicationPayloadPolynomial
            (Nat.size leftValue + Nat.size rightValue) := by
        exact proveBinaryNumeralMultiplication_payloadLength_le_polynomial
          leftValue rightValue
      have harithmeticBackward : arithmeticBackward.payloadLength <=
          arithmetic.payloadLength + paPrimitiveCostEnvelope termBound :=
        proveEqualitySymmetry_payloadLength_le_primitive
          source result arithmetic termBound hsource hresult
      have hthrough : through.payloadLength <=
          arithmeticBackward.payloadLength + congruence.payloadLength +
            paPrimitiveCostEnvelope termBound :=
        proveEqualityTransitivity_payloadLength_le_primitive
          result source middle arithmeticBackward congruence
          termBound hresult hsource hmiddle
      have hclosed : instantiateTerm valuation (.func .mul args) =
          middle := by
        calc
          instantiateTerm valuation (.func .mul args) =
              LO.FirstOrder.Semiterm.func Language.Mul.mul ![
                instantiateTerm valuation (args 0),
                instantiateTerm valuation (args 1)] := rfl
          _ = middle := by
            exact finiteCaseMulTerm_eq_paMulTerm _ _
      have hformula :
          (“!!(shortBinaryNumeralTerm (leftValue * rightValue)) =
            !!middle” : ValuationFormula) =
          (“!!(shortBinaryNumeralTerm
                (termValue valuation (.func .mul args))) =
            !!(instantiateTerm valuation (.func .mul args))” :
            ValuationFormula) := by
        rw [termValue_mul, hclosed]
      have houter :
          (compileInstantiatedTermNormalization valuation
            (.func .mul args)).payloadLength = through.payloadLength := by
        change (CertifiedPAProof.cast hformula through).payloadLength = _
        exact CertifiedPAProof.cast_payloadLength _ _
      rw [houter]
      change through.payloadLength <=
        instantiatedTermNormalizationPayloadResource valuation (args 0) +
          instantiatedTermNormalizationPayloadResource valuation (args 1) +
          binaryNumeralMultiplicationPayloadPolynomial
            (Nat.size leftValue + Nat.size rightValue) +
          3 * paPrimitiveCostEnvelope termBound
      omega

/-! ## Instantiated-term transport recursion -/

/-- Recursive structural budget for transport under the valuation context.
All contexts and formulas are computed from `valuation` and `term`; there is
no external context-code bound. -/
def instantiatedTermTransportPayloadResource
    (valuation : Nat -> Nat) : ValuationTerm -> Nat
  | #index => Fin.elim0 index
  | &index =>
      let Gamma := valuationContext ({index} : Finset Nat) valuation
      let formula :=
        (“!!(iteratedSuccessorTerm 0 (valuation index)) =
          !!(&index : ValuationTerm)” : ValuationFormula)
      CertifiedPAContextProof.assumptionFullPayloadCost Gamma formula
  | .func .zero args =>
      let term := (.func .zero args : ValuationTerm)
      let Gamma := valuationContext term.freeVariables valuation
      let formula :=
        (“!!(instantiateTerm valuation term) = !!term” : ValuationFormula)
      paPrimitiveCostEnvelope (binaryTermCode term).length +
        weakeningFullAssemblyCost (insert formula Gamma)
  | .func .one args =>
      let term := (.func .one args : ValuationTerm)
      let Gamma := valuationContext term.freeVariables valuation
      let formula :=
        (“!!(instantiateTerm valuation term) = !!term” : ValuationFormula)
      paPrimitiveCostEnvelope (binaryTermCode term).length +
        weakeningFullAssemblyCost (insert formula Gamma)
  | .func .add args =>
      let term := (.func .add args : ValuationTerm)
      let Gamma := valuationContext term.freeVariables valuation
      let leftFormula :=
        (“!!(instantiateTerm valuation (args 0)) = !!(args 0)” :
          ValuationFormula)
      let rightFormula :=
        (“!!(instantiateTerm valuation (args 1)) = !!(args 1)” :
          ValuationFormula)
      let leftBound :=
        instantiatedTermTransportPayloadResource valuation (args 0) +
          weakeningFullAssemblyCost (insert leftFormula Gamma)
      let rightBound :=
        instantiatedTermTransportPayloadResource valuation (args 1) +
          weakeningFullAssemblyCost (insert rightFormula Gamma)
      contextualBinaryFunctionCongruenceStructuralPayloadBound Gamma
        Language.Add.add
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1))
        (args 0) (args 1) leftBound rightBound
  | .func .mul args =>
      let term := (.func .mul args : ValuationTerm)
      let Gamma := valuationContext term.freeVariables valuation
      let leftFormula :=
        (“!!(instantiateTerm valuation (args 0)) = !!(args 0)” :
          ValuationFormula)
      let rightFormula :=
        (“!!(instantiateTerm valuation (args 1)) = !!(args 1)” :
          ValuationFormula)
      let leftBound :=
        instantiatedTermTransportPayloadResource valuation (args 0) +
          weakeningFullAssemblyCost (insert leftFormula Gamma)
      let rightBound :=
        instantiatedTermTransportPayloadResource valuation (args 1) +
          weakeningFullAssemblyCost (insert rightFormula Gamma)
      contextualBinaryFunctionCongruenceStructuralPayloadBound Gamma
        Language.Mul.mul
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1))
        (args 0) (args 1) leftBound rightBound

theorem compileInstantiatedTermTransport_payloadLength_le_resource
    (valuation : Nat -> Nat) :
    (term : ValuationTerm) ->
    (compileInstantiatedTermTransport valuation term).payloadLength <=
      instantiatedTermTransportPayloadResource valuation term
  | #index => Fin.elim0 index
  | &index => by
      let term := (&index : ValuationTerm)
      let Gamma := valuationContext ({index} : Finset Nat) valuation
      let assumptionFormula :=
        (“!!(iteratedSuccessorTerm 0 (valuation index)) = !!term” :
          ValuationFormula)
      let targetFormula :=
        (“!!(instantiateTerm valuation term) = !!term” : ValuationFormula)
      have hinstantiate : instantiateTerm valuation term =
          iteratedSuccessorTerm 0 (valuation index) := rfl
      have hformula : assumptionFormula = targetFormula := by
        simp only [assumptionFormula, targetFormula, hinstantiate]
      have hmembership : ∼assumptionFormula ∈ Gamma := by
        simp [term, Gamma, assumptionFormula, valuationContext,
          valuationEqualityAssumption, finiteCaseEqualityFormula_eq_operator]
      let raw := CertifiedPAContextProof.assumption
        Gamma assumptionFormula hmembership
      let casted := CertifiedPAContextProof.cast hformula raw
      have hraw : raw.payloadLength =
          CertifiedPAContextProof.assumptionFullPayloadCost
            Gamma assumptionFormula :=
        CertifiedPAContextProof.assumption_payloadLength_eq
          Gamma assumptionFormula hmembership
      have hcast : casted.payloadLength = raw.payloadLength := by
        change (CertifiedPAContextProof.cast hformula raw).payloadLength = _
        exact CertifiedPAContextProof.cast_payloadLength _ _
      have hcompiled :
          (compileInstantiatedTermTransport valuation term).payloadLength =
            casted.payloadLength := by
        change raw.payloadLength = casted.payloadLength
        exact hcast.symm
      have hcost :
          (compileInstantiatedTermTransport valuation term).payloadLength =
            CertifiedPAContextProof.assumptionFullPayloadCost
              Gamma assumptionFormula := by
        rw [hcompiled, hcast, hraw]
      calc
        (compileInstantiatedTermTransport valuation term).payloadLength <=
            CertifiedPAContextProof.assumptionFullPayloadCost
              Gamma assumptionFormula := hcost.le
        _ = instantiatedTermTransportPayloadResource valuation
            (&index : ValuationTerm) := by rfl
  | .func .zero args => by
      let term := (.func .zero args : ValuationTerm)
      let Gamma := valuationContext term.freeVariables valuation
      let reflexiveFormula := (“!!term = !!term” : ValuationFormula)
      let targetFormula :=
        (“!!(instantiateTerm valuation term) = !!term” : ValuationFormula)
      have hinstantiate : instantiateTerm valuation term = term := rfl
      have hformula : reflexiveFormula = targetFormula := by
        simp only [reflexiveFormula, targetFormula, hinstantiate]
      let proof := proveEqualityReflexivityAtTerm term
      let weakenedRaw := CertifiedPAContextProof.weakenCertified Gamma proof
      let weakened := CertifiedPAContextProof.cast hformula weakenedRaw
      have hproof : proof.payloadLength <=
          paPrimitiveCostEnvelope (binaryTermCode term).length :=
        proveEqualityReflexivityAtTerm_payloadLength_le_primitive
          term (binaryTermCode term).length le_rfl
      have hweaken : weakenedRaw.payloadLength <= proof.payloadLength +
          weakeningFullAssemblyCost (insert reflexiveFormula Gamma) :=
        CertifiedPAContextProof.weakenCertified_payloadLength_le Gamma proof
      have hcast : weakened.payloadLength = weakenedRaw.payloadLength := by
        change (CertifiedPAContextProof.cast hformula weakenedRaw).payloadLength = _
        exact CertifiedPAContextProof.cast_payloadLength _ _
      have hcompiled :
          (compileInstantiatedTermTransport valuation term).payloadLength =
            weakened.payloadLength := by
        change weakenedRaw.payloadLength = weakened.payloadLength
        exact hcast.symm
      calc
        (compileInstantiatedTermTransport valuation term).payloadLength =
            weakened.payloadLength := hcompiled
        _ = weakenedRaw.payloadLength := hcast
        _ <= proof.payloadLength +
            weakeningFullAssemblyCost (insert reflexiveFormula Gamma) := hweaken
        _ <= paPrimitiveCostEnvelope (binaryTermCode term).length +
            weakeningFullAssemblyCost (insert reflexiveFormula Gamma) := by
          exact Nat.add_le_add_right hproof _
        _ = paPrimitiveCostEnvelope (binaryTermCode term).length +
            weakeningFullAssemblyCost (insert targetFormula Gamma) := by
          rw [hformula]
        _ = instantiatedTermTransportPayloadResource valuation
            (.func .zero args) := by
          simp [instantiatedTermTransportPayloadResource, term, Gamma,
            targetFormula]
  | .func .one args => by
      let term := (.func .one args : ValuationTerm)
      let Gamma := valuationContext term.freeVariables valuation
      let reflexiveFormula := (“!!term = !!term” : ValuationFormula)
      let targetFormula :=
        (“!!(instantiateTerm valuation term) = !!term” : ValuationFormula)
      have hinstantiate : instantiateTerm valuation term = term := rfl
      have hformula : reflexiveFormula = targetFormula := by
        simp only [reflexiveFormula, targetFormula, hinstantiate]
      let proof := proveEqualityReflexivityAtTerm term
      let weakenedRaw := CertifiedPAContextProof.weakenCertified Gamma proof
      let weakened := CertifiedPAContextProof.cast hformula weakenedRaw
      have hproof : proof.payloadLength <=
          paPrimitiveCostEnvelope (binaryTermCode term).length :=
        proveEqualityReflexivityAtTerm_payloadLength_le_primitive
          term (binaryTermCode term).length le_rfl
      have hweaken : weakenedRaw.payloadLength <= proof.payloadLength +
          weakeningFullAssemblyCost (insert reflexiveFormula Gamma) :=
        CertifiedPAContextProof.weakenCertified_payloadLength_le Gamma proof
      have hcast : weakened.payloadLength = weakenedRaw.payloadLength := by
        change (CertifiedPAContextProof.cast hformula weakenedRaw).payloadLength = _
        exact CertifiedPAContextProof.cast_payloadLength _ _
      have hcompiled :
          (compileInstantiatedTermTransport valuation term).payloadLength =
            weakened.payloadLength := by
        change weakenedRaw.payloadLength = weakened.payloadLength
        exact hcast.symm
      calc
        (compileInstantiatedTermTransport valuation term).payloadLength =
            weakened.payloadLength := hcompiled
        _ = weakenedRaw.payloadLength := hcast
        _ <= proof.payloadLength +
            weakeningFullAssemblyCost (insert reflexiveFormula Gamma) := hweaken
        _ <= paPrimitiveCostEnvelope (binaryTermCode term).length +
            weakeningFullAssemblyCost (insert reflexiveFormula Gamma) := by
          exact Nat.add_le_add_right hproof _
        _ = paPrimitiveCostEnvelope (binaryTermCode term).length +
            weakeningFullAssemblyCost (insert targetFormula Gamma) := by
          rw [hformula]
        _ = instantiatedTermTransportPayloadResource valuation
            (.func .one args) := by
          simp [instantiatedTermTransportPayloadResource, term, Gamma,
            targetFormula]
  | .func .add args => by
      let term := (.func .add args : ValuationTerm)
      let Gamma := valuationContext term.freeVariables valuation
      let leftFormula :=
        (“!!(instantiateTerm valuation (args 0)) = !!(args 0)” :
          ValuationFormula)
      let rightFormula :=
        (“!!(instantiateTerm valuation (args 1)) = !!(args 1)” :
          ValuationFormula)
      let leftRaw := compileInstantiatedTermTransport valuation (args 0)
      let rightRaw := compileInstantiatedTermTransport valuation (args 1)
      have hleftVariables : (args 0).freeVariables <= term.freeVariables := by
        exact freeVariables_arg_subset_func Language.Add.add args 0
      have hrightVariables : (args 1).freeVariables <= term.freeVariables := by
        exact freeVariables_arg_subset_func Language.Add.add args 1
      have hleftContext :
          valuationContext (args 0).freeVariables valuation <= Gamma := by
        exact valuationContext_mono valuation hleftVariables
      have hrightContext :
          valuationContext (args 1).freeVariables valuation <= Gamma := by
        exact valuationContext_mono valuation hrightVariables
      let left := CertifiedPAContextProof.weakenContext leftRaw hleftContext
      let right := CertifiedPAContextProof.weakenContext rightRaw hrightContext
      let congruenceGeneric :=
        contextualBinaryFunctionCongruenceFromEqualities Language.Add.add
          (instantiateTerm valuation (args 0))
          (instantiateTerm valuation (args 1))
          (args 0) (args 1) left right
      let congruence := contextualAddCongruence
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1))
        (args 0) (args 1) left right
      let leftBound :=
        instantiatedTermTransportPayloadResource valuation (args 0) +
          weakeningFullAssemblyCost (insert leftFormula Gamma)
      let rightBound :=
        instantiatedTermTransportPayloadResource valuation (args 1) +
          weakeningFullAssemblyCost (insert rightFormula Gamma)
      have hleftRaw : leftRaw.payloadLength <=
          instantiatedTermTransportPayloadResource valuation (args 0) :=
        compileInstantiatedTermTransport_payloadLength_le_resource
          valuation (args 0)
      have hrightRaw : rightRaw.payloadLength <=
          instantiatedTermTransportPayloadResource valuation (args 1) :=
        compileInstantiatedTermTransport_payloadLength_le_resource
          valuation (args 1)
      have hleftWeaken : left.payloadLength <= leftRaw.payloadLength +
          weakeningFullAssemblyCost (insert leftFormula Gamma) :=
        CertifiedPAContextProof.weakenContext_payloadLength_le
          leftRaw hleftContext
      have hrightWeaken : right.payloadLength <= rightRaw.payloadLength +
          weakeningFullAssemblyCost (insert rightFormula Gamma) :=
        CertifiedPAContextProof.weakenContext_payloadLength_le
          rightRaw hrightContext
      have hleft : left.payloadLength <= leftBound := by
        calc
          left.payloadLength <=
              leftRaw.payloadLength +
                weakeningFullAssemblyCost (insert leftFormula Gamma) :=
            hleftWeaken
          _ <= instantiatedTermTransportPayloadResource valuation (args 0) +
                weakeningFullAssemblyCost (insert leftFormula Gamma) := by
            exact Nat.add_le_add_right hleftRaw _
          _ = leftBound := by rfl
      have hright : right.payloadLength <= rightBound := by
        calc
          right.payloadLength <=
              rightRaw.payloadLength +
                weakeningFullAssemblyCost (insert rightFormula Gamma) :=
            hrightWeaken
          _ <= instantiatedTermTransportPayloadResource valuation (args 1) +
                weakeningFullAssemblyCost (insert rightFormula Gamma) := by
            exact Nat.add_le_add_right hrightRaw _
          _ = rightBound := by rfl
      have hgeneric :=
        contextualBinaryFunctionCongruence_payloadLength_le
          Language.Add.add
          (instantiateTerm valuation (args 0))
          (instantiateTerm valuation (args 1))
          (args 0) (args 1) left right
      have hgenericBound : congruenceGeneric.payloadLength <=
          contextualBinaryFunctionCongruenceStructuralPayloadBound Gamma
            Language.Add.add
            (instantiateTerm valuation (args 0))
            (instantiateTerm valuation (args 1))
            (args 0) (args 1) leftBound rightBound := by
        calc
          congruenceGeneric.payloadLength <=
              contextualBinaryFunctionCongruenceStructuralPayloadBound Gamma
                Language.Add.add
                (instantiateTerm valuation (args 0))
                (instantiateTerm valuation (args 1))
                (args 0) (args 1) left.payloadLength right.payloadLength := by
            exact hgeneric
          _ <= contextualBinaryFunctionCongruenceStructuralPayloadBound Gamma
                Language.Add.add
                (instantiateTerm valuation (args 0))
                (instantiateTerm valuation (args 1))
                (args 0) (args 1) leftBound rightBound := by
            simp only [contextualBinaryFunctionCongruenceStructuralPayloadBound]
            omega
      have hcongruence : congruence.payloadLength <=
          contextualBinaryFunctionCongruenceStructuralPayloadBound Gamma
            Language.Add.add
            (instantiateTerm valuation (args 0))
            (instantiateTerm valuation (args 1))
            (args 0) (args 1) leftBound rightBound := by
        have hcast : congruence.payloadLength =
            congruenceGeneric.payloadLength := by
          change (CertifiedPAContextProof.cast _ congruenceGeneric).payloadLength = _
          exact CertifiedPAContextProof.cast_payloadLength _ _
        rw [hcast]
        exact hgenericBound
      have houter :
          (compileInstantiatedTermTransport valuation
            (.func .add args)).payloadLength = congruence.payloadLength := by
        change (CertifiedPAContextProof.cast _ congruence).payloadLength = _
        exact CertifiedPAContextProof.cast_payloadLength _ _
      rw [houter]
      change congruence.payloadLength <=
        contextualBinaryFunctionCongruenceStructuralPayloadBound Gamma
          Language.Add.add
          (instantiateTerm valuation (args 0))
          (instantiateTerm valuation (args 1))
          (args 0) (args 1) leftBound rightBound
      exact hcongruence

  | .func .mul args => by
      let term := (.func .mul args : ValuationTerm)
      let Gamma := valuationContext term.freeVariables valuation
      let leftFormula :=
        (“!!(instantiateTerm valuation (args 0)) = !!(args 0)” :
          ValuationFormula)
      let rightFormula :=
        (“!!(instantiateTerm valuation (args 1)) = !!(args 1)” :
          ValuationFormula)
      let leftRaw := compileInstantiatedTermTransport valuation (args 0)
      let rightRaw := compileInstantiatedTermTransport valuation (args 1)
      have hleftVariables : (args 0).freeVariables <= term.freeVariables := by
        exact freeVariables_arg_subset_func Language.Mul.mul args 0
      have hrightVariables : (args 1).freeVariables <= term.freeVariables := by
        exact freeVariables_arg_subset_func Language.Mul.mul args 1
      have hleftContext :
          valuationContext (args 0).freeVariables valuation <= Gamma := by
        exact valuationContext_mono valuation hleftVariables
      have hrightContext :
          valuationContext (args 1).freeVariables valuation <= Gamma := by
        exact valuationContext_mono valuation hrightVariables
      let left := CertifiedPAContextProof.weakenContext leftRaw hleftContext
      let right := CertifiedPAContextProof.weakenContext rightRaw hrightContext
      let congruenceGeneric :=
        contextualBinaryFunctionCongruenceFromEqualities Language.Mul.mul
          (instantiateTerm valuation (args 0))
          (instantiateTerm valuation (args 1))
          (args 0) (args 1) left right
      let congruence := contextualMulCongruence
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1))
        (args 0) (args 1) left right
      let leftBound :=
        instantiatedTermTransportPayloadResource valuation (args 0) +
          weakeningFullAssemblyCost (insert leftFormula Gamma)
      let rightBound :=
        instantiatedTermTransportPayloadResource valuation (args 1) +
          weakeningFullAssemblyCost (insert rightFormula Gamma)
      have hleftRaw : leftRaw.payloadLength <=
          instantiatedTermTransportPayloadResource valuation (args 0) :=
        compileInstantiatedTermTransport_payloadLength_le_resource
          valuation (args 0)
      have hrightRaw : rightRaw.payloadLength <=
          instantiatedTermTransportPayloadResource valuation (args 1) :=
        compileInstantiatedTermTransport_payloadLength_le_resource
          valuation (args 1)
      have hleftWeaken : left.payloadLength <= leftRaw.payloadLength +
          weakeningFullAssemblyCost (insert leftFormula Gamma) :=
        CertifiedPAContextProof.weakenContext_payloadLength_le
          leftRaw hleftContext
      have hrightWeaken : right.payloadLength <= rightRaw.payloadLength +
          weakeningFullAssemblyCost (insert rightFormula Gamma) :=
        CertifiedPAContextProof.weakenContext_payloadLength_le
          rightRaw hrightContext
      have hleft : left.payloadLength <= leftBound := by
        calc
          left.payloadLength <=
              leftRaw.payloadLength +
                weakeningFullAssemblyCost (insert leftFormula Gamma) :=
            hleftWeaken
          _ <= instantiatedTermTransportPayloadResource valuation (args 0) +
                weakeningFullAssemblyCost (insert leftFormula Gamma) := by
            exact Nat.add_le_add_right hleftRaw _
          _ = leftBound := by rfl
      have hright : right.payloadLength <= rightBound := by
        calc
          right.payloadLength <=
              rightRaw.payloadLength +
                weakeningFullAssemblyCost (insert rightFormula Gamma) :=
            hrightWeaken
          _ <= instantiatedTermTransportPayloadResource valuation (args 1) +
                weakeningFullAssemblyCost (insert rightFormula Gamma) := by
            exact Nat.add_le_add_right hrightRaw _
          _ = rightBound := by rfl
      have hgeneric :=
        contextualBinaryFunctionCongruence_payloadLength_le
          Language.Mul.mul
          (instantiateTerm valuation (args 0))
          (instantiateTerm valuation (args 1))
          (args 0) (args 1) left right
      have hgenericBound : congruenceGeneric.payloadLength <=
          contextualBinaryFunctionCongruenceStructuralPayloadBound Gamma
            Language.Mul.mul
            (instantiateTerm valuation (args 0))
            (instantiateTerm valuation (args 1))
            (args 0) (args 1) leftBound rightBound := by
        calc
          congruenceGeneric.payloadLength <=
              contextualBinaryFunctionCongruenceStructuralPayloadBound Gamma
                Language.Mul.mul
                (instantiateTerm valuation (args 0))
                (instantiateTerm valuation (args 1))
                (args 0) (args 1) left.payloadLength right.payloadLength := by
            exact hgeneric
          _ <= contextualBinaryFunctionCongruenceStructuralPayloadBound Gamma
                Language.Mul.mul
                (instantiateTerm valuation (args 0))
                (instantiateTerm valuation (args 1))
                (args 0) (args 1) leftBound rightBound := by
            simp only [contextualBinaryFunctionCongruenceStructuralPayloadBound]
            omega
      have hcongruence : congruence.payloadLength <=
          contextualBinaryFunctionCongruenceStructuralPayloadBound Gamma
            Language.Mul.mul
            (instantiateTerm valuation (args 0))
            (instantiateTerm valuation (args 1))
            (args 0) (args 1) leftBound rightBound := by
        have hcast : congruence.payloadLength =
            congruenceGeneric.payloadLength := by
          change (CertifiedPAContextProof.cast _ congruenceGeneric).payloadLength = _
          exact CertifiedPAContextProof.cast_payloadLength _ _
        rw [hcast]
        exact hgenericBound
      have houter :
          (compileInstantiatedTermTransport valuation
            (.func .mul args)).payloadLength = congruence.payloadLength := by
        change (CertifiedPAContextProof.cast _ congruence).payloadLength = _
        exact CertifiedPAContextProof.cast_payloadLength _ _
      rw [houter]
      change congruence.payloadLength <=
        contextualBinaryFunctionCongruenceStructuralPayloadBound Gamma
          Language.Mul.mul
          (instantiateTerm valuation (args 0))
          (instantiateTerm valuation (args 1))
          (args 0) (args 1) leftBound rightBound
      exact hcongruence

/-! ## Final contextual term-value equality -/

def contextualizedNormalizationPayloadResource
    (valuation : Nat -> Nat) (term : ValuationTerm) : Nat :=
  let Gamma := valuationContext term.freeVariables valuation
  let formula :=
    (“!!(shortBinaryNumeralTerm (termValue valuation term)) =
      !!(instantiateTerm valuation term)” : ValuationFormula)
  instantiatedTermNormalizationPayloadResource valuation term +
    weakeningFullAssemblyCost (insert formula Gamma)

/-- Canonical resource for the complete valuation term compiler.  Both input
coordinates of the final transitivity node are themselves explicit recursive
functions of `valuation` and `term`. -/
def compileTermValueEqualityPayloadResource
    (valuation : Nat -> Nat) (term : ValuationTerm) : Nat :=
  let Gamma := valuationContext term.freeVariables valuation
  contextualEqualityTransitivityStructuralPayloadBound Gamma
    (shortBinaryNumeralTerm (termValue valuation term))
    (instantiateTerm valuation term) term
    (contextualizedNormalizationPayloadResource valuation term)
    (instantiatedTermTransportPayloadResource valuation term)

theorem compileTermValueEquality_payloadLength_le_resource
    (valuation : Nat -> Nat) (term : ValuationTerm) :
    (compileTermValueEquality valuation term).payloadLength <=
      compileTermValueEqualityPayloadResource valuation term := by
  let Gamma := valuationContext term.freeVariables valuation
  let normalizationClosed :=
    compileInstantiatedTermNormalization valuation term
  let normalization := CertifiedPAContextProof.weakenCertified
    Gamma normalizationClosed
  let transport := compileInstantiatedTermTransport valuation term
  let normalizationFormula :=
    (“!!(shortBinaryNumeralTerm (termValue valuation term)) =
      !!(instantiateTerm valuation term)” : ValuationFormula)
  let normalizationBound :=
    contextualizedNormalizationPayloadResource valuation term
  have hnormalizationClosed : normalizationClosed.payloadLength <=
      instantiatedTermNormalizationPayloadResource valuation term :=
    compileInstantiatedTermNormalization_payloadLength_le_resource
      valuation term
  have hnormalizationWeaken : normalization.payloadLength <=
      normalizationClosed.payloadLength +
        weakeningFullAssemblyCost (insert normalizationFormula Gamma) :=
    CertifiedPAContextProof.weakenCertified_payloadLength_le
      Gamma normalizationClosed
  have hnormalization : normalization.payloadLength <=
      normalizationBound := by
    calc
      normalization.payloadLength <=
          normalizationClosed.payloadLength +
            weakeningFullAssemblyCost
              (insert normalizationFormula Gamma) := hnormalizationWeaken
      _ <= instantiatedTermNormalizationPayloadResource valuation term +
            weakeningFullAssemblyCost
              (insert normalizationFormula Gamma) := by
        exact Nat.add_le_add_right hnormalizationClosed _
      _ = normalizationBound := by rfl
  have htransport : transport.payloadLength <=
      instantiatedTermTransportPayloadResource valuation term :=
    compileInstantiatedTermTransport_payloadLength_le_resource
      valuation term
  have htransitivity := contextualEqualityTransitivity_payloadLength_le
    (shortBinaryNumeralTerm (termValue valuation term))
    (instantiateTerm valuation term) term normalization transport
  calc
    (compileTermValueEquality valuation term).payloadLength =
        (contextualEqualityTransitivity
          (shortBinaryNumeralTerm (termValue valuation term))
          (instantiateTerm valuation term) term
          normalization transport).payloadLength := by rfl
    _ <= contextualEqualityTransitivityStructuralPayloadBound Gamma
          (shortBinaryNumeralTerm (termValue valuation term))
          (instantiateTerm valuation term) term
          normalization.payloadLength transport.payloadLength := by
      exact htransitivity
    _ <= contextualEqualityTransitivityStructuralPayloadBound Gamma
          (shortBinaryNumeralTerm (termValue valuation term))
          (instantiateTerm valuation term) term
          normalizationBound
          (instantiatedTermTransportPayloadResource valuation term) := by
      simp only [contextualEqualityTransitivityStructuralPayloadBound]
      omega
    _ = compileTermValueEqualityPayloadResource valuation term := by
      rfl

/-! ## Fixed polynomial envelope -/

/-- A fixed univariate polynomial used as the public envelope over the
canonical recursive resource coordinate. -/
def valuationTermCompilerPayloadPolynomial (resource : Nat) : Nat :=
  resource * resource + 2 * resource + 1

theorem resource_le_valuationTermCompilerPayloadPolynomial
    (resource : Nat) :
    resource <= valuationTermCompilerPayloadPolynomial resource := by
  unfold valuationTermCompilerPayloadPolynomial
  calc
    resource <= 2 * resource := by omega
    _ <= resource * resource + 2 * resource :=
      Nat.le_add_left _ _
    _ <= resource * resource + 2 * resource + 1 :=
      Nat.le_add_right _ _

theorem compileTermValueEqualityPayloadResource_le_fixedPolynomial
    (valuation : Nat -> Nat) (term : ValuationTerm) :
    compileTermValueEqualityPayloadResource valuation term <=
      valuationTermCompilerPayloadPolynomial
        (compileTermValueEqualityPayloadResource valuation term) := by
  exact resource_le_valuationTermCompilerPayloadPolynomial _

/-- Public endpoint for subsequent fixed-matrix compilers: it has no proof,
proof-length, or external resource argument. -/
theorem compileTermValueEquality_payloadLength_le_fixedPolynomial
    (valuation : Nat -> Nat) (term : ValuationTerm) :
    (compileTermValueEquality valuation term).payloadLength <=
      valuationTermCompilerPayloadPolynomial
        (compileTermValueEqualityPayloadResource valuation term) := by
  exact (compileTermValueEquality_payloadLength_le_resource valuation term).trans
    (compileTermValueEqualityPayloadResource_le_fixedPolynomial
      valuation term)

/-- Canonical common coordinate for a fixed finite family of matrix terms. -/
def fixedTermFamilyPayloadResource
    {termCount : Nat} (valuation : Nat -> Nat)
    (terms : Fin termCount -> ValuationTerm) : Nat :=
  Finset.univ.sum
    (fun index => compileTermValueEqualityPayloadResource
      valuation (terms index))

/-- Uniform endpoint for a fixed matrix (or any fixed finite term family).
The matrix caller supplies only its valuation and its fixed term family. -/
theorem compileTermValueEquality_payloadLength_le_fixedTermFamilyPolynomial
    {termCount : Nat} (valuation : Nat -> Nat)
    (terms : Fin termCount -> ValuationTerm) (index : Fin termCount) :
    (compileTermValueEquality valuation (terms index)).payloadLength <=
      valuationTermCompilerPayloadPolynomial
        (fixedTermFamilyPayloadResource valuation terms) := by
  have hpayload := compileTermValueEquality_payloadLength_le_resource
    valuation (terms index)
  have hmember :
      compileTermValueEqualityPayloadResource valuation (terms index) <=
        fixedTermFamilyPayloadResource valuation terms := by
    unfold fixedTermFamilyPayloadResource
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        (compileTermValueEqualityPayloadResource
          valuation (terms candidate)))
      (Finset.mem_univ index)
  exact hpayload.trans
    (hmember.trans
      (resource_le_valuationTermCompilerPayloadPolynomial _))

#print axioms proveShortBinaryNumeralEqualsIterated_payloadLength_le_resource
#print axioms shortToIteratedStepTermCodeResource_le_polynomial
#print axioms shortToIteratedPayloadResource_le_publicPolynomial
#print axioms
  proveShortBinaryNumeralEqualsIterated_payloadLength_le_publicPolynomial
#print axioms compileInstantiatedTermNormalization_payloadLength_le_resource
#print axioms compileInstantiatedTermTransport_payloadLength_le_resource
#print axioms compileTermValueEquality_payloadLength_le_resource
#print axioms compileTermValueEquality_payloadLength_le_fixedPolynomial
#print axioms compileTermValueEquality_payloadLength_le_fixedTermFamilyPolynomial

end FoundationCompactPAValuationTermCompilerBounds
