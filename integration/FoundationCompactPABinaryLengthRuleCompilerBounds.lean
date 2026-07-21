import integration.FoundationCompactPABinaryLengthRuleCompiler
import integration.FoundationCompactPAExponentialShortNumeralTransportBounds
import integration.FoundationCompactPAClosedAtomicCompilerBounds

/-!
# Polynomial bounds for binary-length proofs

Every recursive step is charged against an explicit envelope indexed only by
the current binary width.  Prefix widths are absorbed by a finite cumulative
sum, avoiding any hidden monotonicity premise and keeping the final bound
independent of the numeric magnitude of the represented value.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABinaryLengthRuleCompilerBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExponentialRuleCompiler
open FoundationCompactPAExponentialRuleCompilerBounds
open FoundationCompactPAExponentialShortNumeralCompiler
open FoundationCompactPAExponentialShortNumeralCompilerBounds
open FoundationCompactPAExponentialShortNumeralTransportBounds
open FoundationCompactPAClosedAtomicCompiler
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm
open FoundationCompactPAClosedAtomicCompilerBounds
open FoundationCompactPAClosedAtomicCompilerBounds.ClosedPATerm
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPABinaryLengthRuleCompiler

def binaryLengthTermCodeEnvelope (width : Nat) : Nat :=
  exponentialShortTermCodeEnvelope width

def binaryLengthRuleFormulaSeed : Nat :=
  max
    (binaryFormulaCode binaryLengthEvenOuterBody).length
    (binaryFormulaCode binaryLengthOddOuterBody).length

def binaryLengthRuleFormulaStageOne (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope binaryLengthRuleFormulaSeed termBound

def binaryLengthRuleFormulaStageTwo (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    (binaryLengthRuleFormulaStageOne termBound) termBound

theorem binaryLengthEvenOuterBody_code_le_seed :
    (binaryFormulaCode binaryLengthEvenOuterBody).length <=
      binaryLengthRuleFormulaSeed := by
  exact Nat.le_max_left _ _

theorem binaryLengthOddOuterBody_code_le_seed :
    (binaryFormulaCode binaryLengthOddOuterBody).length <=
      binaryLengthRuleFormulaSeed := by
  exact Nat.le_max_right _ _

theorem binaryLengthEvenInnerBody_code_le_stageOne
    (size : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hsize : (binaryTermCode size).length <= termBound) :
    (binaryFormulaCode
      (binaryLengthEvenInnerBody size)).length <=
        binaryLengthRuleFormulaStageOne termBound := by
  exact instantiatedBodyCode_le_nextStage
    binaryLengthEvenOuterBody
    (binaryLengthEvenInnerBody size)
    size binaryLengthRuleFormulaSeed termBound
    binaryLengthEvenOuterBody_code_le_seed hsize
    (binaryLengthEvenAfterFirst_formula size)

theorem binaryLengthOddInnerBody_code_le_stageOne
    (size : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hsize : (binaryTermCode size).length <= termBound) :
    (binaryFormulaCode
      (binaryLengthOddInnerBody size)).length <=
        binaryLengthRuleFormulaStageOne termBound := by
  exact instantiatedBodyCode_le_nextStage
    binaryLengthOddOuterBody
    (binaryLengthOddInnerBody size)
    size binaryLengthRuleFormulaSeed termBound
    binaryLengthOddOuterBody_code_le_seed hsize
    (binaryLengthOddAfterFirst_formula size)

theorem binaryLengthEvenFormula_code_le_stageTwo
    (size value : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hsize : (binaryTermCode size).length <= termBound)
    (hvalue : (binaryTermCode value).length <= termBound) :
    (binaryFormulaCode
      (“0 < !!value →
        !lengthDef !!size !!value →
        !lengthDef (!!size + 1) (2 * !!value)” :
        LO.FirstOrder.ArithmeticProposition)).length <=
      binaryLengthRuleFormulaStageTwo termBound := by
  have hinner :=
    binaryLengthEvenInnerBody_code_le_stageOne
      size termBound hsize
  have hsubstitution :=
    binaryFormulaCode_substitution_one_length_le_envelope
      (binaryLengthEvenInnerBody size) value
      (binaryLengthRuleFormulaStageOne termBound)
      termBound hinner hvalue
  rw [binaryLengthEvenFinal_formula size value] at hsubstitution
  exact hsubstitution

theorem binaryLengthOddFormula_code_le_stageTwo
    (size value : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hsize : (binaryTermCode size).length <= termBound)
    (hvalue : (binaryTermCode value).length <= termBound) :
    (binaryFormulaCode
      (“!lengthDef !!size !!value →
        !lengthDef (!!size + 1) (2 * !!value + 1)” :
        LO.FirstOrder.ArithmeticProposition)).length <=
      binaryLengthRuleFormulaStageTwo termBound := by
  have hinner :=
    binaryLengthOddInnerBody_code_le_stageOne
      size termBound hsize
  have hsubstitution :=
    binaryFormulaCode_substitution_one_length_le_envelope
      (binaryLengthOddInnerBody size) value
      (binaryLengthRuleFormulaStageOne termBound)
      termBound hinner hvalue
  rw [binaryLengthOddFinal_formula size value] at hsubstitution
  exact hsubstitution

def binaryLengthEvenImplicationPayloadEnvelope
    (termBound : Nat) : Nat :=
  binaryLengthEvenUniversalProof.payloadLength +
    exponentialSpecializationCostEnvelope
      binaryLengthRuleFormulaSeed termBound +
    exponentialSpecializationCostEnvelope
      (binaryLengthRuleFormulaStageOne termBound) termBound

def binaryLengthOddImplicationPayloadEnvelope
    (termBound : Nat) : Nat :=
  binaryLengthOddUniversalProof.payloadLength +
    exponentialSpecializationCostEnvelope
      binaryLengthRuleFormulaSeed termBound +
    exponentialSpecializationCostEnvelope
      (binaryLengthRuleFormulaStageOne termBound) termBound

theorem binaryLengthEvenImplication_payloadLength_le_envelope
    (size value : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hsize : (binaryTermCode size).length <= termBound)
    (hvalue : (binaryTermCode value).length <= termBound) :
    (binaryLengthEvenImplication size value).payloadLength <=
      binaryLengthEvenImplicationPayloadEnvelope termBound := by
  have hinner :=
    binaryLengthEvenInnerBody_code_le_stageOne
      size termBound hsize
  have hfirstCost := specializationCost_le_exponentialEnvelope
    binaryLengthEvenOuterBody size
    binaryLengthRuleFormulaSeed termBound
    binaryLengthEvenOuterBody_code_le_seed hsize
  have hsecondCost := specializationCost_le_exponentialEnvelope
    (binaryLengthEvenInnerBody size) value
    (binaryLengthRuleFormulaStageOne termBound) termBound
    hinner hvalue
  have hraw := specializeTwiceWithCasts_payloadLength_le
    binaryLengthEvenUniversalProof size value
    (binaryLengthEvenAfterFirst_formula size)
    (binaryLengthEvenFinal_formula size value)
  change
    (specializeTwiceWithCasts
      binaryLengthEvenUniversalProof size value
      (binaryLengthEvenAfterFirst_formula size)
      (binaryLengthEvenFinal_formula size value)).payloadLength <= _
  unfold binaryLengthEvenImplicationPayloadEnvelope
  omega

theorem binaryLengthOddImplication_payloadLength_le_envelope
    (size value : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hsize : (binaryTermCode size).length <= termBound)
    (hvalue : (binaryTermCode value).length <= termBound) :
    (binaryLengthOddImplication size value).payloadLength <=
      binaryLengthOddImplicationPayloadEnvelope termBound := by
  have hinner :=
    binaryLengthOddInnerBody_code_le_stageOne
      size termBound hsize
  have hfirstCost := specializationCost_le_exponentialEnvelope
    binaryLengthOddOuterBody size
    binaryLengthRuleFormulaSeed termBound
    binaryLengthOddOuterBody_code_le_seed hsize
  have hsecondCost := specializationCost_le_exponentialEnvelope
    (binaryLengthOddInnerBody size) value
    (binaryLengthRuleFormulaStageOne termBound) termBound
    hinner hvalue
  have hraw := specializeTwiceWithCasts_payloadLength_le
    binaryLengthOddUniversalProof size value
    (binaryLengthOddAfterFirst_formula size)
    (binaryLengthOddFinal_formula size value)
  change
    (specializeTwiceWithCasts
      binaryLengthOddUniversalProof size value
      (binaryLengthOddAfterFirst_formula size)
      (binaryLengthOddFinal_formula size value)).payloadLength <= _
  unfold binaryLengthOddImplicationPayloadEnvelope
  omega

/-! ## Width-indexed positivity and modus-ponens ledgers -/

def binaryLengthPositivePayloadAtWidth (width : Nat) : Nat :=
  let nodeBudget := 3
  let bitWidth := width + 2
  let termBound := compilerTermCodeEnvelope nodeBudget bitWidth
  8 * compilerLocalCostEnvelope nodeBudget bitWidth +
    positiveBinaryNumeralPayloadPolynomial bitWidth +
    orderStepCostEnvelope bitWidth +
    2 * paPrimitiveCostEnvelope termBound +
    2 * orderPrimitiveCostEnvelope termBound

theorem positiveLessThanPayloadPolynomial_numeral_zero_eq_width
    (value : Nat) :
    positiveLessThanPayloadPolynomial
        (.numeral 0) (.numeral value) =
      binaryLengthPositivePayloadAtWidth (Nat.size value) := by
  simp [positiveLessThanPayloadPolynomial,
    positiveLessThanNodeBudget, positiveLessThanBitWidth,
    ClosedPATerm.nodeCount, ClosedPATerm.leafBitWeight,
    binaryLengthPositivePayloadAtWidth]
  rw [show 1 + (Nat.size value + 1) = Nat.size value + 2 by omega]
  omega

def binaryLengthPositivePayloadCumulative (width : Nat) : Nat :=
  ∑ candidate ∈ Finset.range (width + 1),
    binaryLengthPositivePayloadAtWidth candidate

theorem binaryLengthPositivePayloadAtWidth_le_cumulative
    {candidate width : Nat} (hwidth : candidate <= width) :
    binaryLengthPositivePayloadAtWidth candidate <=
      binaryLengthPositivePayloadCumulative width := by
  have hmem : candidate ∈ Finset.range (width + 1) := by
    simp
    omega
  unfold binaryLengthPositivePayloadCumulative
  exact Finset.single_le_sum
    (f := binaryLengthPositivePayloadAtWidth)
    (s := Finset.range (width + 1))
    (fun index _ => Nat.zero_le
      (binaryLengthPositivePayloadAtWidth index))
    hmem

theorem provePositiveLessThan_zero_numeral_payloadLength_le_cumulative
    (value width : Nat) (hwidth : Nat.size value <= width)
    (hpositive : 0 < value) :
    (provePositiveLessThan
        (.numeral 0) (.numeral value) hpositive).payloadLength <=
      binaryLengthPositivePayloadCumulative width := by
  have hlocal :=
    provePositiveLessThan_payloadLength_le_polynomial
      (.numeral 0) (.numeral value) hpositive
  rw [positiveLessThanPayloadPolynomial_numeral_zero_eq_width] at hlocal
  exact hlocal.trans
    (binaryLengthPositivePayloadAtWidth_le_cumulative hwidth)

def binaryLengthMPFormulaEnvelope (termBound : Nat) : Nat :=
  2 * binaryLengthRuleFormulaStageTwo termBound

def binaryLengthMPPayloadEnvelope (termBound : Nat) : Nat :=
  240 + 34 * paAssemblySyntaxEnvelope
    (binaryLengthMPFormulaEnvelope termBound)

theorem implicationAntecedent_code_le_binaryLengthMPEnvelope
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (termBound : Nat)
    (himplication :
      (binaryFormulaCode (antecedent 🡒 consequent)).length <=
        binaryLengthRuleFormulaStageTwo termBound) :
    (binaryFormulaCode antecedent).length <=
      binaryLengthMPFormulaEnvelope termBound := by
  have hantecedent :=
    binaryFormulaCode_antecedent_le_implication antecedent consequent
  unfold binaryLengthMPFormulaEnvelope
  exact hantecedent.trans (Nat.mul_le_mul_left 2 himplication)

theorem implicationConsequent_code_le_binaryLengthMPEnvelope
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (termBound : Nat)
    (himplication :
      (binaryFormulaCode (antecedent 🡒 consequent)).length <=
        binaryLengthRuleFormulaStageTwo termBound) :
    (binaryFormulaCode consequent).length <=
      binaryLengthMPFormulaEnvelope termBound := by
  have hconsequent :=
    (binaryFormulaCode_consequent_le_implication
      antecedent consequent).trans himplication
  unfold binaryLengthMPFormulaEnvelope
  omega

def binaryLengthRecursiveStepPayloadEnvelope (width : Nat) : Nat :=
  let termBound := binaryLengthTermCodeEnvelope width
  binaryLengthEvenImplicationPayloadEnvelope termBound +
    binaryLengthOddImplicationPayloadEnvelope termBound +
    binaryLengthPositivePayloadCumulative width +
    2 * binaryLengthMPPayloadEnvelope termBound

theorem binaryLengthBitStep_payloadLength_le
    (bit : Bool) (value : Nat)
    (hcanonical : value = 0 → bit = true)
    (previous : CertifiedPAProof (binaryLengthRecursiveFormula value)) :
    (binaryLengthBitStep bit value hcanonical previous).payloadLength <=
      previous.payloadLength +
        binaryLengthRecursiveStepPayloadEnvelope
          (Nat.size (Nat.bit bit value)) := by
  have hnonzero : Nat.bit bit value ≠ 0 :=
    Nat.bit_ne_zero_iff.mpr hcanonical
  have hwidth :
      Nat.size (Nat.bit bit value) = Nat.size value + 1 :=
    Nat.size_bit hnonzero
  let currentWidth := Nat.size (Nat.bit bit value)
  let sizeTerm := exponentialExponentTerm (Nat.size value)
  let valueTerm := shortBinaryNumeralTerm value
  let termBound := binaryLengthTermCodeEnvelope currentWidth
  let formulaBound := binaryLengthMPFormulaEnvelope termBound
  let mpCost := binaryLengthMPPayloadEnvelope termBound
  have hsizeTerm :
      (binaryTermCode sizeTerm).length <= termBound := by
    dsimp only [sizeTerm, termBound, binaryLengthTermCodeEnvelope]
    exact exponentialExponentTerm_code_le_shortEnvelope
      (Nat.size value) currentWidth (by omega)
  have hvalueTerm :
      (binaryTermCode valueTerm).length <= termBound := by
    dsimp only [valueTerm, termBound, binaryLengthTermCodeEnvelope]
    exact shortBinaryNumeralTerm_code_le_shortEnvelope
      value currentWidth (by omega)
  have hmpCost :
      mpCost =
        240 + 34 * paAssemblySyntaxEnvelope formulaBound := by
    rfl
  cases bit with
  | false =>
      have hvalueNonzero : value ≠ 0 := by
        intro hzero
        have himpossible := hcanonical hzero
        simp at himpossible
      have hpositive : 0 < value :=
        Nat.pos_of_ne_zero hvalueNonzero
      let positivity := binaryLengthPositivityProof value hpositive
      let implication :=
        binaryLengthEvenImplication sizeTerm valueTerm
      let recursiveFact : CertifiedPAProof
          (“!lengthDef !!sizeTerm !!valueTerm” :
            LO.FirstOrder.ArithmeticProposition) :=
        previous
      let afterPositive :=
        CertifiedPAProof.modusPonens implication positivity
      have himplicationCode :=
        binaryLengthEvenFormula_code_le_stageTwo
          sizeTerm valueTerm termBound hsizeTerm hvalueTerm
      have hpositiveCode :=
        implicationAntecedent_code_le_binaryLengthMPEnvelope
          (“0 < !!valueTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!lengthDef !!sizeTerm !!valueTerm →
            !lengthDef (!!sizeTerm + 1) (2 * !!valueTerm)” :
            LO.FirstOrder.ArithmeticProposition)
          termBound himplicationCode
      have hremainingCodeStrong :=
        (binaryFormulaCode_consequent_le_implication
          (“0 < !!valueTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!lengthDef !!sizeTerm !!valueTerm →
            !lengthDef (!!sizeTerm + 1) (2 * !!valueTerm)” :
            LO.FirstOrder.ArithmeticProposition)).trans
          himplicationCode
      have hremainingCode :=
        implicationConsequent_code_le_binaryLengthMPEnvelope
          (“0 < !!valueTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!lengthDef !!sizeTerm !!valueTerm →
            !lengthDef (!!sizeTerm + 1) (2 * !!valueTerm)” :
            LO.FirstOrder.ArithmeticProposition)
          termBound himplicationCode
      have hpreviousCode :=
        implicationAntecedent_code_le_binaryLengthMPEnvelope
          (“!lengthDef !!sizeTerm !!valueTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!lengthDef (!!sizeTerm + 1) (2 * !!valueTerm)” :
            LO.FirstOrder.ArithmeticProposition)
          termBound hremainingCodeStrong
      have hnextCode :=
        implicationConsequent_code_le_binaryLengthMPEnvelope
          (“!lengthDef !!sizeTerm !!valueTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!lengthDef (!!sizeTerm + 1) (2 * !!valueTerm)” :
            LO.FirstOrder.ArithmeticProposition)
          termBound hremainingCodeStrong
      have hsyntaxFirst :=
        modusPonensSyntaxBudget_le_paAssemblyEnvelope
          (“0 < !!valueTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!lengthDef !!sizeTerm !!valueTerm →
            !lengthDef (!!sizeTerm + 1) (2 * !!valueTerm)” :
            LO.FirstOrder.ArithmeticProposition)
          formulaBound hpositiveCode hremainingCode
      have hsyntaxSecond :=
        modusPonensSyntaxBudget_le_paAssemblyEnvelope
          (“!lengthDef !!sizeTerm !!valueTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!lengthDef (!!sizeTerm + 1) (2 * !!valueTerm)” :
            LO.FirstOrder.ArithmeticProposition)
          formulaBound hpreviousCode hnextCode
      have himplicationPayload :
          implication.payloadLength <=
            binaryLengthEvenImplicationPayloadEnvelope termBound := by
        dsimp only [implication]
        exact
          binaryLengthEvenImplication_payloadLength_le_envelope
            sizeTerm valueTerm termBound hsizeTerm hvalueTerm
      have hpositivityPayload :
          positivity.payloadLength <=
            binaryLengthPositivePayloadCumulative currentWidth := by
        dsimp only [positivity, binaryLengthPositivityProof]
        simp only [CertifiedPAProof.cast_payloadLength]
        exact
          provePositiveLessThan_zero_numeral_payloadLength_le_cumulative
            value currentWidth (by omega) hpositive
      have hfirstRaw :=
        CertifiedPAProof.modusPonens_payloadLength_le
          implication positivity
      have hfirst :
          afterPositive.payloadLength <=
            binaryLengthEvenImplicationPayloadEnvelope termBound +
              binaryLengthPositivePayloadCumulative currentWidth +
              mpCost := by
        dsimp only [afterPositive]
        rw [hmpCost]
        omega
      have hsecondRaw :=
        CertifiedPAProof.modusPonens_payloadLength_le
          afterPositive recursiveFact
      dsimp only [afterPositive] at hfirst hsecondRaw
      have hresult :
          (CertifiedPAProof.modusPonens
            (CertifiedPAProof.modusPonens implication positivity)
            recursiveFact).payloadLength <=
              recursiveFact.payloadLength +
                (binaryLengthEvenImplicationPayloadEnvelope termBound +
                  binaryLengthOddImplicationPayloadEnvelope termBound +
                  binaryLengthPositivePayloadCumulative currentWidth +
                  2 * mpCost) := by
        omega
      have hrecursivePayload :
          recursiveFact.payloadLength = previous.payloadLength := by
        rfl
      rw [hrecursivePayload] at hresult
      unfold binaryLengthBitStep
      simp only [CertifiedPAProof.cast_payloadLength]
      change
        (CertifiedPAProof.modusPonens
          (CertifiedPAProof.modusPonens implication positivity)
          recursiveFact).payloadLength <= _
      unfold binaryLengthRecursiveStepPayloadEnvelope
      change
        (CertifiedPAProof.modusPonens
          (CertifiedPAProof.modusPonens implication positivity)
          previous).payloadLength <=
            previous.payloadLength +
              (binaryLengthEvenImplicationPayloadEnvelope termBound +
                binaryLengthOddImplicationPayloadEnvelope termBound +
                binaryLengthPositivePayloadCumulative currentWidth +
                2 * mpCost)
      exact hresult
  | true =>
      let implication :=
        binaryLengthOddImplication sizeTerm valueTerm
      let recursiveFact : CertifiedPAProof
          (“!lengthDef !!sizeTerm !!valueTerm” :
            LO.FirstOrder.ArithmeticProposition) :=
        previous
      have himplicationCode :=
        binaryLengthOddFormula_code_le_stageTwo
          sizeTerm valueTerm termBound hsizeTerm hvalueTerm
      have hpreviousCode :=
        implicationAntecedent_code_le_binaryLengthMPEnvelope
          (“!lengthDef !!sizeTerm !!valueTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!lengthDef (!!sizeTerm + 1) (2 * !!valueTerm + 1)” :
            LO.FirstOrder.ArithmeticProposition)
          termBound himplicationCode
      have hnextCode :=
        implicationConsequent_code_le_binaryLengthMPEnvelope
          (“!lengthDef !!sizeTerm !!valueTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!lengthDef (!!sizeTerm + 1) (2 * !!valueTerm + 1)” :
            LO.FirstOrder.ArithmeticProposition)
          termBound himplicationCode
      have hsyntax :=
        modusPonensSyntaxBudget_le_paAssemblyEnvelope
          (“!lengthDef !!sizeTerm !!valueTerm” :
            LO.FirstOrder.ArithmeticProposition)
          (“!lengthDef (!!sizeTerm + 1) (2 * !!valueTerm + 1)” :
            LO.FirstOrder.ArithmeticProposition)
          formulaBound hpreviousCode hnextCode
      have himplicationPayload :
          implication.payloadLength <=
            binaryLengthOddImplicationPayloadEnvelope termBound := by
        dsimp only [implication]
        exact
          binaryLengthOddImplication_payloadLength_le_envelope
            sizeTerm valueTerm termBound hsizeTerm hvalueTerm
      have hraw :=
        CertifiedPAProof.modusPonens_payloadLength_le
          implication recursiveFact
      have hresult :
          (CertifiedPAProof.modusPonens
            implication recursiveFact).payloadLength <=
              recursiveFact.payloadLength +
                (binaryLengthEvenImplicationPayloadEnvelope termBound +
                  binaryLengthOddImplicationPayloadEnvelope termBound +
                  binaryLengthPositivePayloadCumulative currentWidth +
                  2 * mpCost) := by
        omega
      have hrecursivePayload :
          recursiveFact.payloadLength = previous.payloadLength := by
        rfl
      rw [hrecursivePayload] at hresult
      unfold binaryLengthBitStep
      simp only [CertifiedPAProof.cast_payloadLength]
      change
        (CertifiedPAProof.modusPonens
          implication recursiveFact).payloadLength <= _
      unfold binaryLengthRecursiveStepPayloadEnvelope
      change
        (CertifiedPAProof.modusPonens
          implication previous).payloadLength <=
            previous.payloadLength +
              (binaryLengthEvenImplicationPayloadEnvelope termBound +
                binaryLengthOddImplicationPayloadEnvelope termBound +
                binaryLengthPositivePayloadCumulative currentWidth +
                2 * mpCost)
      exact hresult

def binaryLengthRecursiveStepPayloadCumulative (width : Nat) : Nat :=
  ∑ candidate ∈ Finset.range (width + 1),
    binaryLengthRecursiveStepPayloadEnvelope candidate

theorem binaryLengthRecursiveStepPayloadEnvelope_le_cumulative
    {candidate width : Nat} (hwidth : candidate <= width) :
    binaryLengthRecursiveStepPayloadEnvelope candidate <=
      binaryLengthRecursiveStepPayloadCumulative width := by
  have hmem : candidate ∈ Finset.range (width + 1) := by
    simp
    omega
  unfold binaryLengthRecursiveStepPayloadCumulative
  exact Finset.single_le_sum
    (f := binaryLengthRecursiveStepPayloadEnvelope)
    (s := Finset.range (width + 1))
    (fun index _ => Nat.zero_le
      (binaryLengthRecursiveStepPayloadEnvelope index))
    hmem

theorem binaryLengthRecursiveStepPayloadCumulative_mono
    {small large : Nat} (hwidth : small <= large) :
    binaryLengthRecursiveStepPayloadCumulative small <=
      binaryLengthRecursiveStepPayloadCumulative large := by
  have hrange :
      Finset.range (small + 1) ⊆ Finset.range (large + 1) := by
    intro candidate hcandidate
    simp only [Finset.mem_range] at hcandidate ⊢
    omega
  unfold binaryLengthRecursiveStepPayloadCumulative
  exact Finset.sum_le_sum_of_subset hrange

def binaryLengthRecursivePayloadPolynomial (width : Nat) : Nat :=
  binaryLengthZeroRecursiveProof.payloadLength +
    width * binaryLengthRecursiveStepPayloadCumulative width

theorem binaryLengthRecursivePayloadStep_arithmetic
    {base sourceWidth currentWidth sourcePayload currentPayload
      currentStep currentCumulative : Nat}
    (hwidth : currentWidth = sourceWidth + 1)
    (hstep : currentPayload <= sourcePayload + currentStep)
    (hrecursive :
      sourcePayload <= base + sourceWidth * currentCumulative)
    (hcomponent : currentStep <= currentCumulative) :
    currentPayload <= base + currentWidth * currentCumulative := by
  rw [hwidth]
  calc
    currentPayload <= sourcePayload + currentStep := hstep
    _ <= (base + sourceWidth * currentCumulative) +
        currentCumulative :=
      Nat.add_le_add hrecursive hcomponent
    _ = base + (sourceWidth + 1) * currentCumulative := by ring

structure PolynomiallyBoundedBinaryLengthRecursiveProof
    (value : Nat) where
  proof : CertifiedPAProof (binaryLengthRecursiveFormula value)
  payload_le :
    proof.payloadLength <=
      binaryLengthRecursivePayloadPolynomial (Nat.size value)

theorem binaryLengthZeroRecursiveProof_payloadLength_le_polynomial
    (width : Nat) :
    binaryLengthZeroRecursiveProof.payloadLength <=
      binaryLengthRecursivePayloadPolynomial width := by
  unfold binaryLengthRecursivePayloadPolynomial
  exact Nat.le_add_right _ _

noncomputable def boundedBinaryLengthRecursiveProofZero :
    PolynomiallyBoundedBinaryLengthRecursiveProof 0 where
  proof := binaryLengthZeroRecursiveProof
  payload_le :=
    binaryLengthZeroRecursiveProof_payloadLength_le_polynomial
      (Nat.size 0)

theorem binaryLengthPayloadStep_le_polynomial
    (bit : Bool) (value sourcePayload currentPayload : Nat)
    (hwidth :
      Nat.size (Nat.bit bit value) = Nat.size value + 1)
    (hstep :
      currentPayload <= sourcePayload +
        binaryLengthRecursiveStepPayloadEnvelope
          (Nat.size (Nat.bit bit value)))
    (hprevious :
      sourcePayload <=
        binaryLengthRecursivePayloadPolynomial (Nat.size value)) :
    currentPayload <=
      binaryLengthRecursivePayloadPolynomial
        (Nat.size (Nat.bit bit value)) := by
  have hsourceWidth :
      Nat.size value <= Nat.size (Nat.bit bit value) := by
    omega
  have hcumulative :=
    binaryLengthRecursiveStepPayloadCumulative_mono hsourceWidth
  have hprevious' := hprevious
  unfold binaryLengthRecursivePayloadPolynomial at hprevious'
  have hrecursive :
      sourcePayload <=
        binaryLengthZeroRecursiveProof.payloadLength +
          Nat.size value *
            binaryLengthRecursiveStepPayloadCumulative
              (Nat.size (Nat.bit bit value)) := by
    exact hprevious'.trans <| Nat.add_le_add_left
      (Nat.mul_le_mul_left (Nat.size value) hcumulative)
      binaryLengthZeroRecursiveProof.payloadLength
  have hcomponent :=
    binaryLengthRecursiveStepPayloadEnvelope_le_cumulative
      (candidate := Nat.size (Nat.bit bit value))
      (width := Nat.size (Nat.bit bit value))
      le_rfl
  unfold binaryLengthRecursivePayloadPolynomial
  exact binaryLengthRecursivePayloadStep_arithmetic
    hwidth hstep hrecursive hcomponent

noncomputable def boundedBinaryLengthRecursiveProofBitStep
    (bit : Bool) (value : Nat)
    (hcanonical : value = 0 → bit = true)
    (previous :
      PolynomiallyBoundedBinaryLengthRecursiveProof value) :
    PolynomiallyBoundedBinaryLengthRecursiveProof
      (Nat.bit bit value) where
  proof := binaryLengthBitStep
    bit value hcanonical previous.proof
  payload_le := by
    have hnonzero : Nat.bit bit value ≠ 0 :=
      Nat.bit_ne_zero_iff.mpr hcanonical
    have hwidth :
        Nat.size (Nat.bit bit value) = Nat.size value + 1 :=
      Nat.size_bit hnonzero
    exact binaryLengthPayloadStep_le_polynomial
      bit value previous.proof.payloadLength
      (binaryLengthBitStep
        bit value hcanonical previous.proof).payloadLength
      hwidth
      (binaryLengthBitStep_payloadLength_le
        bit value hcanonical previous.proof)
      previous.payload_le

noncomputable def boundedBinaryLengthRecursiveProof :
    (value : Nat) →
      PolynomiallyBoundedBinaryLengthRecursiveProof value :=
  Nat.binaryRec'
    boundedBinaryLengthRecursiveProofZero
    boundedBinaryLengthRecursiveProofBitStep

noncomputable def proveBinaryLengthAtRecursiveSizePolynomial
    (value : Nat) :
    CertifiedPAProof (binaryLengthRecursiveFormula value) :=
  (boundedBinaryLengthRecursiveProof value).proof

theorem proveBinaryLengthAtRecursiveSizePolynomial_payloadLength_le
    (value : Nat) :
    (proveBinaryLengthAtRecursiveSizePolynomial value).payloadLength <=
      binaryLengthRecursivePayloadPolynomial (Nat.size value) := by
  exact (boundedBinaryLengthRecursiveProof value).payload_le

theorem proveBinaryLengthAtRecursiveSizePolynomial_verifier_eq_true
    (value : Nat) :
    listedCompactCertifiedPAProofVerifier
        (proveBinaryLengthAtRecursiveSizePolynomial value).code
        (compactFormulaCode
          (binaryLengthRecursiveFormula value)) = true :=
  (proveBinaryLengthAtRecursiveSizePolynomial value).verifier_eq_true

/-! ## Transport from the recursive size term to the exact short numeral -/

def binaryLengthTransportFormulaSeed : Nat :=
  (binaryFormulaCode binaryLengthSizeTransportOuterBody).length

def binaryLengthTransportFormulaStageOne (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    binaryLengthTransportFormulaSeed termBound

def binaryLengthTransportFormulaStageTwo (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    (binaryLengthTransportFormulaStageOne termBound) termBound

def binaryLengthTransportFormulaStageThree (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    (binaryLengthTransportFormulaStageTwo termBound) termBound

theorem binaryLengthSizeTransportOuterBody_code_le_seed :
    (binaryFormulaCode binaryLengthSizeTransportOuterBody).length <=
      binaryLengthTransportFormulaSeed := by
  exact le_rfl

theorem binaryLengthSizeTransportMiddleBody_code_le_stageOne
    (leftSize : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode leftSize).length <= termBound) :
    (binaryFormulaCode
      (binaryLengthSizeTransportMiddleBody leftSize)).length <=
        binaryLengthTransportFormulaStageOne termBound := by
  exact instantiatedBodyCode_le_nextStage
    binaryLengthSizeTransportOuterBody
    (binaryLengthSizeTransportMiddleBody leftSize)
    leftSize binaryLengthTransportFormulaSeed termBound
    binaryLengthSizeTransportOuterBody_code_le_seed hleft
    (binaryLengthSizeTransportAfterFirst_formula leftSize)

theorem binaryLengthSizeTransportInnerBody_code_le_stageTwo
    (leftSize rightSize :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode leftSize).length <= termBound)
    (hright : (binaryTermCode rightSize).length <= termBound) :
    (binaryFormulaCode
      (binaryLengthSizeTransportInnerBody
        leftSize rightSize)).length <=
          binaryLengthTransportFormulaStageTwo termBound := by
  exact instantiatedBodyCode_le_nextStage
    (binaryLengthSizeTransportMiddleBody leftSize)
    (binaryLengthSizeTransportInnerBody leftSize rightSize)
    rightSize
    (binaryLengthTransportFormulaStageOne termBound) termBound
    (binaryLengthSizeTransportMiddleBody_code_le_stageOne
      leftSize termBound hleft)
    hright
    (binaryLengthSizeTransportAfterSecond_formula
      leftSize rightSize)

theorem binaryLengthSizeTransportFormula_code_le_stageThree
    (leftSize rightSize value :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode leftSize).length <= termBound)
    (hright : (binaryTermCode rightSize).length <= termBound)
    (hvalue : (binaryTermCode value).length <= termBound) :
    (binaryFormulaCode
      (“!!leftSize = !!rightSize →
        (!lengthDef !!leftSize !!value →
          !lengthDef !!rightSize !!value)” :
        LO.FirstOrder.ArithmeticProposition)).length <=
      binaryLengthTransportFormulaStageThree termBound := by
  have hinner :=
    binaryLengthSizeTransportInnerBody_code_le_stageTwo
      leftSize rightSize termBound hleft hright
  have hsubstitution :=
    binaryFormulaCode_substitution_one_length_le_envelope
      (binaryLengthSizeTransportInnerBody leftSize rightSize)
      value
      (binaryLengthTransportFormulaStageTwo termBound)
      termBound hinner hvalue
  rw [binaryLengthSizeTransportFinal_formula
    leftSize rightSize value] at hsubstitution
  exact hsubstitution

def binaryLengthTransportPayloadEnvelope
    (termBound : Nat) : Nat :=
  binaryLengthSizeTransportUniversalProof.payloadLength +
    exponentialSpecializationCostEnvelope
      binaryLengthTransportFormulaSeed termBound +
    exponentialSpecializationCostEnvelope
      (binaryLengthTransportFormulaStageOne termBound) termBound +
    exponentialSpecializationCostEnvelope
      (binaryLengthTransportFormulaStageTwo termBound) termBound

theorem binaryLengthSizeTransportImplication_payloadLength_le_envelope
    (leftSize rightSize value :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode leftSize).length <= termBound)
    (hright : (binaryTermCode rightSize).length <= termBound)
    (hvalue : (binaryTermCode value).length <= termBound) :
    (binaryLengthSizeTransportImplication
      leftSize rightSize value).payloadLength <=
        binaryLengthTransportPayloadEnvelope termBound := by
  have hmiddle :=
    binaryLengthSizeTransportMiddleBody_code_le_stageOne
      leftSize termBound hleft
  have hinner :=
    binaryLengthSizeTransportInnerBody_code_le_stageTwo
      leftSize rightSize termBound hleft hright
  have hfirstCost := specializationCost_le_exponentialEnvelope
    binaryLengthSizeTransportOuterBody leftSize
    binaryLengthTransportFormulaSeed termBound
    binaryLengthSizeTransportOuterBody_code_le_seed hleft
  have hsecondCost := specializationCost_le_exponentialEnvelope
    (binaryLengthSizeTransportMiddleBody leftSize) rightSize
    (binaryLengthTransportFormulaStageOne termBound) termBound
    hmiddle hright
  have hthirdCost := specializationCost_le_exponentialEnvelope
    (binaryLengthSizeTransportInnerBody leftSize rightSize) value
    (binaryLengthTransportFormulaStageTwo termBound) termBound
    hinner hvalue
  have hraw := specializeThriceWithCasts_payloadLength_le
    binaryLengthSizeTransportUniversalProof
    leftSize rightSize value
    (binaryLengthSizeTransportAfterFirst_formula leftSize)
    (binaryLengthSizeTransportAfterSecond_formula
      leftSize rightSize)
    (binaryLengthSizeTransportFinal_formula
      leftSize rightSize value)
  change
    (specializeThriceWithCasts
      binaryLengthSizeTransportUniversalProof
      leftSize rightSize value
      (binaryLengthSizeTransportAfterFirst_formula leftSize)
      (binaryLengthSizeTransportAfterSecond_formula
        leftSize rightSize)
      (binaryLengthSizeTransportFinal_formula
        leftSize rightSize value)).payloadLength <= _
  unfold binaryLengthTransportPayloadEnvelope
  omega

def binaryLengthTransportMPFormulaEnvelope
    (termBound : Nat) : Nat :=
  2 * binaryLengthTransportFormulaStageThree termBound

def binaryLengthTransportMPPayloadEnvelope
    (termBound : Nat) : Nat :=
  240 + 34 * paAssemblySyntaxEnvelope
    (binaryLengthTransportMPFormulaEnvelope termBound)

theorem implicationAntecedent_code_le_binaryLengthTransportMPEnvelope
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (termBound : Nat)
    (himplication :
      (binaryFormulaCode (antecedent 🡒 consequent)).length <=
        binaryLengthTransportFormulaStageThree termBound) :
    (binaryFormulaCode antecedent).length <=
      binaryLengthTransportMPFormulaEnvelope termBound := by
  have hantecedent :=
    binaryFormulaCode_antecedent_le_implication antecedent consequent
  unfold binaryLengthTransportMPFormulaEnvelope
  exact hantecedent.trans (Nat.mul_le_mul_left 2 himplication)

theorem implicationConsequent_code_le_binaryLengthTransportMPEnvelope
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (termBound : Nat)
    (himplication :
      (binaryFormulaCode (antecedent 🡒 consequent)).length <=
        binaryLengthTransportFormulaStageThree termBound) :
    (binaryFormulaCode consequent).length <=
      binaryLengthTransportMPFormulaEnvelope termBound := by
  have hconsequent :=
    (binaryFormulaCode_consequent_le_implication
      antecedent consequent).trans himplication
  unfold binaryLengthTransportMPFormulaEnvelope
  omega

noncomputable def proveBinaryLengthAtShortNumeralsPolynomial
    (value : Nat) :
    CertifiedPAProof (binaryLengthShortNumeralFormula value) := by
  let recursiveSize := exponentialExponentTerm (Nat.size value)
  let shortSize := shortBinaryNumeralTerm (Nat.size value)
  let valueTerm := shortBinaryNumeralTerm value
  let transportAfterEquality :=
    CertifiedPAProof.modusPonens
      (binaryLengthSizeTransportImplication
        recursiveSize shortSize valueTerm)
      (exponentialExponentRecursiveToShortProof
        (Nat.size value))
  let result :=
    CertifiedPAProof.modusPonens transportAfterEquality
      (proveBinaryLengthAtRecursiveSizePolynomial value)
  exact result

def binaryLengthAtShortNumeralsPayloadPolynomial
    (width : Nat) : Nat :=
  let termBound := binaryLengthTermCodeEnvelope width
  binaryLengthTransportPayloadEnvelope termBound +
    exponentialExponentRecursiveToShortPayloadPolynomial width +
    binaryLengthRecursivePayloadPolynomial width +
    2 * binaryLengthTransportMPPayloadEnvelope termBound

theorem proveBinaryLengthAtShortNumeralsPolynomial_payloadLength_le
    (value : Nat) :
    (proveBinaryLengthAtShortNumeralsPolynomial value).payloadLength <=
      binaryLengthAtShortNumeralsPayloadPolynomial
        (Nat.size value) := by
  let width := Nat.size value
  let recursiveSize := exponentialExponentTerm width
  let shortSize := shortBinaryNumeralTerm width
  let valueTerm := shortBinaryNumeralTerm value
  let termBound := binaryLengthTermCodeEnvelope width
  let formulaBound :=
    binaryLengthTransportMPFormulaEnvelope termBound
  let mpCost := binaryLengthTransportMPPayloadEnvelope termBound
  have hrecursiveSize :
      (binaryTermCode recursiveSize).length <= termBound := by
    dsimp only [recursiveSize, termBound,
      binaryLengthTermCodeEnvelope]
    exact exponentialExponentTerm_code_le_shortEnvelope
      width width le_rfl
  have hwidthSize : Nat.size width <= width + 1 := by
    exact (nat_size_le_self_short width).trans (by omega)
  have hshortSize :
      (binaryTermCode shortSize).length <= termBound := by
    dsimp only [shortSize, termBound,
      binaryLengthTermCodeEnvelope]
    exact shortBinaryNumeralTerm_code_le_shortEnvelope
      width width hwidthSize
  have hvalueTerm :
      (binaryTermCode valueTerm).length <= termBound := by
    dsimp only [valueTerm, termBound,
      binaryLengthTermCodeEnvelope, width]
    exact shortBinaryNumeralTerm_code_le_shortEnvelope
      value (Nat.size value) (by omega)
  have htransportCode :=
    binaryLengthSizeTransportFormula_code_le_stageThree
      recursiveSize shortSize valueTerm termBound
      hrecursiveSize hshortSize hvalueTerm
  have hequalityCode :=
    implicationAntecedent_code_le_binaryLengthTransportMPEnvelope
      (“!!recursiveSize = !!shortSize” :
        LO.FirstOrder.ArithmeticProposition)
      (“!lengthDef !!recursiveSize !!valueTerm →
        !lengthDef !!shortSize !!valueTerm” :
        LO.FirstOrder.ArithmeticProposition)
      termBound htransportCode
  have hconsequenceCodeStrong :=
    (binaryFormulaCode_consequent_le_implication
      (“!!recursiveSize = !!shortSize” :
        LO.FirstOrder.ArithmeticProposition)
      (“!lengthDef !!recursiveSize !!valueTerm →
        !lengthDef !!shortSize !!valueTerm” :
        LO.FirstOrder.ArithmeticProposition)).trans
      htransportCode
  have hconsequenceCode :=
    implicationConsequent_code_le_binaryLengthTransportMPEnvelope
      (“!!recursiveSize = !!shortSize” :
        LO.FirstOrder.ArithmeticProposition)
      (“!lengthDef !!recursiveSize !!valueTerm →
        !lengthDef !!shortSize !!valueTerm” :
        LO.FirstOrder.ArithmeticProposition)
      termBound htransportCode
  have hrecursiveFactCode :=
    implicationAntecedent_code_le_binaryLengthTransportMPEnvelope
      (“!lengthDef !!recursiveSize !!valueTerm” :
        LO.FirstOrder.ArithmeticProposition)
      (“!lengthDef !!shortSize !!valueTerm” :
        LO.FirstOrder.ArithmeticProposition)
      termBound hconsequenceCodeStrong
  have hfinalCode :=
    implicationConsequent_code_le_binaryLengthTransportMPEnvelope
      (“!lengthDef !!recursiveSize !!valueTerm” :
        LO.FirstOrder.ArithmeticProposition)
      (“!lengthDef !!shortSize !!valueTerm” :
        LO.FirstOrder.ArithmeticProposition)
      termBound hconsequenceCodeStrong
  have hsyntaxEquality :=
    modusPonensSyntaxBudget_le_paAssemblyEnvelope
      (“!!recursiveSize = !!shortSize” :
        LO.FirstOrder.ArithmeticProposition)
      (“!lengthDef !!recursiveSize !!valueTerm →
        !lengthDef !!shortSize !!valueTerm” :
        LO.FirstOrder.ArithmeticProposition)
      formulaBound hequalityCode hconsequenceCode
  have hsyntaxFact :=
    modusPonensSyntaxBudget_le_paAssemblyEnvelope
      (“!lengthDef !!recursiveSize !!valueTerm” :
        LO.FirstOrder.ArithmeticProposition)
      (“!lengthDef !!shortSize !!valueTerm” :
        LO.FirstOrder.ArithmeticProposition)
      formulaBound hrecursiveFactCode hfinalCode
  have hmpCost :
      mpCost =
        240 + 34 * paAssemblySyntaxEnvelope formulaBound := by
    rfl
  let implication :=
    binaryLengthSizeTransportImplication
      recursiveSize shortSize valueTerm
  let equality :=
    exponentialExponentRecursiveToShortProof width
  let recursiveFact : CertifiedPAProof
      (“!lengthDef !!recursiveSize !!valueTerm” :
        LO.FirstOrder.ArithmeticProposition) :=
    proveBinaryLengthAtRecursiveSizePolynomial value
  let afterEquality :=
    CertifiedPAProof.modusPonens implication equality
  have himplication :
      implication.payloadLength <=
        binaryLengthTransportPayloadEnvelope termBound := by
    dsimp only [implication]
    exact
      binaryLengthSizeTransportImplication_payloadLength_le_envelope
        recursiveSize shortSize valueTerm termBound
        hrecursiveSize hshortSize hvalueTerm
  have hequality :
      equality.payloadLength <=
        exponentialExponentRecursiveToShortPayloadPolynomial width := by
    dsimp only [equality]
    exact
      exponentialExponentRecursiveToShortProof_payloadLength_le_polynomial
        width
  have hrecursiveFact :
      recursiveFact.payloadLength <=
        binaryLengthRecursivePayloadPolynomial width := by
    dsimp only [recursiveFact, width]
    exact
      proveBinaryLengthAtRecursiveSizePolynomial_payloadLength_le value
  have hfirstRaw :=
    CertifiedPAProof.modusPonens_payloadLength_le
      implication equality
  have hfirst :
      afterEquality.payloadLength <=
        binaryLengthTransportPayloadEnvelope termBound +
          exponentialExponentRecursiveToShortPayloadPolynomial width +
          mpCost := by
    dsimp only [afterEquality]
    rw [hmpCost]
    omega
  have hsecondRaw :=
    CertifiedPAProof.modusPonens_payloadLength_le
      afterEquality recursiveFact
  unfold proveBinaryLengthAtShortNumeralsPolynomial
  change
    (CertifiedPAProof.modusPonens
      afterEquality recursiveFact).payloadLength <= _
  unfold binaryLengthAtShortNumeralsPayloadPolynomial
  change
    (CertifiedPAProof.modusPonens
      afterEquality recursiveFact).payloadLength <=
        binaryLengthTransportPayloadEnvelope termBound +
          exponentialExponentRecursiveToShortPayloadPolynomial width +
          binaryLengthRecursivePayloadPolynomial width +
          2 * mpCost
  omega

theorem proveBinaryLengthAtShortNumeralsPolynomial_verifier_eq_true
    (value : Nat) :
    listedCompactCertifiedPAProofVerifier
        (proveBinaryLengthAtShortNumeralsPolynomial value).code
        (compactFormulaCode
          (binaryLengthShortNumeralFormula value)) = true :=
  (proveBinaryLengthAtShortNumeralsPolynomial value).verifier_eq_true

theorem proveBinaryLengthAtShortNumerals_checked_polynomial
    (value : Nat) :
    listedCompactCertifiedPAProofVerifier
        (proveBinaryLengthAtShortNumeralsPolynomial value).code
        (compactFormulaCode
          (binaryLengthShortNumeralFormula value)) = true ∧
      (proveBinaryLengthAtShortNumeralsPolynomial value).payloadLength <=
        binaryLengthAtShortNumeralsPayloadPolynomial
          (Nat.size value) := by
  exact ⟨
    proveBinaryLengthAtShortNumeralsPolynomial_verifier_eq_true value,
    proveBinaryLengthAtShortNumeralsPolynomial_payloadLength_le value⟩

#print axioms binaryLengthEvenFormula_code_le_stageTwo
#print axioms binaryLengthOddFormula_code_le_stageTwo
#print axioms binaryLengthEvenImplication_payloadLength_le_envelope
#print axioms binaryLengthOddImplication_payloadLength_le_envelope
#print axioms positiveLessThanPayloadPolynomial_numeral_zero_eq_width
#print axioms provePositiveLessThan_zero_numeral_payloadLength_le_cumulative
#print axioms implicationAntecedent_code_le_binaryLengthMPEnvelope
#print axioms implicationConsequent_code_le_binaryLengthMPEnvelope
#print axioms binaryLengthBitStep_payloadLength_le
#print axioms
  proveBinaryLengthAtRecursiveSizePolynomial_payloadLength_le
#print axioms
  proveBinaryLengthAtRecursiveSizePolynomial_verifier_eq_true
#print axioms
  binaryLengthSizeTransportImplication_payloadLength_le_envelope
#print axioms
  proveBinaryLengthAtShortNumeralsPolynomial_payloadLength_le
#print axioms
  proveBinaryLengthAtShortNumerals_checked_polynomial

end FoundationCompactPABinaryLengthRuleCompilerBounds
