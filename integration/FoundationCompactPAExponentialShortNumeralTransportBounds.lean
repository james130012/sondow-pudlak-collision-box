import integration.FoundationCompactPAExponentialShortNumeralCompilerBounds

/-!
# Bounds for transport to the exact short-binary exponential formula

This module accounts for the three universal specializations in each fixed
equality-transport theorem.  It is separate from the recursive equality
compiler so that Lean can reuse the checked equality-bound object file without
re-elaborating the large recurrence.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAExponentialShortNumeralTransportBounds

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

def exponentialTransportFormulaSeed : Nat :=
  max
    (binaryFormulaCode exponentialValueTransportOuterBody).length
    (binaryFormulaCode exponentialExponentTransportOuterBody).length

def exponentialTransportFormulaStageOne (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope exponentialTransportFormulaSeed termBound

def exponentialTransportFormulaStageTwo (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    (exponentialTransportFormulaStageOne termBound) termBound

def exponentialTransportFormulaStageThree (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    (exponentialTransportFormulaStageTwo termBound) termBound

theorem exponentialValueTransportOuterBody_code_le_seed :
    (binaryFormulaCode exponentialValueTransportOuterBody).length <=
      exponentialTransportFormulaSeed := by
  exact Nat.le_max_left _ _

theorem exponentialExponentTransportOuterBody_code_le_seed :
    (binaryFormulaCode exponentialExponentTransportOuterBody).length <=
      exponentialTransportFormulaSeed := by
  exact Nat.le_max_right _ _

theorem exponentialValueTransportMiddleBody_code_le_stageOne
    (leftValue : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode leftValue).length <= termBound) :
    (binaryFormulaCode
      (exponentialValueTransportMiddleBody leftValue)).length <=
        exponentialTransportFormulaStageOne termBound := by
  exact instantiatedBodyCode_le_nextStage
    exponentialValueTransportOuterBody
    (exponentialValueTransportMiddleBody leftValue)
    leftValue exponentialTransportFormulaSeed termBound
    exponentialValueTransportOuterBody_code_le_seed hleft
    (exponentialValueTransportAfterFirst_formula leftValue)

theorem exponentialValueTransportInnerBody_code_le_stageTwo
    (leftValue rightValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode leftValue).length <= termBound)
    (hright : (binaryTermCode rightValue).length <= termBound) :
    (binaryFormulaCode
      (exponentialValueTransportInnerBody
        leftValue rightValue)).length <=
        exponentialTransportFormulaStageTwo termBound := by
  exact instantiatedBodyCode_le_nextStage
    (exponentialValueTransportMiddleBody leftValue)
    (exponentialValueTransportInnerBody leftValue rightValue)
    rightValue
    (exponentialTransportFormulaStageOne termBound) termBound
    (exponentialValueTransportMiddleBody_code_le_stageOne
      leftValue termBound hleft)
    hright
    (exponentialValueTransportAfterSecond_formula leftValue rightValue)

theorem exponentialValueTransportFormula_code_le_stageThree
    (leftValue rightValue exponent :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode leftValue).length <= termBound)
    (hright : (binaryTermCode rightValue).length <= termBound)
    (hexponent : (binaryTermCode exponent).length <= termBound) :
    (binaryFormulaCode
      (“!!leftValue = !!rightValue →
        (!expDef !!leftValue !!exponent →
          !expDef !!rightValue !!exponent)” :
        LO.FirstOrder.ArithmeticProposition)).length <=
      exponentialTransportFormulaStageThree termBound := by
  have hinner :=
    exponentialValueTransportInnerBody_code_le_stageTwo
      leftValue rightValue termBound hleft hright
  have hsubstitution :=
    binaryFormulaCode_substitution_one_length_le_envelope
      (exponentialValueTransportInnerBody leftValue rightValue)
      exponent
      (exponentialTransportFormulaStageTwo termBound)
      termBound hinner hexponent
  rw [exponentialValueTransportFinal_formula
    leftValue rightValue exponent] at hsubstitution
  exact hsubstitution

theorem exponentialExponentTransportMiddleBody_code_le_stageOne
    (value : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hvalue : (binaryTermCode value).length <= termBound) :
    (binaryFormulaCode
      (exponentialExponentTransportMiddleBody value)).length <=
        exponentialTransportFormulaStageOne termBound := by
  exact instantiatedBodyCode_le_nextStage
    exponentialExponentTransportOuterBody
    (exponentialExponentTransportMiddleBody value)
    value exponentialTransportFormulaSeed termBound
    exponentialExponentTransportOuterBody_code_le_seed hvalue
    (exponentialExponentTransportAfterFirst_formula value)

theorem exponentialExponentTransportInnerBody_code_le_stageTwo
    (value leftExponent :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hvalue : (binaryTermCode value).length <= termBound)
    (hleft : (binaryTermCode leftExponent).length <= termBound) :
    (binaryFormulaCode
      (exponentialExponentTransportInnerBody
        value leftExponent)).length <=
        exponentialTransportFormulaStageTwo termBound := by
  exact instantiatedBodyCode_le_nextStage
    (exponentialExponentTransportMiddleBody value)
    (exponentialExponentTransportInnerBody value leftExponent)
    leftExponent
    (exponentialTransportFormulaStageOne termBound) termBound
    (exponentialExponentTransportMiddleBody_code_le_stageOne
      value termBound hvalue)
    hleft
    (exponentialExponentTransportAfterSecond_formula value leftExponent)

theorem exponentialExponentTransportFormula_code_le_stageThree
    (value leftExponent rightExponent :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hvalue : (binaryTermCode value).length <= termBound)
    (hleft : (binaryTermCode leftExponent).length <= termBound)
    (hright : (binaryTermCode rightExponent).length <= termBound) :
    (binaryFormulaCode
      (“!!leftExponent = !!rightExponent →
        (!expDef !!value !!leftExponent →
          !expDef !!value !!rightExponent)” :
        LO.FirstOrder.ArithmeticProposition)).length <=
      exponentialTransportFormulaStageThree termBound := by
  have hinner :=
    exponentialExponentTransportInnerBody_code_le_stageTwo
      value leftExponent termBound hvalue hleft
  have hsubstitution :=
    binaryFormulaCode_substitution_one_length_le_envelope
      (exponentialExponentTransportInnerBody value leftExponent)
      rightExponent
      (exponentialTransportFormulaStageTwo termBound)
      termBound hinner hright
  rw [exponentialExponentTransportFinal_formula
    value leftExponent rightExponent] at hsubstitution
  exact hsubstitution

def exponentialValueTransportPayloadEnvelope (termBound : Nat) : Nat :=
  exponentialValueTransportUniversalProof.payloadLength +
    exponentialSpecializationCostEnvelope
      exponentialTransportFormulaSeed termBound +
    exponentialSpecializationCostEnvelope
      (exponentialTransportFormulaStageOne termBound) termBound +
    exponentialSpecializationCostEnvelope
      (exponentialTransportFormulaStageTwo termBound) termBound

def exponentialExponentTransportPayloadEnvelope (termBound : Nat) : Nat :=
  exponentialExponentTransportUniversalProof.payloadLength +
    exponentialSpecializationCostEnvelope
      exponentialTransportFormulaSeed termBound +
    exponentialSpecializationCostEnvelope
      (exponentialTransportFormulaStageOne termBound) termBound +
    exponentialSpecializationCostEnvelope
      (exponentialTransportFormulaStageTwo termBound) termBound

theorem exponentialValueTransportImplication_payloadLength_le_envelope
    (leftValue rightValue exponent :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode leftValue).length <= termBound)
    (hright : (binaryTermCode rightValue).length <= termBound)
    (hexponent : (binaryTermCode exponent).length <= termBound) :
    (exponentialValueTransportImplication
      leftValue rightValue exponent).payloadLength <=
        exponentialValueTransportPayloadEnvelope termBound := by
  have hmiddle :=
    exponentialValueTransportMiddleBody_code_le_stageOne
      leftValue termBound hleft
  have hinner :=
    exponentialValueTransportInnerBody_code_le_stageTwo
      leftValue rightValue termBound hleft hright
  have hfirstCost := specializationCost_le_exponentialEnvelope
    exponentialValueTransportOuterBody leftValue
    exponentialTransportFormulaSeed termBound
    exponentialValueTransportOuterBody_code_le_seed hleft
  have hsecondCost := specializationCost_le_exponentialEnvelope
    (exponentialValueTransportMiddleBody leftValue) rightValue
    (exponentialTransportFormulaStageOne termBound) termBound
    hmiddle hright
  have hthirdCost := specializationCost_le_exponentialEnvelope
    (exponentialValueTransportInnerBody leftValue rightValue) exponent
    (exponentialTransportFormulaStageTwo termBound) termBound
    hinner hexponent
  have hraw := specializeThriceWithCasts_payloadLength_le
    exponentialValueTransportUniversalProof
    leftValue rightValue exponent
    (exponentialValueTransportAfterFirst_formula leftValue)
    (exponentialValueTransportAfterSecond_formula leftValue rightValue)
    (exponentialValueTransportFinal_formula
      leftValue rightValue exponent)
  change
    (specializeThriceWithCasts
      exponentialValueTransportUniversalProof
      leftValue rightValue exponent
      (exponentialValueTransportAfterFirst_formula leftValue)
      (exponentialValueTransportAfterSecond_formula leftValue rightValue)
      (exponentialValueTransportFinal_formula
        leftValue rightValue exponent)).payloadLength <= _
  unfold exponentialValueTransportPayloadEnvelope
  omega

theorem exponentialExponentTransportImplication_payloadLength_le_envelope
    (value leftExponent rightExponent :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hvalue : (binaryTermCode value).length <= termBound)
    (hleft : (binaryTermCode leftExponent).length <= termBound)
    (hright : (binaryTermCode rightExponent).length <= termBound) :
    (exponentialExponentTransportImplication
      value leftExponent rightExponent).payloadLength <=
        exponentialExponentTransportPayloadEnvelope termBound := by
  have hmiddle :=
    exponentialExponentTransportMiddleBody_code_le_stageOne
      value termBound hvalue
  have hinner :=
    exponentialExponentTransportInnerBody_code_le_stageTwo
      value leftExponent termBound hvalue hleft
  have hfirstCost := specializationCost_le_exponentialEnvelope
    exponentialExponentTransportOuterBody value
    exponentialTransportFormulaSeed termBound
    exponentialExponentTransportOuterBody_code_le_seed hvalue
  have hsecondCost := specializationCost_le_exponentialEnvelope
    (exponentialExponentTransportMiddleBody value) leftExponent
    (exponentialTransportFormulaStageOne termBound) termBound
    hmiddle hleft
  have hthirdCost := specializationCost_le_exponentialEnvelope
    (exponentialExponentTransportInnerBody value leftExponent) rightExponent
    (exponentialTransportFormulaStageTwo termBound) termBound
    hinner hright
  have hraw := specializeThriceWithCasts_payloadLength_le
    exponentialExponentTransportUniversalProof
    value leftExponent rightExponent
    (exponentialExponentTransportAfterFirst_formula value)
    (exponentialExponentTransportAfterSecond_formula value leftExponent)
    (exponentialExponentTransportFinal_formula
      value leftExponent rightExponent)
  change
    (specializeThriceWithCasts
      exponentialExponentTransportUniversalProof
      value leftExponent rightExponent
      (exponentialExponentTransportAfterFirst_formula value)
      (exponentialExponentTransportAfterSecond_formula value leftExponent)
      (exponentialExponentTransportFinal_formula
        value leftExponent rightExponent)).payloadLength <= _
  unfold exponentialExponentTransportPayloadEnvelope
  omega

/-! ## Four checked modus-ponens assemblies -/

def exponentialTransportMPFormulaEnvelope (termBound : Nat) : Nat :=
  2 * exponentialTransportFormulaStageThree termBound

def exponentialTransportMPPayloadEnvelope (termBound : Nat) : Nat :=
  240 + 34 * paAssemblySyntaxEnvelope
    (exponentialTransportMPFormulaEnvelope termBound)

theorem implicationAntecedent_code_le_transportMPEnvelope
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (termBound : Nat)
    (himplication :
      (binaryFormulaCode (antecedent 🡒 consequent)).length <=
        exponentialTransportFormulaStageThree termBound) :
    (binaryFormulaCode antecedent).length <=
      exponentialTransportMPFormulaEnvelope termBound := by
  have hantecedent :=
    binaryFormulaCode_antecedent_le_implication antecedent consequent
  unfold exponentialTransportMPFormulaEnvelope
  exact hantecedent.trans (Nat.mul_le_mul_left 2 himplication)

theorem implicationConsequent_code_le_transportMPEnvelope
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (termBound : Nat)
    (himplication :
      (binaryFormulaCode (antecedent 🡒 consequent)).length <=
        exponentialTransportFormulaStageThree termBound) :
    (binaryFormulaCode consequent).length <=
      exponentialTransportMPFormulaEnvelope termBound := by
  have hconsequent :=
    (binaryFormulaCode_consequent_le_implication
      antecedent consequent).trans himplication
  have hdouble :
      exponentialTransportFormulaStageThree termBound <=
        2 * exponentialTransportFormulaStageThree termBound := by
    have hscale := Nat.mul_le_mul_right
      (exponentialTransportFormulaStageThree termBound)
      (show 1 <= 2 by decide)
    simpa using hscale
  unfold exponentialTransportMPFormulaEnvelope
  exact hconsequent.trans hdouble

def exponentialPowerAtShortNumeralsPayloadPolynomial
    (height : Nat) : Nat :=
  let termBound := exponentialShortTermCodeEnvelope height
  exponentialValueTransportPayloadEnvelope termBound +
    exponentialExponentTransportPayloadEnvelope termBound +
    exponentialValueRecursiveToShortPayloadPolynomial height +
    exponentialExponentRecursiveToShortPayloadPolynomial height +
    exponentialPowerPayloadPolynomial height +
    4 * exponentialTransportMPPayloadEnvelope termBound

theorem proveExponentialPowerAtShortNumerals_payloadLength_le_polynomial
    (height : Nat) :
    (proveExponentialPowerAtShortNumerals height).payloadLength <=
      exponentialPowerAtShortNumeralsPayloadPolynomial height := by
  let recursiveValue := exponentialPowerValueTerm height
  let shortValue := shortBinaryNumeralTerm (2 ^ height)
  let recursiveExponent := exponentialExponentTerm height
  let shortExponent := shortBinaryNumeralTerm height
  let termBound := exponentialShortTermCodeEnvelope height
  let formulaBound := exponentialTransportMPFormulaEnvelope termBound
  let mpCost := exponentialTransportMPPayloadEnvelope termBound
  have hpowerSize : Nat.size (2 ^ height) <= height + 1 := by
    rw [Nat.size_pow]
  have hheightSize : Nat.size height <= height + 1 := by
    exact (nat_size_le_self_short height).trans (by omega)
  have hrecursiveValue :
      (binaryTermCode recursiveValue).length <= termBound := by
    dsimp only [recursiveValue, termBound]
    exact exponentialPowerValueTerm_code_le_shortEnvelope
      height height le_rfl
  have hshortValue :
      (binaryTermCode shortValue).length <= termBound := by
    dsimp only [shortValue, termBound]
    exact shortBinaryNumeralTerm_code_le_shortEnvelope
      (2 ^ height) height hpowerSize
  have hrecursiveExponent :
      (binaryTermCode recursiveExponent).length <= termBound := by
    dsimp only [recursiveExponent, termBound]
    exact exponentialExponentTerm_code_le_shortEnvelope
      height height le_rfl
  have hshortExponent :
      (binaryTermCode shortExponent).length <= termBound := by
    dsimp only [shortExponent, termBound]
    exact shortBinaryNumeralTerm_code_le_shortEnvelope
      height height hheightSize
  have hvalueTransportCode :=
    exponentialValueTransportFormula_code_le_stageThree
      recursiveValue shortValue recursiveExponent termBound
      hrecursiveValue hshortValue hrecursiveExponent
  have hvalueEqualityCode :=
    implicationAntecedent_code_le_transportMPEnvelope
      (“!!recursiveValue = !!shortValue” :
        LO.FirstOrder.ArithmeticProposition)
      (“!expDef !!recursiveValue !!recursiveExponent →
        !expDef !!shortValue !!recursiveExponent” :
        LO.FirstOrder.ArithmeticProposition)
      termBound hvalueTransportCode
  have hvalueConsequenceCodeStrong :=
    (binaryFormulaCode_consequent_le_implication
      (“!!recursiveValue = !!shortValue” :
        LO.FirstOrder.ArithmeticProposition)
      (“!expDef !!recursiveValue !!recursiveExponent →
        !expDef !!shortValue !!recursiveExponent” :
        LO.FirstOrder.ArithmeticProposition)).trans
      hvalueTransportCode
  have hvalueConsequenceCode :=
    implicationConsequent_code_le_transportMPEnvelope
      (“!!recursiveValue = !!shortValue” :
        LO.FirstOrder.ArithmeticProposition)
      (“!expDef !!recursiveValue !!recursiveExponent →
        !expDef !!shortValue !!recursiveExponent” :
        LO.FirstOrder.ArithmeticProposition)
      termBound hvalueTransportCode
  have hrecursiveFactCode :=
    implicationAntecedent_code_le_transportMPEnvelope
      (“!expDef !!recursiveValue !!recursiveExponent” :
        LO.FirstOrder.ArithmeticProposition)
      (“!expDef !!shortValue !!recursiveExponent” :
        LO.FirstOrder.ArithmeticProposition)
      termBound hvalueConsequenceCodeStrong
  have hshortValueFactCode :=
    implicationConsequent_code_le_transportMPEnvelope
      (“!expDef !!recursiveValue !!recursiveExponent” :
        LO.FirstOrder.ArithmeticProposition)
      (“!expDef !!shortValue !!recursiveExponent” :
        LO.FirstOrder.ArithmeticProposition)
      termBound hvalueConsequenceCodeStrong
  have hexponentTransportCode :=
    exponentialExponentTransportFormula_code_le_stageThree
      shortValue recursiveExponent shortExponent termBound
      hshortValue hrecursiveExponent hshortExponent
  have hexponentEqualityCode :=
    implicationAntecedent_code_le_transportMPEnvelope
      (“!!recursiveExponent = !!shortExponent” :
        LO.FirstOrder.ArithmeticProposition)
      (“!expDef !!shortValue !!recursiveExponent →
        !expDef !!shortValue !!shortExponent” :
        LO.FirstOrder.ArithmeticProposition)
      termBound hexponentTransportCode
  have hexponentConsequenceCodeStrong :=
    (binaryFormulaCode_consequent_le_implication
      (“!!recursiveExponent = !!shortExponent” :
        LO.FirstOrder.ArithmeticProposition)
      (“!expDef !!shortValue !!recursiveExponent →
        !expDef !!shortValue !!shortExponent” :
        LO.FirstOrder.ArithmeticProposition)).trans
      hexponentTransportCode
  have hexponentConsequenceCode :=
    implicationConsequent_code_le_transportMPEnvelope
      (“!!recursiveExponent = !!shortExponent” :
        LO.FirstOrder.ArithmeticProposition)
      (“!expDef !!shortValue !!recursiveExponent →
        !expDef !!shortValue !!shortExponent” :
        LO.FirstOrder.ArithmeticProposition)
      termBound hexponentTransportCode
  have hfinalFactCode :=
    implicationConsequent_code_le_transportMPEnvelope
      (“!expDef !!shortValue !!recursiveExponent” :
        LO.FirstOrder.ArithmeticProposition)
      (“!expDef !!shortValue !!shortExponent” :
        LO.FirstOrder.ArithmeticProposition)
      termBound hexponentConsequenceCodeStrong
  have hsyntaxValueEquality :=
    modusPonensSyntaxBudget_le_paAssemblyEnvelope
      (“!!recursiveValue = !!shortValue” :
        LO.FirstOrder.ArithmeticProposition)
      (“!expDef !!recursiveValue !!recursiveExponent →
        !expDef !!shortValue !!recursiveExponent” :
        LO.FirstOrder.ArithmeticProposition)
      formulaBound hvalueEqualityCode hvalueConsequenceCode
  have hsyntaxValueFact :=
    modusPonensSyntaxBudget_le_paAssemblyEnvelope
      (“!expDef !!recursiveValue !!recursiveExponent” :
        LO.FirstOrder.ArithmeticProposition)
      (“!expDef !!shortValue !!recursiveExponent” :
        LO.FirstOrder.ArithmeticProposition)
      formulaBound hrecursiveFactCode hshortValueFactCode
  have hsyntaxExponentEquality :=
    modusPonensSyntaxBudget_le_paAssemblyEnvelope
      (“!!recursiveExponent = !!shortExponent” :
        LO.FirstOrder.ArithmeticProposition)
      (“!expDef !!shortValue !!recursiveExponent →
        !expDef !!shortValue !!shortExponent” :
        LO.FirstOrder.ArithmeticProposition)
      formulaBound hexponentEqualityCode hexponentConsequenceCode
  have hsyntaxFinal :=
    modusPonensSyntaxBudget_le_paAssemblyEnvelope
      (“!expDef !!shortValue !!recursiveExponent” :
        LO.FirstOrder.ArithmeticProposition)
      (“!expDef !!shortValue !!shortExponent” :
        LO.FirstOrder.ArithmeticProposition)
      formulaBound hshortValueFactCode hfinalFactCode
  have hmpCost :
      mpCost =
        240 + 34 * paAssemblySyntaxEnvelope formulaBound := by
    rfl
  let valueImplication :=
    exponentialValueTransportImplication
      recursiveValue shortValue recursiveExponent
  let valueEquality := exponentialValueRecursiveToShortProof height
  let recursiveFact := proveExponentialPower height
  let valueTransportAfterEquality :=
    CertifiedPAProof.modusPonens valueImplication valueEquality
  let shortValueFact :=
    CertifiedPAProof.modusPonens
      valueTransportAfterEquality recursiveFact
  let exponentImplication :=
    exponentialExponentTransportImplication
      shortValue recursiveExponent shortExponent
  let exponentEquality :=
    exponentialExponentRecursiveToShortProof height
  let exponentTransportAfterEquality :=
    CertifiedPAProof.modusPonens
      exponentImplication exponentEquality
  have hvalueImplication :
      valueImplication.payloadLength <=
        exponentialValueTransportPayloadEnvelope termBound := by
    dsimp only [valueImplication]
    exact exponentialValueTransportImplication_payloadLength_le_envelope
      recursiveValue shortValue recursiveExponent termBound
      hrecursiveValue hshortValue hrecursiveExponent
  have hvalueEquality :
      valueEquality.payloadLength <=
        exponentialValueRecursiveToShortPayloadPolynomial height := by
    dsimp only [valueEquality]
    exact
      exponentialValueRecursiveToShortProof_payloadLength_le_polynomial height
  have hrecursiveFact :
      recursiveFact.payloadLength <=
        exponentialPowerPayloadPolynomial height := by
    dsimp only [recursiveFact]
    exact proveExponentialPower_payloadLength_le_polynomial height
  have hexponentImplication :
      exponentImplication.payloadLength <=
        exponentialExponentTransportPayloadEnvelope termBound := by
    dsimp only [exponentImplication]
    exact exponentialExponentTransportImplication_payloadLength_le_envelope
      shortValue recursiveExponent shortExponent termBound
      hshortValue hrecursiveExponent hshortExponent
  have hexponentEquality :
      exponentEquality.payloadLength <=
        exponentialExponentRecursiveToShortPayloadPolynomial height := by
    dsimp only [exponentEquality]
    exact
      exponentialExponentRecursiveToShortProof_payloadLength_le_polynomial
        height
  have hfirstRaw := CertifiedPAProof.modusPonens_payloadLength_le
    valueImplication valueEquality
  have hfirst :
      valueTransportAfterEquality.payloadLength <=
        exponentialValueTransportPayloadEnvelope termBound +
          exponentialValueRecursiveToShortPayloadPolynomial height +
          mpCost := by
    dsimp only [valueTransportAfterEquality]
    omega
  have hsecondRaw := CertifiedPAProof.modusPonens_payloadLength_le
    valueTransportAfterEquality recursiveFact
  have hsecond :
      shortValueFact.payloadLength <=
        exponentialValueTransportPayloadEnvelope termBound +
          exponentialValueRecursiveToShortPayloadPolynomial height +
          exponentialPowerPayloadPolynomial height +
          2 * mpCost := by
    dsimp only [shortValueFact]
    omega
  have hthirdRaw := CertifiedPAProof.modusPonens_payloadLength_le
    exponentImplication exponentEquality
  have hthird :
      exponentTransportAfterEquality.payloadLength <=
        exponentialExponentTransportPayloadEnvelope termBound +
          exponentialExponentRecursiveToShortPayloadPolynomial height +
          mpCost := by
    dsimp only [exponentTransportAfterEquality]
    omega
  have hfinalRaw := CertifiedPAProof.modusPonens_payloadLength_le
    exponentTransportAfterEquality shortValueFact
  change
    (CertifiedPAProof.modusPonens
      exponentTransportAfterEquality shortValueFact).payloadLength <=
        exponentialValueTransportPayloadEnvelope termBound +
          exponentialExponentTransportPayloadEnvelope termBound +
          exponentialValueRecursiveToShortPayloadPolynomial height +
          exponentialExponentRecursiveToShortPayloadPolynomial height +
          exponentialPowerPayloadPolynomial height +
          4 * mpCost
  omega

theorem proveExponentialPowerAtShortNumerals_checked_polynomial
    (height : Nat) :
    listedCompactCertifiedPAProofVerifier
        (proveExponentialPowerAtShortNumerals height).code
        (compactFormulaCode
          (exponentialShortNumeralFormula height)) = true ∧
      (proveExponentialPowerAtShortNumerals height).payloadLength <=
        exponentialPowerAtShortNumeralsPayloadPolynomial height := by
  exact ⟨
    proveExponentialPowerAtShortNumerals_verifier_eq_true height,
    proveExponentialPowerAtShortNumerals_payloadLength_le_polynomial height⟩

#print axioms
  exponentialValueTransportFormula_code_le_stageThree
#print axioms
  exponentialExponentTransportFormula_code_le_stageThree
#print axioms
  exponentialValueTransportImplication_payloadLength_le_envelope
#print axioms
  exponentialExponentTransportImplication_payloadLength_le_envelope
#print axioms
  proveExponentialPowerAtShortNumerals_payloadLength_le_polynomial
#print axioms
  proveExponentialPowerAtShortNumerals_checked_polynomial

end FoundationCompactPAExponentialShortNumeralTransportBounds
