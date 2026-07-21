import integration.FoundationCompactPABitMembershipValuationContextCompilerBounds

/-!
# Syntax-polynomial bounds for valuation bit transport

The three transport resources used by the valuation bit compiler consist of
fixed checked PA proofs followed by two or three explicit specializations.
This file bounds those specializations by the codes of their actual formulas
and witnesses.  No proof payload or caller-supplied proof bound is an input.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPABitMembershipValuationTransportPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExponentialRuleCompilerBounds
open FoundationCompactPABitMembershipArgumentTransport
open FoundationCompactPABitMembershipValuationContextCompilerBounds

def bitTransportSpecializationScaleEnvelope (syntaxBound : Nat) : Nat :=
  2 * syntaxBound + 1

def bitTransportSpecializationCostEnvelope (syntaxBound : Nat) : Nat :=
  192 + 2048 * bitTransportSpecializationScaleEnvelope syntaxBound *
    bitTransportSpecializationScaleEnvelope syntaxBound *
    bitTransportSpecializationScaleEnvelope syntaxBound

theorem specializationCost_le_bitTransportEnvelope
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (syntaxBound : Nat)
    (hformula : (binaryFormulaCode formula).length <= syntaxBound)
    (hwitness : (binaryTermCode witness).length <= syntaxBound) :
    specializationCost formula witness <=
      bitTransportSpecializationCostEnvelope syntaxBound := by
  have hscale : specializationScale formula witness <=
      bitTransportSpecializationScaleEnvelope syntaxBound := by
    unfold specializationScale bitTransportSpecializationScaleEnvelope
    omega
  unfold specializationCost bitTransportSpecializationCostEnvelope
  gcongr

def binaryBitIndexTransportSyntaxResource
    (leftIndex rightIndex value :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  1 + (binaryFormulaCode binaryBitIndexTransportOuterBody).length +
    (binaryFormulaCode
      (binaryBitIndexTransportMiddleBody leftIndex)).length +
    (binaryFormulaCode
      (binaryBitIndexTransportInnerBody leftIndex rightIndex)).length +
    (binaryTermCode leftIndex).length +
    (binaryTermCode rightIndex).length +
    (binaryTermCode value).length

def binaryBitIndexTransportPayloadPolynomial
    (leftIndex rightIndex value :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  binaryBitIndexTransportUniversalProof.payloadLength +
    3 * bitTransportSpecializationCostEnvelope
      (binaryBitIndexTransportSyntaxResource leftIndex rightIndex value)

theorem binaryBitIndexTransportPayloadResource_le_syntaxPolynomial
    (leftIndex rightIndex value :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryBitIndexTransportPayloadResource leftIndex rightIndex value <=
      binaryBitIndexTransportPayloadPolynomial leftIndex rightIndex value := by
  let resource := binaryBitIndexTransportSyntaxResource
    leftIndex rightIndex value
  have houter : (binaryFormulaCode
      binaryBitIndexTransportOuterBody).length <= resource := by
    dsimp only [resource]
    unfold binaryBitIndexTransportSyntaxResource
    omega
  have hmiddle : (binaryFormulaCode
      (binaryBitIndexTransportMiddleBody leftIndex)).length <= resource := by
    dsimp only [resource]
    unfold binaryBitIndexTransportSyntaxResource
    omega
  have hinner : (binaryFormulaCode
      (binaryBitIndexTransportInnerBody leftIndex rightIndex)).length <=
        resource := by
    dsimp only [resource]
    unfold binaryBitIndexTransportSyntaxResource
    omega
  have hleft : (binaryTermCode leftIndex).length <= resource := by
    dsimp only [resource]
    unfold binaryBitIndexTransportSyntaxResource
    omega
  have hright : (binaryTermCode rightIndex).length <= resource := by
    dsimp only [resource]
    unfold binaryBitIndexTransportSyntaxResource
    omega
  have hvalue : (binaryTermCode value).length <= resource := by
    dsimp only [resource]
    unfold binaryBitIndexTransportSyntaxResource
    omega
  have hfirst := specializationCost_le_bitTransportEnvelope
    binaryBitIndexTransportOuterBody leftIndex resource houter hleft
  have hsecond := specializationCost_le_bitTransportEnvelope
    (binaryBitIndexTransportMiddleBody leftIndex) rightIndex resource
    hmiddle hright
  have hthird := specializationCost_le_bitTransportEnvelope
    (binaryBitIndexTransportInnerBody leftIndex rightIndex) value resource
    hinner hvalue
  unfold binaryBitIndexTransportPayloadResource
    binaryBitIndexTransportPayloadPolynomial
  dsimp only [resource] at hfirst hsecond hthird ⊢
  omega

def binaryBitValueTransportSyntaxResource
    (index leftValue rightValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  1 + (binaryFormulaCode binaryBitValueTransportOuterBody).length +
    (binaryFormulaCode
      (binaryBitValueTransportMiddleBody index)).length +
    (binaryFormulaCode
      (binaryBitValueTransportInnerBody index leftValue)).length +
    (binaryTermCode index).length +
    (binaryTermCode leftValue).length +
    (binaryTermCode rightValue).length

def binaryBitValueTransportPayloadPolynomial
    (index leftValue rightValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  binaryBitValueTransportUniversalProof.payloadLength +
    3 * bitTransportSpecializationCostEnvelope
      (binaryBitValueTransportSyntaxResource index leftValue rightValue)

theorem binaryBitValueTransportPayloadResource_le_syntaxPolynomial
    (index leftValue rightValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryBitValueTransportPayloadResource index leftValue rightValue <=
      binaryBitValueTransportPayloadPolynomial index leftValue rightValue := by
  let resource := binaryBitValueTransportSyntaxResource
    index leftValue rightValue
  have houter : (binaryFormulaCode
      binaryBitValueTransportOuterBody).length <= resource := by
    dsimp only [resource]
    unfold binaryBitValueTransportSyntaxResource
    omega
  have hmiddle : (binaryFormulaCode
      (binaryBitValueTransportMiddleBody index)).length <= resource := by
    dsimp only [resource]
    unfold binaryBitValueTransportSyntaxResource
    omega
  have hinner : (binaryFormulaCode
      (binaryBitValueTransportInnerBody index leftValue)).length <=
        resource := by
    dsimp only [resource]
    unfold binaryBitValueTransportSyntaxResource
    omega
  have hindex : (binaryTermCode index).length <= resource := by
    dsimp only [resource]
    unfold binaryBitValueTransportSyntaxResource
    omega
  have hleft : (binaryTermCode leftValue).length <= resource := by
    dsimp only [resource]
    unfold binaryBitValueTransportSyntaxResource
    omega
  have hright : (binaryTermCode rightValue).length <= resource := by
    dsimp only [resource]
    unfold binaryBitValueTransportSyntaxResource
    omega
  have hfirst := specializationCost_le_bitTransportEnvelope
    binaryBitValueTransportOuterBody index resource houter hindex
  have hsecond := specializationCost_le_bitTransportEnvelope
    (binaryBitValueTransportMiddleBody index) leftValue resource
    hmiddle hleft
  have hthird := specializationCost_le_bitTransportEnvelope
    (binaryBitValueTransportInnerBody index leftValue) rightValue resource
    hinner hright
  unfold binaryBitValueTransportPayloadResource
    binaryBitValueTransportPayloadPolynomial
  dsimp only [resource] at hfirst hsecond hthird ⊢
  omega

def binaryBitEqualitySymmetrySyntaxResource
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  1 + (binaryFormulaCode equalitySymmetryOuterBody).length +
    (binaryFormulaCode (equalitySymmetryInnerBody left)).length +
    (binaryTermCode left).length + (binaryTermCode right).length

def binaryBitEqualitySymmetryPayloadPolynomial
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  equalitySymmetryAxiomProof.payloadLength +
    2 * bitTransportSpecializationCostEnvelope
      (binaryBitEqualitySymmetrySyntaxResource left right)

theorem binaryBitEqualitySymmetryImplicationPayloadResource_le_syntaxPolynomial
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryBitEqualitySymmetryImplicationPayloadResource left right <=
      binaryBitEqualitySymmetryPayloadPolynomial left right := by
  let resource := binaryBitEqualitySymmetrySyntaxResource left right
  have houter : (binaryFormulaCode equalitySymmetryOuterBody).length <=
      resource := by
    dsimp only [resource]
    unfold binaryBitEqualitySymmetrySyntaxResource
    omega
  have hinner : (binaryFormulaCode
      (equalitySymmetryInnerBody left)).length <= resource := by
    dsimp only [resource]
    unfold binaryBitEqualitySymmetrySyntaxResource
    omega
  have hleft : (binaryTermCode left).length <= resource := by
    dsimp only [resource]
    unfold binaryBitEqualitySymmetrySyntaxResource
    omega
  have hright : (binaryTermCode right).length <= resource := by
    dsimp only [resource]
    unfold binaryBitEqualitySymmetrySyntaxResource
    omega
  have hfirst := specializationCost_le_bitTransportEnvelope
    equalitySymmetryOuterBody left resource houter hleft
  have hsecond := specializationCost_le_bitTransportEnvelope
    (equalitySymmetryInnerBody left) right resource hinner hright
  unfold binaryBitEqualitySymmetryImplicationPayloadResource
    binaryBitEqualitySymmetryPayloadPolynomial
  dsimp only [resource] at hfirst hsecond ⊢
  omega

/-! ## Public term-code endpoints -/

def binaryBitTransportFormulaSeed : Nat :=
  max (binaryFormulaCode binaryBitIndexTransportOuterBody).length
    (binaryFormulaCode binaryBitValueTransportOuterBody).length

def binaryBitTransportFormulaStageOne (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope binaryBitTransportFormulaSeed termBound

def binaryBitTransportFormulaStageTwo (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    (binaryBitTransportFormulaStageOne termBound) termBound

theorem binaryBitTransportFormulaStageOne_mono
    {small large : Nat} (hbound : small <= large) :
    binaryBitTransportFormulaStageOne small <=
      binaryBitTransportFormulaStageOne large := by
  exact substitutionFormulaCodeEnvelope_mono_exponential le_rfl hbound

theorem binaryBitTransportFormulaStageTwo_mono
    {small large : Nat} (hbound : small <= large) :
    binaryBitTransportFormulaStageTwo small <=
      binaryBitTransportFormulaStageTwo large := by
  exact substitutionFormulaCodeEnvelope_mono_exponential
    (binaryBitTransportFormulaStageOne_mono hbound) hbound

theorem binaryBitIndexTransportOuterBody_code_le_seed :
    (binaryFormulaCode binaryBitIndexTransportOuterBody).length <=
      binaryBitTransportFormulaSeed :=
  Nat.le_max_left _ _

theorem binaryBitValueTransportOuterBody_code_le_seed :
    (binaryFormulaCode binaryBitValueTransportOuterBody).length <=
      binaryBitTransportFormulaSeed :=
  Nat.le_max_right _ _

theorem binaryBitIndexTransportMiddleBody_code_le_stageOne
    (leftIndex : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode leftIndex).length <= termBound) :
    (binaryFormulaCode
      (binaryBitIndexTransportMiddleBody leftIndex)).length <=
        binaryBitTransportFormulaStageOne termBound := by
  exact instantiatedBodyCode_le_nextStage
    binaryBitIndexTransportOuterBody
    (binaryBitIndexTransportMiddleBody leftIndex) leftIndex
    binaryBitTransportFormulaSeed termBound
    binaryBitIndexTransportOuterBody_code_le_seed hleft
    (binaryBitIndexTransportAfterFirst_formula leftIndex)

theorem binaryBitIndexTransportInnerBody_code_le_stageTwo
    (leftIndex rightIndex : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode leftIndex).length <= termBound)
    (hright : (binaryTermCode rightIndex).length <= termBound) :
    (binaryFormulaCode
      (binaryBitIndexTransportInnerBody leftIndex rightIndex)).length <=
        binaryBitTransportFormulaStageTwo termBound := by
  exact instantiatedBodyCode_le_nextStage
    (binaryBitIndexTransportMiddleBody leftIndex)
    (binaryBitIndexTransportInnerBody leftIndex rightIndex) rightIndex
    (binaryBitTransportFormulaStageOne termBound) termBound
    (binaryBitIndexTransportMiddleBody_code_le_stageOne
      leftIndex termBound hleft) hright
    (binaryBitIndexTransportAfterSecond_formula leftIndex rightIndex)

theorem binaryBitValueTransportMiddleBody_code_le_stageOne
    (index : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hindex : (binaryTermCode index).length <= termBound) :
    (binaryFormulaCode
      (binaryBitValueTransportMiddleBody index)).length <=
        binaryBitTransportFormulaStageOne termBound := by
  exact instantiatedBodyCode_le_nextStage
    binaryBitValueTransportOuterBody
    (binaryBitValueTransportMiddleBody index) index
    binaryBitTransportFormulaSeed termBound
    binaryBitValueTransportOuterBody_code_le_seed hindex
    (binaryBitValueTransportAfterFirst_formula index)

theorem binaryBitValueTransportInnerBody_code_le_stageTwo
    (index leftValue : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hindex : (binaryTermCode index).length <= termBound)
    (hleft : (binaryTermCode leftValue).length <= termBound) :
    (binaryFormulaCode
      (binaryBitValueTransportInnerBody index leftValue)).length <=
        binaryBitTransportFormulaStageTwo termBound := by
  exact instantiatedBodyCode_le_nextStage
    (binaryBitValueTransportMiddleBody index)
    (binaryBitValueTransportInnerBody index leftValue) leftValue
    (binaryBitTransportFormulaStageOne termBound) termBound
    (binaryBitValueTransportMiddleBody_code_le_stageOne
      index termBound hindex) hleft
    (binaryBitValueTransportAfterSecond_formula index leftValue)

def binaryBitIndexTransportPayloadTermPolynomial (termBound : Nat) : Nat :=
  binaryBitIndexTransportUniversalProof.payloadLength +
    exponentialSpecializationCostEnvelope
      binaryBitTransportFormulaSeed termBound +
    exponentialSpecializationCostEnvelope
      (binaryBitTransportFormulaStageOne termBound) termBound +
    exponentialSpecializationCostEnvelope
      (binaryBitTransportFormulaStageTwo termBound) termBound

def binaryBitValueTransportPayloadTermPolynomial (termBound : Nat) : Nat :=
  binaryBitValueTransportUniversalProof.payloadLength +
    exponentialSpecializationCostEnvelope
      binaryBitTransportFormulaSeed termBound +
    exponentialSpecializationCostEnvelope
      (binaryBitTransportFormulaStageOne termBound) termBound +
    exponentialSpecializationCostEnvelope
      (binaryBitTransportFormulaStageTwo termBound) termBound

theorem binaryBitIndexTransportPayloadTermPolynomial_mono
    {small large : Nat} (hbound : small <= large) :
    binaryBitIndexTransportPayloadTermPolynomial small <=
      binaryBitIndexTransportPayloadTermPolynomial large := by
  have hstageOne := binaryBitTransportFormulaStageOne_mono hbound
  have hstageTwo := binaryBitTransportFormulaStageTwo_mono hbound
  have hfirst := exponentialSpecializationCostEnvelope_mono
    (smallFormula := binaryBitTransportFormulaSeed)
    (largeFormula := binaryBitTransportFormulaSeed)
    (smallTerm := small) (largeTerm := large) le_rfl hbound
  have hsecond := exponentialSpecializationCostEnvelope_mono
    (smallFormula := binaryBitTransportFormulaStageOne small)
    (largeFormula := binaryBitTransportFormulaStageOne large)
    (smallTerm := small) (largeTerm := large) hstageOne hbound
  have hthird := exponentialSpecializationCostEnvelope_mono
    (smallFormula := binaryBitTransportFormulaStageTwo small)
    (largeFormula := binaryBitTransportFormulaStageTwo large)
    (smallTerm := small) (largeTerm := large) hstageTwo hbound
  unfold binaryBitIndexTransportPayloadTermPolynomial
  omega

theorem binaryBitValueTransportPayloadTermPolynomial_mono
    {small large : Nat} (hbound : small <= large) :
    binaryBitValueTransportPayloadTermPolynomial small <=
      binaryBitValueTransportPayloadTermPolynomial large := by
  have hstageOne := binaryBitTransportFormulaStageOne_mono hbound
  have hstageTwo := binaryBitTransportFormulaStageTwo_mono hbound
  have hfirst := exponentialSpecializationCostEnvelope_mono
    (smallFormula := binaryBitTransportFormulaSeed)
    (largeFormula := binaryBitTransportFormulaSeed)
    (smallTerm := small) (largeTerm := large) le_rfl hbound
  have hsecond := exponentialSpecializationCostEnvelope_mono
    (smallFormula := binaryBitTransportFormulaStageOne small)
    (largeFormula := binaryBitTransportFormulaStageOne large)
    (smallTerm := small) (largeTerm := large) hstageOne hbound
  have hthird := exponentialSpecializationCostEnvelope_mono
    (smallFormula := binaryBitTransportFormulaStageTwo small)
    (largeFormula := binaryBitTransportFormulaStageTwo large)
    (smallTerm := small) (largeTerm := large) hstageTwo hbound
  unfold binaryBitValueTransportPayloadTermPolynomial
  omega

theorem binaryBitIndexTransportPayloadResource_le_termPolynomial
    (leftIndex rightIndex value :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode leftIndex).length <= termBound)
    (hright : (binaryTermCode rightIndex).length <= termBound)
    (hvalue : (binaryTermCode value).length <= termBound) :
    binaryBitIndexTransportPayloadResource leftIndex rightIndex value <=
      binaryBitIndexTransportPayloadTermPolynomial termBound := by
  have hmiddle := binaryBitIndexTransportMiddleBody_code_le_stageOne
    leftIndex termBound hleft
  have hinner := binaryBitIndexTransportInnerBody_code_le_stageTwo
    leftIndex rightIndex termBound hleft hright
  have hfirst := specializationCost_le_exponentialEnvelope
    binaryBitIndexTransportOuterBody leftIndex
    binaryBitTransportFormulaSeed termBound
    binaryBitIndexTransportOuterBody_code_le_seed hleft
  have hsecond := specializationCost_le_exponentialEnvelope
    (binaryBitIndexTransportMiddleBody leftIndex) rightIndex
    (binaryBitTransportFormulaStageOne termBound) termBound hmiddle hright
  have hthird := specializationCost_le_exponentialEnvelope
    (binaryBitIndexTransportInnerBody leftIndex rightIndex) value
    (binaryBitTransportFormulaStageTwo termBound) termBound hinner hvalue
  unfold binaryBitIndexTransportPayloadResource
    binaryBitIndexTransportPayloadTermPolynomial
  omega

theorem binaryBitValueTransportPayloadResource_le_termPolynomial
    (index leftValue rightValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hindex : (binaryTermCode index).length <= termBound)
    (hleft : (binaryTermCode leftValue).length <= termBound)
    (hright : (binaryTermCode rightValue).length <= termBound) :
    binaryBitValueTransportPayloadResource index leftValue rightValue <=
      binaryBitValueTransportPayloadTermPolynomial termBound := by
  have hmiddle := binaryBitValueTransportMiddleBody_code_le_stageOne
    index termBound hindex
  have hinner := binaryBitValueTransportInnerBody_code_le_stageTwo
    index leftValue termBound hindex hleft
  have hfirst := specializationCost_le_exponentialEnvelope
    binaryBitValueTransportOuterBody index
    binaryBitTransportFormulaSeed termBound
    binaryBitValueTransportOuterBody_code_le_seed hindex
  have hsecond := specializationCost_le_exponentialEnvelope
    (binaryBitValueTransportMiddleBody index) leftValue
    (binaryBitTransportFormulaStageOne termBound) termBound hmiddle hleft
  have hthird := specializationCost_le_exponentialEnvelope
    (binaryBitValueTransportInnerBody index leftValue) rightValue
    (binaryBitTransportFormulaStageTwo termBound) termBound hinner hright
  unfold binaryBitValueTransportPayloadResource
    binaryBitValueTransportPayloadTermPolynomial
  omega

def binaryBitEqualitySymmetryPayloadTermPolynomial (termBound : Nat) : Nat :=
  equalitySymmetryAxiomProof.payloadLength +
    2 * paSpecializationCostEnvelope termBound

theorem binaryBitEqualitySymmetryPayloadTermPolynomial_mono
    {small large : Nat} (hbound : small <= large) :
    binaryBitEqualitySymmetryPayloadTermPolynomial small <=
      binaryBitEqualitySymmetryPayloadTermPolynomial large := by
  have hspecialization :=
    FoundationCompactPAExponentialShortNumeralCompilerBounds.paSpecializationCostEnvelope_mono_short
      hbound
  unfold binaryBitEqualitySymmetryPayloadTermPolynomial
  omega

theorem
    binaryBitEqualitySymmetryImplicationPayloadResource_le_termPolynomial
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    binaryBitEqualitySymmetryImplicationPayloadResource left right <=
      binaryBitEqualitySymmetryPayloadTermPolynomial termBound := by
  have hinner := equalitySymmetryInnerBody_code_le_stage1
    left termBound hleft
  have hfirst := specializationCost_fixedFormula_le
    equalitySymmetryOuterBody left termBound (by simp) hleft
  have hsecond := specializationCost_stage1Formula_le
    (equalitySymmetryInnerBody left) right termBound hinner hright
  unfold binaryBitEqualitySymmetryImplicationPayloadResource
    binaryBitEqualitySymmetryPayloadTermPolynomial
  omega

#print axioms specializationCost_le_bitTransportEnvelope
#print axioms binaryBitIndexTransportPayloadResource_le_syntaxPolynomial
#print axioms binaryBitValueTransportPayloadResource_le_syntaxPolynomial
#print axioms
  binaryBitEqualitySymmetryImplicationPayloadResource_le_syntaxPolynomial
#print axioms binaryBitIndexTransportPayloadResource_le_termPolynomial
#print axioms binaryBitValueTransportPayloadResource_le_termPolynomial
#print axioms
  binaryBitEqualitySymmetryImplicationPayloadResource_le_termPolynomial
#print axioms binaryBitIndexTransportPayloadTermPolynomial_mono
#print axioms binaryBitValueTransportPayloadTermPolynomial_mono
#print axioms binaryBitEqualitySymmetryPayloadTermPolynomial_mono

end FoundationCompactPABitMembershipValuationTransportPolynomialBounds
