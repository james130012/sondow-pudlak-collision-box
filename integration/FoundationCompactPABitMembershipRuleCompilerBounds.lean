import integration.FoundationCompactPABitMembershipRuleCompiler
import integration.FoundationCompactPABinaryLengthRuleCompilerBounds

/-!
# Polynomial payload bounds for binary membership proofs

The proof compiler in `FoundationCompactPABitMembershipRuleCompiler` follows
at most one value bit per index step.  This file charges every specialization,
binary increment, and modus-ponens node against explicit envelopes.  The
resulting bound is polynomial in an ambient budget controlling the numeric bit
index and the binary width of the represented value.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABitMembershipRuleCompilerBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAExponentialRuleCompilerBounds
open FoundationCompactPAExponentialShortNumeralCompilerBounds
open FoundationCompactPABinaryLengthRuleCompilerBounds
open FoundationCompactPABitMembershipRuleCompiler

def binaryBitTermCodeEnvelope (budget : Nat) : Nat :=
  exponentialShortTermCodeEnvelope budget

/-! ## Formula-code envelopes -/

def binaryBitZeroFormulaSeed : Nat :=
  (binaryFormulaCode binaryBitZeroValueNegativeBody).length

def binaryBitZeroFormulaStageOne (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope binaryBitZeroFormulaSeed termBound

def binaryBitLowFormulaSeed : Nat :=
  max
    (binaryFormulaCode (binaryBitLowBody false)).length
    (binaryFormulaCode (binaryBitLowBody true)).length

def binaryBitLowFormulaStageOne (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope binaryBitLowFormulaSeed termBound

def binaryBitStepFormulaSeed : Nat :=
  max
    (max
      (binaryFormulaCode
        (binaryBitStepOuterBody false false)).length
      (binaryFormulaCode
        (binaryBitStepOuterBody false true)).length)
    (max
      (binaryFormulaCode
        (binaryBitStepOuterBody true false)).length
      (binaryFormulaCode
        (binaryBitStepOuterBody true true)).length)

def binaryBitStepFormulaStageOne (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope binaryBitStepFormulaSeed termBound

def binaryBitStepFormulaStageTwo (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    (binaryBitStepFormulaStageOne termBound) termBound

def binaryBitStepFormulaStageThree (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    (binaryBitStepFormulaStageTwo termBound) termBound

theorem binaryBitLowBody_code_le_seed (valueBit : Bool) :
    (binaryFormulaCode (binaryBitLowBody valueBit)).length <=
      binaryBitLowFormulaSeed := by
  cases valueBit with
  | false => exact Nat.le_max_left _ _
  | true => exact Nat.le_max_right _ _

theorem binaryBitStepOuterBody_code_le_seed
    (valueBit expected : Bool) :
    (binaryFormulaCode
      (binaryBitStepOuterBody valueBit expected)).length <=
      binaryBitStepFormulaSeed := by
  cases valueBit with
  | false =>
      cases expected with
      | false =>
          exact (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
      | true =>
          exact (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
  | true =>
      cases expected with
      | false =>
          exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
      | true =>
          exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

theorem binaryBitZeroInstantiated_code_le_stageOne
    (index : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hindex : (binaryTermCode index).length <= termBound) :
    (binaryFormulaCode
      (binaryBitLiteralAtTerms false index binaryBitZeroTerm)).length <=
      binaryBitZeroFormulaStageOne termBound := by
  have hsubstitution :=
    binaryFormulaCode_substitution_one_length_le_envelope
      binaryBitZeroValueNegativeBody index
      binaryBitZeroFormulaSeed termBound le_rfl hindex
  rw [binaryBitZeroValueNegativeFinal_formula index] at hsubstitution
  exact hsubstitution

theorem binaryBitLowInstantiated_code_le_stageOne
    (valueBit : Bool)
    (value : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hvalue : (binaryTermCode value).length <= termBound) :
    (binaryFormulaCode
      (binaryBitLiteralAtTerms valueBit binaryBitZeroTerm
        (binaryBitValueStepTerm valueBit value))).length <=
      binaryBitLowFormulaStageOne termBound := by
  have hsubstitution :=
    binaryFormulaCode_substitution_one_length_le_envelope
      (binaryBitLowBody valueBit) value
      binaryBitLowFormulaSeed termBound
      (binaryBitLowBody_code_le_seed valueBit) hvalue
  rw [binaryBitLowFinal_formula valueBit value] at hsubstitution
  exact hsubstitution

theorem binaryBitStepMiddleBody_code_le_stageOne
    (valueBit expected : Bool)
    (index : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hindex : (binaryTermCode index).length <= termBound) :
    (binaryFormulaCode
      (binaryBitStepMiddleBody valueBit expected index)).length <=
      binaryBitStepFormulaStageOne termBound := by
  exact instantiatedBodyCode_le_nextStage
    (binaryBitStepOuterBody valueBit expected)
    (binaryBitStepMiddleBody valueBit expected index)
    index binaryBitStepFormulaSeed termBound
    (binaryBitStepOuterBody_code_le_seed valueBit expected)
    hindex
    (binaryBitStepAfterFirst_formula valueBit expected index)

theorem binaryBitStepInnerBody_code_le_stageTwo
    (valueBit expected : Bool)
    (index nextIndex :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hindex : (binaryTermCode index).length <= termBound)
    (hnextIndex :
      (binaryTermCode nextIndex).length <= termBound) :
    (binaryFormulaCode
      (binaryBitStepInnerBody valueBit expected
        index nextIndex)).length <=
      binaryBitStepFormulaStageTwo termBound := by
  exact instantiatedBodyCode_le_nextStage
    (binaryBitStepMiddleBody valueBit expected index)
    (binaryBitStepInnerBody valueBit expected index nextIndex)
    nextIndex (binaryBitStepFormulaStageOne termBound) termBound
    (binaryBitStepMiddleBody_code_le_stageOne
      valueBit expected index termBound hindex)
    hnextIndex
    (binaryBitStepAfterSecond_formula
      valueBit expected index nextIndex)

theorem binaryBitStepFormula_code_le_stageThree
    (valueBit expected : Bool)
    (index nextIndex value :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hindex : (binaryTermCode index).length <= termBound)
    (hnextIndex :
      (binaryTermCode nextIndex).length <= termBound)
    (hvalue : (binaryTermCode value).length <= termBound) :
    (binaryFormulaCode
      (binaryBitStepFormula valueBit expected
        index nextIndex value)).length <=
      binaryBitStepFormulaStageThree termBound := by
  have hinner := binaryBitStepInnerBody_code_le_stageTwo
    valueBit expected index nextIndex termBound hindex hnextIndex
  have hsubstitution :=
    binaryFormulaCode_substitution_one_length_le_envelope
      (binaryBitStepInnerBody valueBit expected index nextIndex)
      value (binaryBitStepFormulaStageTwo termBound) termBound
      hinner hvalue
  rw [binaryBitStepFinal_formula
    valueBit expected index nextIndex value] at hsubstitution
  exact hsubstitution

/-! ## Specialization payload envelopes -/

def binaryBitLowUniversalPayloadSeed : Nat :=
  max
    (binaryBitLowUniversalProof false).payloadLength
    (binaryBitLowUniversalProof true).payloadLength

def binaryBitStepUniversalPayloadSeed : Nat :=
  max
    (max
      (binaryBitStepUniversalProof false false).payloadLength
      (binaryBitStepUniversalProof false true).payloadLength)
    (max
      (binaryBitStepUniversalProof true false).payloadLength
      (binaryBitStepUniversalProof true true).payloadLength)

theorem binaryBitLowUniversalProof_payloadLength_le_seed
    (valueBit : Bool) :
    (binaryBitLowUniversalProof valueBit).payloadLength <=
      binaryBitLowUniversalPayloadSeed := by
  cases valueBit with
  | false => exact Nat.le_max_left _ _
  | true => exact Nat.le_max_right _ _

theorem binaryBitStepUniversalProof_payloadLength_le_seed
    (valueBit expected : Bool) :
    (binaryBitStepUniversalProof valueBit expected).payloadLength <=
      binaryBitStepUniversalPayloadSeed := by
  cases valueBit with
  | false =>
      cases expected with
      | false =>
          exact (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
      | true =>
          exact (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
  | true =>
      cases expected with
      | false =>
          exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
      | true =>
          exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

def binaryBitZeroProofPayloadEnvelope (termBound : Nat) : Nat :=
  binaryBitZeroValueNegativeUniversalProof.payloadLength +
    exponentialSpecializationCostEnvelope
      binaryBitZeroFormulaSeed termBound

def binaryBitLowProofPayloadEnvelope (termBound : Nat) : Nat :=
  binaryBitLowUniversalPayloadSeed +
    exponentialSpecializationCostEnvelope
      binaryBitLowFormulaSeed termBound

def binaryBitStepImplicationPayloadEnvelope
    (termBound : Nat) : Nat :=
  binaryBitStepUniversalPayloadSeed +
    exponentialSpecializationCostEnvelope
      binaryBitStepFormulaSeed termBound +
    exponentialSpecializationCostEnvelope
      (binaryBitStepFormulaStageOne termBound) termBound +
    exponentialSpecializationCostEnvelope
      (binaryBitStepFormulaStageTwo termBound) termBound

theorem binaryBitZeroValueNegativeProof_payloadLength_le_envelope
    (index : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hindex : (binaryTermCode index).length <= termBound) :
    (binaryBitZeroValueNegativeProof index).payloadLength <=
      binaryBitZeroProofPayloadEnvelope termBound := by
  have hcost := specializationCost_le_exponentialEnvelope
    binaryBitZeroValueNegativeBody index
    binaryBitZeroFormulaSeed termBound le_rfl hindex
  have hraw := specialize_payloadLength_le_cost
    binaryBitZeroValueNegativeUniversalProof index
  unfold binaryBitZeroValueNegativeProof
  simp only [CertifiedPAProof.cast_payloadLength]
  unfold binaryBitZeroProofPayloadEnvelope
  omega

theorem binaryBitLowProof_payloadLength_le_envelope
    (valueBit : Bool)
    (value : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hvalue : (binaryTermCode value).length <= termBound) :
    (binaryBitLowProof valueBit value).payloadLength <=
      binaryBitLowProofPayloadEnvelope termBound := by
  have hbody := binaryBitLowBody_code_le_seed valueBit
  have hcost := specializationCost_le_exponentialEnvelope
    (binaryBitLowBody valueBit) value
    binaryBitLowFormulaSeed termBound hbody hvalue
  have hraw := specialize_payloadLength_le_cost
    (binaryBitLowUniversalProof valueBit) value
  have huniversal :=
    binaryBitLowUniversalProof_payloadLength_le_seed valueBit
  unfold binaryBitLowProof
  simp only [CertifiedPAProof.cast_payloadLength]
  unfold binaryBitLowProofPayloadEnvelope
  omega

theorem binaryBitStepImplication_payloadLength_le_envelope
    (valueBit expected : Bool)
    (index nextIndex value :
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hindex : (binaryTermCode index).length <= termBound)
    (hnextIndex :
      (binaryTermCode nextIndex).length <= termBound)
    (hvalue : (binaryTermCode value).length <= termBound) :
    (binaryBitStepImplication valueBit expected
      index nextIndex value).payloadLength <=
      binaryBitStepImplicationPayloadEnvelope termBound := by
  have hmiddle := binaryBitStepMiddleBody_code_le_stageOne
    valueBit expected index termBound hindex
  have hinner := binaryBitStepInnerBody_code_le_stageTwo
    valueBit expected index nextIndex termBound hindex hnextIndex
  have hfirstCost := specializationCost_le_exponentialEnvelope
    (binaryBitStepOuterBody valueBit expected) index
    binaryBitStepFormulaSeed termBound
    (binaryBitStepOuterBody_code_le_seed valueBit expected) hindex
  have hsecondCost := specializationCost_le_exponentialEnvelope
    (binaryBitStepMiddleBody valueBit expected index) nextIndex
    (binaryBitStepFormulaStageOne termBound) termBound
    hmiddle hnextIndex
  have hthirdCost := specializationCost_le_exponentialEnvelope
    (binaryBitStepInnerBody valueBit expected index nextIndex) value
    (binaryBitStepFormulaStageTwo termBound) termBound
    hinner hvalue
  have hraw := specializeThriceWithCasts_payloadLength_le
    (binaryBitStepUniversalProof valueBit expected)
    index nextIndex value
    (binaryBitStepAfterFirst_formula valueBit expected index)
    (binaryBitStepAfterSecond_formula
      valueBit expected index nextIndex)
    (binaryBitStepFinal_formula
      valueBit expected index nextIndex value)
  have huniversal :=
    binaryBitStepUniversalProof_payloadLength_le_seed
      valueBit expected
  unfold binaryBitStepImplication
  unfold binaryBitStepImplicationPayloadEnvelope
  omega

/-! ## One recursive membership step -/

def binaryBitMPFormulaEnvelope (termBound : Nat) : Nat :=
  2 * binaryBitStepFormulaStageThree termBound

def binaryBitMPPayloadEnvelope (termBound : Nat) : Nat :=
  240 + 34 * paAssemblySyntaxEnvelope
    (binaryBitMPFormulaEnvelope termBound)

theorem implicationAntecedent_code_le_binaryBitMPEnvelope
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (termBound : Nat)
    (himplication :
      (binaryFormulaCode (antecedent 🡒 consequent)).length <=
        binaryBitStepFormulaStageThree termBound) :
    (binaryFormulaCode antecedent).length <=
      binaryBitMPFormulaEnvelope termBound := by
  have hantecedent :=
    binaryFormulaCode_antecedent_le_implication antecedent consequent
  unfold binaryBitMPFormulaEnvelope
  exact hantecedent.trans (Nat.mul_le_mul_left 2 himplication)

theorem implicationConsequent_code_le_binaryBitMPEnvelope
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition)
    (termBound : Nat)
    (himplication :
      (binaryFormulaCode (antecedent 🡒 consequent)).length <=
        binaryBitStepFormulaStageThree termBound) :
    (binaryFormulaCode consequent).length <=
      binaryBitMPFormulaEnvelope termBound := by
  have hconsequent :=
    (binaryFormulaCode_consequent_le_implication
      antecedent consequent).trans himplication
  unfold binaryBitMPFormulaEnvelope
  omega

def binaryBitRecursiveStepPayloadEnvelope (budget : Nat) : Nat :=
  let termBound := binaryBitTermCodeEnvelope budget
  binaryBitStepImplicationPayloadEnvelope termBound +
    binaryNumeralIncrementPayloadPolynomial budget +
    2 * binaryBitMPPayloadEnvelope termBound

theorem binaryBitStepProofAtShortNumerals_payloadLength_le
    (valueBit expected : Bool)
    (index high budget : Nat)
    (hcanonical : high = 0 → valueBit = true)
    (previous : CertifiedPAProof
      (binaryBitShortLiteralFormula expected index high))
    (hindex : Nat.size index <= budget)
    (hnextIndex : Nat.size (index + 1) <= budget)
    (hhigh : Nat.size high <= budget) :
    (binaryBitStepProofAtShortNumerals
      valueBit expected index high hcanonical previous).payloadLength <=
      previous.payloadLength +
        binaryBitRecursiveStepPayloadEnvelope budget := by
  let indexTerm := shortBinaryNumeralTerm index
  let nextIndexTerm := shortBinaryNumeralTerm (index + 1)
  let highTerm := shortBinaryNumeralTerm high
  let termBound := binaryBitTermCodeEnvelope budget
  let formulaBound := binaryBitMPFormulaEnvelope termBound
  let mpCost := binaryBitMPPayloadEnvelope termBound
  let incrementFormula :=
    binaryBitIncrementEquality indexTerm nextIndexTerm
  let previousFormula :=
    binaryBitLiteralAtTerms expected indexTerm highTerm
  let nextFormula :=
    binaryBitLiteralAtTerms expected nextIndexTerm
      (binaryBitValueStepTerm valueBit highTerm)
  let remainingFormula := previousFormula 🡒 nextFormula
  let implication := binaryBitStepImplication
    valueBit expected indexTerm nextIndexTerm highTerm
  let increment := binaryBitIncrementProof index
  let afterIncrement := CertifiedPAProof.modusPonens
    implication increment
  have hindexTerm :
      (binaryTermCode indexTerm).length <= termBound := by
    dsimp only [indexTerm, termBound, binaryBitTermCodeEnvelope]
    exact shortBinaryNumeralTerm_code_le_shortEnvelope
      index budget (hindex.trans (Nat.le_add_right budget 1))
  have hnextIndexTerm :
      (binaryTermCode nextIndexTerm).length <= termBound := by
    dsimp only [nextIndexTerm, termBound,
      binaryBitTermCodeEnvelope]
    exact shortBinaryNumeralTerm_code_le_shortEnvelope
      (index + 1) budget
        (hnextIndex.trans (Nat.le_add_right budget 1))
  have hhighTerm :
      (binaryTermCode highTerm).length <= termBound := by
    dsimp only [highTerm, termBound, binaryBitTermCodeEnvelope]
    exact shortBinaryNumeralTerm_code_le_shortEnvelope
      high budget (hhigh.trans (Nat.le_add_right budget 1))
  have himplicationCode :=
    binaryBitStepFormula_code_le_stageThree
      valueBit expected indexTerm nextIndexTerm highTerm
      termBound hindexTerm hnextIndexTerm hhighTerm
  have hfullCode :
      (binaryFormulaCode
        (incrementFormula 🡒 remainingFormula)).length <=
        binaryBitStepFormulaStageThree termBound := by
    simpa [remainingFormula, incrementFormula, previousFormula,
      nextFormula, binaryBitStepFormula] using himplicationCode
  have hincrementCode :
      (binaryFormulaCode incrementFormula).length <=
        formulaBound := by
    dsimp only [formulaBound]
    exact implicationAntecedent_code_le_binaryBitMPEnvelope
      incrementFormula remainingFormula termBound hfullCode
  have hremainingCodeStrong :
      (binaryFormulaCode remainingFormula).length <=
        binaryBitStepFormulaStageThree termBound :=
    (binaryFormulaCode_consequent_le_implication
      incrementFormula remainingFormula).trans hfullCode
  have hremainingCode :
      (binaryFormulaCode remainingFormula).length <=
        formulaBound := by
    dsimp only [formulaBound]
    exact implicationConsequent_code_le_binaryBitMPEnvelope
      incrementFormula remainingFormula termBound hfullCode
  have hpreviousCode :
      (binaryFormulaCode previousFormula).length <=
        formulaBound := by
    dsimp only [formulaBound]
    exact implicationAntecedent_code_le_binaryBitMPEnvelope
      previousFormula nextFormula termBound hremainingCodeStrong
  have hnextCode :
      (binaryFormulaCode nextFormula).length <=
        formulaBound := by
    dsimp only [formulaBound]
    exact implicationConsequent_code_le_binaryBitMPEnvelope
      previousFormula nextFormula termBound hremainingCodeStrong
  have hsyntaxFirst :=
    modusPonensSyntaxBudget_le_paAssemblyEnvelope
      incrementFormula remainingFormula formulaBound
      hincrementCode hremainingCode
  have hsyntaxSecond :=
    modusPonensSyntaxBudget_le_paAssemblyEnvelope
      previousFormula nextFormula formulaBound
      hpreviousCode hnextCode
  have himplicationPayload :
      implication.payloadLength <=
        binaryBitStepImplicationPayloadEnvelope termBound := by
    dsimp only [implication]
    exact binaryBitStepImplication_payloadLength_le_envelope
      valueBit expected indexTerm nextIndexTerm highTerm
      termBound hindexTerm hnextIndexTerm hhighTerm
  have hincrementPayload :
      increment.payloadLength <=
        binaryNumeralIncrementPayloadPolynomial budget := by
    dsimp only [increment, binaryBitIncrementProof]
    simp only [CertifiedPAProof.cast_payloadLength]
    exact proveBinaryNumeralIncrement_payloadLength_le_width
      index budget hindex
  have hmpCost :
      mpCost =
        240 + 34 * paAssemblySyntaxEnvelope formulaBound := by
    rfl
  have hfirstRaw :=
    CertifiedPAProof.modusPonens_payloadLength_le
      implication increment
  change
    afterIncrement.payloadLength <=
      implication.payloadLength + increment.payloadLength + 240 +
        34 * FoundationCompactCertifiedModusPonens.modusPonensSyntaxBudget
          incrementFormula remainingFormula at hfirstRaw
  have hfirst :
      afterIncrement.payloadLength <=
        binaryBitStepImplicationPayloadEnvelope termBound +
          binaryNumeralIncrementPayloadPolynomial budget + mpCost := by
    rw [hmpCost]
    omega
  have hsecondRaw :=
    CertifiedPAProof.modusPonens_payloadLength_le
      afterIncrement previous
  change
    (CertifiedPAProof.modusPonens
      afterIncrement previous).payloadLength <=
      afterIncrement.payloadLength + previous.payloadLength + 240 +
        34 * FoundationCompactCertifiedModusPonens.modusPonensSyntaxBudget
          previousFormula nextFormula at hsecondRaw
  have hresult :
      (CertifiedPAProof.modusPonens
        afterIncrement previous).payloadLength <=
        previous.payloadLength +
          (binaryBitStepImplicationPayloadEnvelope termBound +
            binaryNumeralIncrementPayloadPolynomial budget +
            2 * mpCost) := by
    omega
  unfold binaryBitStepProofAtShortNumerals
  simp only [CertifiedPAProof.cast_payloadLength]
  change
    (CertifiedPAProof.modusPonens
      afterIncrement previous).payloadLength <= _
  unfold binaryBitRecursiveStepPayloadEnvelope
  change
    (CertifiedPAProof.modusPonens
      afterIncrement previous).payloadLength <=
      previous.payloadLength +
        (binaryBitStepImplicationPayloadEnvelope termBound +
          binaryNumeralIncrementPayloadPolynomial budget +
          2 * mpCost)
  exact hresult

/-! ## Closed base branches -/

def binaryBitBasePayloadEnvelope (budget : Nat) : Nat :=
  let termBound := binaryBitTermCodeEnvelope budget
  binaryBitZeroProofPayloadEnvelope termBound +
    binaryBitLowProofPayloadEnvelope termBound

theorem binaryBitZeroValueNegativeProofAtShortIndex_payloadLength_le
    (index budget : Nat)
    (hindex : Nat.size index <= budget) :
    (binaryBitZeroValueNegativeProofAtShortIndex index).payloadLength <=
      binaryBitBasePayloadEnvelope budget := by
  let indexTerm := shortBinaryNumeralTerm index
  let termBound := binaryBitTermCodeEnvelope budget
  have hindexTerm :
      (binaryTermCode indexTerm).length <= termBound := by
    dsimp only [indexTerm, termBound, binaryBitTermCodeEnvelope]
    exact shortBinaryNumeralTerm_code_le_shortEnvelope
      index budget (hindex.trans (Nat.le_add_right budget 1))
  have hraw :=
    binaryBitZeroValueNegativeProof_payloadLength_le_envelope
      indexTerm termBound hindexTerm
  unfold binaryBitZeroValueNegativeProofAtShortIndex
  simp only [CertifiedPAProof.cast_payloadLength]
  unfold binaryBitBasePayloadEnvelope
  change
    (binaryBitZeroValueNegativeProof indexTerm).payloadLength <=
      binaryBitZeroProofPayloadEnvelope termBound +
        binaryBitLowProofPayloadEnvelope termBound
  exact hraw.trans (Nat.le_add_right _ _)

theorem binaryBitLowProofAtShortNumerals_payloadLength_le
    (valueBit : Bool) (high budget : Nat)
    (hcanonical : high = 0 → valueBit = true)
    (hhigh : Nat.size high <= budget) :
    (binaryBitLowProofAtShortNumerals
      valueBit high hcanonical).payloadLength <=
      binaryBitBasePayloadEnvelope budget := by
  let highTerm := shortBinaryNumeralTerm high
  let termBound := binaryBitTermCodeEnvelope budget
  have hhighTerm :
      (binaryTermCode highTerm).length <= termBound := by
    dsimp only [highTerm, termBound, binaryBitTermCodeEnvelope]
    exact shortBinaryNumeralTerm_code_le_shortEnvelope
      high budget (hhigh.trans (Nat.le_add_right budget 1))
  have hraw := binaryBitLowProof_payloadLength_le_envelope
    valueBit highTerm termBound hhighTerm
  unfold binaryBitLowProofAtShortNumerals
  simp only [CertifiedPAProof.cast_payloadLength]
  unfold binaryBitBasePayloadEnvelope
  change
    (binaryBitLowProof valueBit highTerm).payloadLength <=
      binaryBitZeroProofPayloadEnvelope termBound +
        binaryBitLowProofPayloadEnvelope termBound
  exact hraw.trans (Nat.le_add_left _ _)

/-! ## Proof-carrying recursion -/

def binaryBitBasePayloadCumulative (budget : Nat) : Nat :=
  ∑ candidate ∈ Finset.range (budget + 1),
    binaryBitBasePayloadEnvelope candidate

theorem binaryBitBasePayloadEnvelope_le_cumulative
    {candidate budget : Nat} (hbudget : candidate <= budget) :
    binaryBitBasePayloadEnvelope candidate <=
      binaryBitBasePayloadCumulative budget := by
  have hmem : candidate ∈ Finset.range (budget + 1) := by
    simp
    omega
  unfold binaryBitBasePayloadCumulative
  exact Finset.single_le_sum
    (f := binaryBitBasePayloadEnvelope)
    (s := Finset.range (budget + 1))
    (fun index _ => Nat.zero_le
      (binaryBitBasePayloadEnvelope index))
    hmem

theorem binaryBitBasePayloadCumulative_mono
    {small large : Nat} (hbudget : small <= large) :
    binaryBitBasePayloadCumulative small <=
      binaryBitBasePayloadCumulative large := by
  have hrange :
      Finset.range (small + 1) ⊆ Finset.range (large + 1) := by
    intro candidate hcandidate
    simp only [Finset.mem_range] at hcandidate ⊢
    omega
  unfold binaryBitBasePayloadCumulative
  exact Finset.sum_le_sum_of_subset hrange

def binaryBitRecursiveStepPayloadCumulative (budget : Nat) : Nat :=
  ∑ candidate ∈ Finset.range (budget + 1),
    binaryBitRecursiveStepPayloadEnvelope candidate

theorem binaryBitRecursiveStepPayloadEnvelope_le_cumulative
    {candidate budget : Nat} (hbudget : candidate <= budget) :
    binaryBitRecursiveStepPayloadEnvelope candidate <=
      binaryBitRecursiveStepPayloadCumulative budget := by
  have hmem : candidate ∈ Finset.range (budget + 1) := by
    simp
    omega
  unfold binaryBitRecursiveStepPayloadCumulative
  exact Finset.single_le_sum
    (f := binaryBitRecursiveStepPayloadEnvelope)
    (s := Finset.range (budget + 1))
    (fun index _ => Nat.zero_le
      (binaryBitRecursiveStepPayloadEnvelope index))
    hmem

theorem binaryBitRecursiveStepPayloadCumulative_mono
    {small large : Nat} (hbudget : small <= large) :
    binaryBitRecursiveStepPayloadCumulative small <=
      binaryBitRecursiveStepPayloadCumulative large := by
  have hrange :
      Finset.range (small + 1) ⊆ Finset.range (large + 1) := by
    intro candidate hcandidate
    simp only [Finset.mem_range] at hcandidate ⊢
    omega
  unfold binaryBitRecursiveStepPayloadCumulative
  exact Finset.sum_le_sum_of_subset hrange

def binaryBitWorkBudget (index value : Nat) : Nat :=
  Nat.size value + index + 1

def binaryBitRecursivePayloadPolynomial (budget : Nat) : Nat :=
  binaryBitBasePayloadCumulative budget +
    budget * binaryBitRecursiveStepPayloadCumulative budget

theorem binaryBitPayloadStep_le_polynomial
    (sourceBudget currentBudget sourcePayload currentPayload : Nat)
    (hbudget : sourceBudget < currentBudget)
    (hstep :
      currentPayload <= sourcePayload +
        binaryBitRecursiveStepPayloadEnvelope currentBudget)
    (hprevious :
      sourcePayload <=
        binaryBitRecursivePayloadPolynomial sourceBudget) :
    currentPayload <=
      binaryBitRecursivePayloadPolynomial currentBudget := by
  have hbudgetLe : sourceBudget <= currentBudget :=
    Nat.le_of_lt hbudget
  have hbase :=
    binaryBitBasePayloadCumulative_mono hbudgetLe
  have hsteps :=
    binaryBitRecursiveStepPayloadCumulative_mono hbudgetLe
  have hpreviousCurrent :
      sourcePayload <=
        binaryBitBasePayloadCumulative currentBudget +
          sourceBudget *
            binaryBitRecursiveStepPayloadCumulative currentBudget := by
    unfold binaryBitRecursivePayloadPolynomial at hprevious
    exact hprevious.trans <| Nat.add_le_add hbase
      (Nat.mul_le_mul_left sourceBudget hsteps)
  have hcomponent :=
    binaryBitRecursiveStepPayloadEnvelope_le_cumulative
      (candidate := currentBudget) (budget := currentBudget) le_rfl
  have hcombined :
      sourcePayload +
          binaryBitRecursiveStepPayloadEnvelope currentBudget <=
        binaryBitBasePayloadCumulative currentBudget +
          (sourceBudget + 1) *
            binaryBitRecursiveStepPayloadCumulative currentBudget := by
    calc
      sourcePayload +
          binaryBitRecursiveStepPayloadEnvelope currentBudget <=
          (binaryBitBasePayloadCumulative currentBudget +
              sourceBudget *
                binaryBitRecursiveStepPayloadCumulative currentBudget) +
            binaryBitRecursiveStepPayloadCumulative currentBudget :=
        Nat.add_le_add hpreviousCurrent hcomponent
      _ = binaryBitBasePayloadCumulative currentBudget +
          (sourceBudget + 1) *
            binaryBitRecursiveStepPayloadCumulative currentBudget := by
        ring
  have hcoefficient : sourceBudget + 1 <= currentBudget := by
    omega
  have hproduct := Nat.mul_le_mul_right
    (binaryBitRecursiveStepPayloadCumulative currentBudget)
    hcoefficient
  unfold binaryBitRecursivePayloadPolynomial
  exact hstep.trans <| hcombined.trans
    (Nat.add_le_add_left hproduct
      (binaryBitBasePayloadCumulative currentBudget))

/-! The recursive result type mentions the computed bit polarity.  Keep each
formula transport named so dependent structure elaboration never has to unfold
a tactic-generated proof merely to recover its unchanged payload length. -/

noncomputable def binaryBitZeroValueProofAtShortIndexExact
    (index : Nat) :
    CertifiedPAProof
      (binaryBitShortLiteralFormula (Nat.testBit 0 index) index 0) :=
  CertifiedPAProof.cast (by simp)
    (binaryBitZeroValueNegativeProofAtShortIndex index)

@[simp] theorem binaryBitZeroValueProofAtShortIndexExact_payloadLength
    (index : Nat) :
    (binaryBitZeroValueProofAtShortIndexExact index).payloadLength =
      (binaryBitZeroValueNegativeProofAtShortIndex index).payloadLength := by
  unfold binaryBitZeroValueProofAtShortIndexExact
  simp only [CertifiedPAProof.cast_payloadLength]

noncomputable def binaryBitLowProofAtShortNumeralsExact
    (valueBit : Bool) (high : Nat)
    (hcanonical : high = 0 → valueBit = true) :
    CertifiedPAProof
      (binaryBitShortLiteralFormula
        ((Nat.bit valueBit high).testBit 0)
        0 (Nat.bit valueBit high)) :=
  CertifiedPAProof.cast (by simp)
    (binaryBitLowProofAtShortNumerals valueBit high hcanonical)

@[simp] theorem binaryBitLowProofAtShortNumeralsExact_payloadLength
    (valueBit : Bool) (high : Nat)
    (hcanonical : high = 0 → valueBit = true) :
    (binaryBitLowProofAtShortNumeralsExact
      valueBit high hcanonical).payloadLength =
      (binaryBitLowProofAtShortNumerals
        valueBit high hcanonical).payloadLength := by
  unfold binaryBitLowProofAtShortNumeralsExact
  simp only [CertifiedPAProof.cast_payloadLength]

noncomputable def binaryBitStepProofAtShortNumeralsExact
    (valueBit : Bool) (high index : Nat)
    (hcanonical : high = 0 → valueBit = true)
    (previous : CertifiedPAProof
      (binaryBitShortLiteralFormula
        (high.testBit index) index high)) :
    CertifiedPAProof
      (binaryBitShortLiteralFormula
        ((Nat.bit valueBit high).testBit (index + 1))
        (index + 1) (Nat.bit valueBit high)) :=
  CertifiedPAProof.cast (by simp [Nat.testBit_bit_succ])
    (binaryBitStepProofAtShortNumerals
      valueBit (high.testBit index) index high hcanonical previous)

@[simp] theorem binaryBitStepProofAtShortNumeralsExact_payloadLength
    (valueBit : Bool) (high index : Nat)
    (hcanonical : high = 0 → valueBit = true)
    (previous : CertifiedPAProof
      (binaryBitShortLiteralFormula
        (high.testBit index) index high)) :
    (binaryBitStepProofAtShortNumeralsExact
      valueBit high index hcanonical previous).payloadLength =
      (binaryBitStepProofAtShortNumerals
        valueBit (high.testBit index) index high hcanonical
        previous).payloadLength := by
  unfold binaryBitStepProofAtShortNumeralsExact
  simp only [CertifiedPAProof.cast_payloadLength]

structure PolynomiallyBoundedBinaryBitLiteralProof
    (value index : Nat) where
  proof : CertifiedPAProof
    (binaryBitShortLiteralFormula
      (value.testBit index) index value)
  payload_le :
    proof.payloadLength <=
      binaryBitRecursivePayloadPolynomial
        (binaryBitWorkBudget index value)

noncomputable def boundedBinaryBitZeroValueProof
    (index : Nat) :
    PolynomiallyBoundedBinaryBitLiteralProof 0 index where
  proof := binaryBitZeroValueProofAtShortIndexExact index
  payload_le := by
    let budget := binaryBitWorkBudget index 0
    have hindexSelf : Nat.size index <= index :=
      nat_size_le_self_short index
    have hindex : Nat.size index <= budget := by
      dsimp only [budget, binaryBitWorkBudget]
      exact hindexSelf.trans (by omega)
    have hbase :=
      binaryBitZeroValueNegativeProofAtShortIndex_payloadLength_le
        index budget hindex
    have hcumulative :=
      binaryBitBasePayloadEnvelope_le_cumulative
        (candidate := budget) (budget := budget) le_rfl
    rw [binaryBitZeroValueProofAtShortIndexExact_payloadLength]
    unfold binaryBitRecursivePayloadPolynomial
    exact hbase.trans <| hcumulative.trans (Nat.le_add_right _ _)

noncomputable def boundedBinaryBitLowProof
    (valueBit : Bool) (high : Nat)
    (hcanonical : high = 0 → valueBit = true) :
    PolynomiallyBoundedBinaryBitLiteralProof
      (Nat.bit valueBit high) 0 where
  proof := binaryBitLowProofAtShortNumeralsExact
    valueBit high hcanonical
  payload_le := by
    let value := Nat.bit valueBit high
    let budget := binaryBitWorkBudget 0 value
    have hnonzero : value ≠ 0 := by
      dsimp only [value]
      exact Nat.bit_ne_zero_iff.mpr hcanonical
    have hsize : Nat.size value = Nat.size high + 1 := by
      dsimp only [value]
      exact Nat.size_bit hnonzero
    have hhigh : Nat.size high <= budget := by
      dsimp only [budget, binaryBitWorkBudget]
      omega
    have hbase :=
      binaryBitLowProofAtShortNumerals_payloadLength_le
        valueBit high budget hcanonical hhigh
    have hcumulative :=
      binaryBitBasePayloadEnvelope_le_cumulative
        (candidate := budget) (budget := budget) le_rfl
    rw [binaryBitLowProofAtShortNumeralsExact_payloadLength]
    unfold binaryBitRecursivePayloadPolynomial
    exact hbase.trans <| hcumulative.trans (Nat.le_add_right _ _)

noncomputable def boundedBinaryBitStepProof
    (valueBit : Bool) (high index : Nat)
    (hcanonical : high = 0 → valueBit = true)
    (previous :
      PolynomiallyBoundedBinaryBitLiteralProof high index) :
    PolynomiallyBoundedBinaryBitLiteralProof
      (Nat.bit valueBit high) (index + 1) where
  proof := binaryBitStepProofAtShortNumeralsExact
    valueBit high index hcanonical previous.proof
  payload_le := by
    let value := Nat.bit valueBit high
    let sourceBudget := binaryBitWorkBudget index high
    let currentBudget := binaryBitWorkBudget (index + 1) value
    have hnonzero : value ≠ 0 := by
      dsimp only [value]
      exact Nat.bit_ne_zero_iff.mpr hcanonical
    have hsize : Nat.size value = Nat.size high + 1 := by
      dsimp only [value]
      exact Nat.size_bit hnonzero
    have hbudget : sourceBudget < currentBudget := by
      dsimp only [sourceBudget, currentBudget, binaryBitWorkBudget]
      omega
    have hindexSelf : Nat.size index <= index :=
      nat_size_le_self_short index
    have hnextSelf : Nat.size (index + 1) <= index + 2 := by
      have hraw := nat_size_le_self_short (index + 1)
      omega
    have hindex : Nat.size index <= currentBudget := by
      dsimp only [currentBudget, binaryBitWorkBudget]
      omega
    have hnextIndex : Nat.size (index + 1) <= currentBudget := by
      dsimp only [currentBudget, binaryBitWorkBudget]
      omega
    have hhigh : Nat.size high <= currentBudget := by
      dsimp only [currentBudget, binaryBitWorkBudget]
      omega
    have hstep :=
      binaryBitStepProofAtShortNumerals_payloadLength_le
        valueBit (high.testBit index) index high currentBudget
        hcanonical previous.proof hindex hnextIndex hhigh
    rw [binaryBitStepProofAtShortNumeralsExact_payloadLength]
    exact binaryBitPayloadStep_le_polynomial
      sourceBudget currentBudget previous.proof.payloadLength
      (binaryBitStepProofAtShortNumerals
        valueBit (high.testBit index) index high hcanonical
        previous.proof).payloadLength
      hbudget hstep previous.payload_le

noncomputable def boundedBinaryBitLiteralProof :
    (value : Nat) → (index : Nat) →
      PolynomiallyBoundedBinaryBitLiteralProof value index :=
  Nat.binaryRec'
    boundedBinaryBitZeroValueProof
    (fun valueBit high hcanonical previous index => by
      cases index with
      | zero =>
          exact boundedBinaryBitLowProof
            valueBit high hcanonical
      | succ index =>
          exact boundedBinaryBitStepProof
            valueBit high index hcanonical (previous index))

noncomputable def proveBinaryBitLiteralAtShortNumeralsPolynomial
    (value index : Nat) :
    CertifiedPAProof
      (binaryBitShortLiteralFormula
        (value.testBit index) index value) :=
  (boundedBinaryBitLiteralProof value index).proof

def binaryBitLiteralPayloadPolynomial
    (index value : Nat) : Nat :=
  binaryBitRecursivePayloadPolynomial
    (binaryBitWorkBudget index value)

theorem proveBinaryBitLiteralAtShortNumeralsPolynomial_payloadLength_le
    (index value : Nat) :
    (proveBinaryBitLiteralAtShortNumeralsPolynomial
      value index).payloadLength <=
      binaryBitLiteralPayloadPolynomial index value := by
  exact (boundedBinaryBitLiteralProof value index).payload_le

theorem proveBinaryBitLiteralAtShortNumeralsPolynomial_verifier_eq_true
    (index value : Nat) :
    listedCompactCertifiedPAProofVerifier
        (proveBinaryBitLiteralAtShortNumeralsPolynomial
          value index).code
        (compactFormulaCode
          (binaryBitShortLiteralFormula
            (value.testBit index) index value)) = true :=
  (proveBinaryBitLiteralAtShortNumeralsPolynomial
    value index).verifier_eq_true

theorem proveBinaryBitLiteralAtShortNumerals_checked_polynomial
    (index value : Nat) :
    listedCompactCertifiedPAProofVerifier
        (proveBinaryBitLiteralAtShortNumeralsPolynomial
          value index).code
        (compactFormulaCode
          (binaryBitShortLiteralFormula
            (value.testBit index) index value)) = true ∧
      (proveBinaryBitLiteralAtShortNumeralsPolynomial
        value index).payloadLength <=
        binaryBitLiteralPayloadPolynomial index value := by
  exact ⟨
    proveBinaryBitLiteralAtShortNumeralsPolynomial_verifier_eq_true
      index value,
    proveBinaryBitLiteralAtShortNumeralsPolynomial_payloadLength_le
      index value⟩

#print axioms binaryBitStepFormula_code_le_stageThree
#print axioms binaryBitZeroValueNegativeProof_payloadLength_le_envelope
#print axioms binaryBitLowProof_payloadLength_le_envelope
#print axioms binaryBitStepImplication_payloadLength_le_envelope
#print axioms binaryBitStepProofAtShortNumerals_payloadLength_le
#print axioms binaryBitZeroValueNegativeProofAtShortIndex_payloadLength_le
#print axioms binaryBitLowProofAtShortNumerals_payloadLength_le
#print axioms binaryBitPayloadStep_le_polynomial
#print axioms
  proveBinaryBitLiteralAtShortNumeralsPolynomial_payloadLength_le
#print axioms
  proveBinaryBitLiteralAtShortNumeralsPolynomial_verifier_eq_true
#print axioms
  proveBinaryBitLiteralAtShortNumerals_checked_polynomial

end FoundationCompactPABitMembershipRuleCompilerBounds
