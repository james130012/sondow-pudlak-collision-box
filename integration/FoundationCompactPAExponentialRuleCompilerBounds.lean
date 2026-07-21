import integration.FoundationCompactPAExponentialRuleCompiler
import integration.FoundationCompactPABinaryNumeralAdditionBounds

/-!
# Polynomial bounds for the fast PA exponential-graph compiler

The logical compiler proves `expDef(2^height, height)` by iterating one fixed
PA successor theorem.  This file accounts for the complete proof and
structural-certificate payload.  All envelopes below are explicit fixed
polynomial expressions in `height`; no proof-length or short-proof hypothesis
is an input.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAExponentialRuleCompilerBounds

set_option maxHeartbeats 300000

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAExponentialRuleCompiler
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactCertifiedModusPonens
open FoundationCompactListedCertifiedVerifier

def exponentialExponentTermStepCode : Nat :=
  (binaryTermCode (Rew.emb (closedNumeralTerm 1))).length +
    binaryFunctionTermCodeOverhead Language.Add.add

def exponentialValueTermStepCode : Nat :=
  (binaryTermCode (Rew.emb (closedNumeralTerm 2))).length +
    binaryFunctionTermCodeOverhead Language.Mul.mul

def exponentialExponentTermCodePolynomial (height : Nat) : Nat :=
  (binaryTermCode (exponentialExponentTerm 0)).length +
    height * exponentialExponentTermStepCode

def exponentialValueTermCodePolynomial (height : Nat) : Nat :=
  (binaryTermCode (exponentialPowerValueTerm 0)).length +
    height * exponentialValueTermStepCode

theorem exponentialExponentTerm_code_length_le
    (height : Nat) :
    (binaryTermCode (exponentialExponentTerm height)).length <=
      exponentialExponentTermCodePolynomial height := by
  induction height with
  | zero =>
      simp [exponentialExponentTermCodePolynomial]
  | succ height ih =>
      have hstep := paAddTerm_code_length_le
        (exponentialExponentTerm height)
        (Rew.emb (closedNumeralTerm 1))
      rw [exponentialExponentTerm]
      have hformula :
          ‘(!!(exponentialExponentTerm height) + 1)’ =
            paAddTerm (exponentialExponentTerm height)
              (Rew.emb (closedNumeralTerm 1)) := by
        simp [paAddTerm, closedNumeralTerm]
      rw [hformula]
      calc
        (binaryTermCode
            (paAddTerm (exponentialExponentTerm height)
              (Rew.emb (closedNumeralTerm 1)))).length <=
            (binaryTermCode (exponentialExponentTerm height)).length +
              (binaryTermCode (Rew.emb (closedNumeralTerm 1))).length +
              binaryFunctionTermCodeOverhead Language.Add.add :=
          hstep
        _ <= exponentialExponentTermCodePolynomial height +
              exponentialExponentTermStepCode := by
          unfold exponentialExponentTermStepCode
          omega
        _ = exponentialExponentTermCodePolynomial (height + 1) := by
          unfold exponentialExponentTermCodePolynomial
          ring

theorem exponentialPowerValueTerm_code_length_le
    (height : Nat) :
    (binaryTermCode (exponentialPowerValueTerm height)).length <=
      exponentialValueTermCodePolynomial height := by
  induction height with
  | zero =>
      simp [exponentialValueTermCodePolynomial]
  | succ height ih =>
      have hstep := paMulTerm_code_length_le
        (Rew.emb (closedNumeralTerm 2))
        (exponentialPowerValueTerm height)
      rw [exponentialPowerValueTerm]
      have hformula :
          ‘(2 * !!(exponentialPowerValueTerm height))’ =
            paMulTerm (Rew.emb (closedNumeralTerm 2))
              (exponentialPowerValueTerm height) := by
        simp [paMulTerm, closedNumeralTerm]
      rw [hformula]
      calc
        (binaryTermCode
            (paMulTerm (Rew.emb (closedNumeralTerm 2))
              (exponentialPowerValueTerm height))).length <=
            (binaryTermCode (Rew.emb (closedNumeralTerm 2))).length +
              (binaryTermCode (exponentialPowerValueTerm height)).length +
              binaryFunctionTermCodeOverhead Language.Mul.mul :=
          hstep
        _ <= exponentialValueTermCodePolynomial height +
              exponentialValueTermStepCode := by
          unfold exponentialValueTermStepCode
          omega
        _ = exponentialValueTermCodePolynomial (height + 1) := by
          unfold exponentialValueTermCodePolynomial
          ring

def exponentialTermCodeEnvelope (height : Nat) : Nat :=
  exponentialExponentTermCodePolynomial height +
    exponentialValueTermCodePolynomial height + 1

theorem exponentialExponentTerm_code_length_le_envelope
    (height : Nat) :
    (binaryTermCode (exponentialExponentTerm height)).length <=
      exponentialTermCodeEnvelope height := by
  exact (exponentialExponentTerm_code_length_le height).trans <| by
    simp [exponentialTermCodeEnvelope]
    omega

theorem exponentialPowerValueTerm_code_length_le_envelope
    (height : Nat) :
    (binaryTermCode (exponentialPowerValueTerm height)).length <=
      exponentialTermCodeEnvelope height := by
  exact (exponentialPowerValueTerm_code_length_le height).trans <| by
    simp [exponentialTermCodeEnvelope]
    omega

theorem exponentialTermCodeEnvelope_mono
    {small large : Nat} (h : small <= large) :
    exponentialTermCodeEnvelope small <=
      exponentialTermCodeEnvelope large := by
  unfold exponentialTermCodeEnvelope
    exponentialExponentTermCodePolynomial
    exponentialValueTermCodePolynomial
  gcongr

def exponentialPowerFormula (height : Nat) :
    LO.FirstOrder.ArithmeticProposition :=
  “!expDef !!(exponentialPowerValueTerm height)
      !!(exponentialExponentTerm height)”

def exponentialSuccFormulaSeed : Nat :=
  (binaryFormulaCode exponentialSuccOuterBody).length

def exponentialSuccFormulaStageOne (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope exponentialSuccFormulaSeed termBound

def exponentialSuccFormulaStageTwo (termBound : Nat) : Nat :=
  substitutionFormulaCodeEnvelope
    (exponentialSuccFormulaStageOne termBound) termBound

theorem exponentialSuccValueBody_code_length_le
    (height termBound : Nat)
    (hterm :
      exponentialTermCodeEnvelope height <= termBound) :
    (binaryFormulaCode
      (exponentialSuccValueBody
        (exponentialExponentTerm height))).length <=
      exponentialSuccFormulaStageOne termBound := by
  apply instantiatedBodyCode_le_nextStage
    exponentialSuccOuterBody
    (exponentialSuccValueBody (exponentialExponentTerm height))
    (exponentialExponentTerm height)
    exponentialSuccFormulaSeed termBound
  · exact le_rfl
  · exact (exponentialExponentTerm_code_length_le_envelope height).trans
      hterm
  · exact exponentialSuccAfterExponent_formula
      (exponentialExponentTerm height)

theorem exponentialPowerStep_formula_code_length_le
    (height : Nat) :
    (binaryFormulaCode
      (exponentialPowerFormula height 🡒
        exponentialPowerFormula (height + 1))).length <=
      exponentialSuccFormulaStageTwo
        (exponentialTermCodeEnvelope (height + 1)) := by
  let termBound := exponentialTermCodeEnvelope (height + 1)
  have hheight : height <= height + 1 := by omega
  have henvelope :
      exponentialTermCodeEnvelope height <= termBound :=
    exponentialTermCodeEnvelope_mono hheight
  have hbody := exponentialSuccValueBody_code_length_le
    height termBound henvelope
  have hvalue :
      (binaryTermCode
        (exponentialPowerValueTerm height)).length <= termBound :=
    (exponentialPowerValueTerm_code_length_le_envelope height).trans
      henvelope
  have hsubstitution :=
    binaryFormulaCode_substitution_one_length_le_envelope
      (exponentialSuccValueBody (exponentialExponentTerm height))
      (exponentialPowerValueTerm height)
      (exponentialSuccFormulaStageOne termBound) termBound
      hbody hvalue
  rw [exponentialSuccImplicationRaw_formula
    (exponentialExponentTerm height)
    (exponentialPowerValueTerm height)] at hsubstitution
  rw [exponentialPowerStep_formula height] at hsubstitution
  simpa [exponentialPowerFormula, exponentialSuccFormulaStageTwo,
    termBound] using hsubstitution

theorem binaryFormulaCode_antecedent_le_implication
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) :
    (binaryFormulaCode antecedent).length <=
      2 * (binaryFormulaCode (antecedent 🡒 consequent)).length := by
  have hdoubleNeg := binaryFormulaCode_neg_length_le (∼antecedent)
  have hnegInImplication :
      (binaryFormulaCode (∼antecedent)).length <=
        (binaryFormulaCode (antecedent 🡒 consequent)).length := by
    rw [show antecedent 🡒 consequent =
      (∼antecedent) ⋎ consequent by simp [DeMorgan.imply]]
    simp [binaryFormulaCode]
    omega
  have hdoubleNegFormula : (∼∼antecedent) = antecedent := by
    simp
  rw [hdoubleNegFormula] at hdoubleNeg
  have hscaled := Nat.mul_le_mul_left 2 hnegInImplication
  exact hdoubleNeg.trans hscaled

theorem binaryFormulaCode_consequent_le_implication
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) :
    (binaryFormulaCode consequent).length <=
      (binaryFormulaCode (antecedent 🡒 consequent)).length := by
  rw [show antecedent 🡒 consequent =
    (∼antecedent) ⋎ consequent by simp [DeMorgan.imply]]
  simp [binaryFormulaCode]
  omega

theorem exponentialPowerFormula_code_length_le_step
    (height : Nat) :
    (binaryFormulaCode (exponentialPowerFormula height)).length <=
      2 * exponentialSuccFormulaStageTwo
        (exponentialTermCodeEnvelope (height + 1)) := by
  have himplication :=
    exponentialPowerStep_formula_code_length_le height
  exact
    (binaryFormulaCode_antecedent_le_implication
      (exponentialPowerFormula height)
      (exponentialPowerFormula (height + 1))).trans
      (Nat.mul_le_mul_left 2 himplication)

theorem exponentialPowerNextFormula_code_length_le_step
    (height : Nat) :
    (binaryFormulaCode
      (exponentialPowerFormula (height + 1))).length <=
      2 * exponentialSuccFormulaStageTwo
        (exponentialTermCodeEnvelope (height + 1)) := by
  have himplication :=
    exponentialPowerStep_formula_code_length_le height
  have hconsequent :=
    (binaryFormulaCode_consequent_le_implication
      (exponentialPowerFormula height)
      (exponentialPowerFormula (height + 1))).trans
      himplication
  exact hconsequent.trans <| by omega

def exponentialSpecializationCostEnvelope
    (formulaBound termBound : Nat) : Nat :=
  192 + 2048 * (formulaBound + termBound + 1) *
    (formulaBound + termBound + 1) *
    (formulaBound + termBound + 1)

theorem specializationCost_le_exponentialEnvelope
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (formulaBound termBound : Nat)
    (hformula : (binaryFormulaCode formula).length <= formulaBound)
    (hterm : (binaryTermCode term).length <= termBound) :
    specializationCost formula term <=
      exponentialSpecializationCostEnvelope formulaBound termBound := by
  have hscale :
      specializationScale formula term <=
        formulaBound + termBound + 1 := by
    simp [specializationScale]
    omega
  unfold specializationCost exponentialSpecializationCostEnvelope
  gcongr

def exponentialSuccImplicationPayloadEnvelope
    (termBound : Nat) : Nat :=
  exponentialSuccCertifiedProof.payloadLength +
    exponentialSpecializationCostEnvelope
      exponentialSuccFormulaSeed termBound +
    exponentialSpecializationCostEnvelope
      (exponentialSuccFormulaStageOne termBound) termBound

theorem exponentialSuccImplication_payloadLength_le_envelope
    (height : Nat) :
    (exponentialSuccImplication
      (exponentialExponentTerm height)
      (exponentialPowerValueTerm height)).payloadLength <=
      exponentialSuccImplicationPayloadEnvelope
        (exponentialTermCodeEnvelope height) := by
  let termBound := exponentialTermCodeEnvelope height
  have hexponent :=
    exponentialExponentTerm_code_length_le_envelope height
  have hvalue :=
    exponentialPowerValueTerm_code_length_le_envelope height
  have hbody := exponentialSuccValueBody_code_length_le
    height termBound le_rfl
  have hfirst := specializationCost_le_exponentialEnvelope
    exponentialSuccOuterBody (exponentialExponentTerm height)
    exponentialSuccFormulaSeed termBound le_rfl hexponent
  have hsecond := specializationCost_le_exponentialEnvelope
    (exponentialSuccValueBody (exponentialExponentTerm height))
    (exponentialPowerValueTerm height)
    (exponentialSuccFormulaStageOne termBound) termBound
    hbody hvalue
  have hraw := exponentialSuccImplication_payloadLength_le
    (exponentialExponentTerm height)
    (exponentialPowerValueTerm height)
  unfold exponentialSuccImplicationPayloadEnvelope
  dsimp only [termBound] at hfirst hsecond hraw ⊢
  omega

theorem substitutionFormulaCodeEnvelope_mono_exponential
    {smallFormula largeFormula smallTerm largeTerm : Nat}
    (hformula : smallFormula <= largeFormula)
    (hterm : smallTerm <= largeTerm) :
    substitutionFormulaCodeEnvelope smallFormula smallTerm <=
      substitutionFormulaCodeEnvelope largeFormula largeTerm := by
  unfold substitutionFormulaCodeEnvelope
  gcongr

theorem exponentialSuccFormulaStageOne_mono
    {small large : Nat} (h : small <= large) :
    exponentialSuccFormulaStageOne small <=
      exponentialSuccFormulaStageOne large := by
  apply substitutionFormulaCodeEnvelope_mono_exponential le_rfl h

theorem exponentialSuccFormulaStageTwo_mono
    {small large : Nat} (h : small <= large) :
    exponentialSuccFormulaStageTwo small <=
      exponentialSuccFormulaStageTwo large := by
  apply substitutionFormulaCodeEnvelope_mono_exponential
  · exact exponentialSuccFormulaStageOne_mono h
  · exact h

theorem exponentialSpecializationCostEnvelope_mono
    {smallFormula largeFormula smallTerm largeTerm : Nat}
    (hformula : smallFormula <= largeFormula)
    (hterm : smallTerm <= largeTerm) :
    exponentialSpecializationCostEnvelope smallFormula smallTerm <=
      exponentialSpecializationCostEnvelope largeFormula largeTerm := by
  unfold exponentialSpecializationCostEnvelope
  gcongr

theorem exponentialSuccImplicationPayloadEnvelope_mono
    {small large : Nat} (h : small <= large) :
    exponentialSuccImplicationPayloadEnvelope small <=
      exponentialSuccImplicationPayloadEnvelope large := by
  unfold exponentialSuccImplicationPayloadEnvelope
  have hfirst := exponentialSpecializationCostEnvelope_mono
    (smallFormula := exponentialSuccFormulaSeed)
    (largeFormula := exponentialSuccFormulaSeed)
    (smallTerm := small) (largeTerm := large) le_rfl h
  have hsecond := exponentialSpecializationCostEnvelope_mono
    (smallFormula := exponentialSuccFormulaStageOne small)
    (largeFormula := exponentialSuccFormulaStageOne large)
    (smallTerm := small) (largeTerm := large)
    (exponentialSuccFormulaStageOne_mono h) h
  omega

def exponentialPowerStepPayloadEnvelope (termBound : Nat) : Nat :=
  exponentialSuccImplicationPayloadEnvelope termBound +
    240 + 34 * paAssemblySyntaxEnvelope
      (2 * exponentialSuccFormulaStageTwo termBound)

theorem exponentialPowerStepPayloadEnvelope_mono
    {small large : Nat} (h : small <= large) :
    exponentialPowerStepPayloadEnvelope small <=
      exponentialPowerStepPayloadEnvelope large := by
  have himplication :=
    exponentialSuccImplicationPayloadEnvelope_mono h
  have hformula := exponentialSuccFormulaStageTwo_mono h
  unfold exponentialPowerStepPayloadEnvelope paAssemblySyntaxEnvelope
  gcongr

theorem proveExponentialPower_succ_payloadLength_le
    (height : Nat) :
    (proveExponentialPower (height + 1)).payloadLength <=
      (proveExponentialPower height).payloadLength +
        exponentialPowerStepPayloadEnvelope
          (exponentialTermCodeEnvelope (height + 1)) := by
  let antecedent := exponentialPowerFormula height
  let consequent := exponentialPowerFormula (height + 1)
  let termBound := exponentialTermCodeEnvelope (height + 1)
  let formulaBound := 2 * exponentialSuccFormulaStageTwo termBound
  let implicationProof :=
    CertifiedPAProof.cast
      (exponentialPowerStep_formula height)
      (exponentialSuccImplication
        (exponentialExponentTerm height)
        (exponentialPowerValueTerm height))
  have hmp := CertifiedPAProof.modusPonens_payloadLength_le
    implicationProof (proveExponentialPower height)
  have htermMono :
      exponentialTermCodeEnvelope height <= termBound :=
    exponentialTermCodeEnvelope_mono (by omega)
  have himplicationRaw :=
    exponentialSuccImplication_payloadLength_le_envelope height
  have himplication :
      implicationProof.payloadLength <=
        exponentialSuccImplicationPayloadEnvelope termBound := by
    have hcast :
        implicationProof.payloadLength =
          (exponentialSuccImplication
            (exponentialExponentTerm height)
            (exponentialPowerValueTerm height)).payloadLength :=
      CertifiedPAProof.cast_payloadLength
        (exponentialPowerStep_formula height)
        (exponentialSuccImplication
          (exponentialExponentTerm height)
          (exponentialPowerValueTerm height))
    rw [hcast]
    exact himplicationRaw.trans
      (exponentialSuccImplicationPayloadEnvelope_mono htermMono)
  have hantecedent :
      (binaryFormulaCode antecedent).length <= formulaBound := by
    simpa [antecedent, formulaBound, termBound] using
      (exponentialPowerFormula_code_length_le_step height)
  have hconsequent :
      (binaryFormulaCode consequent).length <= formulaBound := by
    simpa [consequent, formulaBound, termBound] using
      (exponentialPowerNextFormula_code_length_le_step height)
  have hsyntax :=
    modusPonensSyntaxBudget_le_paAssemblyEnvelope
      antecedent consequent formulaBound hantecedent hconsequent
  have hsyntax' :
      modusPonensSyntaxBudget
          (“!expDef !!(exponentialPowerValueTerm height)
              !!(exponentialExponentTerm height)” :
            LO.FirstOrder.ArithmeticProposition)
          (“!expDef !!(exponentialPowerValueTerm (height + 1))
              !!(exponentialExponentTerm (height + 1))” :
            LO.FirstOrder.ArithmeticProposition) <=
        paAssemblySyntaxEnvelope formulaBound := by
    simpa [antecedent, consequent, exponentialPowerFormula] using hsyntax
  change
    (CertifiedPAProof.modusPonens implicationProof
      (proveExponentialPower height)).payloadLength <= _
  unfold exponentialPowerStepPayloadEnvelope
  dsimp only [termBound, formulaBound] at himplication hsyntax' ⊢
  omega

def exponentialPowerPayloadStep (height : Nat) : Nat :=
  exponentialPowerStepPayloadEnvelope
    (exponentialTermCodeEnvelope height)

theorem exponentialPowerPayloadStep_mono :
    Monotone exponentialPowerPayloadStep := by
  intro small large h
  exact exponentialPowerStepPayloadEnvelope_mono
    (exponentialTermCodeEnvelope_mono h)

def monotonePayloadRecurrence
    (base : Nat) (step : Nat → Nat) : Nat → Nat
  | 0 => base
  | height + 1 =>
      monotonePayloadRecurrence base step height + step (height + 1)

def exponentialPowerPayloadRecurrence (height : Nat) : Nat :=
  monotonePayloadRecurrence exponentialPowerZeroProof.payloadLength
    exponentialPowerPayloadStep height

def exponentialPowerPayloadPolynomial (height : Nat) : Nat :=
  exponentialPowerZeroProof.payloadLength +
    height * exponentialPowerPayloadStep height

theorem base_add_mul_succ
    (base height step : Nat) :
    (base + height * step) + step =
      base + (height + 1) * step := by
  ring

theorem monotonePayloadRecurrence_le_final_step
    (base : Nat) (step : Nat → Nat)
    (hmono : Monotone step) (height : Nat) :
    monotonePayloadRecurrence base step height <=
      base + height * step height := by
  induction height with
  | zero =>
      simp [monotonePayloadRecurrence]
  | succ height ih =>
      have hstep : step height <= step (height + 1) :=
        hmono (by omega)
      rw [monotonePayloadRecurrence]
      calc
        monotonePayloadRecurrence base step height + step (height + 1) <=
            (base + height * step height) + step (height + 1) :=
          Nat.add_le_add_right ih _
        _ <= (base + height * step (height + 1)) +
              step (height + 1) := by
          exact Nat.add_le_add_right
            (Nat.add_le_add_left
              (Nat.mul_le_mul_left height hstep) base)
            _
        _ = base + (height + 1) * step (height + 1) :=
          base_add_mul_succ _ _ _

theorem proveExponentialPower_payloadLength_le_recurrence
    (height : Nat) :
    (proveExponentialPower height).payloadLength <=
      exponentialPowerPayloadRecurrence height := by
  induction height with
  | zero =>
      simp [proveExponentialPower, exponentialPowerPayloadRecurrence,
        monotonePayloadRecurrence]
  | succ height ih =>
      have hstep := proveExponentialPower_succ_payloadLength_le height
      change
        (proveExponentialPower (height + 1)).payloadLength <=
          monotonePayloadRecurrence
            exponentialPowerZeroProof.payloadLength
            exponentialPowerPayloadStep (height + 1)
      rw [monotonePayloadRecurrence]
      have hstep' :
          (proveExponentialPower (height + 1)).payloadLength <=
            (proveExponentialPower height).payloadLength +
              exponentialPowerPayloadStep (height + 1) := by
        simpa only [exponentialPowerPayloadStep] using hstep
      exact hstep'.trans (Nat.add_le_add_right ih _)

theorem exponentialPowerPayloadRecurrence_le_polynomial
    (height : Nat) :
    exponentialPowerPayloadRecurrence height <=
      exponentialPowerPayloadPolynomial height := by
  exact monotonePayloadRecurrence_le_final_step
    exponentialPowerZeroProof.payloadLength
    exponentialPowerPayloadStep
    exponentialPowerPayloadStep_mono height

theorem proveExponentialPower_payloadLength_le_polynomial
    (height : Nat) :
    (proveExponentialPower height).payloadLength <=
      exponentialPowerPayloadPolynomial height := by
  exact (proveExponentialPower_payloadLength_le_recurrence height).trans
    (exponentialPowerPayloadRecurrence_le_polynomial height)

theorem proveExponentialPower_checked_polynomial
    (height : Nat) :
    listedCompactCertifiedPAProofVerifier
        (proveExponentialPower height).code
        (compactFormulaCode (exponentialPowerFormula height)) = true ∧
      (proveExponentialPower height).payloadLength <=
        exponentialPowerPayloadPolynomial height := by
  constructor
  · simpa [exponentialPowerFormula] using
      proveExponentialPower_verifier_eq_true height
  · exact proveExponentialPower_payloadLength_le_polynomial height

#print axioms exponentialExponentTerm_code_length_le
#print axioms exponentialPowerValueTerm_code_length_le
#print axioms exponentialTermCodeEnvelope_mono
#print axioms exponentialPowerStep_formula_code_length_le
#print axioms exponentialSuccImplication_payloadLength_le_envelope
#print axioms proveExponentialPower_payloadLength_le_polynomial
#print axioms proveExponentialPower_checked_polynomial

end FoundationCompactPAExponentialRuleCompilerBounds
