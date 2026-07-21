import integration.FoundationCompactPAExponentialShortNumeralCompiler
import integration.FoundationCompactPAExponentialRuleCompilerBounds
import integration.FoundationCompactPABinaryNumeralAdditionBounds

/-!
# Polynomial bounds for the exact short-binary exponential compiler

The logical compiler transports the recursive proof of
`expDef(2^height, height)` to the exact short-binary numeral coordinate used by
the direct proof predicate.  This file accounts for the complete payload of
the two equality bridges.  The bounds are built from the concrete checked PA
constructors; no proof-length or short-proof assumption is an input.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAExponentialShortNumeralCompilerBounds

set_option maxHeartbeats 300000

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeEqualityTransitivity
open FoundationCompactPAQuantitativeFunctionCongruence
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExponentialRuleCompiler
open FoundationCompactPAExponentialRuleCompilerBounds
open FoundationCompactPAExponentialShortNumeralCompiler

theorem nat_size_le_self_short (value : Nat) :
    Nat.size value <= value := by
  rw [Nat.size_le]
  exact value.lt_two_pow_self

theorem binaryNumeralTermCodeEnvelope_mono_short
    {small large : Nat} (h : small <= large) :
    binaryNumeralTermCodeEnvelope small <=
      binaryNumeralTermCodeEnvelope large := by
  unfold binaryNumeralTermCodeEnvelope
  gcongr

/--
One bound for every term occurring in the transition whose target height is
`height`.  The extra binary digit covers the value numeral `2^height`.
-/
def exponentialShortTermCodeEnvelope (height : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope (height + 1) +
    exponentialTermCodeEnvelope height +
    (binaryTermCode paOneTerm).length +
    (binaryTermCode arithmeticTwoTerm).length +
    binaryFunctionTermCodeOverhead Language.Add.add +
    binaryFunctionTermCodeOverhead Language.Mul.mul + 1

theorem exponentialShortTermCodeEnvelope_mono
    {small large : Nat} (h : small <= large) :
    exponentialShortTermCodeEnvelope small <=
      exponentialShortTermCodeEnvelope large := by
  have hbinary :
      binaryNumeralTermCodeEnvelope (small + 1) <=
        binaryNumeralTermCodeEnvelope (large + 1) :=
    binaryNumeralTermCodeEnvelope_mono_short (by omega)
  have hexponential :
      exponentialTermCodeEnvelope small <=
        exponentialTermCodeEnvelope large :=
    exponentialTermCodeEnvelope_mono h
  unfold exponentialShortTermCodeEnvelope
  omega

theorem shortBinaryNumeralTerm_code_le_shortEnvelope
    (value height : Nat)
    (hsize : Nat.size value <= height + 1) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      exponentialShortTermCodeEnvelope height := by
  have hcode := binaryNumeralTerm_code_length_le_envelope
    value (height + 1) hsize
  unfold exponentialShortTermCodeEnvelope
  omega

theorem exponentialExponentTerm_code_le_shortEnvelope
    (sourceHeight targetHeight : Nat)
    (hheight : sourceHeight <= targetHeight) :
    (binaryTermCode (exponentialExponentTerm sourceHeight)).length <=
      exponentialShortTermCodeEnvelope targetHeight := by
  have hcode :=
    exponentialExponentTerm_code_length_le_envelope sourceHeight
  have henvelope :=
    exponentialTermCodeEnvelope_mono hheight
  unfold exponentialShortTermCodeEnvelope
  omega

theorem exponentialPowerValueTerm_code_le_shortEnvelope
    (sourceHeight targetHeight : Nat)
    (hheight : sourceHeight <= targetHeight) :
    (binaryTermCode (exponentialPowerValueTerm sourceHeight)).length <=
      exponentialShortTermCodeEnvelope targetHeight := by
  have hcode :=
    exponentialPowerValueTerm_code_length_le_envelope sourceHeight
  have henvelope :=
    exponentialTermCodeEnvelope_mono hheight
  unfold exponentialShortTermCodeEnvelope
  omega

theorem paOneTerm_code_le_shortEnvelope (height : Nat) :
    (binaryTermCode paOneTerm).length <=
      exponentialShortTermCodeEnvelope height := by
  unfold exponentialShortTermCodeEnvelope
  omega

theorem arithmeticTwoTerm_code_le_shortEnvelope (height : Nat) :
    (binaryTermCode arithmeticTwoTerm).length <=
      exponentialShortTermCodeEnvelope height := by
  unfold exponentialShortTermCodeEnvelope
  omega

/-! ## Monotonicity of the concrete primitive cost ledger -/

theorem substitutionFormulaCodeEnvelope_mono_short
    {smallFormula largeFormula smallTerm largeTerm : Nat}
    (hformula : smallFormula <= largeFormula)
    (hterm : smallTerm <= largeTerm) :
    substitutionFormulaCodeEnvelope smallFormula smallTerm <=
      substitutionFormulaCodeEnvelope largeFormula largeTerm := by
  unfold substitutionFormulaCodeEnvelope
  gcongr

theorem instantiatedFormulaCodeEnvelope_mono_short
    {small large : Nat} (h : small <= large) :
    instantiatedFormulaCodeEnvelope small <=
      instantiatedFormulaCodeEnvelope large := by
  have hstageOne := substitutionFormulaCodeEnvelope_mono_short
    (smallFormula := instantiatedFormulaStage0)
    (largeFormula := instantiatedFormulaStage0) le_rfl h
  change instantiatedFormulaStage1 small <=
    instantiatedFormulaStage1 large at hstageOne
  have hstageTwo := substitutionFormulaCodeEnvelope_mono_short
    hstageOne h
  change instantiatedFormulaStage2 small <=
    instantiatedFormulaStage2 large at hstageTwo
  have hstageThree := substitutionFormulaCodeEnvelope_mono_short
    hstageTwo h
  change instantiatedFormulaStage3 small <=
    instantiatedFormulaStage3 large at hstageThree
  have hstageFour := substitutionFormulaCodeEnvelope_mono_short
    hstageThree h
  change instantiatedFormulaStage4 small <=
    instantiatedFormulaStage4 large at hstageFour
  unfold instantiatedFormulaCodeEnvelope
  omega

theorem paFormulaCodeEnvelope_mono_short
    {small large : Nat} (h : small <= large) :
    paFormulaCodeEnvelope small <= paFormulaCodeEnvelope large := by
  have hinstantiated := instantiatedFormulaCodeEnvelope_mono_short h
  unfold paFormulaCodeEnvelope paEqualityFormulaCodeEnvelope
  omega

theorem paAssemblySyntaxEnvelope_mono_short
    {small large : Nat} (h : small <= large) :
    paAssemblySyntaxEnvelope small <= paAssemblySyntaxEnvelope large := by
  unfold paAssemblySyntaxEnvelope
  omega

theorem paPrimitiveAssemblyCostEnvelope_mono_short
    {small large : Nat} (h : small <= large) :
    paPrimitiveAssemblyCostEnvelope small <=
      paPrimitiveAssemblyCostEnvelope large := by
  have hformula := paFormulaCodeEnvelope_mono_short h
  have hderived := paAssemblySyntaxEnvelope_mono_short hformula
  have hlocal := paAssemblySyntaxEnvelope_mono_short hderived
  exact paAssemblySyntaxEnvelope_mono_short hlocal

theorem paSpecializationCostEnvelope_mono_short
    {small large : Nat} (h : small <= large) :
    paSpecializationCostEnvelope small <=
      paSpecializationCostEnvelope large := by
  have hformula := instantiatedFormulaCodeEnvelope_mono_short h
  have hscale :
      paSpecializationScaleEnvelope small <=
        paSpecializationScaleEnvelope large := by
    unfold paSpecializationScaleEnvelope
    omega
  unfold paSpecializationCostEnvelope
  gcongr

theorem paPrimitiveCostEnvelope_mono_short
    {small large : Nat} (h : small <= large) :
    paPrimitiveCostEnvelope small <= paPrimitiveCostEnvelope large := by
  have hspecialization := paSpecializationCostEnvelope_mono_short h
  have hformula := paFormulaCodeEnvelope_mono_short h
  have hderived := paAssemblySyntaxEnvelope_mono_short hformula
  have hlocal := paAssemblySyntaxEnvelope_mono_short hderived
  have hprimitive := paAssemblySyntaxEnvelope_mono_short hlocal
  have hlocalAlias :
      paLocalAssemblyCostEnvelope small <=
        paLocalAssemblyCostEnvelope large := by
    unfold paLocalAssemblyCostEnvelope paDerivedFormulaCodeEnvelope
    exact hlocal
  have hprimitiveAlias :
      paPrimitiveAssemblyCostEnvelope small <=
        paPrimitiveAssemblyCostEnvelope large :=
    paPrimitiveAssemblyCostEnvelope_mono_short h
  unfold paPrimitiveCostEnvelope
  omega

theorem paGeneratedTermCodeEnvelope_mono_short
    {small large : Nat} (h : small <= large) :
    paGeneratedTermCodeEnvelope small <=
      paGeneratedTermCodeEnvelope large := by
  have hbinary := binaryNumeralTermCodeEnvelope_mono_short h
  unfold paGeneratedTermCodeEnvelope paGeneratedTermAtomEnvelope
    paTermCodeBaseEnvelope
  omega

theorem paAlgebraStepCostEnvelope_mono_short
    {small large : Nat} (h : small <= large) :
    paAlgebraStepCostEnvelope small <=
      paAlgebraStepCostEnvelope large := by
  have hterms := paGeneratedTermCodeEnvelope_mono_short h
  have hprimitive := paPrimitiveCostEnvelope_mono_short hterms
  unfold paAlgebraStepCostEnvelope
  gcongr

theorem paIncrementLocalCostEnvelope_mono_short
    {small large : Nat} (h : small <= large) :
    paIncrementLocalCostEnvelope small <=
      paIncrementLocalCostEnvelope large := by
  have hstep := paAlgebraStepCostEnvelope_mono_short h
  unfold paIncrementLocalCostEnvelope
  gcongr

theorem binaryNumeralIncrementPayloadPolynomial_mono_short
    {small large : Nat} (h : small <= large) :
    binaryNumeralIncrementPayloadPolynomial small <=
      binaryNumeralIncrementPayloadPolynomial large := by
  have hlocal := paIncrementLocalCostEnvelope_mono_short h
  unfold binaryNumeralIncrementPayloadPolynomial
  gcongr

/-! ## One-step payload bounds for the two direct equality compilers -/

def exponentialShortDirectStepPayloadEnvelope (height : Nat) : Nat :=
  binaryNumeralIncrementPayloadPolynomial height +
    8 * paPrimitiveCostEnvelope
      (exponentialShortTermCodeEnvelope height)

theorem exponentialShortDirectStepPayloadEnvelope_mono :
    Monotone exponentialShortDirectStepPayloadEnvelope := by
  intro small large h
  have hincrement :=
    binaryNumeralIncrementPayloadPolynomial_mono_short h
  have hterms := exponentialShortTermCodeEnvelope_mono h
  have hprimitive := paPrimitiveCostEnvelope_mono_short hterms
  unfold exponentialShortDirectStepPayloadEnvelope
  gcongr

theorem exponentialExponentShortToRecursiveDirectProof_succ_payloadLength_le
    (height : Nat) :
    (exponentialExponentShortToRecursiveDirectProof
      (height + 1)).payloadLength <=
      (exponentialExponentShortToRecursiveDirectProof height).payloadLength +
        exponentialShortDirectStepPayloadEnvelope (height + 1) := by
  let previous :=
    exponentialExponentShortToRecursiveDirectProof height
  let source := paAddTerm
    (shortBinaryNumeralTerm height) paOneTerm
  let target := paAddTerm
    (exponentialExponentTerm height) paOneTerm
  let increment := proveBinaryNumeralIncrement height
  let incrementReverse := proveEqualitySymmetry source
    (shortBinaryNumeralTerm (height + 1)) increment
  let reflexivity := proveEqualityReflexivityAtTerm paOneTerm
  let congruenceRaw := proveAddCongruence
    (shortBinaryNumeralTerm height) paOneTerm
    (exponentialExponentTerm height) paOneTerm
    previous reflexivity
  let congruence : CertifiedPAProof
      (“!!source = !!target” :
        LO.FirstOrder.ArithmeticProposition) :=
    CertifiedPAProof.cast
      (addEqualityAsTerm_formula
        (shortBinaryNumeralTerm height) paOneTerm
        (exponentialExponentTerm height) paOneTerm)
      congruenceRaw
  let through := proveEqualityTransitivity
    (shortBinaryNumeralTerm (height + 1)) source target
    incrementReverse congruence
  let termBound := exponentialShortTermCodeEnvelope (height + 1)
  have hheightSize : Nat.size height <= (height + 1) + 1 := by
    exact (nat_size_le_self_short height).trans (by omega)
  have hnextSize : Nat.size (height + 1) <= (height + 1) + 1 := by
    exact (nat_size_le_self_short (height + 1)).trans (by omega)
  have hshortComponent :=
    binaryNumeralTerm_code_length_le_envelope
      height ((height + 1) + 1) hheightSize
  have hnextComponent :=
    binaryNumeralTerm_code_length_le_envelope
      (height + 1) ((height + 1) + 1) hnextSize
  have hexponentComponent :
      (binaryTermCode (exponentialExponentTerm height)).length <=
        exponentialTermCodeEnvelope (height + 1) := by
    exact
      (exponentialExponentTerm_code_length_le_envelope height).trans
        (exponentialTermCodeEnvelope_mono (by omega))
  have hshort :
      (binaryTermCode (shortBinaryNumeralTerm height)).length <=
        termBound := by
    dsimp only [termBound]
    exact shortBinaryNumeralTerm_code_le_shortEnvelope
      height (height + 1) hheightSize
  have hnext :
      (binaryTermCode
        (shortBinaryNumeralTerm (height + 1))).length <= termBound := by
    dsimp only [termBound]
    exact shortBinaryNumeralTerm_code_le_shortEnvelope
      (height + 1) (height + 1) hnextSize
  have hexponent :
      (binaryTermCode (exponentialExponentTerm height)).length <=
        termBound := by
    dsimp only [termBound]
    exact exponentialExponentTerm_code_le_shortEnvelope
      height (height + 1) (by omega)
  have hone :
      (binaryTermCode paOneTerm).length <= termBound :=
    paOneTerm_code_le_shortEnvelope (height + 1)
  have hsourceRaw := paAddTerm_code_length_le
    (shortBinaryNumeralTerm height) paOneTerm
  have hsource : (binaryTermCode source).length <= termBound := by
    dsimp only [source, termBound]
    unfold exponentialShortTermCodeEnvelope
    omega
  have htargetRaw := paAddTerm_code_length_le
    (exponentialExponentTerm height) paOneTerm
  have htarget : (binaryTermCode target).length <= termBound := by
    dsimp only [target, termBound]
    unfold exponentialShortTermCodeEnvelope
    omega
  have hincrement :
      increment.payloadLength <=
        binaryNumeralIncrementPayloadPolynomial (height + 1) := by
    exact proveBinaryNumeralIncrement_payloadLength_le_width
      height (height + 1)
        ((nat_size_le_self_short height).trans (by omega))
  have hincrementReverse :
      incrementReverse.payloadLength <=
        increment.payloadLength + paPrimitiveCostEnvelope termBound := by
    exact proveEqualitySymmetry_payloadLength_le_primitive
      source (shortBinaryNumeralTerm (height + 1)) increment termBound
      hsource hnext
  have hreflexivity :
      reflexivity.payloadLength <=
        paPrimitiveCostEnvelope termBound := by
    exact proveEqualityReflexivityAtTerm_payloadLength_le_primitive
      paOneTerm termBound hone
  have hcongruenceRaw :
      congruenceRaw.payloadLength <=
        previous.payloadLength + reflexivity.payloadLength +
          paPrimitiveCostEnvelope termBound := by
    exact proveAddCongruence_payloadLength_le_primitive
      (shortBinaryNumeralTerm height) paOneTerm
      (exponentialExponentTerm height) paOneTerm
      previous reflexivity termBound hshort hone hexponent hone
  have hcongruence :
      congruence.payloadLength <=
        previous.payloadLength + reflexivity.payloadLength +
          paPrimitiveCostEnvelope termBound := by
    change (CertifiedPAProof.cast _ congruenceRaw).payloadLength <= _
    rw [CertifiedPAProof.cast_payloadLength]
    exact hcongruenceRaw
  have hthrough :
      through.payloadLength <=
        incrementReverse.payloadLength + congruence.payloadLength +
          paPrimitiveCostEnvelope termBound := by
    exact proveEqualityTransitivity_payloadLength_le_primitive
      (shortBinaryNumeralTerm (height + 1)) source target
      incrementReverse congruence termBound hnext hsource htarget
  change (CertifiedPAProof.cast _ through).payloadLength <= _
  rw [CertifiedPAProof.cast_payloadLength]
  change through.payloadLength <=
    previous.payloadLength +
      exponentialShortDirectStepPayloadEnvelope (height + 1)
  unfold exponentialShortDirectStepPayloadEnvelope
  dsimp only [termBound] at *
  omega

theorem exponentialValueShortToRecursiveDirectProof_succ_payloadLength_le
    (height : Nat) :
    (exponentialValueShortToRecursiveDirectProof
      (height + 1)).payloadLength <=
      (exponentialValueShortToRecursiveDirectProof height).payloadLength +
        exponentialShortDirectStepPayloadEnvelope (height + 1) := by
  let previous :=
    exponentialValueShortToRecursiveDirectProof height
  let source := paMulTerm arithmeticTwoTerm
    (shortBinaryNumeralTerm (2 ^ height))
  let target := paMulTerm arithmeticTwoTerm
    (exponentialPowerValueTerm height)
  let reflexivity := proveEqualityReflexivityAtTerm arithmeticTwoTerm
  let congruenceRaw := proveMulCongruence
    arithmeticTwoTerm (shortBinaryNumeralTerm (2 ^ height))
    arithmeticTwoTerm (exponentialPowerValueTerm height)
    reflexivity previous
  let congruence : CertifiedPAProof
      (“!!source = !!target” :
        LO.FirstOrder.ArithmeticProposition) :=
    CertifiedPAProof.cast
      (mulEqualityAsTerm_formula
        arithmeticTwoTerm (shortBinaryNumeralTerm (2 ^ height))
        arithmeticTwoTerm (exponentialPowerValueTerm height))
      congruenceRaw
  let termBound := exponentialShortTermCodeEnvelope (height + 1)
  have hpowerSize : Nat.size (2 ^ height) <= (height + 1) + 1 := by
    rw [Nat.size_pow]
    omega
  have hshortComponent :=
    binaryNumeralTerm_code_length_le_envelope
      (2 ^ height) ((height + 1) + 1) hpowerSize
  have hvalueComponent :
      (binaryTermCode (exponentialPowerValueTerm height)).length <=
        exponentialTermCodeEnvelope (height + 1) := by
    exact
      (exponentialPowerValueTerm_code_length_le_envelope height).trans
        (exponentialTermCodeEnvelope_mono (by omega))
  have hshort :
      (binaryTermCode
        (shortBinaryNumeralTerm (2 ^ height))).length <= termBound := by
    dsimp only [termBound]
    exact shortBinaryNumeralTerm_code_le_shortEnvelope
      (2 ^ height) (height + 1) hpowerSize
  have hvalue :
      (binaryTermCode (exponentialPowerValueTerm height)).length <=
        termBound := by
    dsimp only [termBound]
    exact exponentialPowerValueTerm_code_le_shortEnvelope
      height (height + 1) (by omega)
  have htwo :
      (binaryTermCode arithmeticTwoTerm).length <= termBound :=
    arithmeticTwoTerm_code_le_shortEnvelope (height + 1)
  have hsourceRaw := paMulTerm_code_length_le
    arithmeticTwoTerm (shortBinaryNumeralTerm (2 ^ height))
  have hsource : (binaryTermCode source).length <= termBound := by
    dsimp only [source, termBound]
    unfold exponentialShortTermCodeEnvelope
    omega
  have htargetRaw := paMulTerm_code_length_le
    arithmeticTwoTerm (exponentialPowerValueTerm height)
  have htarget : (binaryTermCode target).length <= termBound := by
    dsimp only [target, termBound]
    unfold exponentialShortTermCodeEnvelope
    omega
  have hreflexivity :
      reflexivity.payloadLength <=
        paPrimitiveCostEnvelope termBound := by
    exact proveEqualityReflexivityAtTerm_payloadLength_le_primitive
      arithmeticTwoTerm termBound htwo
  have hcongruenceRaw :
      congruenceRaw.payloadLength <=
        reflexivity.payloadLength + previous.payloadLength +
          paPrimitiveCostEnvelope termBound := by
    exact proveMulCongruence_payloadLength_le_primitive
      arithmeticTwoTerm (shortBinaryNumeralTerm (2 ^ height))
      arithmeticTwoTerm (exponentialPowerValueTerm height)
      reflexivity previous termBound htwo hshort htwo hvalue
  have hcongruence :
      congruence.payloadLength <=
        reflexivity.payloadLength + previous.payloadLength +
          paPrimitiveCostEnvelope termBound := by
    change (CertifiedPAProof.cast _ congruenceRaw).payloadLength <= _
    rw [CertifiedPAProof.cast_payloadLength]
    exact hcongruenceRaw
  change (CertifiedPAProof.cast _ congruence).payloadLength <= _
  rw [CertifiedPAProof.cast_payloadLength]
  change congruence.payloadLength <=
    previous.payloadLength +
      exponentialShortDirectStepPayloadEnvelope (height + 1)
  unfold exponentialShortDirectStepPayloadEnvelope
  dsimp only [termBound] at *
  omega

/-! ## Closed polynomial recurrences -/

def exponentialExponentShortDirectPayloadRecurrence (height : Nat) : Nat :=
  monotonePayloadRecurrence
    (exponentialExponentShortToRecursiveDirectProof 0).payloadLength
    exponentialShortDirectStepPayloadEnvelope height

def exponentialValueShortDirectPayloadRecurrence (height : Nat) : Nat :=
  monotonePayloadRecurrence
    (exponentialValueShortToRecursiveDirectProof 0).payloadLength
    exponentialShortDirectStepPayloadEnvelope height

def exponentialExponentShortDirectPayloadPolynomial (height : Nat) : Nat :=
  (exponentialExponentShortToRecursiveDirectProof 0).payloadLength +
    height * exponentialShortDirectStepPayloadEnvelope height

def exponentialValueShortDirectPayloadPolynomial (height : Nat) : Nat :=
  (exponentialValueShortToRecursiveDirectProof 0).payloadLength +
    height * exponentialShortDirectStepPayloadEnvelope height

theorem exponentialExponentShortToRecursiveDirectProof_payloadLength_le_recurrence
    (height : Nat) :
    (exponentialExponentShortToRecursiveDirectProof height).payloadLength <=
      exponentialExponentShortDirectPayloadRecurrence height := by
  induction height with
  | zero =>
      rw [exponentialExponentShortDirectPayloadRecurrence,
        monotonePayloadRecurrence]
  | succ height ih =>
      have hstep :=
        exponentialExponentShortToRecursiveDirectProof_succ_payloadLength_le
          height
      rw [exponentialExponentShortDirectPayloadRecurrence,
        monotonePayloadRecurrence]
      exact hstep.trans (Nat.add_le_add_right ih _)

theorem exponentialValueShortToRecursiveDirectProof_payloadLength_le_recurrence
    (height : Nat) :
    (exponentialValueShortToRecursiveDirectProof height).payloadLength <=
      exponentialValueShortDirectPayloadRecurrence height := by
  induction height with
  | zero =>
      rw [exponentialValueShortDirectPayloadRecurrence,
        monotonePayloadRecurrence]
  | succ height ih =>
      have hstep :=
        exponentialValueShortToRecursiveDirectProof_succ_payloadLength_le
          height
      rw [exponentialValueShortDirectPayloadRecurrence,
        monotonePayloadRecurrence]
      exact hstep.trans (Nat.add_le_add_right ih _)

theorem exponentialExponentShortDirectPayloadRecurrence_le_polynomial
    (height : Nat) :
    exponentialExponentShortDirectPayloadRecurrence height <=
      exponentialExponentShortDirectPayloadPolynomial height := by
  exact monotonePayloadRecurrence_le_final_step
    (exponentialExponentShortToRecursiveDirectProof 0).payloadLength
    exponentialShortDirectStepPayloadEnvelope
    exponentialShortDirectStepPayloadEnvelope_mono height

theorem exponentialValueShortDirectPayloadRecurrence_le_polynomial
    (height : Nat) :
    exponentialValueShortDirectPayloadRecurrence height <=
      exponentialValueShortDirectPayloadPolynomial height := by
  exact monotonePayloadRecurrence_le_final_step
    (exponentialValueShortToRecursiveDirectProof 0).payloadLength
    exponentialShortDirectStepPayloadEnvelope
    exponentialShortDirectStepPayloadEnvelope_mono height

theorem exponentialExponentShortToRecursiveDirectProof_payloadLength_le_polynomial
    (height : Nat) :
    (exponentialExponentShortToRecursiveDirectProof height).payloadLength <=
      exponentialExponentShortDirectPayloadPolynomial height := by
  exact
    (exponentialExponentShortToRecursiveDirectProof_payloadLength_le_recurrence
      height).trans
      (exponentialExponentShortDirectPayloadRecurrence_le_polynomial height)

theorem exponentialValueShortToRecursiveDirectProof_payloadLength_le_polynomial
    (height : Nat) :
    (exponentialValueShortToRecursiveDirectProof height).payloadLength <=
      exponentialValueShortDirectPayloadPolynomial height := by
  exact
    (exponentialValueShortToRecursiveDirectProof_payloadLength_le_recurrence
      height).trans
      (exponentialValueShortDirectPayloadRecurrence_le_polynomial height)

theorem exponentialExponentShortToRecursiveDirectProof_checked_polynomial
    (height : Nat) :
    listedCompactCertifiedPAProofVerifier
        (exponentialExponentShortToRecursiveDirectProof height).code
        (compactFormulaCode
          (“!!(shortBinaryNumeralTerm height) =
            !!(exponentialExponentTerm height)” :
            LO.FirstOrder.ArithmeticProposition)) = true ∧
      (exponentialExponentShortToRecursiveDirectProof height).payloadLength <=
        exponentialExponentShortDirectPayloadPolynomial height := by
  exact ⟨
    exponentialExponentShortToRecursiveDirectProof_verifier_eq_true height,
    exponentialExponentShortToRecursiveDirectProof_payloadLength_le_polynomial
      height⟩

theorem exponentialValueShortToRecursiveDirectProof_checked_polynomial
    (height : Nat) :
    listedCompactCertifiedPAProofVerifier
        (exponentialValueShortToRecursiveDirectProof height).code
        (compactFormulaCode
          (“!!(shortBinaryNumeralTerm (2 ^ height)) =
            !!(exponentialPowerValueTerm height)” :
            LO.FirstOrder.ArithmeticProposition)) = true ∧
      (exponentialValueShortToRecursiveDirectProof height).payloadLength <=
        exponentialValueShortDirectPayloadPolynomial height := by
  exact ⟨
    exponentialValueShortToRecursiveDirectProof_verifier_eq_true height,
    exponentialValueShortToRecursiveDirectProof_payloadLength_le_polynomial
      height⟩

/-! ## Reverse equalities -/

def exponentialExponentRecursiveToShortPayloadPolynomial
    (height : Nat) : Nat :=
  exponentialExponentShortDirectPayloadPolynomial height +
    paPrimitiveCostEnvelope (exponentialShortTermCodeEnvelope height)

def exponentialValueRecursiveToShortPayloadPolynomial
    (height : Nat) : Nat :=
  exponentialValueShortDirectPayloadPolynomial height +
    paPrimitiveCostEnvelope (exponentialShortTermCodeEnvelope height)

theorem exponentialExponentRecursiveToShortProof_payloadLength_le_polynomial
    (height : Nat) :
    (exponentialExponentRecursiveToShortProof height).payloadLength <=
      exponentialExponentRecursiveToShortPayloadPolynomial height := by
  have hheightSize : Nat.size height <= height + 1 := by
    exact (nat_size_le_self_short height).trans (by omega)
  have hshort := shortBinaryNumeralTerm_code_le_shortEnvelope
    height height hheightSize
  have hrecursive := exponentialExponentTerm_code_le_shortEnvelope
    height height le_rfl
  have hsymmetry :=
    proveEqualitySymmetry_payloadLength_le_primitive
      (shortBinaryNumeralTerm height)
      (exponentialExponentTerm height)
      (exponentialExponentShortToRecursiveDirectProof height)
      (exponentialShortTermCodeEnvelope height)
      hshort hrecursive
  have hforward :=
    exponentialExponentShortToRecursiveDirectProof_payloadLength_le_polynomial
      height
  change
    (proveEqualitySymmetry
      (shortBinaryNumeralTerm height)
      (exponentialExponentTerm height)
      (exponentialExponentShortToRecursiveDirectProof height)).payloadLength <= _
  unfold exponentialExponentRecursiveToShortPayloadPolynomial
  omega

theorem exponentialValueRecursiveToShortProof_payloadLength_le_polynomial
    (height : Nat) :
    (exponentialValueRecursiveToShortProof height).payloadLength <=
      exponentialValueRecursiveToShortPayloadPolynomial height := by
  have hpowerSize : Nat.size (2 ^ height) <= height + 1 := by
    rw [Nat.size_pow]
  have hshort := shortBinaryNumeralTerm_code_le_shortEnvelope
    (2 ^ height) height hpowerSize
  have hrecursive := exponentialPowerValueTerm_code_le_shortEnvelope
    height height le_rfl
  have hsymmetry :=
    proveEqualitySymmetry_payloadLength_le_primitive
      (shortBinaryNumeralTerm (2 ^ height))
      (exponentialPowerValueTerm height)
      (exponentialValueShortToRecursiveDirectProof height)
      (exponentialShortTermCodeEnvelope height)
      hshort hrecursive
  have hforward :=
    exponentialValueShortToRecursiveDirectProof_payloadLength_le_polynomial
      height
  change
    (proveEqualitySymmetry
      (shortBinaryNumeralTerm (2 ^ height))
      (exponentialPowerValueTerm height)
      (exponentialValueShortToRecursiveDirectProof height)).payloadLength <= _
  unfold exponentialValueRecursiveToShortPayloadPolynomial
  omega

/-
/-! ## Formula-code and payload bounds for the fixed transport theorems -/

def exponentialTransportFormulaSeed : Nat :=
  (binaryFormulaCode exponentialValueTransportOuterBody).length +
    (binaryFormulaCode exponentialExponentTransportOuterBody).length + 1

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
  unfold exponentialTransportFormulaSeed
  omega

theorem exponentialExponentTransportOuterBody_code_le_seed :
    (binaryFormulaCode exponentialExponentTransportOuterBody).length <=
      exponentialTransportFormulaSeed := by
  unfold exponentialTransportFormulaSeed
  omega

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

#print axioms
  exponentialExponentShortToRecursiveDirectProof_payloadLength_le_polynomial
#print axioms
  exponentialValueShortToRecursiveDirectProof_payloadLength_le_polynomial
#print axioms
  exponentialExponentShortToRecursiveDirectProof_checked_polynomial
#print axioms
  exponentialValueShortToRecursiveDirectProof_checked_polynomial
#print axioms
  exponentialExponentRecursiveToShortProof_payloadLength_le_polynomial
#print axioms
  exponentialValueRecursiveToShortProof_payloadLength_le_polynomial
#print axioms
  exponentialValueTransportImplication_payloadLength_le_envelope
#print axioms
  exponentialExponentTransportImplication_payloadLength_le_envelope
-/

#print axioms
  exponentialExponentShortToRecursiveDirectProof_payloadLength_le_polynomial
#print axioms
  exponentialValueShortToRecursiveDirectProof_payloadLength_le_polynomial
#print axioms
  exponentialExponentShortToRecursiveDirectProof_checked_polynomial
#print axioms
  exponentialValueShortToRecursiveDirectProof_checked_polynomial
#print axioms
  exponentialExponentRecursiveToShortProof_payloadLength_le_polynomial
#print axioms
  exponentialValueRecursiveToShortProof_payloadLength_le_polynomial

end FoundationCompactPAExponentialShortNumeralCompilerBounds
