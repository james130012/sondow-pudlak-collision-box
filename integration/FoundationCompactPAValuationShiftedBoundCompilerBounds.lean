import integration.FoundationCompactPAValuationBoundedFormulaCompiler
import integration.FoundationCompactPAValuationTermCompilerBounds

/-!
# Payload bound for the shifted valuation-bound compiler

The bounded-universal branch normalizes its bound term after one valuation
shift.  This file charges every proof constructor used by that normalization.
The resource contains no proof object or proof-length premise.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAValuationShiftedBoundCompilerBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAAxiomCertificate
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPACertifiedContextEquality

/-- Explicit payload resource for `compileShiftedBoundEquality`. -/
def compileShiftedBoundEqualityPayloadResource
    (valuation : Nat -> Nat) (outerVariables : Finset Nat)
    (boundSource : ValuationTerm) : Nat :=
  let shiftedValuation := extendValuation 0 valuation
  let localContext := valuationContext
    (Rew.shift boundSource).freeVariables shiftedValuation
  let outerContext :=
    (valuationContext outerVariables valuation).image Rewriting.shift
  let value := termValue valuation boundSource
  let source := shortBinaryNumeralTerm value
  let middle := iteratedSuccessorTerm 0 value
  let target := Rew.shift boundSource
  let bridgeFormula :=
    (“!!source = !!middle” : ValuationFormula)
  let backwardFormula :=
    (“!!middle = !!source” : ValuationFormula)
  let resultFormula :=
    (“!!middle = !!target” : ValuationFormula)
  let termBound := compileTermValueEqualityPayloadResource
    shiftedValuation (Rew.shift boundSource)
  let contextualBridgeBound := shortToIteratedPayloadResource value +
    weakeningFullAssemblyCost (insert bridgeFormula localContext)
  let bridgeBackwardBound :=
    (equalitySymmetryImplication source middle).payloadLength +
      weakeningFullAssemblyCost
        (insert (bridgeFormula 🡒 backwardFormula) localContext) +
      contextualBridgeBound +
      contextualModusPonensFullAssemblyCost localContext
        bridgeFormula backwardFormula
  contextualEqualityTransitivityStructuralPayloadBound localContext
      middle source target bridgeBackwardBound termBound +
    weakeningFullAssemblyCost (insert resultFormula outerContext)

theorem compileShiftedBoundEquality_payloadLength_le_resource
    (valuation : Nat -> Nat) (outerVariables : Finset Nat)
    (boundSource : ValuationTerm)
    (hvariables : boundSource.freeVariables ⊆ outerVariables) :
    (compileShiftedBoundEquality valuation outerVariables boundSource
      hvariables).payloadLength ≤
      compileShiftedBoundEqualityPayloadResource
        valuation outerVariables boundSource := by
  let shiftedValuation := extendValuation 0 valuation
  let localContext := valuationContext
    (Rew.shift boundSource).freeVariables shiftedValuation
  let outerContext :=
    (valuationContext outerVariables valuation).image Rewriting.shift
  let value := termValue valuation boundSource
  let source := shortBinaryNumeralTerm value
  let middle := iteratedSuccessorTerm 0 value
  let target := Rew.shift boundSource
  let bridgeFormula :=
    (“!!source = !!middle” : ValuationFormula)
  let backwardFormula :=
    (“!!middle = !!source” : ValuationFormula)
  let resultFormula :=
    (“!!middle = !!target” : ValuationFormula)

  let termRaw := compileTermValueEquality
    shiftedValuation (Rew.shift boundSource)
  have hvalue := termValue_shift 0 valuation boundSource
  let termProof : CertifiedPAContextProof localContext
      (“!!source = !!target” : ValuationFormula) := by
    have hformula :
        (“!!(shortBinaryNumeralTerm
            (termValue shiftedValuation (Rew.shift boundSource))) =
          !!(Rew.shift boundSource)” : ValuationFormula) =
        (“!!source = !!target” : ValuationFormula) := by
      dsimp only [source, target, value]
      rw [hvalue]
    exact CertifiedPAContextProof.cast hformula termRaw
  have htermRaw : termRaw.payloadLength ≤
      compileTermValueEqualityPayloadResource
        shiftedValuation (Rew.shift boundSource) :=
    compileTermValueEquality_payloadLength_le_resource
      shiftedValuation (Rew.shift boundSource)
  have hterm : termProof.payloadLength ≤
      compileTermValueEqualityPayloadResource
        shiftedValuation (Rew.shift boundSource) := by
    have hcast : termProof.payloadLength = termRaw.payloadLength := by
      dsimp only [termProof]
      exact CertifiedPAContextProof.cast_payloadLength _ _
    rw [hcast]
    exact htermRaw

  let bridge := proveShortBinaryNumeralEqualsIterated value
  let contextualBridge := CertifiedPAContextProof.weakenCertified
    localContext bridge
  have hbridge : bridge.payloadLength ≤
      shortToIteratedPayloadResource value :=
    proveShortBinaryNumeralEqualsIterated_payloadLength_le_resource value
  have hcontextualBridgeRaw :=
    CertifiedPAContextProof.weakenCertified_payloadLength_le
      localContext bridge
  have hcontextualBridge : contextualBridge.payloadLength ≤
      shortToIteratedPayloadResource value +
        weakeningFullAssemblyCost
          (insert bridgeFormula localContext) := by
    dsimp only [contextualBridge]
    exact hcontextualBridgeRaw.trans
      (Nat.add_le_add_right hbridge _)

  let bridgeBackward := CertifiedPAContextProof.equalitySymmetry
    source middle contextualBridge
  have hbridgeBackwardRaw :=
    CertifiedPAContextProof.equalitySymmetry_payloadLength_le
      source middle contextualBridge
  have hbridgeBackward : bridgeBackward.payloadLength ≤
      (equalitySymmetryImplication source middle).payloadLength +
        weakeningFullAssemblyCost
          (insert (bridgeFormula 🡒 backwardFormula) localContext) +
        (shortToIteratedPayloadResource value +
          weakeningFullAssemblyCost
            (insert bridgeFormula localContext)) +
        contextualModusPonensFullAssemblyCost localContext
          bridgeFormula backwardFormula := by
    dsimp only [bridgeBackward]
    dsimp only [source, middle, bridgeFormula, backwardFormula] at hbridgeBackwardRaw hcontextualBridge ⊢
    omega

  let localEquality := contextualEqualityTransitivity
    middle source target bridgeBackward termProof
  have hlocalRaw := contextualEqualityTransitivity_payloadLength_le
    middle source target bridgeBackward termProof
  have hlocal : localEquality.payloadLength ≤
      contextualEqualityTransitivityStructuralPayloadBound localContext
        middle source target
        ((equalitySymmetryImplication source middle).payloadLength +
          weakeningFullAssemblyCost
            (insert (bridgeFormula 🡒 backwardFormula) localContext) +
          (shortToIteratedPayloadResource value +
            weakeningFullAssemblyCost
              (insert bridgeFormula localContext)) +
          contextualModusPonensFullAssemblyCost localContext
            bridgeFormula backwardFormula)
        (compileTermValueEqualityPayloadResource
          shiftedValuation (Rew.shift boundSource)) := by
    dsimp only [localEquality]
    exact hlocalRaw.trans (by
      simp only [contextualEqualityTransitivityStructuralPayloadBound]
      omega)

  let result := CertifiedPAContextProof.weakenContext localEquality
    (shiftedTermValuationContext_subset
      0 valuation boundSource outerVariables hvariables)
  have hresultRaw := CertifiedPAContextProof.weakenContext_payloadLength_le
    localEquality
    (shiftedTermValuationContext_subset
      0 valuation boundSource outerVariables hvariables)
  have hcompiled :
      (compileShiftedBoundEquality valuation outerVariables boundSource
        hvariables).payloadLength = result.payloadLength := by
    rfl
  rw [hcompiled]
  unfold compileShiftedBoundEqualityPayloadResource
  dsimp only [result]
  dsimp only [shiftedValuation, localContext, outerContext, value, source,
    middle, target, bridgeFormula, backwardFormula, resultFormula] at *
  omega

/-! ## Direct closed short-numeral bound equality -/

private def certifiedEmptyContextProofOfGlobal
    {formula : ArithmeticProposition}
    (proof : CertifiedPAProof formula) :
    CertifiedPAContextProof ∅ formula where
  derivation := by simpa using proof.derivation
  certificate := proof.certificate
  certificate_valid := by simpa using proof.certificate_valid

private theorem certifiedEmptyContextProofOfGlobal_payloadLength_eq
    {formula : ArithmeticProposition}
    (proof : CertifiedPAProof formula) :
    (certifiedEmptyContextProofOfGlobal proof).payloadLength =
      proof.payloadLength := by
  rw [CertifiedPAProof.payloadLength_eq]
  rfl

/-- The exact forward equality required by a contextual bounded universal
whose source bound is already a closed short-binary numeral. -/
noncomputable def compileClosedShortBoundEquality (bound : Nat) :
    CertifiedPAContextProof ∅
      (“!!(iteratedSuccessorTerm 0 bound) =
        !!(shortBinaryNumeralTerm bound)” : ArithmeticProposition) :=
  certifiedEmptyContextProofOfGlobal
    (proveEqualitySymmetry
      (shortBinaryNumeralTerm bound)
      (iteratedSuccessorTerm 0 bound)
      (proveShortBinaryNumeralEqualsIterated bound))

def closedShortBoundEqualityPayloadPolynomial (bound : Nat) : Nat :=
  shortToIteratedPayloadPolynomial bound +
    paPrimitiveCostEnvelope
      (shortToIteratedStepTermCodePolynomial bound)

theorem compileClosedShortBoundEquality_payloadLength_le_publicPolynomial
    (bound : Nat) :
    (compileClosedShortBoundEquality bound).payloadLength <=
      closedShortBoundEqualityPayloadPolynomial bound := by
  let source := shortBinaryNumeralTerm bound
  let target := iteratedSuccessorTerm 0 bound
  let forward := proveShortBinaryNumeralEqualsIterated bound
  let backward := proveEqualitySymmetry source target forward
  have hsourceRaw := binaryNumeralTerm_code_length_le_envelope
    bound (bound + 1) (by
      exact (Nat.size_le_size le_rfl).trans (by
        have hsize : Nat.size bound <= bound := by
          rw [Nat.size_le]
          exact bound.lt_two_pow_self
        omega))
  have hsource : (binaryTermCode source).length <=
      shortToIteratedStepTermCodePolynomial bound := by
    dsimp only [source]
    apply hsourceRaw.trans
    change binaryNumeralTermCodeEnvelope (bound + 1) <=
      5 * binaryNumeralTermCodeEnvelope (bound + 1) +
        2 * iteratedSuccessorTermCodePolynomial 0 bound +
        2 * (binaryTermCode (finiteCaseOneTerm 0)).length +
        2 * binaryFunctionTermCodeOverhead Language.Add.add + 1
    omega
  have htargetRaw :=
    iteratedSuccessorTerm_code_length_le_polynomial 0 bound
  have htarget : (binaryTermCode target).length <=
      shortToIteratedStepTermCodePolynomial bound := by
    dsimp only [target]
    apply htargetRaw.trans
    change iteratedSuccessorTermCodePolynomial 0 bound <=
      5 * binaryNumeralTermCodeEnvelope (bound + 1) +
        2 * iteratedSuccessorTermCodePolynomial 0 bound +
        2 * (binaryTermCode (finiteCaseOneTerm 0)).length +
        2 * binaryFunctionTermCodeOverhead Language.Add.add + 1
    omega
  have hforward :=
    proveShortBinaryNumeralEqualsIterated_payloadLength_le_publicPolynomial
      bound
  have hforward' : forward.payloadLength <=
      shortToIteratedPayloadPolynomial bound := by
    simpa only [forward] using hforward
  have hbackward := proveEqualitySymmetry_payloadLength_le_primitive
    source target forward (shortToIteratedStepTermCodePolynomial bound)
    hsource htarget
  have hbackward' : backward.payloadLength <=
      forward.payloadLength +
        paPrimitiveCostEnvelope
          (shortToIteratedStepTermCodePolynomial bound) := by
    simpa only [backward] using hbackward
  unfold compileClosedShortBoundEquality
  rw [certifiedEmptyContextProofOfGlobal_payloadLength_eq]
  change backward.payloadLength <= _
  unfold closedShortBoundEqualityPayloadPolynomial
  exact hbackward'.trans (Nat.add_le_add_right hforward' _)

def shiftedBoundCompilerPayloadPolynomial (resource : Nat) : Nat :=
  resource * resource + 2 * resource + 1

theorem compileShiftedBoundEquality_payloadLength_le_fixedPolynomial
    (valuation : Nat -> Nat) (outerVariables : Finset Nat)
    (boundSource : ValuationTerm)
    (hvariables : boundSource.freeVariables ⊆ outerVariables) :
    (compileShiftedBoundEquality valuation outerVariables boundSource
      hvariables).payloadLength ≤
      shiftedBoundCompilerPayloadPolynomial
        (compileShiftedBoundEqualityPayloadResource
          valuation outerVariables boundSource) := by
  apply (compileShiftedBoundEquality_payloadLength_le_resource
    valuation outerVariables boundSource hvariables).trans
  unfold shiftedBoundCompilerPayloadPolynomial
  omega

#print axioms compileShiftedBoundEquality_payloadLength_le_resource
#print axioms compileShiftedBoundEquality_payloadLength_le_fixedPolynomial
#print axioms compileClosedShortBoundEquality_payloadLength_le_publicPolynomial

end FoundationCompactPAValuationShiftedBoundCompilerBounds
