import integration.FoundationCompactPAValuationShiftedBoundCompilerBounds
import integration.FoundationCompactPAValuationTermCompilerPublicBounds
import integration.FoundationCompactPABitMembershipValuationTransportPolynomialBounds

/-!
# Public resource for a closed shifted bound

The fixed-width universal compiler shifts a closed width term under its bound
variable.  This module replaces the exact term-normalization, numeral bridge,
and equality-symmetry resources in that route by their proved public
polynomials.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAValuationShiftedBoundCompilerPublicBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABitMembershipValuationContextCompilerBounds
open FoundationCompactPABitMembershipValuationTransportPolynomialBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerBounds
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPACertifiedContextEquality
open FoundationCompactCertifiedContextualModusPonens

theorem shiftedTerm_freeVariables_eq_empty_of_closed
    (term : ValuationTerm) (hclosed : term.freeVariables = ∅) :
    (Rew.shift term).freeVariables = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro candidate hcandidate
  rcases mem_freeVariables_shiftTerm term hcandidate with
    ⟨sourceIndex, hsource, _⟩
  rw [hclosed] at hsource
  simp at hsource

def closedShiftedBoundTermCodeResource
    (valuation : Nat -> Nat) (boundSource : ValuationTerm) : Nat :=
  let value := termValue valuation boundSource
  (binaryTermCode (shortBinaryNumeralTerm value)).length +
    (binaryTermCode (iteratedSuccessorTerm 0 value)).length + 1

def compileClosedShiftedBoundEqualityPayloadPolynomial
    (valuation : Nat -> Nat) (boundSource : ValuationTerm) : Nat :=
  let shiftedValuation := extendValuation 0 valuation
  let localContext := valuationContext
    (Rew.shift boundSource).freeVariables shiftedValuation
  let outerContext :=
    (valuationContext (∅ : Finset Nat) valuation).image Rewriting.shift
  let value := termValue valuation boundSource
  let source := shortBinaryNumeralTerm value
  let middle := iteratedSuccessorTerm 0 value
  let target := Rew.shift boundSource
  let bridgeFormula := (“!!source = !!middle” : ValuationFormula)
  let backwardFormula := (“!!middle = !!source” : ValuationFormula)
  let resultFormula := (“!!middle = !!target” : ValuationFormula)
  let termBound := compileTermValueEqualityPayloadPolynomial
    shiftedValuation target
  let termCodeResource := closedShiftedBoundTermCodeResource
    valuation boundSource
  let contextualBridgeBound := shortToIteratedPayloadPolynomial value +
    weakeningFullAssemblyCost (insert bridgeFormula localContext)
  let bridgeBackwardBound :=
    binaryBitEqualitySymmetryPayloadTermPolynomial termCodeResource +
      weakeningFullAssemblyCost
        (insert (bridgeFormula 🡒 backwardFormula) localContext) +
      contextualBridgeBound +
      contextualModusPonensFullAssemblyCost localContext
        bridgeFormula backwardFormula
  contextualEqualityTransitivityStructuralPayloadBound localContext
      middle source target bridgeBackwardBound termBound +
    weakeningFullAssemblyCost (insert resultFormula outerContext)

def compileShiftedBoundEqualityPayloadPublicPolynomial
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
  let bridgeFormula := (“!!source = !!middle” : ValuationFormula)
  let backwardFormula := (“!!middle = !!source” : ValuationFormula)
  let resultFormula := (“!!middle = !!target” : ValuationFormula)
  let termBound := compileTermValueEqualityPayloadPolynomial
    shiftedValuation target
  let termCodeResource := closedShiftedBoundTermCodeResource
    valuation boundSource
  let contextualBridgeBound := shortToIteratedPayloadPolynomial value +
    weakeningFullAssemblyCost (insert bridgeFormula localContext)
  let bridgeBackwardBound :=
    binaryBitEqualitySymmetryPayloadTermPolynomial termCodeResource +
      weakeningFullAssemblyCost
        (insert (bridgeFormula 🡒 backwardFormula) localContext) +
      contextualBridgeBound +
      contextualModusPonensFullAssemblyCost localContext
        bridgeFormula backwardFormula
  contextualEqualityTransitivityStructuralPayloadBound localContext
      middle source target bridgeBackwardBound termBound +
    weakeningFullAssemblyCost (insert resultFormula outerContext)

theorem compileShiftedBoundEqualityPayloadResource_le_publicPolynomial
    (valuation : Nat -> Nat) (outerVariables : Finset Nat)
    (boundSource : ValuationTerm)
    (hclosed : boundSource.freeVariables = ∅) :
    compileShiftedBoundEqualityPayloadResource valuation outerVariables
        boundSource <=
      compileShiftedBoundEqualityPayloadPublicPolynomial
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
  let bridgeFormula := (“!!source = !!middle” : ValuationFormula)
  let backwardFormula := (“!!middle = !!source” : ValuationFormula)
  let resultFormula := (“!!middle = !!target” : ValuationFormula)
  let oldTermBound := compileTermValueEqualityPayloadResource
    shiftedValuation target
  let newTermBound := compileTermValueEqualityPayloadPolynomial
    shiftedValuation target
  let termCodeResource := closedShiftedBoundTermCodeResource
    valuation boundSource
  let oldContextualBridgeBound := shortToIteratedPayloadResource value +
    weakeningFullAssemblyCost (insert bridgeFormula localContext)
  let newContextualBridgeBound := shortToIteratedPayloadPolynomial value +
    weakeningFullAssemblyCost (insert bridgeFormula localContext)
  let oldBridgeBackwardBound :=
    (equalitySymmetryImplication source middle).payloadLength +
      weakeningFullAssemblyCost
        (insert (bridgeFormula 🡒 backwardFormula) localContext) +
      oldContextualBridgeBound +
      contextualModusPonensFullAssemblyCost localContext
        bridgeFormula backwardFormula
  let newBridgeBackwardBound :=
    binaryBitEqualitySymmetryPayloadTermPolynomial termCodeResource +
      weakeningFullAssemblyCost
        (insert (bridgeFormula 🡒 backwardFormula) localContext) +
      newContextualBridgeBound +
      contextualModusPonensFullAssemblyCost localContext
        bridgeFormula backwardFormula
  have hshiftClosed := shiftedTerm_freeVariables_eq_empty_of_closed
    boundSource hclosed
  have htargetVars : target.freeVariables ⊆ {0} := by
    dsimp only [target]
    rw [hshiftClosed]
    simp
  have hterm :=
    compileTermValueEqualityPayloadResource_le_publicPolynomial
      shiftedValuation target htargetVars
  have hbridge := shortToIteratedPayloadResource_le_publicPolynomial value
  have hsource : (binaryTermCode source).length <= termCodeResource := by
    unfold termCodeResource closedShiftedBoundTermCodeResource
    dsimp only [source, value]
    omega
  have hmiddle : (binaryTermCode middle).length <= termCodeResource := by
    unfold termCodeResource closedShiftedBoundTermCodeResource
    dsimp only [middle, value]
    omega
  have hsymmetryRaw :=
    equalitySymmetryImplication_payloadLength_le_binaryBitResource
      source middle
  have hsymmetryPolynomial :=
    binaryBitEqualitySymmetryImplicationPayloadResource_le_termPolynomial
      source middle termCodeResource hsource hmiddle
  have hsymmetry :
      (equalitySymmetryImplication source middle).payloadLength <=
        binaryBitEqualitySymmetryPayloadTermPolynomial termCodeResource :=
    hsymmetryRaw.trans hsymmetryPolynomial
  have hcontextualBridge : oldContextualBridgeBound <=
      newContextualBridgeBound := by
    dsimp only [oldContextualBridgeBound, newContextualBridgeBound]
    omega
  have hbridgeBackward : oldBridgeBackwardBound <=
      newBridgeBackwardBound := by
    dsimp only [oldBridgeBackwardBound, newBridgeBackwardBound]
    omega
  have htransitivity :=
    contextualEqualityTransitivityStructuralPayloadBound_mono localContext
      middle source target oldBridgeBackwardBound oldTermBound
      newBridgeBackwardBound newTermBound hbridgeBackward hterm
  unfold compileShiftedBoundEqualityPayloadResource
    compileShiftedBoundEqualityPayloadPublicPolynomial
  dsimp only [shiftedValuation, localContext, outerContext, value, source,
    middle, target, bridgeFormula, backwardFormula, resultFormula,
    oldTermBound, newTermBound, termCodeResource,
    oldContextualBridgeBound, newContextualBridgeBound,
    oldBridgeBackwardBound, newBridgeBackwardBound] at htransitivity ⊢
  omega

theorem compileShiftedBoundEqualityPayloadResource_le_closedPolynomial
    (valuation : Nat -> Nat) (boundSource : ValuationTerm)
    (hclosed : boundSource.freeVariables = ∅) :
    compileShiftedBoundEqualityPayloadResource valuation ∅ boundSource <=
      compileClosedShiftedBoundEqualityPayloadPolynomial
        valuation boundSource := by
  have hpublic :=
    compileShiftedBoundEqualityPayloadResource_le_publicPolynomial
      valuation ∅ boundSource hclosed
  simpa only [compileShiftedBoundEqualityPayloadPublicPolynomial,
    compileClosedShiftedBoundEqualityPayloadPolynomial] using hpublic

#print axioms shiftedTerm_freeVariables_eq_empty_of_closed
#print axioms
  compileShiftedBoundEqualityPayloadResource_le_publicPolynomial
#print axioms
  compileShiftedBoundEqualityPayloadResource_le_closedPolynomial

end FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
