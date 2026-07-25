import integration.FoundationCompactNumericListedDirectTokenSliceBitUniversalOuterVariables
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
import integration.FoundationCompactPAHybridBranchesLeafResourceMonotonicity
import integration.FoundationCompactPAValuationContextShiftedCodeSumBounds

/-!
# Generic fixed assembly for inner token-slice branches

This module combines already established bounds without inspecting the
concrete numeral representation of the four token-slice parameters.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceBitBranchesFixedAssembly

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAHybridBranchesLeafResourceMonotonicity
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceBitAtomFixedBounds
open FoundationCompactNumericListedDirectTokenSliceBitUniversalFixedBounds

def tokenSliceBitUniversalSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound + tokenSliceBitUniversalBodyCodePolynomial bitBound

def tokenSliceBitUniversalFormulaFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  boundedUniversalClosedFormulaEnvelope
      (tokenSliceBitUniversalSyntaxFixedPolynomial numericBound bitBound) +
    2 * tokenSliceBitUniversalBodyCodePolynomial bitBound

def tokenSliceBitUniversalLocalPayloadFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (tokenSliceBitUniversalFormulaFixedPolynomial numericBound bitBound +
      2 * valuationContextFormulaCodeSumEnvelope 1 numericBound
        tokenSliceBitBranchVariableCodeCeiling)

def tokenSliceBitUniversalContextFormulaFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  tokenSliceBitUniversalFormulaFixedPolynomial numericBound bitBound +
    2 * valuationContextFormulaCodeSumEnvelope 1 numericBound
      tokenSliceBitBranchVariableCodeCeiling

def tokenSliceBitBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  (numericBound + 1) *
    (tokenSliceAtValuationBitBranchPayloadSumFixedPolynomial numericBound
        bitBound +
      3 * tokenSliceBitUniversalLocalPayloadFixedPolynomial numericBound
        bitBound)

theorem tokenSliceBitBranchesTransparentEnvelope_le_fixed_of_components
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm : ValuationTerm)
    (offset numericBound bitBound : Nat)
    (hbound :
      termValue (extendValuation offset valuation) (Rew.shift widthTerm) <=
        numericBound)
    (hleaf :
      tokenSliceAtValuationBitBranchPayloadResourceSum valuation tokenTableTerm
          widthTerm sourceStartTerm targetStartTerm offset <=
        tokenSliceAtValuationBitBranchPayloadSumFixedPolynomial numericBound
          bitBound)
    (houter :
      let body := tokenSliceAtValuationBitBody tokenTableTerm widthTerm
        sourceStartTerm targetStartTerm
      let boundTerm := Rew.shift widthTerm
      let outerFormula := ∀⁰ termBoundedUniversalBody
        (Rew.bShift boundTerm) body
      outerFormula.freeVariables ⊆ {0})
    (hbody :
      (binaryFormulaCode
        (tokenSliceAtValuationBitBody tokenTableTerm widthTerm
          sourceStartTerm targetStartTerm)).length <=
        tokenSliceBitUniversalBodyCodePolynomial bitBound)
    (hGammaCode :
      let body := tokenSliceAtValuationBitBody tokenTableTerm widthTerm
        sourceStartTerm targetStartTerm
      let boundTerm := Rew.shift widthTerm
      let outerFormula := ∀⁰ termBoundedUniversalBody
        (Rew.bShift boundTerm) body
      let outerVariables := outerFormula.freeVariables
      let branchValuation := extendValuation offset valuation
      contextualHybridUniversalFormulaCodeSum
          ((valuationContext outerVariables branchValuation).image
            Rewriting.shift) <=
        2 * valuationContextFormulaCodeSumEnvelope 1 numericBound
          tokenSliceBitBranchVariableCodeCeiling) :
    tokenSliceAtValuationBitBranchesTransparentEnvelope valuation
        tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset <=
      tokenSliceBitBranchesFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let branchValuation := extendValuation offset valuation
  let body := tokenSliceAtValuationBitBody tokenTableTerm widthTerm
    sourceStartTerm targetStartTerm
  let boundTerm := Rew.shift widthTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue branchValuation boundTerm
  let leafBound :=
    tokenSliceAtValuationBitBranchPayloadSumFixedPolynomial numericBound
      bitBound
  let exactCore :=
    hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
      branchValuation body
      (tokenSliceAtValuationBitBranchPayloadResourceSum valuation
        tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset)
      bound
  let fixedLeafCore :=
    hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
      branchValuation body leafBound bound
  let Gamma :=
    (valuationContext outerVariables branchValuation).image Rewriting.shift
  let contextualCore :=
    contextualHybridUniversalBranchesPayloadPolynomial Gamma bound bound body
      leafBound
  have hcore : exactCore <= fixedLeafCore := by
    dsimp only [exactCore, fixedLeafCore, leafBound]
    exact
      hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf
        bound outerVariables branchValuation body hleaf bound
  have houter' : outerVariables ⊆ {0} := by
    simpa only [outerVariables, outerFormula, body, boundTerm] using houter
  have houterCard : outerVariables.card <= 1 :=
    (Finset.card_le_card houter').trans (by simp)
  have hGammaCard : Gamma.card <= 1 := by
    dsimp only [Gamma]
    have hcontext :
        (valuationContext outerVariables branchValuation).card <=
          outerVariables.card := by
      unfold valuationContext
      exact Finset.card_image_le
    exact Finset.card_image_le.trans (hcontext.trans houterCard)
  have hcontextual : fixedLeafCore <= contextualCore := by
    dsimp only [fixedLeafCore, contextualCore]
    exact
      hybridBranchesUniformStructuralPayloadEnvelope_le_contextualPolynomial
        bound outerVariables branchValuation body leafBound hGammaCard
        (caseCount := bound) le_rfl
  have hbody' :
      (binaryFormulaCode body).length <=
        tokenSliceBitUniversalBodyCodePolynomial bitBound := by
    simpa only [body] using hbody
  have hbound' : bound <= numericBound := by
    simpa only [bound, branchValuation, boundTerm] using hbound
  have hsyntax :
      explicitHybridUniversalSyntaxResource bound body <=
        tokenSliceBitUniversalSyntaxFixedPolynomial numericBound bitBound := by
    unfold explicitHybridUniversalSyntaxResource
      tokenSliceBitUniversalSyntaxFixedPolynomial
    exact Nat.add_le_add hbound' hbody'
  have hformula :
      explicitHybridUniversalFormulaEnvelope bound body <=
        tokenSliceBitUniversalFormulaFixedPolynomial numericBound
          bitBound := by
    have hclosed :=
      boundedUniversalClosedFormulaEnvelope_mono_completed hsyntax
    unfold explicitHybridUniversalFormulaEnvelope
      tokenSliceBitUniversalFormulaFixedPolynomial
    exact Nat.add_le_add hclosed (Nat.mul_le_mul_left 2 hbody')
  have hGammaCode' :
      contextualHybridUniversalFormulaCodeSum Gamma <=
        2 * valuationContextFormulaCodeSumEnvelope 1 numericBound
          tokenSliceBitBranchVariableCodeCeiling := by
    simpa only [Gamma, outerVariables, outerFormula, body, boundTerm,
      branchValuation] using hGammaCode
  have hcontextFormula :
      contextualHybridUniversalFormulaEnvelope Gamma bound body <=
        tokenSliceBitUniversalFormulaFixedPolynomial numericBound bitBound +
          2 * valuationContextFormulaCodeSumEnvelope 1 numericBound
            tokenSliceBitBranchVariableCodeCeiling := by
    unfold contextualHybridUniversalFormulaEnvelope
    exact Nat.add_le_add hformula hGammaCode'
  have hlocal :
      contextualHybridUniversalLocalPayloadEnvelope Gamma bound body <=
        tokenSliceBitUniversalLocalPayloadFixedPolynomial numericBound
          bitBound := by
    unfold tokenSliceBitUniversalLocalPayloadFixedPolynomial
    exact smallContextAssemblyEnvelope_mono_local hcontextFormula
  have hfixed :
      contextualCore <=
        tokenSliceBitBranchesFullyFixedPayloadPolynomial numericBound
          bitBound := by
    unfold contextualCore contextualHybridUniversalBranchesPayloadPolynomial
      tokenSliceBitBranchesFullyFixedPayloadPolynomial
    exact Nat.mul_le_mul (by omega) (Nat.add_le_add le_rfl
      (Nat.mul_le_mul_left 3 hlocal))
  have htransparent :
      tokenSliceAtValuationBitBranchesTransparentEnvelope valuation
          tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset =
        exactCore := by
    unfold tokenSliceAtValuationBitBranchesTransparentEnvelope
    rfl
  rw [htransparent]
  exact hcore.trans (hcontextual.trans hfixed)

#print axioms tokenSliceBitBranchesTransparentEnvelope_le_fixed_of_components

end FoundationCompactNumericListedDirectTokenSliceBitBranchesFixedAssembly
