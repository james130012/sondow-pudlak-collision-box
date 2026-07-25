import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# General-context assembly bound for hybrid conjunctions

This is the context-cardinality-free assembly estimate used when component
certificates already provide their own payload and conclusion-code bounds.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAHybridConjunctionGeneralContextBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds

def hybridConjunctionGeneralPayloadEnvelope
    (resource leftResource rightResource : Nat) : Nat :=
  leftResource + rightResource + 3 * generalContextAssemblyEnvelope resource

theorem hybridConjunctionStructuralPayloadEnvelope_le_general
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (leftResource rightResource resource : Nat)
    (hresource : 1 <= resource)
    (hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext (left ⋏ right).freeVariables valuation) <= resource)
    (hleft : (binaryFormulaCode left).length <= resource)
    (hright : (binaryFormulaCode right).length <= resource)
    (hconjunction :
      (binaryFormulaCode (left ⋏ right)).length <= resource) :
    hybridConjunctionStructuralPayloadEnvelope valuation left right
        leftResource rightResource <=
      hybridConjunctionGeneralPayloadEnvelope
        resource leftResource rightResource := by
  let Gamma := valuationContext (left ⋏ right).freeVariables valuation
  have hleftInsert :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (insert left Gamma) <= generalContextCoordinate resource := by
    have hraw := formulaCodeSum_insert_le Gamma left
    dsimp only [Gamma] at hraw ⊢
    unfold generalContextCoordinate
    omega
  have hrightInsert :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (insert right Gamma) <= generalContextCoordinate resource := by
    have hraw := formulaCodeSum_insert_le Gamma right
    dsimp only [Gamma] at hraw ⊢
    unfold generalContextCoordinate
    omega
  have hweakLeft := weakeningFullAssemblyCost_le_general
    (insert left Gamma) resource hleftInsert
  have hweakRight := weakeningFullAssemblyCost_le_general
    (insert right Gamma) resource hrightInsert
  have hconjunctionCost := conjunctionFullAssemblyCost_le_general
    Gamma left right resource hresource hcontext hleft hright hconjunction
  unfold hybridConjunctionStructuralPayloadEnvelope
    hybridConjunctionGeneralPayloadEnvelope
  dsimp only [Gamma] at hweakLeft hweakRight hconjunctionCost ⊢
  omega

theorem transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (leftResource rightResource syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryFormulaCode left).length <= syntaxResource)
    (hrightCode : (binaryFormulaCode right).length <= syntaxResource)
    (hconjunctionCode : (binaryFormulaCode (left ⋏ right)).length <=
      syntaxResource) :
    transparentHybridConjunctionPayloadEnvelope valuation left right
        leftResource rightResource <=
      hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
        rightResource := by
  have hclosed : (left ⋏ right).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hleftClosed,
      hrightClosed]
    simp
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
        (valuationContext (left ⋏ right).freeVariables valuation) <=
          syntaxResource := by
    rw [hclosed]
    simp [valuationContext,
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum]
  have hraw := hybridConjunctionStructuralPayloadEnvelope_le_general
    valuation left right leftResource rightResource syntaxResource hpositive
    hcontext hleftCode hrightCode hconjunctionCode
  simpa only [transparentHybridConjunctionPayloadEnvelope,
    hybridConjunctionStructuralPayloadEnvelope] using hraw

#print axioms hybridConjunctionStructuralPayloadEnvelope_le_general
#print axioms transparentHybridConjunctionPayloadEnvelope_le_closedGeneral

end FoundationCompactPAHybridConjunctionGeneralContextBounds
