import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# General-context assembly bounds for hybrid disjunctions

These estimates charge the weakening and disjunction-introduction steps against
one syntax coordinate.  They are independent of the selected disjunct and of
the proof object carried by that disjunct.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAHybridDisjunctionGeneralContextBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAHybridConnectiveTransparentBounds

def hybridDisjunctionGeneralPayloadEnvelope
    (resource childResource : Nat) : Nat :=
  childResource + 2 * generalContextAssemblyEnvelope resource

theorem disjunctionFullAssemblyCost_le_general
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (left right : LO.FirstOrder.ArithmeticProposition)
    (resource : Nat)
    (hresource : 1 <= resource)
    (hGamma : formulaCodeSum Gamma <= resource)
    (hleft : (binaryFormulaCode left).length <= resource)
    (hright : (binaryFormulaCode right).length <= resource)
    (hdisjunction : (binaryFormulaCode (left ⋎ right)).length <= resource) :
    disjunctionFullAssemblyCost Gamma left right <=
      generalContextAssemblyEnvelope resource := by
  have hrootSum :
      formulaCodeSum (insert (left ⋎ right) Gamma) <=
        generalContextCoordinate resource := by
    have hraw := formulaCodeSum_insert_le Gamma (left ⋎ right)
    unfold generalContextCoordinate
    omega
  have hbothSum :
      formulaCodeSum (insert left (insert right (insert (left ⋎ right) Gamma))) <=
        generalContextCoordinate resource := by
    have hfirst := formulaCodeSum_insert_le Gamma (left ⋎ right)
    have hsecond := formulaCodeSum_insert_le (insert (left ⋎ right) Gamma) right
    have hthird := formulaCodeSum_insert_le
      (insert right (insert (left ⋎ right) Gamma)) left
    unfold generalContextCoordinate
    omega
  have hroot := binarySequentCode_length_le_general
    (insert (left ⋎ right) Gamma) resource hrootSum
  have hboth := binarySequentCode_length_le_general
    (insert left (insert right (insert (left ⋎ right) Gamma))) resource
      hbothSum
  have hcoordinate : resource <= generalContextCoordinate resource := by
    unfold generalContextCoordinate
    omega
  have htag4 : (binaryNatCode 4).length <= 32 := by decide
  have htag7 : (binaryNatCode 7).length <= 32 := by decide
  unfold disjunctionFullAssemblyCost disjunctionDerivationCost
    generalContextAssemblyEnvelope
  dsimp only
  omega

theorem transparentHybridDisjunctionLeftPayloadEnvelope_le_general
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (childResource resource : Nat)
    (hresource : 1 <= resource)
    (hcontext : formulaCodeSum
      (valuationContext (left ⋎ right).freeVariables valuation) <= resource)
    (hleft : (binaryFormulaCode left).length <= resource)
    (hright : (binaryFormulaCode right).length <= resource)
    (hdisjunction : (binaryFormulaCode (left ⋎ right)).length <= resource) :
    transparentHybridDisjunctionLeftPayloadEnvelope valuation left right
        childResource <=
      hybridDisjunctionGeneralPayloadEnvelope resource childResource := by
  let Gamma := valuationContext (left ⋎ right).freeVariables valuation
  have hinsert : formulaCodeSum (insert left Gamma) <=
      generalContextCoordinate resource := by
    have hraw := formulaCodeSum_insert_le Gamma left
    dsimp only [Gamma] at hraw ⊢
    unfold generalContextCoordinate
    omega
  have hweak := weakeningFullAssemblyCost_le_general
    (insert left Gamma) resource hinsert
  have hdisjunctionCost := disjunctionFullAssemblyCost_le_general Gamma left
    right resource hresource hcontext hleft hright hdisjunction
  unfold transparentHybridDisjunctionLeftPayloadEnvelope
    hybridDisjunctionGeneralPayloadEnvelope
  dsimp only [Gamma] at hweak hdisjunctionCost ⊢
  omega

theorem transparentHybridDisjunctionRightPayloadEnvelope_le_general
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (childResource resource : Nat)
    (hresource : 1 <= resource)
    (hcontext : formulaCodeSum
      (valuationContext (left ⋎ right).freeVariables valuation) <= resource)
    (hleft : (binaryFormulaCode left).length <= resource)
    (hright : (binaryFormulaCode right).length <= resource)
    (hdisjunction : (binaryFormulaCode (left ⋎ right)).length <= resource) :
    transparentHybridDisjunctionRightPayloadEnvelope valuation left right
        childResource <=
      hybridDisjunctionGeneralPayloadEnvelope resource childResource := by
  let Gamma := valuationContext (left ⋎ right).freeVariables valuation
  have hinsert : formulaCodeSum (insert right Gamma) <=
      generalContextCoordinate resource := by
    have hraw := formulaCodeSum_insert_le Gamma right
    dsimp only [Gamma] at hraw ⊢
    unfold generalContextCoordinate
    omega
  have hweak := weakeningFullAssemblyCost_le_general
    (insert right Gamma) resource hinsert
  have hdisjunctionCost := disjunctionFullAssemblyCost_le_general Gamma left
    right resource hresource hcontext hleft hright hdisjunction
  unfold transparentHybridDisjunctionRightPayloadEnvelope
    hybridDisjunctionGeneralPayloadEnvelope
  dsimp only [Gamma] at hweak hdisjunctionCost ⊢
  omega

#print axioms disjunctionFullAssemblyCost_le_general
#print axioms transparentHybridDisjunctionLeftPayloadEnvelope_le_general
#print axioms transparentHybridDisjunctionRightPayloadEnvelope_le_general

end FoundationCompactPAHybridDisjunctionGeneralContextBounds
