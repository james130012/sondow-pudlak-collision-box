import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Transparent structural bounds for hybrid propositional connectives

These envelopes expose exactly the two child resources and the generated
weakening/connective assembly costs.  They contain no proof object.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option Elab.async false

namespace FoundationCompactPAHybridConnectiveTransparentBounds

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate

def transparentHybridConjunctionPayloadEnvelope
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (leftResource rightResource : Nat) : Nat :=
  let Gamma := valuationContext (left ⋏ right).freeVariables valuation
  leftResource + weakeningFullAssemblyCost (insert left Gamma) +
    rightResource + weakeningFullAssemblyCost (insert right Gamma) +
    conjunctionFullAssemblyCost Gamma left right

theorem transparentHybridConjunctionPayloadBound_le
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (leftCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation left)
    (rightCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation right)
    (leftResource rightResource : Nat)
    (hleft : hybridFormulaStructuralPayloadBound leftCertificate <=
      leftResource)
    (hright : hybridFormulaStructuralPayloadBound rightCertificate <=
      rightResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          leftCertificate rightCertificate) <=
      transparentHybridConjunctionPayloadEnvelope valuation left right
        leftResource rightResource := by
  simp only [hybridFormulaStructuralPayloadBound]
  unfold transparentHybridConjunctionPayloadEnvelope
  dsimp only
  omega

def transparentHybridDisjunctionLeftPayloadEnvelope
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (leftResource : Nat) : Nat :=
  let Gamma := valuationContext (left ⋎ right).freeVariables valuation
  leftResource + weakeningFullAssemblyCost (insert left Gamma) +
    disjunctionFullAssemblyCost Gamma left right

theorem transparentHybridDisjunctionLeftPayloadBound_le
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (leftCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation left)
    (leftResource : Nat)
    (hleft : hybridFormulaStructuralPayloadBound leftCertificate <=
      leftResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := right) leftCertificate) <=
      transparentHybridDisjunctionLeftPayloadEnvelope valuation left right
        leftResource := by
  simp only [hybridFormulaStructuralPayloadBound]
  unfold transparentHybridDisjunctionLeftPayloadEnvelope
  dsimp only
  omega

def transparentHybridDisjunctionRightPayloadEnvelope
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (rightResource : Nat) : Nat :=
  let Gamma := valuationContext (left ⋎ right).freeVariables valuation
  rightResource + weakeningFullAssemblyCost (insert right Gamma) +
    disjunctionFullAssemblyCost Gamma left right

theorem transparentHybridDisjunctionRightPayloadBound_le
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (rightCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation right)
    (rightResource : Nat)
    (hright : hybridFormulaStructuralPayloadBound rightCertificate <=
      rightResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := left) rightCertificate) <=
      transparentHybridDisjunctionRightPayloadEnvelope valuation left right
        rightResource := by
  simp only [hybridFormulaStructuralPayloadBound]
  unfold transparentHybridDisjunctionRightPayloadEnvelope
  dsimp only
  omega

#print axioms transparentHybridConjunctionPayloadBound_le
#print axioms transparentHybridDisjunctionLeftPayloadBound_le
#print axioms transparentHybridDisjunctionRightPayloadBound_le

end FoundationCompactPAHybridConnectiveTransparentBounds
