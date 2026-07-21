import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Transparent bounds for direct propositional proof assembly

These constructors combine already compiled contextual PA proofs.  Their
resource envelopes expose both child bounds and every weakening/connective
assembly cost.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option Elab.async false

namespace FoundationCompactPADirectConnectiveTransparentBounds

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds

structure ExplicitDirectFormulaBound
    (valuation : Nat -> Nat) (formula : ValuationFormula)
    (resource : Nat) where
  proof : CertifiedPAContextProof
    (valuationContext formula.freeVariables valuation) formula
  payloadLength_le : proof.payloadLength ≤ resource

noncomputable def compileDirectConjunction
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (leftProof : CertifiedPAContextProof
      (valuationContext left.freeVariables valuation) left)
    (rightProof : CertifiedPAContextProof
      (valuationContext right.freeVariables valuation) right) :
    CertifiedPAContextProof
      (valuationContext (left ⋏ right).freeVariables valuation)
      (left ⋏ right) := by
  let Gamma := valuationContext (left ⋏ right).freeVariables valuation
  have hleft : left.freeVariables ⊆ (left ⋏ right).freeVariables := by
    simp
  have hright : right.freeVariables ⊆ (left ⋏ right).freeVariables := by
    simp
  let leftAtTarget := CertifiedPAContextProof.weakenContext leftProof
    (valuationContext_mono valuation hleft)
  let rightAtTarget := CertifiedPAContextProof.weakenContext rightProof
    (valuationContext_mono valuation hright)
  exact CertifiedPAContextProof.conjunction leftAtTarget rightAtTarget

theorem compileDirectConjunction_payloadLength_le
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (leftProof : CertifiedPAContextProof
      (valuationContext left.freeVariables valuation) left)
    (rightProof : CertifiedPAContextProof
      (valuationContext right.freeVariables valuation) right)
    (leftResource rightResource : Nat)
    (hleft : leftProof.payloadLength ≤ leftResource)
    (hright : rightProof.payloadLength ≤ rightResource) :
    (compileDirectConjunction leftProof rightProof).payloadLength ≤
      transparentHybridConjunctionPayloadEnvelope valuation left right
        leftResource rightResource := by
  let Gamma := valuationContext (left ⋏ right).freeVariables valuation
  have hleftVariables : left.freeVariables ⊆
      (left ⋏ right).freeVariables := by simp
  have hrightVariables : right.freeVariables ⊆
      (left ⋏ right).freeVariables := by simp
  let leftAtTarget := CertifiedPAContextProof.weakenContext leftProof
    (valuationContext_mono valuation hleftVariables)
  let rightAtTarget := CertifiedPAContextProof.weakenContext rightProof
    (valuationContext_mono valuation hrightVariables)
  have hleftWeak := CertifiedPAContextProof.weakenContext_payloadLength_le
    leftProof (valuationContext_mono valuation hleftVariables)
  have hrightWeak := CertifiedPAContextProof.weakenContext_payloadLength_le
    rightProof (valuationContext_mono valuation hrightVariables)
  have hleftAtTarget : leftAtTarget.payloadLength ≤
      leftResource + weakeningFullAssemblyCost (insert left Gamma) :=
    hleftWeak.trans (Nat.add_le_add_right hleft _)
  have hrightAtTarget : rightAtTarget.payloadLength ≤
      rightResource + weakeningFullAssemblyCost (insert right Gamma) :=
    hrightWeak.trans (Nat.add_le_add_right hright _)
  have hconjunction := CertifiedPAContextProof.conjunction_payloadLength_le
    leftAtTarget rightAtTarget
  have hfinal : (CertifiedPAContextProof.conjunction
      leftAtTarget rightAtTarget).payloadLength ≤
      transparentHybridConjunctionPayloadEnvelope valuation left right
        leftResource rightResource := by
    unfold transparentHybridConjunctionPayloadEnvelope
    dsimp only [Gamma] at hleftAtTarget hrightAtTarget hconjunction ⊢
    omega
  simpa only [compileDirectConjunction] using hfinal

noncomputable def compileDirectDisjunctionLeft
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (leftProof : CertifiedPAContextProof
      (valuationContext left.freeVariables valuation) left) :
    CertifiedPAContextProof
      (valuationContext (left ⋎ right).freeVariables valuation)
      (left ⋎ right) := by
  have hleft : left.freeVariables ⊆ (left ⋎ right).freeVariables := by
    simp
  let leftAtTarget := CertifiedPAContextProof.weakenContext leftProof
    (valuationContext_mono valuation hleft)
  exact CertifiedPAContextProof.disjunctionLeft leftAtTarget

theorem compileDirectDisjunctionLeft_payloadLength_le
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (leftProof : CertifiedPAContextProof
      (valuationContext left.freeVariables valuation) left)
    (leftResource : Nat)
    (hleft : leftProof.payloadLength ≤ leftResource) :
    (compileDirectDisjunctionLeft (right := right) leftProof).payloadLength ≤
      transparentHybridDisjunctionLeftPayloadEnvelope valuation left right
        leftResource := by
  let Gamma := valuationContext (left ⋎ right).freeVariables valuation
  have hvariables : left.freeVariables ⊆
      (left ⋎ right).freeVariables := by simp
  let leftAtTarget := CertifiedPAContextProof.weakenContext leftProof
    (valuationContext_mono valuation hvariables)
  have hweak := CertifiedPAContextProof.weakenContext_payloadLength_le
    leftProof (valuationContext_mono valuation hvariables)
  have hleftAtTarget : leftAtTarget.payloadLength ≤
      leftResource + weakeningFullAssemblyCost (insert left Gamma) :=
    hweak.trans (Nat.add_le_add_right hleft _)
  have hdisjunction :=
    CertifiedPAContextProof.disjunctionLeft_payloadLength_le
      (right := right) leftAtTarget
  have hfinal : (CertifiedPAContextProof.disjunctionLeft
      (right := right) leftAtTarget).payloadLength ≤
      transparentHybridDisjunctionLeftPayloadEnvelope valuation left right
        leftResource := by
    unfold transparentHybridDisjunctionLeftPayloadEnvelope
    dsimp only [Gamma] at hleftAtTarget hdisjunction ⊢
    omega
  simpa only [compileDirectDisjunctionLeft] using hfinal

noncomputable def compileDirectDisjunctionRight
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (rightProof : CertifiedPAContextProof
      (valuationContext right.freeVariables valuation) right) :
    CertifiedPAContextProof
      (valuationContext (left ⋎ right).freeVariables valuation)
      (left ⋎ right) := by
  have hright : right.freeVariables ⊆ (left ⋎ right).freeVariables := by
    simp
  let rightAtTarget := CertifiedPAContextProof.weakenContext rightProof
    (valuationContext_mono valuation hright)
  exact CertifiedPAContextProof.disjunctionRight rightAtTarget

theorem compileDirectDisjunctionRight_payloadLength_le
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (rightProof : CertifiedPAContextProof
      (valuationContext right.freeVariables valuation) right)
    (rightResource : Nat)
    (hright : rightProof.payloadLength ≤ rightResource) :
    (compileDirectDisjunctionRight (left := left) rightProof).payloadLength ≤
      transparentHybridDisjunctionRightPayloadEnvelope valuation left right
        rightResource := by
  let Gamma := valuationContext (left ⋎ right).freeVariables valuation
  have hvariables : right.freeVariables ⊆
      (left ⋎ right).freeVariables := by simp
  let rightAtTarget := CertifiedPAContextProof.weakenContext rightProof
    (valuationContext_mono valuation hvariables)
  have hweak := CertifiedPAContextProof.weakenContext_payloadLength_le
    rightProof (valuationContext_mono valuation hvariables)
  have hrightAtTarget : rightAtTarget.payloadLength ≤
      rightResource + weakeningFullAssemblyCost (insert right Gamma) :=
    hweak.trans (Nat.add_le_add_right hright _)
  have hdisjunction :=
    CertifiedPAContextProof.disjunctionRight_payloadLength_le
      (left := left) rightAtTarget
  have hfinal : (CertifiedPAContextProof.disjunctionRight
      (left := left) rightAtTarget).payloadLength ≤
      transparentHybridDisjunctionRightPayloadEnvelope valuation left right
        rightResource := by
    unfold transparentHybridDisjunctionRightPayloadEnvelope
    dsimp only [Gamma] at hrightAtTarget hdisjunction ⊢
    omega
  simpa only [compileDirectDisjunctionRight] using hfinal

#print axioms compileDirectConjunction_payloadLength_le
#print axioms compileDirectDisjunctionLeft_payloadLength_le
#print axioms compileDirectDisjunctionRight_payloadLength_le

end FoundationCompactPADirectConnectiveTransparentBounds
