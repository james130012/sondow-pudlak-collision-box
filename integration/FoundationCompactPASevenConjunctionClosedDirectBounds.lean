import integration.FoundationCompactPAHybridSixConjunctionClosedGeneralBounds
import integration.FoundationCompactPADirectConnectiveTransparentBounds

/-! # Closed direct assembly of seven right-associated conjunction leaves -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactPASevenConjunctionClosedDirectBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridSixConjunctionClosedGeneralBounds

def sevenConjunctionClosedDirectPayloadEnvelope
    (syntaxResource resource1 resource2 resource3 resource4 resource5
      resource6 resource7 : Nat) : Nat :=
  hybridSixConjunctionGeneralPayloadEnvelope syntaxResource resource1 resource2
    resource3 resource4 resource5
    (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource6
      resource7)

noncomputable def sevenConjunctionClosedDirectBound
    (valuation : Nat -> Nat)
    (formula1 formula2 formula3 formula4 formula5 formula6 formula7 :
      ValuationFormula)
    (resource1 resource2 resource3 resource4 resource5 resource6 resource7
      syntaxResource : Nat)
    (proof1 : CertifiedPAContextProof ∅ formula1)
    (proof2 : CertifiedPAContextProof ∅ formula2)
    (proof3 : CertifiedPAContextProof ∅ formula3)
    (proof4 : CertifiedPAContextProof ∅ formula4)
    (proof5 : CertifiedPAContextProof ∅ formula5)
    (proof6 : CertifiedPAContextProof ∅ formula6)
    (proof7 : CertifiedPAContextProof ∅ formula7)
    (hproof1 : proof1.payloadLength <= resource1)
    (hproof2 : proof2.payloadLength <= resource2)
    (hproof3 : proof3.payloadLength <= resource3)
    (hproof4 : proof4.payloadLength <= resource4)
    (hproof5 : proof5.payloadLength <= resource5)
    (hproof6 : proof6.payloadLength <= resource6)
    (hproof7 : proof7.payloadLength <= resource7)
    (hclosed1 : formula1.freeVariables = ∅)
    (hclosed2 : formula2.freeVariables = ∅)
    (hclosed3 : formula3.freeVariables = ∅)
    (hclosed4 : formula4.freeVariables = ∅)
    (hclosed5 : formula5.freeVariables = ∅)
    (hclosed6 : formula6.freeVariables = ∅)
    (hclosed7 : formula7.freeVariables = ∅)
    (hcode6 : (binaryFormulaCode formula6).length <= syntaxResource)
    (hcode7 : (binaryFormulaCode formula7).length <= syntaxResource)
    (hcode67 : (binaryFormulaCode (formula6 ⋏ formula7)).length <=
      syntaxResource)
    (hfullCode :
      (binaryFormulaCode
        (formula1 ⋏
          (formula2 ⋏
            (formula3 ⋏
              (formula4 ⋏ (formula5 ⋏ (formula6 ⋏ formula7))))))).length <=
        syntaxResource)
    (hpositive : 1 <= syntaxResource) :
    ExplicitDirectFormulaBound valuation
      (formula1 ⋏
        (formula2 ⋏
          (formula3 ⋏
            (formula4 ⋏ (formula5 ⋏ (formula6 ⋏ formula7))))))
      (sevenConjunctionClosedDirectPayloadEnvelope syntaxResource resource1
        resource2 resource3 resource4 resource5 resource6 resource7) := by
  let direct1 : CertifiedPAContextProof
      (valuationContext formula1.freeVariables valuation) formula1 :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed1]
      simp [valuationContext]) proof1
  let direct2 : CertifiedPAContextProof
      (valuationContext formula2.freeVariables valuation) formula2 :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed2]
      simp [valuationContext]) proof2
  let direct3 : CertifiedPAContextProof
      (valuationContext formula3.freeVariables valuation) formula3 :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed3]
      simp [valuationContext]) proof3
  let direct4 : CertifiedPAContextProof
      (valuationContext formula4.freeVariables valuation) formula4 :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed4]
      simp [valuationContext]) proof4
  let direct5 : CertifiedPAContextProof
      (valuationContext formula5.freeVariables valuation) formula5 :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed5]
      simp [valuationContext]) proof5
  let direct6 : CertifiedPAContextProof
      (valuationContext formula6.freeVariables valuation) formula6 :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed6]
      simp [valuationContext]) proof6
  let direct7 : CertifiedPAContextProof
      (valuationContext formula7.freeVariables valuation) formula7 :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed7]
      simp [valuationContext]) proof7
  have hdirect1 : direct1.payloadLength <= resource1 := by
    rw [show direct1.payloadLength = proof1.payloadLength by
      exact CertifiedPAContextProof.castContext_payloadLength _ _]
    exact hproof1
  have hdirect2 : direct2.payloadLength <= resource2 := by
    rw [show direct2.payloadLength = proof2.payloadLength by
      exact CertifiedPAContextProof.castContext_payloadLength _ _]
    exact hproof2
  have hdirect3 : direct3.payloadLength <= resource3 := by
    rw [show direct3.payloadLength = proof3.payloadLength by
      exact CertifiedPAContextProof.castContext_payloadLength _ _]
    exact hproof3
  have hdirect4 : direct4.payloadLength <= resource4 := by
    rw [show direct4.payloadLength = proof4.payloadLength by
      exact CertifiedPAContextProof.castContext_payloadLength _ _]
    exact hproof4
  have hdirect5 : direct5.payloadLength <= resource5 := by
    rw [show direct5.payloadLength = proof5.payloadLength by
      exact CertifiedPAContextProof.castContext_payloadLength _ _]
    exact hproof5
  have hdirect6 : direct6.payloadLength <= resource6 := by
    rw [show direct6.payloadLength = proof6.payloadLength by
      exact CertifiedPAContextProof.castContext_payloadLength _ _]
    exact hproof6
  have hdirect7 : direct7.payloadLength <= resource7 := by
    rw [show direct7.payloadLength = proof7.payloadLength by
      exact CertifiedPAContextProof.castContext_payloadLength _ _]
    exact hproof7
  let resource67 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    resource6 resource7
  let direct67 := compileDirectConjunction direct6 direct7
  have hdirect67Raw := compileDirectConjunction_payloadLength_le direct6
    direct7 resource6 resource7 hdirect6 hdirect7
  have hpairGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula6 formula7 resource6 resource7 syntaxResource hpositive hclosed6
      hclosed7 hcode6 hcode7 hcode67
  have hdirect67 : direct67.payloadLength <= resource67 := by
    simpa only [direct67, resource67] using hdirect67Raw.trans hpairGeneral
  let direct567 := compileDirectConjunction direct5 direct67
  have hdirect567 := compileDirectConjunction_payloadLength_le direct5 direct67
    resource5 resource67 hdirect5 hdirect67
  let direct4567 := compileDirectConjunction direct4 direct567
  have hdirect4567 := compileDirectConjunction_payloadLength_le direct4
    direct567 resource4
    (transparentHybridConjunctionPayloadEnvelope valuation formula5
      (formula6 ⋏ formula7) resource5 resource67)
    hdirect4 (by simpa only [direct567] using hdirect567)
  let direct34567 := compileDirectConjunction direct3 direct4567
  have hdirect34567 := compileDirectConjunction_payloadLength_le direct3
    direct4567 resource3
    (transparentHybridConjunctionPayloadEnvelope valuation formula4
      (formula5 ⋏ (formula6 ⋏ formula7)) resource4
      (transparentHybridConjunctionPayloadEnvelope valuation formula5
        (formula6 ⋏ formula7) resource5 resource67))
    hdirect3 (by simpa only [direct4567] using hdirect4567)
  let direct234567 := compileDirectConjunction direct2 direct34567
  have hdirect234567 := compileDirectConjunction_payloadLength_le direct2
    direct34567 resource2
    (transparentHybridConjunctionPayloadEnvelope valuation formula3
      (formula4 ⋏ (formula5 ⋏ (formula6 ⋏ formula7))) resource3
      (transparentHybridConjunctionPayloadEnvelope valuation formula4
        (formula5 ⋏ (formula6 ⋏ formula7)) resource4
        (transparentHybridConjunctionPayloadEnvelope valuation formula5
          (formula6 ⋏ formula7) resource5 resource67)))
    hdirect2 (by simpa only [direct34567] using hdirect34567)
  let assembled := compileDirectConjunction direct1 direct234567
  have hassembled := compileDirectConjunction_payloadLength_le direct1
    direct234567 resource1
    (transparentHybridConjunctionPayloadEnvelope valuation formula2
      (formula3 ⋏ (formula4 ⋏ (formula5 ⋏ (formula6 ⋏ formula7)))) resource2
      (transparentHybridConjunctionPayloadEnvelope valuation formula3
        (formula4 ⋏ (formula5 ⋏ (formula6 ⋏ formula7))) resource3
        (transparentHybridConjunctionPayloadEnvelope valuation formula4
          (formula5 ⋏ (formula6 ⋏ formula7)) resource4
          (transparentHybridConjunctionPayloadEnvelope valuation formula5
            (formula6 ⋏ formula7) resource5 resource67))))
    hdirect1 (by simpa only [direct234567] using hdirect234567)
  have hclosed67 : (formula6 ⋏ formula7).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hclosed6, hclosed7]
    simp
  have hgeneral :=
    transparentHybridSixConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula1 formula2 formula3 formula4 formula5 (formula6 ⋏ formula7)
      resource1 resource2 resource3 resource4 resource5 resource67
      syntaxResource hpositive hclosed1 hclosed2 hclosed3 hclosed4 hclosed5
      hclosed67 hfullCode
  refine ⟨assembled, ?_⟩
  unfold sevenConjunctionClosedDirectPayloadEnvelope
  simpa only [resource67] using hassembled.trans hgeneral

end FoundationCompactPASevenConjunctionClosedDirectBounds
