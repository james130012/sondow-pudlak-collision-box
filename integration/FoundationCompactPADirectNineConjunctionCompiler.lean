import integration.FoundationCompactPADirectConnectiveTransparentBounds

/-! # Direct compiler for nine right-associated conjunction leaves -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactPADirectNineConjunctionCompiler

open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPADirectConnectiveTransparentBounds

noncomputable def compileDirectNineConjunction
    {valuation : Nat -> Nat}
    {formula1 formula2 formula3 formula4 formula5 formula6 formula7 formula8
      formula9 : ValuationFormula}
    (proof1 : CertifiedPAContextProof
      (valuationContext formula1.freeVariables valuation) formula1)
    (proof2 : CertifiedPAContextProof
      (valuationContext formula2.freeVariables valuation) formula2)
    (proof3 : CertifiedPAContextProof
      (valuationContext formula3.freeVariables valuation) formula3)
    (proof4 : CertifiedPAContextProof
      (valuationContext formula4.freeVariables valuation) formula4)
    (proof5 : CertifiedPAContextProof
      (valuationContext formula5.freeVariables valuation) formula5)
    (proof6 : CertifiedPAContextProof
      (valuationContext formula6.freeVariables valuation) formula6)
    (proof7 : CertifiedPAContextProof
      (valuationContext formula7.freeVariables valuation) formula7)
    (proof8 : CertifiedPAContextProof
      (valuationContext formula8.freeVariables valuation) formula8)
    (proof9 : CertifiedPAContextProof
      (valuationContext formula9.freeVariables valuation) formula9) :
    CertifiedPAContextProof
      (valuationContext
        (formula1 ⋏
          (formula2 ⋏
            (formula3 ⋏
              (formula4 ⋏
                (formula5 ⋏
                  (formula6 ⋏
                    (formula7 ⋏ (formula8 ⋏ formula9)))))))).freeVariables
        valuation)
      (formula1 ⋏
        (formula2 ⋏
          (formula3 ⋏
            (formula4 ⋏
              (formula5 ⋏
                (formula6 ⋏
                  (formula7 ⋏ (formula8 ⋏ formula9)))))))) :=
  compileDirectConjunction proof1
    (compileDirectConjunction proof2
      (compileDirectConjunction proof3
        (compileDirectConjunction proof4
          (compileDirectConjunction proof5
            (compileDirectConjunction proof6
              (compileDirectConjunction proof7
                (compileDirectConjunction proof8 proof9)))))))

def directNineConjunctionTransparentPayloadEnvelope
    (valuation : Nat -> Nat)
    (formula1 formula2 formula3 formula4 formula5 formula6 formula7 formula8
      formula9 : ValuationFormula)
    (resource1 resource2 resource3 resource4 resource5 resource6 resource7
      resource8 resource9 : Nat) : Nat :=
  let tail89 := transparentHybridConjunctionPayloadEnvelope valuation formula8
    formula9 resource8 resource9
  let tail789 := transparentHybridConjunctionPayloadEnvelope valuation formula7
    (formula8 ⋏ formula9) resource7 tail89
  let tail6789 := transparentHybridConjunctionPayloadEnvelope valuation formula6
    (formula7 ⋏ (formula8 ⋏ formula9)) resource6 tail789
  let tail56789 := transparentHybridConjunctionPayloadEnvelope valuation formula5
    (formula6 ⋏ (formula7 ⋏ (formula8 ⋏ formula9))) resource5 tail6789
  let tail456789 := transparentHybridConjunctionPayloadEnvelope valuation
    formula4
    (formula5 ⋏ (formula6 ⋏ (formula7 ⋏ (formula8 ⋏ formula9))))
    resource4 tail56789
  let tail3456789 := transparentHybridConjunctionPayloadEnvelope valuation
    formula3
    (formula4 ⋏
      (formula5 ⋏ (formula6 ⋏ (formula7 ⋏ (formula8 ⋏ formula9)))))
    resource3 tail456789
  let tail23456789 := transparentHybridConjunctionPayloadEnvelope valuation
    formula2
    (formula3 ⋏
      (formula4 ⋏
        (formula5 ⋏ (formula6 ⋏ (formula7 ⋏ (formula8 ⋏ formula9))))))
    resource2 tail3456789
  transparentHybridConjunctionPayloadEnvelope valuation formula1
    (formula2 ⋏
      (formula3 ⋏
        (formula4 ⋏
          (formula5 ⋏
            (formula6 ⋏ (formula7 ⋏ (formula8 ⋏ formula9)))))))
    resource1 tail23456789

theorem compileDirectNineConjunction_payloadLength_le_transparent
    {valuation : Nat -> Nat}
    {formula1 formula2 formula3 formula4 formula5 formula6 formula7 formula8
      formula9 : ValuationFormula}
    (proof1 : CertifiedPAContextProof
      (valuationContext formula1.freeVariables valuation) formula1)
    (proof2 : CertifiedPAContextProof
      (valuationContext formula2.freeVariables valuation) formula2)
    (proof3 : CertifiedPAContextProof
      (valuationContext formula3.freeVariables valuation) formula3)
    (proof4 : CertifiedPAContextProof
      (valuationContext formula4.freeVariables valuation) formula4)
    (proof5 : CertifiedPAContextProof
      (valuationContext formula5.freeVariables valuation) formula5)
    (proof6 : CertifiedPAContextProof
      (valuationContext formula6.freeVariables valuation) formula6)
    (proof7 : CertifiedPAContextProof
      (valuationContext formula7.freeVariables valuation) formula7)
    (proof8 : CertifiedPAContextProof
      (valuationContext formula8.freeVariables valuation) formula8)
    (proof9 : CertifiedPAContextProof
      (valuationContext formula9.freeVariables valuation) formula9)
    (resource1 resource2 resource3 resource4 resource5 resource6 resource7
      resource8 resource9 : Nat)
    (hresource1 : proof1.payloadLength <= resource1)
    (hresource2 : proof2.payloadLength <= resource2)
    (hresource3 : proof3.payloadLength <= resource3)
    (hresource4 : proof4.payloadLength <= resource4)
    (hresource5 : proof5.payloadLength <= resource5)
    (hresource6 : proof6.payloadLength <= resource6)
    (hresource7 : proof7.payloadLength <= resource7)
    (hresource8 : proof8.payloadLength <= resource8)
    (hresource9 : proof9.payloadLength <= resource9) :
    (compileDirectNineConjunction proof1 proof2 proof3 proof4 proof5 proof6
      proof7 proof8 proof9).payloadLength <=
      directNineConjunctionTransparentPayloadEnvelope valuation formula1
        formula2 formula3 formula4 formula5 formula6 formula7 formula8 formula9
        resource1 resource2 resource3 resource4 resource5 resource6 resource7
        resource8 resource9 := by
  let tail89 := compileDirectConjunction proof8 proof9
  have h89 := compileDirectConjunction_payloadLength_le proof8 proof9
    resource8 resource9 hresource8 hresource9
  let tail789 := compileDirectConjunction proof7 tail89
  have h789 := compileDirectConjunction_payloadLength_le proof7 tail89
    resource7
    (transparentHybridConjunctionPayloadEnvelope valuation formula8 formula9
      resource8 resource9) hresource7 h89
  let tail6789 := compileDirectConjunction proof6 tail789
  have h6789 := compileDirectConjunction_payloadLength_le proof6 tail789
    resource6
    (transparentHybridConjunctionPayloadEnvelope valuation formula7
      (formula8 ⋏ formula9) resource7
      (transparentHybridConjunctionPayloadEnvelope valuation formula8 formula9
        resource8 resource9)) hresource6 h789
  let tail56789 := compileDirectConjunction proof5 tail6789
  have h56789 := compileDirectConjunction_payloadLength_le proof5 tail6789
    resource5 _ hresource5 h6789
  let tail456789 := compileDirectConjunction proof4 tail56789
  have h456789 := compileDirectConjunction_payloadLength_le proof4 tail56789
    resource4 _ hresource4 h56789
  let tail3456789 := compileDirectConjunction proof3 tail456789
  have h3456789 := compileDirectConjunction_payloadLength_le proof3 tail456789
    resource3 _ hresource3 h456789
  let tail23456789 := compileDirectConjunction proof2 tail3456789
  have h23456789 := compileDirectConjunction_payloadLength_le proof2
    tail3456789 resource2 _ hresource2 h3456789
  have htotal := compileDirectConjunction_payloadLength_le proof1
    tail23456789 resource1 _ hresource1 h23456789
  simpa only [compileDirectNineConjunction,
    directNineConjunctionTransparentPayloadEnvelope, tail89, tail789,
    tail6789, tail56789, tail456789, tail3456789, tail23456789] using htotal

end FoundationCompactPADirectNineConjunctionCompiler
