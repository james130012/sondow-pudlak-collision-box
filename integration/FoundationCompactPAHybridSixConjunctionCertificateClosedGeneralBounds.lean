import integration.FoundationCompactPAHybridSixConjunctionClosedGeneralBounds

/-!
# Closed general bound for six checked conjunction certificates

This lifts the six-leaf transparent assembly bound to six actual checked
certificates.  It keeps large callers from repeatedly reducing the complete
right-associated certificate tree.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactPAHybridSixConjunctionCertificateClosedGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridSixConjunctionClosedGeneralBounds

theorem checkedHybridSixConjunctionPayloadBound_le_closedGeneral
    (valuation : Nat -> Nat)
    (formula1 formula2 formula3 formula4 formula5 formula6 :
      ValuationFormula)
    (certificate1 :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula1)
    (certificate2 :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula2)
    (certificate3 :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula3)
    (certificate4 :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula4)
    (certificate5 :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula5)
    (certificate6 :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula6)
    (resource1 resource2 resource3 resource4 resource5 resource6
      syntaxResource : Nat)
    (hresource1 :
      hybridFormulaStructuralPayloadBound certificate1 <= resource1)
    (hresource2 :
      hybridFormulaStructuralPayloadBound certificate2 <= resource2)
    (hresource3 :
      hybridFormulaStructuralPayloadBound certificate3 <= resource3)
    (hresource4 :
      hybridFormulaStructuralPayloadBound certificate4 <= resource4)
    (hresource5 :
      hybridFormulaStructuralPayloadBound certificate5 <= resource5)
    (hresource6 :
      hybridFormulaStructuralPayloadBound certificate6 <= resource6)
    (hpositive : 1 <= syntaxResource)
    (hclosed1 : formula1.freeVariables = ∅)
    (hclosed2 : formula2.freeVariables = ∅)
    (hclosed3 : formula3.freeVariables = ∅)
    (hclosed4 : formula4.freeVariables = ∅)
    (hclosed5 : formula5.freeVariables = ∅)
    (hclosed6 : formula6.freeVariables = ∅)
    (hcode :
      (binaryFormulaCode
        (formula1 ⋏
          (formula2 ⋏
            (formula3 ⋏ (formula4 ⋏ (formula5 ⋏ formula6)))))).length <=
        syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          certificate1
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            certificate2
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              certificate3
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                certificate4
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  certificate5 certificate6))))) <=
      hybridSixConjunctionGeneralPayloadEnvelope syntaxResource resource1
        resource2 resource3 resource4 resource5 resource6 := by
  let tail56 :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction certificate5
      certificate6
  let tail456 :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction certificate4
      tail56
  let tail3456 :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction certificate3
      tail456
  let tail23456 :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction certificate2
      tail3456
  have h56 := transparentHybridConjunctionPayloadBound_le certificate5
    certificate6 _ _ hresource5 hresource6
  have h456 := transparentHybridConjunctionPayloadBound_le certificate4
    tail56 _ _ hresource4 h56
  have h3456 := transparentHybridConjunctionPayloadBound_le certificate3
    tail456 _ _ hresource3 h456
  have h23456 := transparentHybridConjunctionPayloadBound_le certificate2
    tail3456 _ _ hresource2 h3456
  have hall := transparentHybridConjunctionPayloadBound_le certificate1
    tail23456 _ _ hresource1 h23456
  have hassembly :=
    transparentHybridSixConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula1 formula2 formula3 formula4 formula5 formula6 resource1
      resource2 resource3 resource4 resource5 resource6 syntaxResource
      hpositive hclosed1 hclosed2 hclosed3 hclosed4 hclosed5 hclosed6 hcode
  exact hall.trans hassembly

#print axioms checkedHybridSixConjunctionPayloadBound_le_closedGeneral

end FoundationCompactPAHybridSixConjunctionCertificateClosedGeneralBounds
